--!native
--[[
	A Luau port of mapbox/delaunator (https://github.com/mapbox/delaunator)
	ISC License, Copyright (c) 2026, Mapbox (see LICENSE).

	Differences from the JavaScript library:
	- Point ids and halfedge ids are 1-based; -1 still means "no neighbour". The triangle a
	  halfedge belongs to is identified by its first halfedge (1, 4, 7, ...).
	- The in-circle test is robust (robust-predicates' incircle) rather than plain floating point.
]]

local RobustPredicates = require("./RobustPredicates")

local orient2d = RobustPredicates.orient2d
local incircle = RobustPredicates.incircle

local EPSILON = 2 ^ -52
local EDGE_LIMIT = 512
local EDGE_STACK = table.create(EDGE_LIMIT) :: { number }

local Delaunator = {}
Delaunator.__index = Delaunator

export type Delaunator = typeof(setmetatable(
	{} :: {
		-- Flat point coordinates: x1, y1, x2, y2, ...
		coords: { number },
		-- Point ids, three per triangle.
		triangles: { number },
		-- The twin of each halfedge in the adjacent triangle, or -1 on the hull.
		halfedges: { number },
		-- Point ids on the convex hull.
		hull: { number },
		trianglesLen: number,

		_triangles: { number },
		_halfedges: { number },
		_hashSize: number,
		_hullPrev: { number },
		_hullNext: { number },
		_hullTri: { number },
		_hullHash: { [number]: number },
		_hullStart: number,
		_ids: { number },
		_dists: { number },
		_cx: number,
		_cy: number,
	},
	Delaunator
))

local function defaultGetX(p: any): number
	return p[1]
end

local function defaultGetY(p: any): number
	return p[2]
end

-- Triangulates an array of points, reading each one's coordinates with getX and getY
-- (by default p[1] and p[2]).
function Delaunator.from<T>(points: { T }, getX: ((T) -> number)?, getY: ((T) -> number)?): Delaunator
	local readX, readY = getX or defaultGetX, getY or defaultGetY
	local n = #points
	local coords = table.create(n * 2)

	for i = 1, n do
		local p = points[i]
		coords[2 * i - 1] = readX(p)
		coords[2 * i] = readY(p)
	end

	return Delaunator.new(coords)
end

function Delaunator.new(coords: { number }): Delaunator
	local n = #coords // 2
	if n > 0 and type(coords[1]) ~= "number" then error("Expected coords to contain numbers.") end

	-- arrays that will store the triangulation graph
	local maxTriangles = math.max(2 * n - 5, 0)
	local self = setmetatable({
		coords = coords,
		triangles = {},
		halfedges = {},
		hull = {},
		trianglesLen = 0,

		_triangles = table.create(maxTriangles * 3),
		_halfedges = table.create(maxTriangles * 3),

		-- temporary arrays for tracking the edges of the advancing convex hull
		_hashSize = math.ceil(math.sqrt(n)),
		_hullPrev = table.create(n), -- edge to prev edge
		_hullNext = table.create(n), -- edge to next edge
		_hullTri = table.create(n), -- edge to adjacent triangle
		_hullHash = {}, -- angular edge hash, keyed from 0
		_hullStart = 1,

		-- temporary arrays for sorting points
		_ids = table.create(n),
		_dists = table.create(n),
		_cx = 0,
		_cy = 0,
	}, Delaunator)

	self:update()

	return self
end

-- monotonically increases with real angle, but doesn't need expensive trigonometry
local function pseudoAngle(dx: number, dy: number): number
	local p = dx / (math.abs(dx) + math.abs(dy))
	return (if dy > 0 then 3 - p else 1 + p) / 4 -- [0..1]
end

local function dist(ax: number, ay: number, bx: number, by: number): number
	local dx = ax - bx
	local dy = ay - by
	return dx * dx + dy * dy
end

local function circumradius(ax: number, ay: number, bx: number, by: number, cx: number, cy: number): number
	local dx = bx - ax
	local dy = by - ay
	local ex = cx - ax
	local ey = cy - ay

	local bl = dx * dx + dy * dy
	local cl = ex * ex + ey * ey
	local d = 0.5 / (dx * ey - dy * ex)

	local x = (ey * bl - dy * cl) * d
	local y = (dx * cl - ex * bl) * d

	return x * x + y * y
end

local function circumcenter(ax: number, ay: number, bx: number, by: number, cx: number, cy: number): (number, number)
	local dx = bx - ax
	local dy = by - ay
	local ex = cx - ax
	local ey = cy - ay

	local bl = dx * dx + dy * dy
	local cl = ex * ex + ey * ey
	local d = 0.5 / (dx * ey - dy * ex)

	return ax + (ey * bl - dy * cl) * d, ay + (dx * cl - ex * bl) * d
end

local function quicksort(ids: { number }, dists: { number }, left: number, right: number)
	if right - left <= 20 then
		for i = left + 1, right do
			local temp = ids[i]
			local tempDist = dists[temp]
			local j = i - 1
			while j >= left and dists[ids[j]] > tempDist do
				ids[j + 1] = ids[j]
				j -= 1
			end
			ids[j + 1] = temp
		end
	else
		local median = (left + right) // 2
		local i = left + 1
		local j = right
		ids[i], ids[median] = ids[median], ids[i]
		if dists[ids[left]] > dists[ids[right]] then
			ids[left], ids[right] = ids[right], ids[left]
		end
		if dists[ids[i]] > dists[ids[right]] then
			ids[i], ids[right] = ids[right], ids[i]
		end
		if dists[ids[left]] > dists[ids[i]] then
			ids[left], ids[i] = ids[i], ids[left]
		end

		local temp = ids[i]
		local tempDist = dists[temp]
		while true do
			repeat
				i += 1
			until not (dists[ids[i]] < tempDist)
			repeat
				j -= 1
			until not (dists[ids[j]] > tempDist)
			if j < i then break end
			ids[i], ids[j] = ids[j], ids[i]
		end
		ids[left + 1] = ids[j]
		ids[j] = temp

		if right - i + 1 >= j - left then
			quicksort(ids, dists, i, right)
			quicksort(ids, dists, left, j - 1)
		else
			quicksort(ids, dists, left, j - 1)
			quicksort(ids, dists, i, right)
		end
	end
end

-- Triangulates again after `coords` was changed in place (same number of points).
function Delaunator.update(self: Delaunator)
	local coords, hullPrev, hullNext, hullTri, hullHash = self.coords, self._hullPrev, self._hullNext, self._hullTri, self._hullHash
	local n = #coords // 2

	-- populate an array of point indices; calculate input data bbox
	local minX = math.huge
	local minY = math.huge
	local maxX = -math.huge
	local maxY = -math.huge

	for i = 1, n do
		local x = coords[2 * i - 1]
		local y = coords[2 * i]
		if x < minX then minX = x end
		if y < minY then minY = y end
		if x > maxX then maxX = x end
		if y > maxY then maxY = y end
		self._ids[i] = i
	end
	local cx = (minX + maxX) / 2
	local cy = (minY + maxY) / 2

	-- like upstream, the seeds default to the first point, which sends degenerate input down
	-- the collinear path below
	local i0, i1, i2 = 1, 1, 1

	-- pick a seed point close to the center
	local minDist = math.huge
	for i = 1, n do
		local d = dist(cx, cy, coords[2 * i - 1], coords[2 * i])
		if d < minDist then
			i0 = i
			minDist = d
		end
	end
	local i0x, i0y = coords[2 * i0 - 1] or 0, coords[2 * i0] or 0

	-- find the point closest to the seed
	minDist = math.huge
	for i = 1, n do
		if i == i0 then continue end
		local d = dist(i0x, i0y, coords[2 * i - 1], coords[2 * i])
		if d < minDist and d > 0 then
			i1 = i
			minDist = d
		end
	end
	local i1x, i1y = coords[2 * i1 - 1] or 0, coords[2 * i1] or 0

	local minRadius = math.huge

	-- find the third point which forms the smallest circumcircle with the first two
	for i = 1, n do
		if i == i0 or i == i1 then continue end
		local r = circumradius(i0x, i0y, i1x, i1y, coords[2 * i - 1], coords[2 * i])
		if r < minRadius then
			i2 = i
			minRadius = r
		end
	end

	if minRadius == math.huge then
		-- order collinear points by dx (or dy if all x are identical)
		-- and return the list as a hull
		for i = 1, n do
			local d = coords[2 * i - 1] - coords[1]
			self._dists[i] = if d ~= 0 then d else coords[2 * i] - coords[2]
		end
		quicksort(self._ids, self._dists, 1, n)
		local hull = table.create(n) :: { number }
		local d0 = -math.huge
		for i = 1, n do
			local id = self._ids[i]
			local d = self._dists[id]
			if d > d0 then
				table.insert(hull, id)
				d0 = d
			end
		end
		self.hull = hull
		self.triangles = {}
		self.halfedges = {}
		self.trianglesLen = 0
		return
	end

	-- swap the order of the seed points for counter-clockwise orientation
	local i2x, i2y = coords[2 * i2 - 1], coords[2 * i2]
	if orient2d(i0x, i0y, i1x, i1y, i2x, i2y) < 0 then
		i1, i2 = i2, i1
		i1x, i1y, i2x, i2y = i2x, i2y, i1x, i1y
	end

	self._cx, self._cy = circumcenter(i0x, i0y, i1x, i1y, i2x, i2y)

	for i = 1, n do
		self._dists[i] = dist(coords[2 * i - 1], coords[2 * i], self._cx, self._cy)
	end

	-- sort the points by distance from the seed triangle circumcenter
	quicksort(self._ids, self._dists, 1, n)

	-- set up the seed triangle as the starting hull
	self._hullStart = i0
	local hullSize = 3

	hullNext[i0], hullPrev[i2] = i1, i1
	hullNext[i1], hullPrev[i0] = i2, i2
	hullNext[i2], hullPrev[i1] = i0, i0

	hullTri[i0] = 1
	hullTri[i1] = 2
	hullTri[i2] = 3

	for key = 0, self._hashSize - 1 do
		hullHash[key] = -1
	end
	hullHash[self:_hashKey(i0x, i0y)] = i0
	hullHash[self:_hashKey(i1x, i1y)] = i1
	hullHash[self:_hashKey(i2x, i2y)] = i2

	self.trianglesLen = 0
	self:_addTriangle(i0, i1, i2, -1, -1, -1)

	local xp, yp = 0, 0
	for k = 1, n do
		local i = self._ids[k]
		local x = coords[2 * i - 1]
		local y = coords[2 * i]

		-- skip near-duplicate points
		if k > 1 and math.abs(x - xp) <= EPSILON and math.abs(y - yp) <= EPSILON then continue end
		xp, yp = x, y

		-- skip seed triangle points
		if i == i0 or i == i1 or i == i2 then continue end

		-- find a visible edge on the convex hull using edge hash
		local start = 1
		local key = self:_hashKey(x, y)
		for j = 0, self._hashSize - 1 do
			start = hullHash[(key + j) % self._hashSize]
			if start ~= -1 and start ~= hullNext[start] then break end
		end

		start = hullPrev[start]
		local e = start
		local q = hullNext[e]
		while orient2d(x, y, coords[2 * e - 1], coords[2 * e], coords[2 * q - 1], coords[2 * q]) >= 0 do
			e = q
			if e == start then
				e = -1
				break
			end
			q = hullNext[e]
		end
		if e == -1 then continue end -- likely a near-duplicate point; skip it

		-- add the first triangle from the point
		local t = self:_addTriangle(e, i, hullNext[e], -1, -1, hullTri[e])

		-- recursively flip triangles from the point until they satisfy the Delaunay condition
		hullTri[i] = self:_legalize(t + 2)
		hullTri[e] = t -- keep track of boundary triangles on the hull
		hullSize += 1

		-- walk forward through the hull, adding more triangles and flipping recursively
		local nxt = hullNext[e]
		q = hullNext[nxt]
		while orient2d(x, y, coords[2 * nxt - 1], coords[2 * nxt], coords[2 * q - 1], coords[2 * q]) < 0 do
			t = self:_addTriangle(nxt, i, q, hullTri[i], -1, hullTri[nxt])
			hullTri[i] = self:_legalize(t + 2)
			hullNext[nxt] = nxt -- mark as removed
			hullSize -= 1
			nxt = q
			q = hullNext[nxt]
		end

		-- walk backward from the other side, adding more triangles and flipping
		if e == start then
			q = hullPrev[e]
			while orient2d(x, y, coords[2 * q - 1], coords[2 * q], coords[2 * e - 1], coords[2 * e]) < 0 do
				t = self:_addTriangle(q, i, e, -1, hullTri[e], hullTri[q])
				self:_legalize(t + 2)
				hullTri[q] = t
				hullNext[e] = e -- mark as removed
				hullSize -= 1
				e = q
				q = hullPrev[e]
			end
		end

		-- update the hull indices
		self._hullStart, hullPrev[i] = e, e
		hullNext[e], hullPrev[nxt] = i, i
		hullNext[i] = nxt

		-- save the two new edges in the hash table
		hullHash[self:_hashKey(x, y)] = i
		hullHash[self:_hashKey(coords[2 * e - 1], coords[2 * e])] = e
	end

	local hull = table.create(hullSize) :: { number }
	local e = self._hullStart
	for i = 1, hullSize do
		hull[i] = e
		e = hullNext[e]
	end
	self.hull = hull

	-- trim the working arrays
	self.triangles = table.move(self._triangles, 1, self.trianglesLen, 1, table.create(self.trianglesLen))
	self.halfedges = table.move(self._halfedges, 1, self.trianglesLen, 1, table.create(self.trianglesLen))
end

function Delaunator._hashKey(self: Delaunator, x: number, y: number): number
	local key = math.floor(pseudoAngle(x - self._cx, y - self._cy) * self._hashSize) % self._hashSize
	-- a point exactly on the circumcenter has no angle; JavaScript ignores the NaN key, Luau can't
	return if key == key then key else 0
end

function Delaunator._legalize(self: Delaunator, a: number): number
	local coords, triangles, halfedges = self.coords, self._triangles, self._halfedges

	local i = 1
	local ar: number
	-- the index arithmetic below is upstream's, on 0-based ids
	a -= 1

	-- recursion eliminated with a fixed-size stack
	while true do
		local b = halfedges[a + 1] - 1

		--[[ if the pair of triangles doesn't satisfy the Delaunay condition
		 * (p1 is inside the circumcircle of [p0, pl, pr]), flip them,
		 * then do the same check/flip recursively for the new pair of triangles
		 *
		 *           pl                    pl
		 *          /||\                  /  \
		 *       al/ || \bl            al/    \a
		 *        /  ||  \              /      \
		 *       /  a||b  \    flip    /___ar___\
		 *     p0\   ||   /p1   =>   p0\---bl---/p1
		 *        \  ||  /              \      /
		 *       ar\ || /br             b\    /br
		 *          \||/                  \  /
		 *           pr                    pr
		 ]]
		local a0 = a - a % 3
		ar = a0 + (a + 2) % 3

		if b == -2 then -- convex hull edge (halfedge -1)
			if i == 1 then break end
			i -= 1
			a = EDGE_STACK[i] - 1
			continue
		end

		local b0 = b - b % 3
		local al = a0 + (a + 1) % 3
		local bl = b0 + (b + 2) % 3

		local p0 = triangles[ar + 1]
		local pr = triangles[a + 1]
		local pl = triangles[al + 1]
		local p1 = triangles[bl + 1]

		local illegal = incircle(
			coords[2 * p0 - 1],
			coords[2 * p0],
			coords[2 * pr - 1],
			coords[2 * pr],
			coords[2 * pl - 1],
			coords[2 * pl],
			coords[2 * p1 - 1],
			coords[2 * p1]
		) < 0

		if illegal then
			triangles[a + 1] = p1
			triangles[b + 1] = p0

			local hbl = halfedges[bl + 1]

			-- edge swapped on the other side of the hull (rare); fix the halfedge reference
			if hbl == -1 then
				local e = self._hullStart
				repeat
					if self._hullTri[e] == bl + 1 then
						self._hullTri[e] = a + 1
						break
					end
					e = self._hullPrev[e]
				until e == self._hullStart
			end
			self:_link(a + 1, hbl)
			self:_link(b + 1, halfedges[ar + 1])
			self:_link(ar + 1, bl + 1)

			local br = b0 + (b + 1) % 3

			-- don't worry about hitting the cap: it can only happen on extremely degenerate input
			if i <= EDGE_LIMIT then
				EDGE_STACK[i] = br + 1
				i += 1
			end
		else
			if i == 1 then break end
			i -= 1
			a = EDGE_STACK[i] - 1
		end
	end

	return ar + 1
end

function Delaunator._link(self: Delaunator, a: number, b: number)
	self._halfedges[a] = b
	if b ~= -1 then self._halfedges[b] = a end
end

-- add a new triangle given vertex indices and adjacent half-edge ids
function Delaunator._addTriangle(self: Delaunator, i0: number, i1: number, i2: number, a: number, b: number, c: number): number
	local t = self.trianglesLen + 1

	self._triangles[t] = i0
	self._triangles[t + 1] = i1
	self._triangles[t + 2] = i2

	self:_link(t, a)
	self:_link(t + 1, b)
	self:_link(t + 2, c)

	self.trianglesLen += 3

	return t
end

-- The next halfedge around the same triangle.
function Delaunator.nextHalfedge(e: number): number
	return if (e - 1) % 3 == 2 then e - 2 else e + 1
end

-- The previous halfedge around the same triangle.
function Delaunator.prevHalfedge(e: number): number
	return if (e - 1) % 3 == 0 then e + 2 else e - 1
end

-- The triangle a halfedge belongs to, as the triangle's first halfedge.
function Delaunator.triangleOfEdge(e: number): number
	return e - (e - 1) % 3
end

return Delaunator
