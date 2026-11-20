/- Scratch matrix. Each declaration uses exactly the same body and consumer. -/

-- abbrev A0 := body
-- def A1 := body
-- @[reducible] def A2 := body
-- A3 uses the body expression at the original consumer site.

-- The important audit fields are the environment hints:
-- A0: def/abbrev; A1: def/regular; A2: regular definition under reducible transparency.
-- Do not compare source spelling without recording these hints.
