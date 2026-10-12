## What changed

Added `etale_affine_qcoherent_succ`, an intermediate successor-degree statement left for
parallel proof, and proved the original theorem by decomposing every positive degree as
`1 + n` and applying it.

## Proved and sorry left

`etale_affine_qcoherent` is proved. `etale_affine_qcoherent_succ` remains sorry; node
`lem-sc-etale-affine-qcoherent-succ` records the Cech argument required for it.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The original node's proof is a substantial Cech and derived-functor argument unavailable
as a single existing declaration; it was split at the successor-degree interface.

## New nodes

`lem-sc-etale-affine-qcoherent-succ`.

## Second reading by U1

1. The delivered module was diffed against the repository version. The existing theorem
   `etale_affine_qcoherent` has the same signature; the only added declaration is the
   reported successor-degree interface, and no target or definition was changed.
2. The file compiles with the launcher compiler. The only remaining `sorry` is the named
   theorem `etale_affine_qcoherent_succ`, and its matching DAG node supplies the source,
   proof plan, and statement. No forbidden declarations or hollow definitions were added.
3. The successor statement is true and has exactly the hypotheses and conclusion needed
   to reduce every positive degree to a successor. It is not supplied by Mathlib or the
   existing Sheaf library; checked searches found no matching theorem.
4. The proof follows the recorded affine Cech/Amitsur route. The original proof
   dependencies and imports remain available for the split theorem, and no old node is
   unused by the recorded route.
5. The new node's Lean record, proof text, dependencies, source, unit, and chapter agree
   with the module. The unit `sk-prop-h2` route is retained.

Changed during second reading: shortened the overlong `simpa` line to satisfy the style
linter. No mathematical or interface change was required.
