## What changed

Completed `CategoryTheory.ProjectiveResolution.exists_ext_signed_dual_homology_equiv`
in `Sheaf.CategoryTheory.ExtSignedDualHomology` with its signature unchanged.
Added proof imports of `Mathlib.Algebra.Homology.ShortComplex.ModuleCat`,
and `Mathlib.CategoryTheory.Abelian.Projective.Ext`.
The proof constructs the linear surjection from cycles to Ext using `P.extMk`,
identifies its kernel with boundaries, and applies the first isomorphism theorem
and `ShortComplex.moduleCatHomologyIso`. A fully proved private helper
`extMk_zero_iff` handles degree zero through the cocycle comparison and the
vanishing of the positive terms of `P.cochainComplex`.
Updated the existing node's proof and proof origin to this route. No public
interface or definition changes. The unit route is preserved.

## Proved and sorry left

Closed the single original hole in
`CategoryTheory.ProjectiveResolution.exists_ext_signed_dual_homology_equiv`
(node `new-j3-ext-signed-dual-homology`). The private helper `extMk_zero_iff`
is also proved. Holes closed: 1. Holes added: 0. No `sorry` remains in the
item or is introduced elsewhere. This is a proof, not a decomposition.
Local single-file compilation passes without errors or warnings.

## No longer needed

No existing imports, nodes, or modules were removed. The second reading removed
the redundant newly added proof import `Mathlib.LinearAlgebra.Isomorphisms`;
its first-isomorphism API is already available through the retained imports. The original node
has no proof dependencies to prune; the proof uses only Mathlib. It avoids
constructing a full termwise isomorphism of total Hom complexes, using the
existing `extMk` comparison API instead.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The original plan's quotient comparison can be
implemented more directly by the surjective cycle-to-Ext map and its kernel.
The degree-zero boundary case was checked separately, rather than applying
`extMk_eq_zero_iff`, which requires a natural predecessor and therefore only
applies in positive degrees. Sign cancellation uses only that powers of -1
are units and square to 1, so no characteristic assumption is needed.

## Second reading by G3

1. Compared the entire delivered module with the repository using `diff -u`.
   The existing public theorem signature is byte for byte unchanged, as are
   its docstring, visibility, and the three original public imports. The only
   new declaration is the proved private `extMk_zero_iff`; there are no
   definition or statement changes and no forced adaptations. Verdict: pass.
2. Independently compiled the module using `lcompile.py`: no errors or warnings.
   Compiled a scratch copy with `#print axioms` for both the public theorem
   and the private helper. Both use exactly `propext`, `Classical.choice`, and
   `Quot.sound`. Read every proof step: cycle evaluation gives an A-linear
   surjection to Ext; its kernel is precisely the boundaries; the final
   composition has direction Ext to homology. There is no `sorry`, forbidden
   declaration, hollow definition, or arbitrary witness from an unproved
   theorem. Verdict: pass.
3. No statements are split off and no holes are added. Checked the private
   helper against Mathlib's cocycle-to-single coboundary criterion: its
   possible degree-one source object is zero. Checked degree zero separately
   from positive degrees, and checked sign inversion algebra: powers of -1
   are units and their square is 1 over every commutative ring, including
   characteristic two and the zero ring. No finite rank, regularity, or
   nonzero-ring hypothesis is silently needed. Verdict: pass.
4. Searched again with Lean Finder for "linear isomorphism Ext cocycles quotient
   boundaries projective resolution", and used `rg` in Mathlib, upstream
   WeilConjectures, and Sheaf for Ext/homology comparisons and extMk kernel
   results. The hits provide the primitives used here, not a direct theorem
   for the displayed arbitrary signed complex. No shorter route found.
   Removed the redundant newly added `Mathlib.LinearAlgebra.Isomorphisms`
   import after a successful scratch compilation without it; both other
   proof imports supply APIs directly used by the proof. The old
   `proof_deps` is empty, so there are no omitted pruned nodes. Read
   `dag/units/sk-thm-picard-duality.json`: its realized statement and step
   lists are empty, and this local comparison changes none of the unit's
   route. Verdict: pass after import cleanup.
5. Compared the existing and delivered node records. Only `proof` and
   `proof_origin` have substantive updates; `proof_deps` stays empty.
   The three proof steps accurately describe the cycle-to-Ext surjection,
   its kernel in both degree cases, and the linear quotient equivalence.
   The node's statement, Lean signature, source, chapter, and unit are
   preserved. No new nodes or change records are needed. Verdict: pass.

Second reading changed only the redundant proof import and this report.
The proof itself required no repair. One original hole closed, zero added;
this is a complete proof of the item, not a decomposition.
