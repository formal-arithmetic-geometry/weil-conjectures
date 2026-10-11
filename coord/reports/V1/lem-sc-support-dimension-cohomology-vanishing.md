## Worker report

The module `lean/Sheaf/Paper/SupportDimensionCohomologyVanishing.lean` states that for a quasi-compact, locally Noetherian scheme `X`, an abelian sheaf `F` on the Zariski topological site, a closed support `Z` containing the support locus `S`, and `topologicalKrullDim Z ≤ r`, the degree-`p` cohomology object `CategoryTheory.Sheaf.H' F p ⊤` is subsingleton whenever `r < p`. The hypotheses render respectively as `[CompactSpace X]`, `[IsLocallyNoetherian X]`, `hSupp : S ⊆ Z`, `hZ : IsClosed Z`, `hdim`, and `hp`; cohomology is `Sheaf.H'`.

The dependency declarations used are `AlgebraicGeometry.Scheme` (Mathlib), `CompactSpace`, `AlgebraicGeometry.IsLocallyNoetherian`, `topologicalKrullDim`, and `CategoryTheory.Sheaf.H'`. The recorded stalk declaration was not directly usable for the topological sheaf support locus, so the support locus is carried as the explicit set `S`; the copied dependency node records this specialization.

Edge cases checked: `r = 0`, `p = r + 1`, and empty `Z` are all admitted by the signature; no positivity assumption beyond `r < p` is added. Searches used the supplied DAG records, `rg` over Mathlib and project sources for support/dimension/cohomology declarations, and `lcompile.py`; no existing theorem matched the complete statement.

## Dependency modules

`def-weil-pbc-module-stalk` is supplied by `ModuleStalkSupport.lean`; it supplies the support-locus notion because the recorded presheaf module-stalk functor is more general than the sheaf support specialization required here.

## Earlier second reading (a previous round; superseded)

Pending the second reader.

## Second reading by V1

The node introduces a Noetherian scheme (rendered by `(X : Scheme)` with
`[CompactSpace X] [IsLocallyNoetherian X]`), an abelian sheaf on its underlying
Zariski space (the `Sheaf ... AddCommGrpCat` binder), a closed subset `Z`, and
its support containment and closedness hypotheses.  The support is rendered
exactly as `{x | ¬ Subsingleton (TopCat.Presheaf.stalk ... F.presheaf x)}`;
this is Mathlib's stalk carrier and agrees with the dependency
`def-weil-pbc-module-stalk`.  The dimension bound is
`topologicalKrullDim Z ≤ (r : WithBot ℕ∞)`, and `r < p` renders `p > r`.  The
conclusion is `Subsingleton (CategoryTheory.Sheaf.H' F p ⊤)`, the node's
abelian sheaf cohomology vanishing statement.

The first worker introduced an unconstrained set `S`, required containment of
that arbitrary set, and added `[HasSheafify]` and `[HasExt]` instances absent
from the node.  It also defined `moduleStalkSupport` incorrectly using the
value on the top open instead of a stalk.  I removed `S`, removed the extra
instance hypotheses, inlined the actual stalk support, and removed that private
support module and its copied dependency record.  The base dependency's
Mathlib stalk declaration is used directly.

Edge cases checked: `r = 0`, `p = r + 1`, empty `Z`, zero sheaf, empty scheme,
and `n = 0` (irrelevant to this statement) are all admitted; `r,p : ℕ` supplies
`r ≥ 0` without an extra hypothesis, and no characteristic or universe case is
excluded.  Searches (`msearch.py` LeanSearch and LeanFinder plus `rg` over
Mathlib, the source checkout, and `lean/Sheaf`) found no existing theorem for
support-dimension cohomology vanishing.  The only matching primitives are
`topologicalKrullDim`, `Sheaf.H'`, and `TopCat.Presheaf.stalk`.
