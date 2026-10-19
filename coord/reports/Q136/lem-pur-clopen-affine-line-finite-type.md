## Worker report

The module `Sheaf.AlgebraicGeometry.PurityClopenAffineLineFiniteType` states
`AlgebraicGeometry.clopen_affine_space_separated_finite_type`. It introduces no new
definitions and leaves exactly the theorem proof as `sorry`.

The field hypothesis is rendered by `{k : Type u} [Field k]`. The separated finite-type
`k`-scheme `Y` is rendered by its structure morphism
`f : Y ⟶ Spec (.of k)` with `[IsSeparated f]`, `[LocallyOfFiniteType f]`, and
`[QuasiCompact f]`; these are the Mathlib encoding of separated and finite type used by
the recorded `def-weil-proper-morphism` and `def-weil-finite-type-morphism` declarations.
The open subscheme is `j : U ⟶ Y` with `[IsOpenImmersion j]`, and its underlying subset
being closed is exactly `hU : IsClosed (Set.range j.base)`. The first conclusion conjunct
is separatedness and finite type of the restricted structure morphism `j ≫ f`, written as
`IsSeparated (j ≫ f) ∧ LocallyOfFiniteType (j ≫ f) ∧ QuasiCompact (j ≫ f)`. The second
conclusion quantifies over every `r : ℕ`; its affine space is precisely
`AffineSpace (ULift.{u} (Fin r)) U`, whose canonical projection is
`AffineSpace ... U ↘ U`, and the composite structure morphism is
`(AffineSpace ... U ↘ U) ≫ j ≫ f`. The three corresponding separated and finite-type
properties are stated for this composite. No nonemptiness assumption on `U` and no
positive-rank assumption on `r` occurs.

The dependency declarations used are the recorded Mathlib declarations:

- `def-weil-field`: `Field` from `Mathlib.Algebra.Field.Defs`.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsSeparated` from
  `Mathlib.AlgebraicGeometry.Morphisms.Proper` (the record also records `IsProper` and
  `UniversallyClosed`; the statement uses its separatedness declaration).
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact` from `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
  and `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion` from
  `Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion`.
- `def-sbc-affine-space`: `AlgebraicGeometry.AffineSpace` and its canonical-over map
  from `Mathlib.AlgebraicGeometry.AffineSpace`.

Edge cases checked are `U = Y` with `j = 𝟙 Y`, the empty open subscheme, `r = 0` (where
Mathlib's affine-space projection is canonically an isomorphism), `r = 1`, arbitrary
positive `r`, and nonreduced schemes. The signature has no hypothesis excluding any of
these cases.

Searches made before writing were:

- `msearch.py ... leanfinder "clopen open subscheme of a separated finite type scheme over a
  field and relative affine space are separated and finite type"`: hits included
  `AlgebraicGeometry.AffineSpace`, affine morphism and separatedness infrastructure, but no
  theorem with the combined clopen restriction and all finite-type conclusions.
- `msearch.py ... loogle "AffineSpace, IsSeparated, LocallyOfFiniteType, QuasiCompact"`:
  no hits (the service reported `AffineSpace` as an unknown identifier); the equivalent
  qualified search also reported no hits.
- `msearch.py ... grep "clopen|AffineSpace|IsSeparated" AlgebraicGeometry`: hits were
  generic `AffineSpace`, separatedness, and projective-spectrum declarations; no matching
  theorem.
- `rg -n "clopen_affine_space_separated_finite_type|lem-pur-clopen-affine-line-finite-type|
  AffineSpace.*IsSeparated"` over `WeilConjectures/` and `lean/Sheaf/`: no declaration
  matched.
- The existing DAG node search found no duplicate statement or existing Lean record for this item.

The per-file compile command, with its required file argument, is:

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q136 lem-pur-clopen-affine-line-finite-type lean/Sheaf/AlgebraicGeometry/PurityClopenAffineLineFiniteType.lean
```

The immutable module was independently recompiled during maintainer review with exit
code 0 and no diagnostics. The module disables the expected `sorry` warning.
There are no `STATEMENT-DISPUTED` issues, no node faults, no new nodes, and no dependency
modules.

## Second reading by Q136

I reopened the node and the module. The field, scheme, open-immersion, and closed-range
hypotheses match the node clause by clause. The first conclusion uses exactly the
restricted morphism `j ≫ f`; the affine-space clause uses every natural rank and the
canonical Mathlib relative affine space over `U`, followed by the same restricted
structure morphism. Each finite-type assertion is the exact pair of Mathlib properties
`LocallyOfFiniteType` and `QuasiCompact`, and each separatedness assertion is
`IsSeparated`. The empty-open and rank-zero cases remain admitted by the signature.
No mismatch or correction was found.


### Independent maintainer review of immutable delivery

Reviewed delivery `16544dc67094c753b7fd23a3c43c255b08506ad1`, using its extracted
snapshot. All five statement dependencies and their exact Mathlib declarations were
read. The field, separatedness, local finite type, quasi-compactness, open immersion,
and closed range match the node; both conclusions use the specified composite
structure morphisms. `AffineSpace.over` is the first projection, not an arbitrary
map. `ULift.{u} (Fin r)` has exactly r coordinates and satisfies the existing
same-universe affine-space interface for every universe u, including u = 0.
The empty U, empty Y, identity open immersion, arbitrary characteristic, nonreduced
schemes, and ranks 0, 1 and arbitrary natural rank are admitted. No new mathematical
hypothesis or conclusion is required, and the recorded signature remains verbatim.

Two mechanical corrections are supplied in the replacement module. First, import
`Sheaf.AlgebraicGeometry.ClosedImmersionProducts` without `public`, as required by
stage-2 rule 7 for the recorded proof dependency
`lem-weil-pbc-closed-immersion-products` (H9). Its exact first conjunct is the
composition result used in Step 5; its declaration and docstring were read.
Second, expand the proof docstring to all six node steps, retaining the cartesian
diagonal arguments and naming their dependency nodes (H8). The theorem and its
single `sorry` are unchanged. The compile command above also repairs the original
report's omission of the required file argument.

The original module compiled through `scompile.py` in both sandbox and canonical
library modes (1.5 s and 1.6 s), with no errors or warnings. The replacement was
also checked through the prescribed wrapper; detailed final compiler evidence is
in the independent `review.md`. The installed wrapper uses the server side-overlay
compiler, rather than a local-only path. No direct SSH, global build, repository
edit, claim, delivery, or Git mutation was performed. No new definition or
prerequisite, universe repair, statement correction, or pro-etale substitution is
involved. Existing search records include LeanSearch, LeanFinder, Loogle and grep;
independent text searches found no duplicate of the combined theorem.
