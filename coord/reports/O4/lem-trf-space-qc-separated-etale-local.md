## Worker report

The delivery adds `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal` and states the
DAG lemma `lem-trf-space-qc-separated-etale-local`.  It introduces the precise
presheaf formulations needed by the source sentence:

- `IsQuasiCompactPresheafMap g` quantifies over an affine scheme test
  `Z : Over S`, a map `h : yoneda.obj Z ⟶ F`, and a scheme `U` with map `p : U ⟶ Z`
  and map `q : yoneda.obj U ⟶ G` over `h`.  The induced map to the presheaf
  pullback is both `IsEtale` and `IsSurjective`, and `CompactSpace U.left`
  renders quasi-compactness of the atlas scheme.
- `diagonalPresheafMap g` is the categorical diagonal into
  `CategoryTheory.Limits.pullback g g`.
- `IsSeparatedPresheafMap g` uses the recorded
  `AlgebraicSpace.IsRepresentableWith` dependency with the property
  `IsClosedImmersion p.left`, exactly expressing a representable diagonal that
  is a closed immersion on every scheme test.
- `IsJointlySurjectiveEtaleFamily Y I Yᵢ a` says each `a i` is the recorded
  `AlgebraicSpace.IsEtale` and that every scheme-test section of `Y` is hit by
  some member of the family.
- `quasiCompact_separated_etaleLocal` quantifies `X Y : AlgebraicSpace S`,
  `f : X ⟶ Y`, an arbitrary index type `I : Type u`, an étale family of scheme
  maps to `Y`, and asserts the equivalence between the two predicates for `f`
  and for every base-change map
  `CategoryTheory.Limits.pullback.snd f.hom.hom (a i)`.  The proof is `sorry`.

The hypotheses and clauses are rendered in Lean as follows.  `S` is the implicit
`{S : Scheme.{u}}`; the family hypothesis is `ha`; quasi-compactness and
separatedness occur as the two conjuncts on each side of the equivalence; and
base change is the categorical pullback second projection.  The `CompactSpace`
class is Mathlib's finite-subcover condition for the underlying scheme topology.

Dependency declarations used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` from Mathlib.
- `def-trf-algebraic-space`: `AlgebraicGeometry.AlgebraicSpace` and its
  `AlgebraicSpace.IsRepresentableWith`, `IsEtale`, and `IsSurjective`
  declarations in `Sheaf.AlgebraicGeometry.AlgebraicSpace`.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion` from
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `def-weil-pbc-quasi-compact-scheme`: Mathlib `CompactSpace` from
  `Mathlib.Topology.Defs.Filter` (used through the imported compactness API).

Proof dependencies are imported in the node plan but are not needed for the
statement elaboration: `lem-pc-fpqc-descend-closed-immersion`,
`lem-trf-space-fibre-products-etale-covers`,
`lem-weil-pbc-closed-immersion-base-change`,
`lem-weil-pbc-etale-covering-affine-refinement`,
`lem-weil-pbc-etale-covering-composition`, and
`lem-weil-pbc-fpqc-finer-than-etale`.

Edge cases checked: `I` is an arbitrary `Type u`, including the empty family;
no nonemptiness or finiteness is added.  The affine test `Z` may be empty, and
`CompactSpace U.left` allows the empty scheme.  The diagonal definition uses
Mathlib's categorical pullback and does not impose a chosen atlas or an
extra separatedness hypothesis.  The family condition is stated testwise, so
it covers all scheme-test sections and does not assume a point-set topology on
an algebraic space.

Searches made:

- `msearch.py ... leanfinder "quasi-compact separated algebraic space morphism etale local on target"`:
  hits were scheme `IsEtale`, quasi-compact/quasi-separated morphism instances,
  and scheme separatedness; no algebraic-space locality theorem or matching
  presheaf predicates.
- `msearch.py ... loogle "IsQuasiCompactPresheafMap, IsSeparatedPresheafMap, AlgebraicSpace"`:
  zero hits (the new predicate names are absent).
- `msearch.py ... grep "AlgebraicSpace|IsQuasiCompactPresheafMap|IsSeparatedPresheafMap" Mathlib/AlgebraicGeometry`:
  zero matching declarations for algebraic spaces or these predicates.
- Repository `rg` searches over `lean/Sheaf` and the read-only upstream
  `WeilConjectures` tree found no existing algebraic-space quasi-compactness or
  separatedness locality declaration.  The only relevant existing framework is
  `Sheaf.AlgebraicGeometry.AlgebraicSpace`.

No statement correction or `STATEMENT-DISPUTED` flag is needed.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
