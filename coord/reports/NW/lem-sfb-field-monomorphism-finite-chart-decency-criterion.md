## Worker report

Item: lem-sfb-field-monomorphism-finite-chart-decency-criterion.

The module `Sheaf.AlgebraicGeometry.FieldMonomorphismFiniteChartDecencyCriterion`
states
`AlgebraicGeometry.AlgebraicSpace.quasiCompact_field_representatives_of_finite_etale_chart_fibres`.
Its only theorem has proof `by sorry`; no definitions or auxiliary theorems are added.
The node changes only in `lean`.

Source read: `literature/stacks-project/decent-spaces.tex`,
`lemma-UR-finite-above-x`, Tag 03JV, the full six-condition statement and proof,
especially (3) implies (4) and (4) implies (6). The latest blueprint's
`sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and
`sk-thm-sf-ctf-stability-direct-images.proof.md` were read for the inherited
supporting direct-image route. The item is a supporting lemma, not the blueprint
unit's own statement. The source and node agree; no statement correction is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Algebraic space X over Spec Z | `X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))`; the lift makes Spec Z an object of `Scheme.{u}` without changing its geometry. |
| Point x in the underlying point set | `x : Point X.obj.obj`, the existing quotient of field-valued representatives. The topology is imported from the node's recorded point-topology module. |
| There are a field k and a map Spec k to X | The supplied witness is `(K : Type u) [Field K]`, its structural map `b`, and `j : yoneda.obj (Over.mk b) ⟶ X.obj.obj`. Quantifying over each such witness and proving the conclusion from its properties renders the existential hypothesis without an additional choice. |
| j represents x | `hj : schemePointMap j (IsLocalRing.closedPoint K) = x`; a field spectrum has one point, whose residue-field class is the class of j. |
| j is monomorphic on every scheme test | `hmono` quantifies over every `H : Over (Spec (.of (ULift.{u} ℤ)))` and states `Function.Injective (fun a : yoneda.obj H ⟶ yoneda.obj (Over.mk b) ↦ a ≫ j)`. Over Spec Z every scheme has its unique structural map, so every scheme test is included. |
| Every affine U and every representable etale U to X | `hfinite` universally quantifies over `U`, assumes `IsAffine U.left`, then universally quantifies over `a : yoneda.obj U ⟶ X.obj.obj` with `IsEtale a`. This existing space predicate includes representability and tests etaleness of its scheme projections. |
| The scheme U times_X Spec k is finite over k | `hfinite` supplies `V`, `p : V ⟶ Over.mk b`, and `r : yoneda.obj V ⟶ yoneda.obj U`, with `IsPullback r (yoneda.map p) a j ∧ IsFinite p.left`. The actual representing square has V in its upper left, U in its upper right, Spec K in its lower left, and X in its lower right. In particular finiteness is imposed on the projection to Spec K. |
| Every field-valued representative Spec L to X of x | The conclusion universally quantifies over `(L : Type u) [Field L]`, its structural map `c`, and `q`, with `schemePointMap q (IsLocalRing.closedPoint L) = x`. No monomorphism or finiteness of q or L/K is assumed. |
| For every affine T to X, without an etale hypothesis | The final universal quantifiers are `(T : Over (Spec (.of (ULift.{u} ℤ))))`, `IsAffine T.left`, and arbitrary `t : yoneda.obj T ⟶ X.obj.obj`. There is no `IsEtale t` premise. |
| T times_X Spec L is a quasi-compact scheme | The conclusion supplies the actual representing scheme V and maps `p : V ⟶ T`, `r : yoneda.obj V ⟶ yoneda.obj (Over.mk c)`, with `IsPullback r (yoneda.map p) q t ∧ CompactSpace V.left`. A representing square determines the fibre scheme up to unique isomorphism; compactness transports across that isomorphism. This expresses quasi-compactness of the entire fibre scheme, not just a quasi-compact atlas. |

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpace`, `IsRepresentableWith`,
  `IsRepresentable`, and `IsEtale`. The full signatures and docstrings were read;
  the representing-square interface is used directly rather than copied.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `pointTopologicalSpace`; its prerequisite
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`: `PointRepresentative`,
  `PointRepresentative.Rel`, `Point`, and `schemePointMap`. These are the
  existing common-field point classes, with no new point equivalence relation.
- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`,
  used by the existing representable-etale predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme`; full signatures and proof docstrings read.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (no Hausdorff assumption).

The recorded modules for the stated proof dependencies are imported privately:
`AlgebraicSpaceAffineEtaleCover`, `AlgebraicSpaceQuasiCompactFppfLocal`,
and `SpaceQuasiCompactAffineTests`, together with Mathlib's quasi-separated,
separated and scheme-limits infrastructure for the scheme permanence leaves.
Affine morphism permanence is available through the finite-morphism import.
`def-a1-algebraic-space-point-classes` is also available publicly through the
point-topology dependency. `lem-sfb-monomorphism-into-field-coproduct` has no
Lean record or Mathlib match in the read node; it is a proof-only dependency,
so no import can yet be supplied for it. It is named explicitly in the theorem's
four-step natural-language proof, and its statement is not duplicated here.

Edge cases checked before writing and on rereading:

- X empty: no `x : Point X.obj.obj` or representing field map exists; the theorem
  imposes no false existence assertion on the empty space.
- Empty affine chart U, or a chart missing x: its fibre may be empty. Neither
  `hfinite` nor the conclusion imposes nonemptiness of V; empty schemes are finite
  over a field and quasi-compact.
- Empty affine test T: the same permitted empty fibre gives the conclusion.
- X a field spectrum with j its identity: the finite etale chart fibres satisfy
  the hypothesis; any field extension representative is permitted by the conclusion.
- Infinite and transcendental extensions L/K: no finite extension or algebraicity
  hypothesis appears. The proof uses quasi-compactness of a morphism between affine
  schemes, not finite degree.
- Arbitrary characteristic: no characteristic or separability condition on K or L.
- Non-etale affine tests T to X are explicitly retained. No global quasi-separated,
  finite-type, or locally separated condition on X is assumed.
- All schemes, rings and test fields lie in the single chosen universe u, matching
  the existing algebraic-space and point-class definitions. There is no smaller,
  independently quantified test universe and no cardinality bound on charts.

Searches actually run:

1. `msearch.py ... leanfinder` with query
   `A field monomorphism into an algebraic space with finite fibres on all affine etale charts implies every representative of the point is quasi compact`:
   OK, eight hits. They concern scheme quasi-compactness and locally quasi-finite
   maps: `instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat`,
   `QuasiCompact`, `LocallyQuasiFinite`, `quasiCompact_over_affine_iff`,
   `instQuasiCompactOfIsAffineHom`, `quasiCompact_iff_forall_affine`,
   `quasiCompact_of_compactSpace`, `locallyQuasiFinite_iff`.
   None states the algebraic-space point criterion.
2. `msearch.py ... loogle '"AlgebraicSpace", "QuasiCompact"'`: OK, zero hits.
3. `msearch.py ... grep 'AlgebraicSpace|[Dd]ecent|[Ff]ield.*[Qq]uasi[Cc]ompact' AlgebraicGeometry`:
   OK, zero Mathlib hits.
4. `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the item id: no hits.
   Searches for `finite_chart`, finite-chart quasi-compactness, field
   quasi-compactness, and field monomorphisms found scheme extension results,
   `ReducedSingletonFieldFactorization`, `DecentSpaceFiniteFieldMap`,
   `DecentAlgebraicFieldImageClosed`, and `ChartPairFiniteResidualRelation`.
   The two decent-space modules were read: they assume decency and conclude
   finiteness or closedness, whereas this item derives a point's quasi-compact
   field representatives from finite chart fibres. No exact match.
5. Exact declaration-name search in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`,
   and `dag/lean_names_upstream.json`: no collision.

No new nodes, dependency repairs, or statement disputes.

Validation: the prescribed `scompile.py NW
lem-sfb-field-monomorphism-finite-chart-decency-criterion <module>` completed
with exit 0, both sandbox and library-module checks, with no errors or warnings.

## Second reading by NW

This is the dispatcher's single-worker delivery; no additional agent was started.
The independent maintainer review follows delivery. On a separate reread of the
node, source and completed module, the worker checked every row of the correspondence
table above. In particular the finite projection lands in Spec K, the conclusion's
projection lands in the arbitrary affine T, both squares use the correct horizontal
maps into X, and there is no etale premise on T or finite-degree premise on L.
The explicit cancellation quantifies over all scheme tests. There is no second
definition of points, etaleness, finiteness, representability, or quasi-compactness.
No mathematical mismatch was found on this reread; no statement changes were made.
