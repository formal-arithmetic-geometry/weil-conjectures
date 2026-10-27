## Worker report

Item: `lem-sfb-space-relative-dimension-base-change`.
Module: `Sheaf.AlgebraicGeometry.SpaceRelativeDimensionBaseChange`.
Main declaration: `AlgebraicGeometry.AlgebraicSpace.geometricFibreDimensionLE_baseChange_and_descent`.

The module states the two implications of the node, together as one conjunction, with
one postponed theorem proof. Its real definition `GeometricFibreDimensionLE` is exactly
the predicate P_d explicitly introduced by the item, not an independent missing notion.
It has no choice or postponed data: it quantifies over algebraically closed fields and
compares the Krull dimension of the actual geometric-fibre point space with d.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Schemes and algebraic spaces in the fixed size convention | Explicit `universe u w`, `S : Scheme.{u}`, `X : AlgebraicSpace S`, `T : Over S`. The arbitrary ambient S is the base of the existing big-site encoding. Every map X → T is included, in particular by taking S = T and the identity structural map on T. |
| A morphism f from an algebraic space to a scheme | `f : X.obj.obj ⟶ yoneda.obj T`. Algebraic-space morphisms are the natural transformations of their underlying sheaves; the representable target is its actual Yoneda presheaf. |
| Locally of finite type on étale scheme charts | `hft : MapToSchemeIsLocally (@LocallyOfFiniteType) X T f`. This existing predicate tests every representable étale chart and the actual Yoneda-preimage scheme map to T. |
| Quasi-separated, meaning quasi-compact relative diagonal | `hqs : MapIsQuasiCompact (Limits.pullback.diagonal f)`. The existing quasi-compactness predicate tests pullbacks along affine schemes, with compact underlying point spaces; for the representable diagonal this is the scheme quasi-compactness condition. No absolute quasi-separatedness of the base is imposed. |
| A nonnegative integer d | `d : ℕ`; dimensions are compared with `(d : WithBot ℕ∞)`. |
| P_d(f): every geometric fibre has dimension at most d | `GeometricFibreDimensionLE T f d`. |
| Geometric points use algebraically closed fields Ω | In the helper: `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ T.left)`. This is the existing big-site field universe, not an independent smaller test universe. No algebraicity condition over a residue field is added. |
| The geometric fibre is X ×_T Spec Ω | `Limits.pullback f (yoneda.map (Over.homMk (U := Over.mk (a ≫ T.hom)) (V := T) a rfl))`. The field spectrum acquires its actual composite structural map to S. |
| Dimension of its underlying topological space | `topologicalKrullDim (Point (...))`, using the existing field-point equivalence classes and `pointTopologicalSpace` atlas topology. It is not the dimension of local rings or a chosen chart. |
| P_d survives every scheme map T′ → T | First conjunct: `GeometricFibreDimensionLE T f d → ∀ (T' : Over S) (g : T' ⟶ T), GeometricFibreDimensionLE T' (Limits.pullback.snd f (yoneda.map g)) d`. The projection is the actual base-changed morphism. Every scheme map to T receives the composite S-structure, so requiring its expression in `Over S` imposes no restriction. |
| Conversely, any family {T_i → T} | Second conjunct quantifies `I : Type w`, `Tᵢ : I → Over S`, and `g : ∀ i : I, Tᵢ i ⟶ T`. No finiteness, topology, flatness, étaleness or nonemptiness of the family is assumed. |
| Jointly surjective means every base point is in an image | `(∀ t : T.left, ∃ (i : I) (tᵢ : (Tᵢ i).left), (g i).left tᵢ = t)`. This is ordinary scheme-point surjectivity, not surjectivity of Ω-valued points. |
| If P_d holds after every family member, P_d(f) holds | `(∀ i : I, GeometricFibreDimensionLE (Tᵢ i) (Limits.pullback.snd f (yoneda.map (g i))) d) → GeometricFibreDimensionLE T f d`. |

The sentence about quasi-separated geometric fibres being decent explains why the
node's topological dimension has its intended geometric meaning; it introduces no
additional hypothesis or independent conclusion. The theorem docstring carries all
four proof steps, including the field-extension dimension comparison and residue-field
amalgamation for covering detection.

Dependency declarations used and inspected:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsEtale`, `IsRepresentableWith`, and the sheaf/atlas definition.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms,
  `Spec`, and `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`;
  its base-change property is a proof input. `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
  supplies scheme quasi-compactness and its base-change property for the proof.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, valued in `WithBot ℕ∞`.
- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.FieldTheory.IsAlgClosed.Basic`:
  `IsAlgClosed`; `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`
  for the proof's common algebraically closed extension.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme`;
  these certify the sheaf fibre products used in the statement are algebraic spaces.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`,
  with `Point` and its field-valued representatives from `AlgebraicSpacePointClasses`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapIsQuasiCompact` and
  `MapToSchemeIsLocally`. Its proper-curve predicate already uses the identical
  geometric-fibre formula at bound one; this delivery does not redefine that predicate.
- Proof-only recorded modules: `Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange`
  (`fibre_dimension_after_base_change`),
  `WeilConjectures.Topology.DimensionSupremumLocalDimensions`
  (`topologicalKrullDim_eq_iSup_topologicalKrullDimAt`),
  `WeilConjectures.Mathlib.Topology.KrullDimension` (`topologicalKrullDimAt`),
  `WeilConjectures.FieldTheory.CommonExtensionFields` (`Field.exists_common_extension`),
  `Mathlib.AlgebraicGeometry.ResidueField` (`Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`), and `Mathlib.AlgebraicGeometry.PullbackCarrier`
  (surjective base-change and field-spectrum surjectivity inputs).
- `def-weil-size-convention` is a convention record: it is rendered by the explicit
  universe binders, not by a fabricated declaration.
- `lem-sfb-quasiseparated-space-atlas-dimension` has no recorded Lean module on the
  read base, so there is no proof import to add for it. It remains named in the proof
  docstring and the existing proof dependency list. No statement interface requires it.

The only node changes are its Lean record and the addition of the two already-landed
definition nodes `def-a1-space-point-topology` and `def-sfb-proper-curve-moduli` to
statement dependencies, to register the existing topology and chart/quasi-compactness
interfaces actually used. There is no statement correction, new node, dependency repair,
or disputed statement.

Edge cases checked before writing:

- Empty X or empty geometric fibres: the actual point space is empty and its dimension
  is bottom, which satisfies every natural bound, including d = 0.
- Empty T: there are no maps from a field spectrum, so the condition is vacuous.
- Empty I: the pointwise covering hypothesis forces T empty; no `Nonempty I` appears.
- d = 0: zero-dimensional and empty fibres are permitted; no positive-dimension binder.
- Non-equidimensional fibres: only total topological dimension is bounded.
- Infinite-dimensional fibres fail the bound, rather than being truncated to a natural.
- Arbitrary base changes and family members: none must be surjective individually,
  quasi-compact, étale, locally finite type, or flat. Only X → T has hft and hqs.
- Non-quasi-separated base schemes and non-quasi-compact sources are allowed; hqs is
  relative diagonal quasi-compactness, and there is no compactness assumption on X.
- Fields and schemes share universe u as in the published algebraic-space point
  framework. The covering index universe w is independent and unrestricted.

Searches made before writing (2026-10-24):

- `msearch.py ... leanfinder "Geometric fibre dimension bounds of locally finite type algebraic spaces preserved by base change and detected by jointly surjective scheme families"`:
  eight hits, all scheme property base-change or jointly-surjective-preservation APIs;
  none states this algebraic-space topological dimension theorem.
- `msearch.py ... loogle "topologicalKrullDim, AlgebraicGeometry.AlgebraicSpace"`:
  zero hits; Loogle does not index the project's AlgebraicSpace identifier.
- `msearch.py ... grep "geometric.*[Ff]ib.*[Dd]im|[Rr]elative[Dd]im|AlgebraicSpace" AlgebraicGeometry`:
  ten hits in Mathlib concern smooth relative dimension and the étale characterization;
  no matching general algebraic-space theorem.
- `rg` of the project `Sheaf` and `WeilConjectures` trees for relative/geometric fibre
  dimension, the item id, and the planned declaration names: no exact theorem or named
  P_d predicate. Read `AlgebraicSpaceLocalFibreDimensionOpen` (local dimension/open locus)
  and `AlgebraicSpaceEtaleDimension` (chart dimension); neither gives the statement.
  Read `ProperCurveModuli` and reused its actual chart and quasi-compactness definitions.
- DAG searches found `lem-sfb-space-fibre-dimension-base-change`, the older forward-only
  node, and `lem-sfb-space-etale-atlas-topological-dimension`, an atlas comparison.
  Neither has a Lean record and neither states both clauses. No duplicate was introduced.
- A final exact-name `rg` across Mathlib, `WeilConjectures`, and `Sheaf` found neither
  `GeometricFibreDimensionLE` nor `geometricFibreDimensionLE_baseChange_and_descent`.

Source checks: read Stacks `spaces-morphisms.tex`, definitions of relative dimension
and lemma-dimension-fibre-after-base-change (Tags 06LR and 04NS), and the accepted
four-step node proof with its Tag 0D52 and Tag 0A4J citations. The statement is unchanged.

Validation: server `scompile.py` compiles the standalone sandbox file and its intended
library module cleanly (only the expected postponed theorem). An initial namespace
resolution error for bare `pullback` was repaired by writing `Limits.pullback` explicitly;
the existing algebraic-space étale pullback functor otherwise shadows that name.

## Second reading by N9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
