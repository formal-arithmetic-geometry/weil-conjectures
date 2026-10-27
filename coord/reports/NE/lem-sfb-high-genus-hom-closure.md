## Worker report

The delivery states lem-sfb-high-genus-hom-closure in
`Sheaf.AlgebraicGeometry.HighGenusHomClosure`. The main theorem is
`AlgebraicGeometry.exists_projective_generic_hom_closure`. Its naturality and finite-group
clauses are `generic_hom_closure_natural` and `generic_hom_closure_group_action`.
All three theorem proofs are `sorry`; none of the definitions contains `sorry`.

Source read: de Jong, Families of curves and alterations, printed p.609, §§3.9--3.12,
Claim 3.10 and Lemma 3.13, publisher PDF
https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf . Section 3.9 constructs the
morphism scheme and closure, Claim 3.10 asserts properness, §3.11 supplies projectivity
and the action, and Lemma 3.13 contracts the rational exceptional curves. The live node's
reviewed generalization replaces the genus condition exactly by the absence of nonconstant
projective-line maps into the geometric target fibres. The natural-language statement and
its ten proof steps are preserved.

Hypothesis-by-hypothesis correspondence:

- The field is `(k : Type u) [Field k]`; the projective finite-type base is
  `(S : Scheme.{u}) (pS : S ⟶ Spec (.of k)) [IsHProjective pS]
  [LocallyOfFiniteType pS]`. H-projectivity implies properness and quasi-compactness,
  so the latter is exactly finite type in this context. `[IsIntegral S]` is the integral
  hypothesis. `hnormal` asks for an integrally closed domain at every local ring.
- `S.functionField` is the generic stalk by the recorded FunctionField module and
  Mathlib definition, and `S.fromSpecStalk (genericPoint S)` is its canonical map to `S`.
  This uses `Spec k(S)` directly, avoiding a noncanonical identification of function fields.
- `(f : W ⟶ S)` has `[IsHProjective f] [Flat f] [LocallyOfFinitePresentation f]`.
  Properness supplies quasi-compactness and separatedness, hence finite presentation.
- `hnodal : HasNodalGeometricFibres f` is the existing definition: every algebraically
  closed test field has a connected (therefore nonempty) dimension-one fibre, with the
  displayed completed local-ring equation at nonsmooth points. `hred` explicitly supplies
  reducedness of every such fibre. No private definition of nodal fibres is introduced.
- The two generic-fibre instances are `Smooth` and `GeometricallyIntegral` on the
  second projection of the base change along the generic-stalk map.
- `(g : Q ⟶ S) [IsHProjective g]` is the entire target family hypothesis. In particular
  there is no flatness, integrality, dimension, or reducedness assumption on `Q`.
- `hnoRational` quantifies over every algebraically closed `Ω : Type u`, every geometric
  point `t`, and every morphism `a : ProjectiveLine (Spec Ω) ⟶ pullback g t` over `Ω`.
  Its conclusion says precisely that `a` factors through an `Ω`-point of the target fibre.
  This is the constant-map condition, including constant maps and the absence of maps
  into an empty fibre. Test-field size follows Mathlib's geometric-property convention.
- `uη` is a morphism between the actual two generic pullbacks; `huη` makes it a
  `Spec k(S)`-morphism. No generic isomorphism or dominance is required.

Conclusion-by-conclusion correspondence:

- `RelativeHomSchemeData` is a helper interface for the very representing object that
  the item constructs. `parameter`, `projection`, and `evaluation` give the scheme over
  `S` and its universal map. `evaluation_over` makes it a map over `S`.
- `universal` says that for EVERY test scheme `T` and `t : T ⟶ S`, every map
  `z : W_T ⟶ Q` over `S` comes from exactly one map `a : T ⟶ parameter` over `S`.
  Maps to `Q` over `S` from `W_T` are canonically equivalent to maps to `Q_T` over `T`
  by the pullback property: the inverse sends `z` to `(z, pullback.snd)`.
  The correspondence is natural in `T` because it is induced by pulling back a single
  universal evaluation. Thus this is the full relative Hom functor's representing
  property, not only a bijection of generic points or a parametrization of a subset.
- `pieces` is a pairwise disjoint open cover `U : I → parameter.Opens` with supremum
  `⊤`. Each `U i` is an open subscheme of an H-projective `S`-scheme. The open cover
  is precisely the disjoint-union presentation by quasi-projective `S`-schemes required
  by the node. Arbitrary `I : Type u`, including empty pieces, is allowed.
- The witnesses `m` and `hm` are the point associated to `uη`, and the first equality
  in the main conclusion states exactly that its represented morphism is `uη`.
- `closureIdeal` is `Scheme.IdealSheafData.vanishingIdeal (.closure (Set.range m))`;
  `closureScheme` is its actual `subscheme`, with canonical `subschemeι` inclusion.
  Since `Spec k(S)` has one point, this is exactly the reduced closure of that point.
  It is not an arbitrary integral modification or a choice from a mere existence theorem.
- `IsIntegral (D.closureScheme m)` and `IsHProjective (D.closureProjection m)` are the
  integral and projective conclusions. H-projectivity also gives properness.
  The displayed dense open `U` with `IsIso (D.closureProjection m ∣_ U)` is precisely
  the node's convention for birationality, including that the whole inverse image is
  isomorphic to the open base.
- `closureEvaluationToTarget` is defined by restriction of the actual universal
  evaluation. `closureEvaluation` pairs it with the second projection, giving the
  actual morphism `W ×_S R ⟶ Q ×_S R` over `R`. Its data use only canonical pullback
  maps; the elementary compatibility proof is discharged in the definition.
- The witnesses `a` and `ha` lift the generic point into this closure; the inclusion
  equation says it is the specified `m`. The final equality identifies restriction
  of the actual evaluation with `uη`. Equality after projection to `Q` is sufficient
  because both morphisms have the same second projection to `Spec k(S)`.
- `generic_hom_closure_natural` handles compatible isomorphisms of ANY two base/source/
  target triples and their generic test schemes. The `hf`, `hg`, and `hj` squares are
  compatibility with the structure maps, and `hu` is preservation of the generic
  morphism. It supplies unique parameter and closure isomorphisms, commuting with
  the generic point, closure inclusions, structure maps, and evaluations.
  Uniqueness enforces identity and composition compatibility. No projective embedding
  or field-linear isomorphism is required. The theorem applies to any presentations,
  so no choice of the existential presentation in the main theorem affects naturality.
- `generic_hom_closure_group_action` takes an arbitrary finite group in universe `v`
  and its compatible actions on `S,W,Q`. `genericHomSourceAction` constructs the action
  on the actual generic source using `Scheme.functionFieldAut` and `Spec.map`, so
  no separate generic action is assumed. `hu` is exactly
  invariance of the generic map. The output `σM` and `σR` are monoid homomorphisms
  into scheme automorphisms, so all action laws are included. Its equations state
  equivariance of the base projection, generic point, closure inclusion and both
  evaluations. The base-induced generic action is used directly in the output point
  equation. No faithfulness or action on `k` fixing its elements is required.

Dependency declarations read and reused:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.Algebra.Algebra.Defs`: `Algebra`.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`, `IsReduced`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`; the separated and
  universally-closed classes are those in the corresponding Mathlib modules.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`: `GeometricallyIntegral`, with the
  irreducible/reduced companion definitions read in the dependency record and imports.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`, with its
  finite projective-space embedding and properness instance, rather than its retired twin.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite` and `.Integral`: `IsFinite`, `IsIntegralHom`;
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective` (proof vocabulary).
- `WeilConjectures.AlgebraicGeometry.StalkAut`: `Scheme.functionFieldAut` and
  `Scheme.SpecMap_functionFieldAut_hom_fromSpecFunctionField`, supplying the actual
  canonical generic action and its compatibility, with no extra existence assumption.
- `WeilConjectures.AlgebraicGeometry.FunctionField`: the recorded component-product
  declaration and its arbitrary-integral-scheme clause reusing `Scheme.functionField`.
- `Sheaf.FieldTheory.FieldTower`: `FieldExtension.degree` (not needed by this particular
  statement, which contains no finite extension or degree condition).
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `.FinitePresentation`, `.Smooth`,
  `.ClosedImmersion` and `.Etale`: `Flat`, `LocallyOfFinitePresentation`, `Smooth`,
  `IsClosedImmersion`, `Etale`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its projections,
  `pullback.map` and `pullback.lift`, used for all base changes and evaluation restrictions.
- `Sheaf.AlgebraicGeometry.ReducedNormalization`: its component definition shows the
  already established vanishing-ideal/subscheme convention. Actual normalization is
  not needed in this statement. The closure uses Mathlib `IdealSheafData.vanishingIdeal`
  and `.subscheme` directly.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`;
  `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, reused through the existing
  nodal-fibre definition. `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`:
  `Scheme.arithmeticGenus` was read; genus does not occur in the reviewed generalized
  statement, so no genus hypothesis or extra import is introduced.
- Added the already landed `def-trf-nodal-geometric-fibres` to `stmt_deps` as authorized
  for existing landed notions. Its recorded declaration is
  `AlgebraicGeometry.HasNodalGeometricFibres` in
  `Sheaf.AlgebraicGeometry.NodalGeometricFibres`. No dependency node is changed.

Imports for stated proof dependencies are retained: `ProjectiveBaseChange`,
`HProjectiveComposition`, `GenericFibreIsoSpreadBaseOpen`,
`ProjectiveNodalFamilyGeometry`, `ProperQuasiFinite`, and `FiniteBirationalNormalIso`.
Projective-proper is already publicly imported through the projective definitions.
The generic-DVR, Hilbert-representability, graphs-open and rational-domination proof
prerequisites have no recorded Lean declarations at inspection time; they are named in
its proof docstring but not silently replaced with assumptions or private theorems.
They are not prerequisites for typing any notion used here.

Edge cases checked: constant `uη` is allowed throughout; no generic isomorphism is
assumed. A point target satisfies the rational-map hypothesis and yields the base
closure. Empty target fibres have no projective-line maps; an empty generic target
cannot admit the supplied `uη` since the generic source is nonempty. Empty Hilbert
pieces and an infinite set of components are allowed by `pieces`. Nonfaithful and
semilinear group actions are included, as is the trivial group. No characteristic
restriction is imposed. The normal integral base is necessarily nonempty. All scheme,
field, and group universes are explicit, and `autoImplicit` is disabled.

Searches actually run:

- `msearch.py leanfinder`, query: "The reduced closure of a generic morphism from a
  nodal projective curve family into a projective scheme with no rational curves is
  projective birational". Eight hits included Weierstrass nonsingularity, Proj valuative
  properness and rational-map representatives. None states this relative Hom closure.
- `msearch.py loogle`, query `AlgebraicGeometry, Hom, IsRepresentable`: reported unknown
  identifier `AlgebraicGeometry`, hence not a usable negative result. Re-ran with the
  quoted query `"AlgebraicGeometry", "Hom", "Proper"`: twelve general
  `AlgebraicGeometry.HasRingHomProperty` hits, no matching statement or Hom-scheme
  construction.
- `msearch.py grep`, query `HomScheme|homScheme|relativeHom|reducedClosure` in
  `AlgebraicGeometry`: zero hits.
- `rg` over `lean/WeilConjectures/AlgebraicGeometry` and
  `lean/Sheaf/AlgebraicGeometry` for `HomScheme|homScheme|morphismFunctor|relativeHom|`
  `IsRepresentedBy|IsRepresentable|hilbertFunctor|HilbertFunctor|reducedClosure` found
  unrelated representability interfaces, not a relative Hom-scheme statement.
- Searched `lean/WeilConjectures` for the exact node id: no declaration. Searched the
  project for nodal definitions and found the recorded `HasNodalGeometricFibres` above.
  Direct source searches found `ProjectiveLine`, the canonical function field, and
  vanishing-ideal subschemes, all reused. No duplicate notion is constructed.

Validation: scompile.py compiled the delivered module against the live server build in
both its sandbox and final module name, cleanly. Initial noncomputability and closure-map
unfolding errors were repaired before this clean compile. Three expected theorem sorries
are the only postponed proofs. No statement dispute or statement correction is needed.
After the first successful dry run, the generic group-action interface was strengthened
by constructing the induced generic action from the existing StalkAut API instead of
requiring callers to supply it separately. It is checked again before delivery.
The earlier worker's unchanged-node rejection is repaired by supplying the previously
missing genuine Lean statement record and module, rather than redelivering the stage-1 split.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
