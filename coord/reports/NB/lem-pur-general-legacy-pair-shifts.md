## Worker report

Existing match: `Sheaf.Paper.AlgebraicallyClosedCoefficients`, principally
`WeilConjectures.AlgebraicallyClosedCoefficients.shift_exists` (lines 852–891), with
`hasShift`, `shiftAdditive`, `inclusionCommShift`, `inclusion_additive`, `zero_exists`,
and `transitionIso_commShift`. No module, definition, theorem, or dependency repair is added.
Only the item's `lean` record changes. Its `statement` is the existing primary signature
verbatim, including the explicit instance-binding lambdas.

Sources read: the item's complete statement and six proof steps; the current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors-basics/`
`sk-thm-sfb-qlbar-two-colimit/_section.md`; the retained construction in
`AlgebraicallyClosedCoefficients.lean`, especially lines 216–351, 440–549, 704–808,
and 827–946; and `WeilConjectures/CategoryTheory/StageSystem/Shift.lean` in full.
The current blueprint describes finite coefficient descent. The item specifically retains
old argument 7 on the older rational presentation; it does not identify that presentation
with the current datum-free categories. The existing declaration family has exactly that scope.

Hypotheses and clauses, in order:

- The global datum is `D : FiniteFieldDatum.{d}`. The coefficient prime is `l : ℕ`
  with `[Fact l.Prime]` and `hl : l ≠ D.p`. The closure is `Ω : Type v` with
  `[Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]`.
  The scheme is `Y : AlgebraicGeometry.Scheme.{u}` with no structure morphism,
  finite-type, nonemptiness, or characteristic assumption on Y. These are the
  surrounding section variables of every listed specialized declaration.
- `Index l Ω = Padic.FiniteCoefficientFields l Ω`. `Coefficient.{u} l Ω E` is
  `Shrink.{u} E.val`, with its actual `Shrink.algEquiv`. `coefficientSmall` obtains
  smallness from finite-dimensional coordinates. Thus d, u, and v are independent;
  no equality between the datum, closure, and scheme universes is imposed.
  `coefficientInclusion` is exactly conjugation of `IntermediateField.inclusion h`
  by the two algebra equivalences, not an arbitrary chosen field map.
- `Stage D l hl Ω Y E` is literally `rationalConstructibleCategory D l hl
  (Coefficient l Ω E) Y`. `transition` is literally `rationalScalarExtension` along
  `coefficientInclusion`. This is the named old raw localization, without idempotent
  completion. `stageSystem` is determined by `stageSystem_existsUnique`, using the
  tensor-normalized associators, and `Pair` is that system's literal `PairCategory`.
- The specified colimit group laws are `homAddCommGroup` and `preadditive` of this
  module. The existing proof `preadditive_eq_native` identifies this structure with
  the native quotient structure. Both `shift_exists` and `shiftAdditive` explicitly
  transfer additivity along this equality; they do not silently substitute a second
  preadditive structure. The Hom-coordinate node currently has no Lean record, but
  its exact construction is already present as `homCoordinates_existsUnique`,
  `homCoordinates`, `homCoordinatesAddEquiv`, and the group-comparison proofs here.
  An existing match does not require restating that prerequisite or changing its record.
- Existence of the coherent integer shifts is the initial existential
  `∃ s : HasShift (Pair D l hl Ω Y) ℤ` in `shift_exists`. `HasShift` includes the
  monoidal coherence of zero and addition, rather than merely unrelated functors.
  Its exhibited witness is exactly `StageSystem.PairCategory.hasShift ... ℤ`, which
  is also the definition of the module's public `hasShift` instance. The upstream
  `shiftMkCore` descends the stage zero/addition comparisons and proves all three
  coherence diagrams componentwise.
- The second conjunct of `shift_exists` gives the object formula using `shiftPair`,
  whose fields are `⟨A.stage, (shiftFunctor (Stage ... A.stage) n).obj A.obj⟩`.
  The public generic `StageSystem.PairCategory.shiftFunctor_obj` supplies the same
  literal formula for the installed witness.
- The third conjunct gives the map on every representative `ofHom A B L hA hB f`.
  `shiftRepresentative` is
  `sigma_source.hom.app A.obj ≫ (shiftFunctor (Stage ... L) n).map f ≫
  sigma_target.inv.app B.obj`. Lean composes left to right, so this is exactly the
  node's right-to-left expression `sigma_target⁻¹ ∘ f[n] ∘ sigma_source`.
  `HEq` only accommodates endpoints identified by the object formula; it does not
  weaken equality of arrows. `stageTransitionCommShift` is transport of the
  prescribed `transitionCommShift` along `stageSystem_transition`.
  The public generic `shiftFunctor_map_mkHom` records this formula for the installed shift.
- The first conjunct states `∀ n : ℤ, (shiftFunctor (Pair ...) n).Additive` for the
  specified Hom colimit laws; `shiftAdditive` supplies it for the installed witness.
- The final existential supplies `∀ E, (inclusion E).CommShift ℤ`; its nested clause
  says each hom component is heterogeneously equal to the identity on the literal
  shifted pair. `CommShift` includes shift-zero and shift-add coherence. The installed
  `inclusionCommShift` is `StageSystem.ι_commShift E`, exactly the witness used by
  `shift_exists`. The public `StageSystem.ι_commShiftIso_hom_app` states the identity
  formula for this witness without the existential packaging.
- A stage zero pair is zero: `inclusion_additive` and Mathlib's
  `CategoryTheory.Functor.map_isZero` specialize to every E and every stage object K
  with `IsZero K`, producing `IsZero ((inclusion E).obj K)`. This object is literally
  `(E,K)`. Independently `zero_exists` supplies `HasZeroObject (Pair ...)`, constructing
  one at the bottom coefficient field. This is not a substitution of mere existence
  for the node's assertion about all stage zero objects.
- Finally `transitionIso_commShift E L h` asserts
  `NatTrans.CommShift ((stageSystem ...).transIso h).hom ℤ` for the already installed
  comparisons. Mathlib `NatTrans.shift_app_comm`, expanding
  `Functor.commShiftIso_comp_hom_app`, reads
  `j_L(sigma) ≫ beta_L ≫ theta[n] = theta_at_shift ≫ beta_E`, exactly the displayed
  square in the node. Its theta is the existing `transIso`, not a newly chosen
  isomorphism. This instance is obtained directly from `StageSystem.transIso_commShift`.

Dependency declarations read:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, including its
  field, prime, cardinality, algebra, and algebraic-closure fields.
- Mathlib `NumberTheory/Padics/PadicNumbers.lean`: `Padic`; and
  `FieldTheory/IsAlgClosed/Basic.lean`: `IsAlgClosed`, `IsAlgClosure`.
- `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`: `Padic.FiniteCoefficientFields`,
  its finite-dimensional instance, compositum, base, and properties theorem.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and its full
  subcategory. `Sheaf.Paper.SfRationalizationKaroubi`:
  `sfRationalConstructibleCategory`, rational shift structures, localization and
  scalar-extension interface. These recorded dependencies now refer to the intrinsic
  presentation. The item's text explicitly fixes the older presentation instead;
  the matching existing declarations use the older declarations as required, and
  assert no comparison between the two. No private copy or new notion is introduced.
- `Sheaf.Paper.AlgebraicallyClosedCoefficients`: `stageSystem_existsUnique`,
  `stageSystem_transition`, `stageSystem_associator`, `stageTransitionCommShift`,
  `stageAssociatorCommShift`, `Pair`, Hom coordinates and preadditivity.
- `Sheaf.CategoryTheory.ExactStagePairData`:
  `CategoryTheory.StageSystem.ExactStagePairData`; read all its supplied structures.
  This node needs its underlying system and pair construction, not an assumed
  pretriangulation of the pair category.
- `Sheaf.Paper.ScalarExtensionExactIntrinsic`: `sfScalarExtension_exact_triangulated`;
  `Sheaf.Paper.ScalarExtensionAssociatorShifts`:
  `rationalConstructibleScalarComp_commShift`. The matching old module instead uses
  its existing `ScalarExtensionExact` normalized legacy comparisons and transports
  precisely those via `stageTransitionCommShift`. Its associator instance uses the
  recorded scalar-associator theorem.
- Mathlib `CategoryTheory/Triangulated/Pretriangulated.lean`: `Pretriangulated`;
  `CategoryTheory/Shift/Basic.lean`: `HasShift`; `Shift/CommShift.lean`:
  `Functor.CommShift`, `NatTrans.CommShift`, `NatTrans.shift_app_comm`.
- Proof helper `WeilConjectures.CategoryTheory.StageSystem.Functor`:
  `StageSystem.Morphism.functor`, `ιCompFunctorIso` and descent, used by the existing
  upstream shift construction. No new proof is written in this delivery.

Edge cases checked: all integer shifts, including zero and negative integers; arbitrary
schemes, including the empty scheme; independent closure and site universes; the bottom
coefficient field; repeated fields E=L=M, with no assumption that T_EE or its associator
is the identity; zero objects at any stage, not just the selected bottom-stage zero.
`shiftRepresentative` retains both scalar comparisons even for repeated fields.
The canonical theta square uses the actual repeated-index associator. There are no
empty directed-index cases since the base coefficient field is present.

Searches actually run:

- msearch LeanFinder: "Integer shifts on legacy rational coefficient pair categories
  with additive colimit Hom groups, identity inclusion comparisons, zero objects and
  shift compatible transition isomorphisms". Eight hits, including
  `CommShift₂Setup.int_ε`, `HomRel.IsCompatibleWithShift`, `GradedObject.hasShift`,
  `ShiftedHom`, and complex-shift lemmas; no exact specialized match.
- msearch Loogle: `CategoryTheory.HasShift, CategoryTheory.Functor.CommShift`.
  Twelve hits describing generic shift comparisons and coherence; no specialized match.
- msearch grep: `shiftMorphism|shiftFunctor_map_mkHom|transIso_commShift`.
  Zero Mathlib hits. Direct rg of `lean/WeilConjectures` finds the exact generic
  StageSystem/Shift API; direct rg of `lean/Sheaf` finds the exact older specialized
  declarations in `AlgebraicallyClosedCoefficients.lean` and distinguishes the
  datum-free and intrinsic variants. A grep of this item's id in `lean/WeilConjectures`
  returns no hits; the item is recently split from the old owning argument.
- Direct rg of `dag/lean_names_upstream.json` for the specialized declaration names
  returns no hits. The current source itself supplies the matching declarations.

No statement correction, new node, disputed statement, or added sorry is needed.

## Second reading by NB

This is a second pass by the same worker, not an independent review: the dispatcher
explicitly forbids starting other agents. The maintainer performs the independent review.
I reopened the node and existing source and checked every conjunct against the item.
The main risks were the intrinsic/legacy distinction, additivity for the specified
rather than only native group laws, simultaneous use of the same installed shift and
inclusion comparisons in the theta square, and the distinction between existence of
one zero and preservation of every stage zero. The source addresses these respectively
through `Stage`/`transition`, `preadditive_eq_native`, definitionally identical exhibited
witnesses plus `transitionIso_commShift`, and `inclusion_additive`/`Functor.map_isZero`.
The record includes the auxiliary declarations rather than pretending `shift_exists`
alone states the zero and theta clauses. No Lean source or node statement was changed.
