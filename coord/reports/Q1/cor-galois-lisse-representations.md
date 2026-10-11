## Worker report

Repair of H10 in review R-sub-D of f6404ca40. The mathematical statement and the
previously accepted source correction are preserved. The theorem now quantifies a
`GaloisLisseFiniteCorrespondence` and the existence, for every allowed adic coefficient
setting, of a `GaloisLisseAdicCorrespondence` over that same finite correspondence.
The shared data are inherited from `GaloisLisseFiniteData` and `GaloisLisseAdicData`;
each conclusion is a Prop-valued field whose named predicate expands to its old clause.

Earlier repairs: R-glr of aa136832c. The delivery now consists of the module
`Sheaf.Paper.GaloisLisseRepresentations` and the new definition node referring to
the already landed `Sheaf.Paper.LisseAdicFiberFunctors` (`existing: true`). All theorem proofs remain `sorry`. Definitions
have actual data; their required existence and category-law proofs are named theorems
with source citations and complete proof descriptions. The fibre functors have their own new definition node under rule (A).

The main theorem now gives one simultaneous family of evaluation equivalences. Its
finite and adic clauses share the same fundamental-group model and the same evaluation
action. Here is the hypothesis and clause correspondence.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Connected scheme and geometric point | `Y : Scheme.{u}`, `[ConnectedSpace Y]`, `Ω : Type u`, `[Field Ω] [IsAlgClosed Ω]`, `y : Spec (.of Ω) ⟶ Y`. |
| The specified fundamental group | `G : Type u` with `[Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]`, the actions on `(FiniteEtale.fiber y).obj P`, and `[IsFundamentalGroup (FiniteEtale.fiber y) G]`. |
| Identification with natural automorphisms on FLC sheaves | The homeomorphic group isomorphism `γ`, the Yoneda-compatible equivalence `Φ`, the fibre comparison `η`, and the displayed equality intertwining `γ` on `Φ(P)` with the specified action `g • z` on each finite étale fibre. Thus `γ` is tied to the given model, not an unrelated group. |
| Finite ring, finite left modules, linear equivariant morphisms | The family `e Λ` quantifies `[Ring Λ] [Finite Λ]`, including noncommutative rings. Its source is `LisseModuleSheafCategory Y Λ`; its target is a full subcategory of `Rep Λ G`, whose morphisms are equivariant linear maps. |
| Discrete continuity | Exactly `Finite X.V ∧ ∀ x : X.V, IsOpen {g : G | X.ρ g x = x}`. This is intentionally the open-stabilizer form: the landed `Rep.IsFiniteContinuous` accepts only commutative rings. The earlier report's claim that the file used that named predicate was incorrect. |
| Evaluation at the specified geometric point | `τ Λ` identifies `e Λ ⋙ ι ⋙ forget₂` naturally with `ι ⋙ (pointSmallEtale y).sheafFiber`. |
| The action is the natural automorphism on the underlying FLC sheaf | For each `F`, the theorem supplies its underlying FLC proof `h` and an equivalence `κ` between the module stalk's underlying set and the underlying set-sheaf stalk. Its germ equation fixes this comparison canonically. The last equation says `κ (τ (ρ g z)) = (γ g) (κ (τ z))`. |
| Full abelian subcategory, kernels and cokernels | `Nonempty (Abelian (LisseModuleSheafCategory Y Λ))`, `ObjectProperty.IsClosedUnderKernels IsLisseModuleSheaf`, and `ObjectProperty.IsClosedUnderCokernels IsLisseModuleSheaf`. Fullness is built into `ObjectProperty.FullSubcategory`. |
| Exact equivalence | `PreservesFiniteLimits (e Λ).functor` and `PreservesFiniteColimits (e Λ).functor`. |
| Commutative finite-ring tensor equivalence, including all constraints | For `[CommRing R]`, the existential monoidal and braided structures on the lisse subcategory make both its inclusion into sheaves and `(e R).functor ⋙ ι` into `Rep R G` braided strong monoidal functors. The ambient sheaf structure is explicitly `Sheaf.monoidalCategory` / `Sheaf.braidedCategory`; `Rep` has the diagonal tensor action. `Functor.Braided` includes natural tensor and unit isomorphisms, associativity and unit coherence, and compatibility with commutativity. No file-local instance selects a different sheaf tensor. |
| Constant coefficient unit goes to the trivial representation | For every finite ring `Λ` (including noncommutative rings), an object whose underlying sheaf is exactly `(constantSheaf ...).obj (ModuleCat.of Λ Λ)` and an isomorphism of its image with `Rep.trivial Λ G Λ`; the commutative tensor clause also records this unit explicitly. |
| Base change along arbitrary finite-ring maps | The functor family `B R S f`, its sheaf comparison `α`, and its representation comparison `β`. The latter uses `Rep.repIsoAction`, `ModuleCat.ringExtendScalars f` on actions, and the inverse representation/action equivalence. The action is therefore `1 ⊗ σ`, and both comparisons are natural transformations of functors. |
| Compatibility with composite finite-ring maps | For `f : R →+* S`, `g : S →+* T`, the natural isomorphism `c : B f ⋙ B g ≅ B (g.comp f)`. The representation square explicitly uses `ModuleCat.ringExtensionComp`. The sheaf section equation sends `b ⊗ (a ⊗ z)` to `(b * g a) ⊗ z`, through the same `c`. Thus the two comparisons are coherent together, not independent object isomorphisms. |
| Adic hypotheses apply only to part (2) | The adic conjunct begins `∀ (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)] ...`. None of these are theorem binders or restrictions on the finite clauses. |
| Algebraic closure and finite subextensions | `Q : Type (u + 1)` with `[Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]`; `E : Padic.FiniteCoefficientFields l Q` supplies exactly a finite intermediate field and its finite-dimensionality instance. |
| Continuous integral, continuous rational, and algebraic l-adic representations | The target predicates are the recorded `Representation.IsContinuousIntegral`, `Representation.IsContinuousCoefficient`, and `Representation.IsLAdic`. They receive `Rep.ρ` converted by `Representation.asGroupHom` and `LinearMap.GeneralLinearGroup.generalLinearEquiv`. `P : ProfiniteGrp` is paired with `δ : G ≃ₜ* P`; the action in each predicate is pulled back along `δ.symm`. This merely supplies the bundled input required by the recorded predicates, while all representation categories and fibre actions remain over the same `G`. |
| Equivalences at all three adic levels | The families `eI E`, `eR E`, and `eA` from the recorded `LisseIntegralSheaf`, `LisseRationalSheaf`, and `LisseAlgebraicSheaf` categories to those predicates. |
| Fibres are the specified fibres at `y`, naturally | `τI`, `τR`, and `τA` identify each equivalence followed by the forgetful functor with the functor extensions of the recorded integral, rational and algebraic fibre functions. The new definition module fixes their object values and their map formulas; it does not introduce alternative fibres. |
| Action through part (1) at every finite level | The integral clause has a germ-preserving `κ` at each level and the equality intertwining `limit.π` of the integral representation action with the same `γ` on the underlying finite locally constant set sheaf. Rational actions are fixed by `a ⊗ z ↦ a ⊗ ρ(g)z`. The algebraic-model comparison uses `Representation.coefficientScalarExtension` and fixes its fibre map on `a ⊗ z` to the corresponding scalar-extended rational fibre. |
| Abelian categories and exactness at E and Qlbar | `Nonempty (Abelian ...)` on both source and target categories and preservation of finite limits and colimits for `eR E` and `eA`. The integral equivalence is not given an extra exactness requirement absent from this clause. |
| Tensor at all adic levels | Existential `MonoidalCategory` structures with tensor-object and unit-object operations equal to the recorded `lisseIntegralTensor`, `lisseRationalTensor`, `lisseAlgebraicTensor` and units, and strong monoidal structures on the representation functors. The subsequent linear-equivalence equations explicitly identify the actions with `Representation.tensorDiagonal`. |
| Units at all adic levels | Explicit isomorphisms to `Rep.trivial` for `lisseIntegralUnit`, `lisseRationalUnit`, and `lisseAlgebraicUnit`. |
| Scalar extension E ⊂ L | The integral natural isomorphism uses `lisseIntegralScalarExtension`, `lisseIntegerInclusion` and extension of the representation action. The rational linear-equivalence family uses exactly `lisseRationalScalarExtension` and `Representation.coefficientScalarExtension`, with both an equivariance equation and a naturality equation for every morphism. The auxiliary `[Algebra E.val L.val]` is constrained by `algebraMap = (IntermediateField.inclusion h).toRingHom`; the inclusion's `toAlgebra` supplies it, so no embedding case is excluded. |

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale`:
  `AlgebraicGeometry.Scheme.FiniteEtale.fiber` (lines 114-124, including its docstring).
- `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence`:
  `FiniteEtale.exists_fiber_flc_equivalence`, read in full as the model for the group
  identification and its action comparisons. `FiniteEtale.fiber` remains the recorded
  fundamental-group convention.
- `Mathlib.CategoryTheory.Sites.Point.Basic`: `Point.sheafFiber` (lines 275-284),
  `Point.toPresheafFiber`; `Mathlib.AlgebraicGeometry.Sites.EtalePoint`:
  `Scheme.pointSmallEtale` (lines 58-70); `Mathlib.AlgebraicGeometry.Sites.Etale`:
  `Scheme.smallEtaleTopology` and the covering criterion (lines 47-66).
- `Sheaf.AlgebraicGeometry.EtaleSheaves`: the recorded
  `IsFiniteLocallyConstantEtaleSheafOfSets`.
- `Sheaf.Paper.LisseModuleSheaves`: `IsLisseModuleSheaf` and
  `LisseModuleSheafCategory`, read with the full trivializing-cover definition and
  `lisseModuleSheaf_iff_underlying_finiteLocallyConstant`.
- `Sheaf.Paper.LisseAdicSheaves`: the three categories, the three object fibres,
  tensor products, units, coefficient pairs/localization and the integral/rational
  scalar-extension functors, all read from their declarations and docstrings.
- `Sheaf.RepresentationTheory.LAdic`: all six recorded declarations, read in full:
  `IsContinuousIntegral`, `IsContinuousCoefficient`, `IsLAdic`, `IsEquivariant`,
  `tensorDiagonal`, `coefficientScalarExtension`. The first three are used literally;
  `Rep.Hom` already supplies equivariant linear morphisms.
- `Sheaf.Paper.LisseTensorScalarExtension` and
  `Sheaf.Algebra.Category.ModuleCat.RingScalarExtension`: the sheaf tensor structures,
  general-ring scalar extension, pure tensor generators and `ringExtensionComp`.
- Mathlib `Rep.repIsoAction`, `Representation.asGroupHom`,
  `GeneralLinearGroup.generalLinearEquiv`, `Functor.Braided`, `Functor.Monoidal`,
  `ObjectProperty.IsClosedUnderKernels` and `IsClosedUnderCokernels` were opened and
  checked against their signatures. In particular, the conversion to linear
  automorphisms is available; the earlier claim that `IsLAdic` could not be used was wrong.

Edge cases checked before finishing: noncommutative finite rings are included; the zero
ring and zero modules/vector spaces are included; no nontriviality or positive rank is
assumed. A geometric point excludes the empty scheme already, and no new nonemptiness
hypothesis is imposed. Non-Noetherian and nonseparated connected schemes remain in
part (1). `Spec F_l` remains in the finite clause but is excluded from the adic clause
by the required invertibility assumption. `l = 0` and `l = 1` are excluded only in the
adic clause by primality. The integral index starts at `n = 0`, corresponding to the
original first finite quotient at exponent `n + 1`. Coefficient-field equality and
identity/composite ring maps are allowed; the composite equation specializes correctly
when either map is the identity. No hypothetical continuity witness `True` remains.

Searches actually run in this repair (the launcher log records them): LeanFinder for
“equivalence locally constant finite module sheaves continuous representations fundamental
group tensor scalar extension” returned eight condensed-module results, none this
corollary. Loogle `Rep, CategoryTheory.Equivalence` found `Rep.repIsoAction` and
`Rep.equivalenceModuleMonoidAlgebra`; the first is used, and the second is not this
statement. Launcher grep `galois_lisse_representations|lisse.*equivalence` found no
Mathlib match. LeanSearch “lisse integral rational algebraic sheaf geometric fiber
functor” returned Internal Server Error and is recorded as unavailable. Launcher grep
for the four new fibre/model functor names found no Mathlib match. Loogle
`CategoryTheory.Limits.lim, CategoryTheory.Functor.whiskeringRight` returned the generic
limit/whiskering comparisons, which support the integral construction but do not give
the specialized rational or algebraic fibre functors. Direct `rg` searches in
`WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` found no existing
specialized fibre functors or whole-corollary declaration. Source reading of Mathlib
`Rep.Basic`, `Sites.Point.Basic`, `Sites.Monoidal`, `Sites.Point.Monoidal`, `LAdic` and
`RingScalarExtension` found and reused the relevant notions. No unavailable service
is reported as “no match”.

Sources checked: [Stacks 0DV5](https://stacks.math.columbia.edu/tag/0DV5) for the finite
part; the DAG node's complete proof and `coord/HUMAN.md` for the requested correction;
[Deligne, Weil II](https://www.numdam.org/item/PMIHES_1980__52__137_0/) (PDF downloaded
and pages 144, 146-147 read with `pdftotext`) for (0.1) and (1.1.1) b)-d). The source
explicitly distinguishes inverse limits of integral finite levels, rationalization of
Hom, and the coefficient-field 2-colimit. None is replaced with a constant or hollow
category.

## New nodes

`def-pod-lisse-adic-fibre-functors`: its recorded `Sheaf.Paper.LisseAdicSheaves` remains the
single source of all categories, fibre objects, tensors, units and scalar extensions.
The existing node records usable fibre objects; functoriality is a further notion. An
expression `e.functor ⋙ forget ≅ lisseRationalFiber ...` could not be typed. The module added in earlier rounds, now landed, imports that module and supplies
only the missing functor extensions. This new node refers to that identical landed
module with `existing: true`; this delivery adds its DAG record, not its source file. Integrally,
it is `ι ⋙ whiskeringRight(stalk) ⋙ lim`, whose object is definitionally the recorded
integral fibre. Rationally, the existence theorem fixes the objects and maps
`a ⊗ f` to `a • (f_y ⊗ 1)`; category-law proofs are named, and the chosen functor has
no `sorry` data. Algebraically, the canonical model inclusion maps are localization
images of Grothendieck arrows with the pseudofunctor identity constraint. The existence
theorem fixes all objects and supplies natural comparisons on each rational model
whose components are fixed on pure tensors. Its functor therefore extends the same
recorded coefficient fibres, rather than arbitrary object assignments. The object
comparison and model identity/composition lemmas are named theorem placeholders with
proof descriptions. Source: Weil II (1.1.1) b)-d), pp. 146-147, referring to SGA 5 VI.
The new node states the integral inverse-limit map, rational balanced-tensor map,
and algebraic coefficient-2-colimit functor with scalar extension on rational models.
LeanSearch was unavailable (Internal Server Error); Loogle returned twelve generic
limit/whiskering hits; Mathlib grep and direct project/source/DAG name searches
returned no specialized fibre functors. Blueprint text search found no node defining
these functors. These searches are recorded in the new node. The original
`def-pod-lisse-l-adic-sheaves` record is restored byte-for-byte, including its
main declaration `LisseIntegralSheaf` and all 52 declaration names.

## Statement corrected

The base statement's preamble and its entire part (1) are unchanged. Only part (2)
now begins: “Assume moreover that Y is Noetherian and separated and that ell is
invertible on Y.” This follows the exact proposal in `coord/HUMAN.md`, Weil II (0.1)
and (1.1.1) b)-d). The earlier repair incorrectly imposed these assumptions on the
preamble and the entire theorem. The counterexample to the omitted adic invertibility
assumption is `Y = Spec F_l`. The node's `statement_change.old_statement` is the base
statement verbatim; `proof` and `proof_deps` are unchanged; `stmt_deps` gains only the new
fibre-functor node, with its base list recorded in `old_stmt_deps`.

All five citers were found by examining `stmt_deps` and `proof_deps` across all node
JSON files, and their statements were read:

- `def-wf-fundamental-representation`: holds. Its separated finite-type finite-field
  scheme satisfies the adic conditions with the standing prime-to-characteristic
  coefficient convention.
- `lem-wf-weil-fundamental-representation`: holds, inheriting the same setup.
- `lem-wf-dense-open-pi1-surjective`: **holds: false** for its unrestricted adic use
  in (3). It assumes only connected normal Noetherian V, without separatedness or
  invertibility. Its finite-coefficient claims and separated finite-type Weil/curve
  claims are unaffected. That citer needs its own review/correction and is not edited
  in this delivery.
- `prop-wf-weil-sheaf-representation-equivalence`: holds in its separated finite-type
  curve setting, with the standing prime-to-characteristic convention.
- `lemma-weil-pbc-curve-locally-constant-reduction`: holds, using only the unrestricted
  finite-coefficient part on a connected scheme.

## Repair checklist for R-glr

1. H7: moved the three adic hypotheses out of the preamble and theorem binders;
   preserved all of part (1), and rewrote the correction record and citer analysis.
2. H3, untied fundamental group: replaced every unrelated existential group by one
   explicit `IsFundamentalGroup (FiniteEtale.fiber y) G` model, tied `γ` to its finite
   étale action, and tied each finite sheaf action to that `γ` through canonical germs.
3. H3, untied adic fibres: added the missing fibre functors and `τI`, `τR`, `τA`;
   fixed integral actions at every finite level and rational/algebraic actions by
   the canonical scalar-extension formulas.
4. H3, missing clauses: included full abelian closure, braided tensor equivalence,
   trivial finite unit, general-ring scalar extension naturality and composites;
   included rational/algebraic abelianity and exactness, all adic tensors and units,
   and integral/rational coefficient extension, including the recorded rational
   scalar-extension functor and representation action.
5. H3/H4, wrong predicates: used all three recorded continuity/descent predicates
   through the explicit general-linear-group conversion; removed `True` and all
   inline adic-topology copies; consistently documented the open-stabilizer predicate.
6. H11: the earlier second reading was superseded by R-glr. It is not a review of
   these repaired files. A fresh independent second reading is required and is left
   to the dispatcher, as instructed; this report does not impersonate it.

Validation: both modules compile together locally with no errors or warnings. Final
server compilation and delivery preflight are run by the requested dry-run command;
no push is made by this worker.

## Earlier second reading (a previous round; superseded)

Historical second reading of the returned version; a fresh independent reader must
check the new node and repaired packaging before delivery.

I reread the corrected node, its proof steps, the Stacks source for 0DV5, and Weil II
(0.1) and (1.1.1) b)-d). The statement introduces a connected scheme `Y`, a
geometric point `y : Spec (.of Ω) ⟶ Y`, and a fundamental-group model `G` for the
finite-etale fibre functor. The Lean binders are `Y`, `[ConnectedSpace Y]`, `Ω` with
`[Field Ω] [IsAlgClosed Ω]`, `y`, `G`, the group/topological/compact instances, the
fibre actions, and `[IsFundamentalGroup (FiniteEtale.fiber y) G]`; these render exactly
those objects and hypotheses.

The finite-coefficient conclusion is rendered by `γ`, the finite-etale/FLC equivalence
`Φ`, its fibre comparison `η`, and the family `e Λ` into the full subcategory of finite
modules with open stabilizers. The displayed `τ Λ` is evaluation at `y`; the first
conjunct identifies the finite-etale model and the next equation identifies its action.
For each finite ring the theorem records abelianity, kernel/cokernel closure, finite-limit
and finite-colimit preservation, the constant coefficient unit, the canonical germ
comparison, and the action equation. The commutative-ring conjunct supplies the sheaf
and representation braided strong-monoidal structures and the trivial unit. The following
existential `B, α, β, c` supplies arbitrary finite-ring base change, naturality, and the
composite-map coherence, including the pure-tensor formula. No finite-ring commutativity
or positive-rank assumption is present.

The ℓ-adic conclusion starts with `∀ (l : ℕ) [Fact l.Prime] [IsNoetherian Y]
[Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]`; these assumptions are
inside part (2), as required by the corrected statement, and do not restrict part (1).
It quantifies an algebraic closure `Q`, finite coefficient fields `E`, the profinite model
`P` and topological group isomorphism `δ`, and the three equivalences `eI`, `eR`, `eA`
into the recorded continuity predicates. The three natural fibre comparisons `τI`,
`τR`, `τA`, rational and algebraic action equations, abelianity/exactness at `E` and
`Q`, all three tensor/unit clauses, and integral/rational scalar-extension clauses are
present. The action is converted through `Representation.asGroupHom` and the recorded
general-linear equivalences, so it is the same `G` action as in part (1). The auxiliary
finite coefficient fields and the algebra-map equality have the stated coefficient-field
meaning. Quantifier order agrees with the node.

Edge cases checked: zero and noncommutative finite rings, zero modules and vector spaces,
identity and composite coefficient maps, `n = 0` in the integral tower, arbitrary
connected schemes in part (1), the empty scheme excluded by the geometric point, and
`Spec F_l` excluded only from part (2) by invertibility. The prime hypothesis excludes
`l = 0,1` only in the adic clause. Universes are tied (`Ω : Type u`, coefficient objects
at `Type (u+1)`), and the finite index is not given an independent universe.

Searches were repeated with `rg` over `WeilConjectures`, `lean/Sheaf`, and
`dag/lean_names_upstream.json`, plus LeanFinder/Loogle queries for lisse sheaf
representation equivalences, fibre functors, and scalar extension. No existing whole
corollary or specialized rational/algebraic fibre functor was found. Mathlib matches
(`Rep.repIsoAction`, `Functor.Braided`, and the recorded representation predicates) are
used directly. The dependency declaration for the lisse-adic sheaf notions remains the
recorded `LisseAdicSheaves`; its usable object-valued fibres are extended
by `LisseAdicFiberFunctors`, now carried by its own new definition node.

No further statement mismatch was found. The only repair retained from the worker is the
source-mandated correction moving Noetherian, separatedness, and invertibility into the
part (2) binder; the node's `statement_change` and all citer verdicts document it. Both
modules compile together with only the permitted `sorry` declarations.

## Repair checklist for R-h1f302 (head 1f3026ba4)

1. Restored `def-pod-lisse-l-adic-sheaves.json` byte-for-byte from sheaf-dag.
2. Added `def-pod-lisse-adic-fibre-functors` under rule (A), with all required fields,
   the existing twelve-declaration fibre-functor record without `note`, source and
   actual searches. Changed every blueprint tag in its module to this new node;
   all remaining Lean text is unchanged.
3. Added only that new node to the item's `stmt_deps`; the theorem module is unchanged.
4. Renamed the dependency section to `## New nodes` and documented the new notion,
   source and searches. A fresh independent second reading is still required.

## Earlier second reading by Q1 (R-sub-D accepted; before H10 refactor)

Independent reading of the repaired delivery, 2026-10-12. I read the corrected
statement before comparing its Lean. Stacks `etale-cohomology.tex`,
`lemma-locally-constant-on-connected` (0DV5), introduces only a connected scheme
and geometric point in its finite-ring clause. The local Stacks checkout used was
`c1-stacks-review`; the repository's literature checkout is absent on this machine.
Weil II PDF text, printed pages 144 and 146-147, explicitly imposes Noetherian,
separated and ell-invertible in (0.1), defines the inverse systems in (1.1.1)b),
rationalized Hom in c), and coefficient 2-colimit in d). The correction applies
these assumptions only to part (2), as required. It does not change a unit target.

Objects, hypotheses and conclusions, checked against the actual signatures:

| Node item | Lean rendering and verdict |
| --- | --- |
| Connected scheme Y | `{Y : Scheme.{u}} [ConnectedSpace Y]`; matches. |
| Geometric point | `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`, `y : Spec (.of Ω) ⟶ Y`; matches the recorded geometric-point convention. |
| Specified profinite fundamental group | `G`, group/topology/compact instances, fibre actions, `IsFundamentalGroup (FiniteEtale.fiber y) G`; matches the recorded fundamental-group model, rather than an arbitrary unrelated group. |
| Its interpretation as automorphisms of the FLC fibre | `γ`, `Φ`, `η`, Yoneda comparison and the equation on every finite-etale fibre; matches. `γ` is fixed relative to the supplied actions through `η`. |
| Arbitrary finite ring and left modules | `e` quantifies `Λ : Type (u+1)` with `[Ring Λ] [Finite Λ]`. Source `LisseModuleSheafCategory` is the full subcategory defined by finite-module trivializations; target is the full subcategory of `Rep Λ G`; matches, including noncommutative rings. |
| Continuous discrete actions and equivariant linear maps | Target property `Finite X.V ∧ ∀ x, IsOpen {g | X.ρ g x = x}` is precisely finite discrete continuity. `Rep` morphisms are equivariant linear maps; matches. |
| Evaluation as functor, including the specified natural action | `τ Λ` is a natural module-valued fibre comparison. The `h`, germ-preserving `κ`, and action equation identify it with `γ` on the underlying FLC sheaf; matches. |
| Full abelian subcategory closed under kernels/cokernels | Fullness is built into `ObjectProperty.FullSubcategory`; `Nonempty (Abelian ...)`, `IsClosedUnderKernels`, `IsClosedUnderCokernels` are explicit; matches. |
| Exact finite equivalence | `e Λ` is an equivalence with preservation of finite limits and colimits; matches exactness. |
| Commutative tensor equivalence and all constraints | Existential source monoidal/braided structures and `Functor.Braided` for both the inclusion into sheaves and representation functor; matches the ambient sheaf tensor and diagonal representation tensor. I opened Mathlib's `Functor.Braided`: it extends `Functor.Monoidal`, so the comparison maps are invertible, not merely lax. |
| Constant coefficient unit | `C.obj = (constantSheaf ...).obj (ModuleCat.of Λ Λ)` and image isomorphism to `Rep.trivial`; matches, also for noncommutative finite rings. |
| Finite-ring coefficient change, naturally | Shared family `B`, sheaf comparison `α`, representation comparison `β` through `ringExtendScalars.mapAction`; matches sheafified balanced tensor and the `1 ⊗ σ` action. |
| Composite coefficient changes | One `c : B f ⋙ B g ≅ B (g.comp f)` satisfies both the representation diagram using `ringExtensionComp` and the sheaf equation `b ⊗ (a ⊗ z) ↦ b*g(a) ⊗ z`; matches. |
| Additional hypotheses only in (2) | Nested quantification `[IsNoetherian Y] [Y.IsSeparated] [∀ x, Invertible (l : Y.residueField x)]`; matches, without restricting finite coefficients. |
| Prime, algebraic closure, finite coefficient extensions | `[Fact l.Prime]`, `Q` with `IsAlgClosure`, and `E : Padic.FiniteCoefficientFields l Q`; matches. |
| Three adic sheaf/representation categories | `eI`, `eR`, `eA` use the recorded categories and `Representation.IsContinuousIntegral`, `IsContinuousCoefficient`, `IsLAdic`. The general-linear conversion and pullback along `δ.symm` supply their required inputs; matches. `δ : G ≃ₜ* P` keeps the same fundamental group. |
| Three natural evaluation fibres | `τI`, `τR`, `τA` use the new functor extensions of the existing fibre objects; matches. |
| Finite-level integral action | For every `F,n`, germ comparison `κ` and `limit.π` equation use the same `γ` as part (1); matches. |
| Rational and algebraic actions | Rational pure-tensor equation fixes `a ⊗ z ↦ a ⊗ ρ(g)z`; algebraic model comparison fixes scalar extension and its fibre map on every pure tensor; matches. |
| Abelianity and exactness at E and Qlbar | Explicit source and target `Abelian` existences and finite limit/colimit preservation for `eR` and `eA`; matches. No integral exactness hypothesis added. |
| Adic tensors and units | Monoidal structures have tensor objects and units equal to the recorded operations; strong monoidal functors plus explicit `tensorDiagonal` intertwining and `Rep.trivial` units at all three levels; matches. |
| Extension E ⊂ L | Integral natural isomorphism uses `lisseIntegralScalarExtension` and `lisseIntegerInclusion`; rational linear equivalences use `lisseRationalScalarExtension`, with equivariance and naturality. The auxiliary algebra structure is constrained to the specified inclusion, whose `toAlgebra` supplies it; matches. |

Dependency reading: I opened `FiniteEtale.fiber` in the upstream module, Mathlib
`pointSmallEtale` and `Point.sheafFiber`, the set-valued local-constancy predicates
in `EtaleSheaves`, the full definitions of `IsLisseModuleSheaf` and
`LisseModuleSheafCategory`, the integral/rational categories and fibres and algebraic
coefficient-localization definitions in `LisseAdicSheaves`, all three continuity
definitions and both tensor/scalar action definitions in `LAdic`, the
`exists_fiber_flc_equivalence` signature, and the tensor/scalar comparison module.
These signatures give the notions used above. In particular the integral levels are
sheaves of O_E-modules killed by powers of the uniformizer; they are not being
mistaken for arbitrary finite O_E-modules without the reduction condition.

New node `def-pod-lisse-adic-fibre-functors`: I read its full statement, fields and
module against Weil II (1.1.1)b)-d). It extends the existing fibres rather than
redefining their objects. Integral maps are whiskered stalk maps followed by `lim`.
Rational functor existence prescribes the map on `a ⊗ f` using scalar extension of
the integral map. The algebraic model map is the localization of the identity-base
Grothendieck arrow with the pseudofunctor identity constraint; its category laws
are separate named theorem placeholders. Algebraic functor existence specifies
all fibre objects and natural scalar comparisons on rational models, including
the pure-tensor formula. The `choose` definitions select these prescribed data
from named existence theorems; no definition's data is `sorry`. All theorem proofs
remain `sorry`. The new node has definition kind, split status, empty proof and
proof dependencies, the item's chapter/unit, proper ancestry and creation record,
source and search records, and is cited by the item. The extra sandbox copy of
`def-pod-lisse-l-adic-sheaves` equals the base node; it supplies no dependency module
and makes no change to that recorded definition.

Independent duplicate searches: LeanFinder query “geometric stalk equivalence finite
continuous linear fundamental group actions” returned the generic Galois action tools
(`IsFundamentalGroup`, `fiberIsoQuotientStabilizer`, etc.), not this corollary. Loogle
`CategoryTheory.Sheaf, CategoryTheory.Equivalence` returned generic site-comparison
and sheaf-category equivalences. Launcher grep for
`adic.*[Ff]iber.*[Ff]unctor|lisse.*[Rr]epresentation|[Ff]iber.*[Ee]quivalence`
returned generic Galois, algebraic and fibre-category results. LeanFinder query
“inverse system lisse sheaves rationalized morphisms stalk functor algebraic coefficient
colimit” returned condensed/light-condensed locally constant presheaf results, not
the specialized functors. LeanSearch query “geometric fiber functor lisse adic sheaves
continuous representations” was UNAVAILABLE (Internal Server Error), not a negative
search result. Direct `rg` searches by these concepts in upstream, project Lean and
the DAG found no other node for these specialized functors.

The independent upstream search did find
`Scheme.exists_equivalence_isFiniteLocallyConstantSheaf_of_isFundamentalGroup` in
`WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystems`. I opened the whole
file and checked its signature: it requires a commutative finite ring, asserts only
the underlying module fibre comparison, and omits the specified action, coefficient
change coherence and the adic clauses. Its own implementation notes explicitly
acknowledge these omissions. It cannot replace this node with `existing: true`.
The generic limit and sheaf fibre functors are reused in the new module.

Edge cases: the zero ring and zero modules/vector spaces are allowed (no positive
rank or nontriviality binder). Empty schemes cannot have the supplied geometric
point, so excluding them introduces no extra assumption. There is no freely varying
index set to make empty; the integral index is all natural numbers and `n=0` means
quotient exponent one, matching the recorded convention. Ell=0,1 are excluded only
by the prime condition in the adic clause. Characteristic ell is allowed in the
finite clause and excluded in the adic clause by invertibility, as the source
requires. Identity and composite ring maps and equal coefficient fields are allowed.
The scheme, geometric field and fundamental-group model share universe `u` as in
the recorded dependencies; coefficients and sheaf values use `u+1`, with arbitrary
`u` and no finite cardinal bound or independent smaller test universe.

Correction citer spot checks: I opened `lem-wf-dense-open-pi1-surjective`, whose
part (3) has unrestricted adic wording but lacks separatedness/invertibility;
its `holds:false` is honest. I also opened
`lemma-weil-pbc-curve-locally-constant-reduction`: its F_r-module argument uses
only the unchanged finite clause, so its `holds:true` is correct. No citer was edited.

No additional Lean or node mismatch was found in this repaired version. I retained
both modules and their node signatures, rather than rewriting correct code. The
only second-reader change is this independent review report. Both modules compiled
together locally, in dependency order, with exit code 0 and no warnings. Server
compile and packaging validation follow through `deliver2.py --no-push`.


## H10 repair of R-sub-D (f6404ca40)

1. Named all repeated representation targets: `galoisFiniteRepresentations`,
   `galoisIntegralRepresentations`, `galoisCoefficientRepresentations`, and
   `galoisAdicRepresentations`. The latter three use `galoisRepLinearAction` and
   the same pullback along `δ.symm`. Named the underlying module sheaf of sets
   `galoisUnderlyingSetSheaf` and its supplied FLC witness `galoisUnderlyingFLC`.
   Named the diagonal and scalar actions `galoisTensorAction` and `galoisScalarAction`.
   Each is a definition with actual data, source docstring and the item's blueprint tag;
   the old recorded predicates and action definitions are reused directly.
2. Replaced the large existential/conjunction with two correspondence structures.
   Each inherits its shared data from a separate data structure. Naming the clause
   predicates also keeps generated constructors, recursors and projections small.
   All property fields are Prop-valued. Independent conjuncts under universal
   quantifiers are split; clauses sharing an existential witness stay together.
   No mathematical hypothesis or conclusion has changed. In particular the SAME
   `c.γ` fixes the integral action through `κ` and the projections at every finite
   level, and rational/algebraic actions are tied to that integral action exactly
   as before. No new DAG notion is introduced by these internal packages; all are
   declarations of this item in its own module, as requested by the reviewer.

Current field map (the detailed hypothesis/clause table above still describes
exactly these fields and their unfolded predicates):

| Content | Correspondence field(s) |
| --- | --- |
| Finite group/fibre identification | Inherited `γ`, `Φ`, `η`, `e`, `τ`; `yonedaComparison`, `finiteEtaleAction`. |
| Finite abelian category, kernel/cokernel closure, exactness | `finiteAbelian`, `finiteKernels`, `finiteCokernels`, `finiteLimits`, `finiteColimits`. |
| Finite constant unit and canonical evaluation action | `finiteUnit`, `finiteEvaluationAction`; `h` and `κ` remain shared inside the latter. |
| Finite tensor and all braided constraints | `finiteTensor`; the SAME existential `m,b` governs both functors and the unit clause. |
| Finite scalar extension and composites | `finiteScalarExtension`; the SAME existential `B,α,β` and comparison `c` govern both diagrams. |
| Adic model and natural evaluation equivalences | Inherited `P`, `δ`, `eI`, `eR`, `eA`, `τI`, `τR`, `τA`. |
| Rational and algebraic abelianity/exactness | `rationalSheavesAbelian`, `rationalRepresentationsAbelian`, `rationalFiniteLimits`, `rationalFiniteColimits`; the corresponding four `algebraic…` fields. |
| Evaluation action through the finite correspondence | `integralEvaluationAction` refers to `c.γ`; `rationalEvaluationAction`; `algebraicModelScalarExtension` includes its original pure-tensor fibre equation. |
| Adic monoidal functors with prescribed tensors/units | `integralMonoidal`, `rationalMonoidal`, `algebraicMonoidal`, each retaining the shared existential monoidal structure. |
| Diagonal tensor actions and trivial units | `integralTensor`, `integralUnit`, `rationalTensor`, `rationalUnit`, `algebraicTensor`, `algebraicUnit`. |
| Coefficient-model and coefficient-extension comparisons | `algebraicModelScalarExtension`, `integralScalarExtension`, `rationalScalarExtension`; the last retains one family of linear equivalences shared by equivariance and naturality. |

Searches repeated for this refactor: launcher LeanFinder query “lisse sheaves finite
and adic continuous representations fundamental group equivalence tensor scalar
extension” returned generic condensed-module constructions, not this statement.
Loogle query `Representation.asGroupHom, LinearMap.GeneralLinearGroup.generalLinearEquiv`
returned no combined hit; both individual declarations are reused from the imports.
Launcher Mathlib grep `galois.*(Representations|Correspondence|TensorAction|ScalarAction|Underlying)`
returned unrelated field-theoretic Galois correspondences. Exact-name `rg` over Mathlib,
upstream `WeilConjectures` and project `lean/Sheaf` found no clashes for the new names.
These are transparent packaging definitions of the item's existing terms, not
replacement definitions of continuity, tensor, scalar extension or lisse sheaves.

Edge cases rechecked: finite noncommutative and zero rings remain admitted;
all zero module/vector-space cases remain admitted; `n=0`, identity and composite
coefficient maps are included; all Noetherian/separated/invertibility/prime and
algebraic-closure hypotheses remain exclusively in part (2). Quantifier order is
still one simultaneous finite family followed by every allowed adic setting.
`LisseAdicFiberFunctors.lean` and its node are unchanged. The restored dependency
`def-pod-lisse-l-adic-sheaves` is unchanged. All theorem proofs remain `sorry`;
this module's only theorem is `galois_lisse_representations`.

Local validation: the repaired item compiled in 24.5 s with exit code 0, no warnings,
and both auto-implicit options disabled. A fresh independent second reader must
review this refactoring; the earlier second reading above is historical only.

3. Server serialization validation: compiled the item alone against the landed
   `LisseAdicFiberFunctors`, from the project's Lean directory with the options
   sourced from `tools/sheaf_env.sh` (the same options used by `tools/lean_file.sh`),
   `LEAN_PATH` from `lake env printenv LEAN_PATH`, two threads, `nice -n 19`, and
   a hard `timeout 60`. Added both `-o` and `-i` to the Lean command on a scratch
   copy. `/usr/bin/time` measured **59.14 s**, exit **0**, without warnings.
   Both artifacts were produced: `.olean` 4.3 MiB, `.ilean` 159 KiB.
   This checks serialization, unlike `compile_remote.sh` or `lcompile.py`.
   The scratch-copy comments describing the data records were clarified afterward;
   every declaration and its elaborated type are unchanged from this measured compile.

Packaging repair following the dry-run preflight: as R-sub-D's notice records,
`LisseAdicFiberFunctors.lean` has already landed identically, without its new DAG
node. The first dry run therefore rejected the unchanged module as not a commit
change. The new node now records `existing: true`, `branch: sheaf-dag` and the same
module/declarations/signature; its `file` key is removed. The identical module is
preserved in the sandbox scratchpad and omitted from this delivery. Its data and
proof statements are untouched. The item continues importing the landed module
and citing the new node. This is precisely the existing-project-declaration form
of brief-stage2 §5 and changes no mathematical content or statement dependency.
The old independent second reading is historical; this worker does not write a
new one. The next worker must review the correspondence refactor and this existing
record before pushing.

## Second reading by Q1

Fresh independent second reading of the H10 correspondence refactor, 2026-10-12.
I opened the corrected node, all 779 lines of GaloisLisseRepresentations.lean,
the dependency records and their declarations, and the existing fibre-functor module.
The historical readings above are not the basis of this verdict.

I first checked the correction against Stacks etale-cohomology.tex,
lemma-locally-constant-on-connected (0DV5), in /home/ubuntu/c1-stacks-review,
and the supplied Weil II PDF text (0.1), (1.1.1)b)-d), printed pages 144, 146-147.
Stacks assumes only connectedness and a geometric point for finite rings, including
noncommutative rings. Weil II imposes Noetherianity, separatedness and invertibility
of ell throughout. Keeping these assumptions exclusively in part (2) is correct.
I opened lem-wf-dense-open-pi1-surjective: its unrestricted adic clause does not
supply the new assumptions, so holds:false is appropriate. I also opened
lemma-weil-pbc-curve-locally-constant-reduction: its finite F_r argument uses only
part (1), so holds:true is appropriate. No citer or unit target was changed.

The object/hypothesis/conclusion inventory and its rendering are:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Connected scheme Y | Scheme.{u}, ConnectedSpace Y in the theorem | Matches. |
| Geometric point | Field Ω, IsAlgClosed Ω, y : Spec (.of Ω) ⟶ Y | Matches. |
| Specified profinite pi_1 and its evaluation action | G, IsFundamentalGroup (FiniteEtale.fiber y) G, γ, Φ, η, yonedaComparison, finiteEtaleAction | Matches; η ties γ to the given actions, rather than choosing an unrelated group action. |
| Every finite ring and finite left modules | finite data e quantifies Ring Λ, Finite Λ; LisseModuleSheafCategory and galoisFiniteRepresentations | Matches; no commutativity restriction on this clause. |
| Local trivializations, module-linear maps, discrete continuous equivariant maps | IsLisseModuleSheaf, full subcategory of Rep, finite carrier and open stabilizers | Matches; morphisms are inherited linear equivariant maps. |
| Evaluation on fibres, naturally, with the prescribed action | τ plus finiteEvaluationAction; κ preserves every germ and intertwines ρ with γ | Matches. |
| Full abelian subcategory, kernels/cokernels, exactness | full-subcategory definition, finiteAbelian, finiteKernels, finiteCokernels, finiteLimits, finiteColimits | Matches. |
| Commutative tensor equivalence and associativity/commutativity/unit constraints | finiteTensor: one shared m,b, strong braided inclusion and representation functor | Matches; inclusion ties the source tensor to the ambient sheaf tensor. |
| Constant unit sent to trivial representation | finiteUnit and finiteTensor's constant-sheaf clause | Matches, including arbitrary finite rings. |
| Finite coefficient extension, naturality, action 1 tensor σ | finiteScalarExtension: shared B, α to Sheaf.ringExtendScalars, β through ringExtendScalars.mapAction | Matches. |
| Compatibility with composite ring maps | same comparison c in the representation diagram and sheaf pure-section equation b tensor (a tensor z) maps to b*g(a) tensor z | Matches; shared witnesses retained by the refactor. |
| Adic assumptions only in part (2) | nested Fact l.Prime, IsNoetherian Y, Y.IsSeparated, residue-field Invertible | Matches the source correction. |
| Algebraic closure and every finite coefficient field E | Q with IsAlgClosure, Padic.FiniteCoefficientFields l Q | Matches. |
| Three equivalences for integral, rational and algebraic coefficients | eI, eR, eA in GaloisLisseAdicData | Matches recorded lisse categories and representation predicates. |
| Same fundamental group at all three levels | P and δ : G ≃ₜ* P; action pulled back by δ.symm | Matches; P is a bundled model, not a replacement action. |
| Natural integral/rational/algebraic evaluation | τI, τR, τA to existing lisse*FiberFunctor | Matches. |
| Finite-level action through part (1) | integralEvaluationAction uses c.γ, germ-preserving κ and every limit.π | Matches; the shared c survives structure inheritance. |
| Rational and algebraic action induced by scalar extension | rationalEvaluationAction pure-tensor formula; algebraicModelScalarExtension equivariance and τA/τR fibre formula | Matches. |
| Rational and algebraic categories abelian, equivalences exact | four rational fields and four algebraic fields for Abelian and preservation of finite limits/colimits | Matches; no extra integral exactness condition. |
| Tensor and units at every adic level | integral/rational/algebraicMonoidal prescribe tensorObj and tensorUnit; corresponding Tensor and Unit fields | Matches; diagonal actions use Representation.tensorDiagonal and units Rep.trivial. |
| Extension E ⊂ L | integralScalarExtension natural iso; rationalScalarExtension one family c with equivariance and naturality | Matches; algebraMap is constrained to the actual inclusion, whose toAlgebra supplies an instance. |
| Quantifier order | one simultaneous finite correspondence c, followed by all admissible l,Q and simultaneous coefficient-field families | Matches; γ is fixed before all adic settings. |

I read FiniteEtale.fiber, pointSmallEtale and Point.sheafFiber, the set-valued
local-constancy predicates, IsLisseModuleSheaf, LisseModuleSheafCategory,
IsLisseIntegralDiagram and the rational Hom/category and coefficient localization
in LisseAdicSheaves, the full LAdic representation predicates/actions, and
exists_fiber_flc_equivalence. Integral levels are killed by I^(n+1) and have the
surjective transition/kernel reduction condition. Rational morphisms are genuinely
rationalized Hom; algebraic morphisms are the coefficient 2-colimit localization.
The target predicates require finite generation, finite dimension and the prescribed
topologies/descent, rather than arbitrary actions.

The new node def-pod-lisse-adic-fibre-functors is justified by Weil II (1.1.1)b)-d).
Its existing:true record names the landed module, whose twelve declarations I opened.
Integral maps are whiskered stalk maps followed by lim. The rational existence theorem
prescribes a tensor f to a times the extended integral stalk map. The algebraic theorem
prescribes the fibre object and natural scalar comparisons on each model with the pure
tensor formula. Definitions choose these specified functors from named existence
statements; their data are not sorry. Model category laws are separately named theorem
placeholders. The node has the required source, searches, definition/split status,
ancestry, chapter/unit, creation data, empty proof and proof_deps, and audit-none fields.
There is no delivery dependency module: the restored def-pod-lisse-l-adic-sheaves node
is unchanged, and the existing fibre-functor module is correctly omitted from delivery.

Independent searches: launcher LeanFinder query "locally constant module sheaf stalk
equivalence continuous fundamental group representations" found eight condensed-module
results, no matching corollary. Loogle "CategoryTheory.Sheaf, CategoryTheory.Equivalence"
found twelve generic site/sheaf equivalences. Launcher grep
"lisse.*[Rr]epresentation|adic.*[Ff]iber.*[Ff]unctor" found no Mathlib result.
Direct rg over upstream WeilConjectures, project lean/Sheaf and the DAG found the landed
fibre functors and generic fibre equivalences, no other DAG definition of these specialized
functors. I opened the upstream exists_equivalence_isFiniteLocallyConstantSheaf_of_isFundamentalGroup:
it uses CommRing, only specifies the underlying module fibre, and omits coefficient change,
the specified evaluation action and adic clauses. It cannot replace the whole corollary.
I also opened Rep.IsFiniteContinuous: it requires CommRing, so it does not supply the
noncommutative Ring predicate needed here. The refactor's category/action wrappers reuse
existing notions and add no alternative definition of lisse sheaves or adic continuity.

Edge cases: zero rings and zero modules/vector spaces are allowed. Empty schemes cannot
have the supplied geometric point. There is no freely quantified index family; the adic
index ℕ includes n=0, representing exponent one. Ell=0,1 are excluded by primality only
in part (2). Characteristic ell is allowed in part (1) and excluded by invertibility only
in part (2). Identity/composite ring maps and E=L are included. The universe u is arbitrary;
scheme, geometric field and fundamental-group model follow the recorded same-universe
convention, with module coefficients/values in u+1 and no independent smaller test universe.

No new mathematical mismatch was found. I retained the Lean and node records without
rewriting correct clauses. The sole second-reader change is this fresh review section.
The theorem docstring gives all proof steps, every declaration carries the source and
blueprint tag, no data definition contains sorry, and the only theorem proof in the item
is sorry. All binders/universes are explicit. Local compilation completed in 24.8 seconds,
exit 0, without warnings. The recorded theorem signature agrees verbatim with the file.
