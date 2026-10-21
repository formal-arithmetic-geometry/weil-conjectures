## Worker report

Delivered module: `Sheaf.RepresentationTheory.ProfiniteAlgclDerivedInvariantsComparison`.
Main declaration:
`Profinite.AlgclInvariantsComparison.profinite_algcl_derived_invariants_comparison`.
This is a stage-2 statement, with precisely one postponed theorem, whose proof is `sorry`.
All definitions contain actual data or define propositions/specifications; no object is
chosen using the main theorem or any unspecified existence theorem.

The previous worker's stale-assignment diagnosis confused completion of stage 1 with
completion of stage 2. `coord/ledger.md:23387` records NN's reviewed proof split; NN's
report ends "No Lean was written and no compiler or build command was run." The item's
live node had no `lean` record. Consequently this delivery supplies its first Lean
statement and does not repeat or modify the stage-1 split.

### Hypotheses and clauses

- Prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`.
- Norm-topological algebraic closure: the existing `PadicAlgCl ℓ`, with its existing norm
  and topology, is the chosen model of the algebraic closure. It is not `PadicComplex ℓ`
  and is not completed in this module. This is the same model used by the recorded
  `sk-def-sfb-qlbar-condensed` declaration.
- Finite intermediate field: `(E : PadicAlgCl.FiniteIntermediateField ℓ)`. Its subtype
  field, embedding and inherited norm topology are the existing ones. No Galois or
  unramified condition is imposed on E.
- Arbitrary profinite group: `(G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]`.
  Compact Hausdorff totally disconnected groups are precisely profinite groups. There
  is no finite generation, finite dimension, index or cohomological dimension hypothesis.
- A is `scalarRing`, which only bundles the existing `continuousMapRingObj E` as a
  `CondensedBar.Ring`. Its internal modules and actions are the recorded `Modules` and
  `Equivariant`, hence the actual `Mod` and `CondensedAction.ActionModule` categories.
- C is the existing `padicAlgClRingObj ℓ`, with exactly finite-subextension-valued
  continuous sections. `finiteModule` is its regular internal module restricted along
  the existing `padicSubfieldRingObjToPadicAlgCl ℓ E`.
- B is the existing `continuousMapRingObj (PadicAlgCl ℓ)`, with all norm-continuous
  sections. `normModule` is its regular internal module restricted along
  `normScalarMap`. The latter is the abelian-sheaf image of the existing continuous
  ring-sheaf postcomposition map for the inclusion E into Omega.
- Scalar inclusion c is an internal A-linear map `finiteModule ⟶ normModule`.
  The FIRST conjunct of `Comparison` fixes its section map at EVERY profinite S by
  `((c.hom.hom.app (op S)) z).down = z.down.val`. This is literal subtype inclusion,
  including the canonical ULift convention. It is not an arbitrary scalar map.
- The ordinary relative tensor is `TensorModel.underlying`, a natural isomorphism with
  `forgetAction ⋙ (curriedTensor _).obj R`. Thus the tensor is the recorded internal
  tensor OVER A, not tensor over integers or an underived surrogate for the derived
  tensor. `TensorModel.action` fixes the action on every local pure tensor to
  `g (z tensor m) = z tensor (g m)`, using the existing internal relative `pureTensor`.
  Both coefficient modules have trivial G-action; the input retains its given action.
  Naturality of the underlying isomorphism also fixes the functor's maps.
- The SECOND conjunct of `Comparison` fixes the ordinary natural transformation eta
  by `eta_M ; underlying_B = underlying_C ; (c ▷ M.module)`. On local generators this
  is exactly `z tensor v ↦ c(z) tensor v`.
- `DerivedTensor` has the actual unbounded `DerivedCategory` as source and target and
  carries its counit and Mathlib `IsLeftDerivedFunctor` universal property. Its
  `kflat` field requires the counit to be invertible on EVERY equivariant complex
  whose underlying A-module complex is K-flat, with the existing
  `CochainComplex.IsKFlatForTotalTensor`. Thus it computes scalar tensor on K-flat
  representatives. Its shift is compatible with the counit (`shiftCounit`), so it
  is the derived shift structure, not an unrelated choice of shifts.
- `derivedCoefficientMap` is the actual Mathlib `Functor.leftDerivedNatTrans` induced
  by eta on the homotopy category. Its defining universal counit equation determines
  it uniquely. No map or isomorphism is selected from `Nonempty`.
- `V : CondensedBar.Invariants` uses the recorded normalized invariant-subsheaf
  functor: inclusion is sectionwise injective with image exactly the sections fixed
  after every profinite base change, and both adjunction transposes retain those
  same section maps.
- `pointEvaluation` is literally `Mod.forget ⋙ sheafToPresheaf ⋙ evaluation` at
  `Profinite.of (ULift PUnit)`. It forgets scalars and evaluates at a one-point
  profinite set. Its additivity and exactness are ASSERTED by `Comparison`, never
  assumed as hypotheses of the theorem.
- The functors in the conclusion are
  `LC.functor ⋙ (V.functor ⋙ pointEvaluation).rightDerivedFunctor` and its B analogue.
  These are the node's functors expressed AFTER restriction to A. The node's recorded
  bar theorem explicitly supplies scalar-restriction compatibility, with the map
  induced by the inclusion of invariant submodules and termwise derived Hom maps.
  Hence forgetting the R-action before computing ordinary derived invariants gives
  the same underlying derived object and the same specified morphism as forgetting
  it afterward. This is used in the item's own proof step 2 and the scalar-naturality
  part of step 4. Exact point evaluation also identifies
  `R(ev_* Gamma_G)` with `ev_* R Gamma_G`: apply the same K-injective resolution to
  Gamma_G and then the exact evaluation functor. This presentation does not assert
  either coefficient comparison is an internal condensed isomorphism.
- `Comparison` asserts that both derived tensor functors are triangulated. Composing
  with the existing triangulated ordinary right-derived functor gives the two exact
  functors to `DerivedCategory Ab.{u+1}` required by the node. Its
  `NatTrans.CommShift` conjunct supplies compatibility of the FINAL comparison with
  their standard shift isomorphisms.
- Finite-dimensional norm-topological W is `(W : Type (u+1)) [NormedAddCommGroup W]
  [NormedSpace E W] [FiniteDimensional E W]`; its E-linear action is
  `ρ : G →* Module.End E W`, and its CONTINUOUS action is exactly
  `Continuous (fun x : G × W ↦ ρ x.1 x.2)`. No discrete topology is substituted.
- `RepresentationModel` specifies underline W through additive section equivalences
  with `C(S,W)`, restriction by precomposition, pointwise scalar multiplication and
  `g(s)` acting via the given rho. Existence of this object for EVERY such W and rho
  is part of the assertion. These formulas uniquely identify it up to the compatible
  internal equivariant isomorphism; it is not an arbitrary object or chosen model.
- The last clause is `IsIso` of the ACTUAL whiskered derived natural transformation
  at `((DerivedCategory.singleFunctor _ 0).obj N.object)`, in `D(Ab)` itself. It is
  not just an isomorphism on each individual cohomology group.
- `Assertion` existentially supplies the abelian and Grothendieck structures on the
  SAME recorded action category, uses the standard derived localizations, and asserts
  `Comparison`. Thus no extra abelian/Grothendieck/K-flat resolution assumptions were
  added to the mathematical hypotheses. This follows the recorded bar assertion's
  way of making the underlying category structures explicit.

### Dependencies actually used

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, reexported by the
  action interface. Rings retain the existing tensor-abelian sheaf structure.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, regular modules, module
  morphisms and scalar restriction; the action and tensor modules publicly expose it.
- `Sheaf.CategoryTheory.CondensedActionModule`:
  `Profinite.CondensedAction.ActionModule`, `Modules`, `Invariants`, their section
  modules and fixed-section normalization. `CondensedBar.Equivariant` and
  `CondensedBar.Invariants` are transparent aliases for precisely these declarations.
- `Sheaf.CategoryTheory.CondensedDerivedInvariantBar`:
  `CategoryTheory.CondensedBar.condensed_derived_invariant_bar`, including its
  scalar-restriction and augmentation normalization; its public data module exports
  `Ring`, `Modules`, `Equivariant`, `ActionAbelian` and `Invariants`.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClRingObj`, `padicAlgClCondensedRing` and the all-continuous
  ring objects. The imported `FiniteSubextension` module exports the exact recorded
  finite-field scalar inclusion and the finite-field colimit comparison.
- `Sheaf.Topology.ContinuousMapCondensedRing`: the recorded universe-general
  continuous-map sheaf interface. The Type-0 specialization here is definitionally
  the published `continuousMapRingSheaf`/`continuousMapRingObj` on the fixed fields.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the recorded
  unbounded derived convention. In these Grothendieck categories the actual ordinary
  right-derived functor is the existing upstream `Functor.rightDerivedFunctor` from
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`, with its
  standard triangulated structure from `...RightDerivedFunctor.Triangulated`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`: the recorded
  relative derived tensor/Hom convention and its generic module-object tensor
  machinery. The relative tensor used in `TensorModel` is that existing tensor;
  its universal left-derived pair implements the K-flat convention equivariantly.
- `Profinite.CondensedAction.InternalBar.pureTensor` (publicly exported by the bar
  module) is the existing local generator map for relative internal module tensor.
- Mathlib `Functor.IsLeftDerivedFunctor`, `Functor.leftDerivedNatTrans`,
  `NatTrans.mapHomotopyCategory`, `Functor.IsTriangulated`, `NatTrans.CommShift`,
  `DerivedCategory.singleFunctor` supply the universal functor/map and shift APIs.

All recorded proof-dependency modules that already have Lean declarations are imported
as plain proof imports; the module-level docstring reproduces all eight proof steps.
The still-unstated analytic proof nodes are cited in that proof plan, rather than
assumed as hypotheses or replaced with continuous-cochain computations by definition.
No dependency module and no new independent notion/node is required: the specifications
in this module are helper declarations of the comparison notion itself, as permitted
by the human's missing-helper authorization. All are listed in `lean.declarations`.

### Edge cases checked before writing and in the second pass

W = 0 is allowed (no positive rank/basis-size binder); both derived tensors and the
comparison reduce to zero. G = 1 and finite G are allowed without any change of
topology or cohomological-dimension hypotheses. Profinite test objects S may be empty;
section equivalences and generator equations quantify over all S and are compatible
with its unique continuous section. Degree zero is `singleFunctor _ 0`; negative
degrees are not discarded from the ambient unbounded categories. No positivity of
cohomological degree is assumed in the final `IsIso` statement. E may be the base
field. B remains incomplete Omega, whereas C has precisely one finite field for an
entire section; compact images are never assumed to lie in a finite extension.
The site universe u and section universe u+1 are the recorded size convention; W
lives in u+1 and the standard derived categories have hom universe u+2. Finite
-dimensional spaces in larger presentations can be transported along their finite
basis isomorphism, with their given norm topology. No equality between the site's
object and morphism universes was imposed.

### Searches

The sandbox's `searches.jsonl` retains the actual msearch results.

- `msearch.py ... leanfinder`: "Underlying derived invariants comparison for profinite
  continuous finite dimensional representations with finite subextension and norm
  algebraic closure coefficients". Eight hits: Hilbert 90, algebraic invariant rings
  and infinite Galois projections; none states this ordinary internal-condensed
  comparison after point evaluation.
- `msearch.py ... loogle`: `PadicAlgCl, invariants, Condensed`. No hit; Loogle reports
  unknown identifier `invariants`. This is a failed name query, not proof that no
  relevant declaration exists.
- `msearch.py ... grep`: `(Condensed|PadicAlgCl).*(invariant|[Cc]omparison)`.
  Four hits are imports of condensed TopComparison; none is this statement.
- `msearch.py ... leansearch`: "ordinary condensed derived invariants compare norm
  algebraic closure coefficients finite subextension valued coefficients profinite
  group". Eight hits on PadicComplex norms, valuations, spectral norms, closed
  subgroups and the profinite inverse-limit isomorphism. None is the comparison.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
  by the exact node id and proposed namespace/module name: only the downstream
  `NormAlgclCohomologyTopologyComparison` proof docstring cites this node; no existing
  statement. `grep -rn` of the exact id in `lean/WeilConjectures` returned no hit.
- Concept searches of condensed action, scalar restriction, tensor action, continuous
  module condensation, and profinite derived invariants found the exact existing
  action/bar, pure-tensor and finite-subextension interfaces used above. The
  discrete-representation derived-invariants comparison has different coefficients
  and a different category; it is not used to replace this statement.

No statement correction and no STATEMENT-DISPUTED flag. The four analytic obligations
of the stage-1 proof remain obligations; this stage-2 delivery does not claim them
proved or supplied by the blueprint paragraph.

### Validation

The prescribed scompile.py checked the file separately under its sandbox module name
and its final library module name, with no errors or warnings (14.6 s and 15.7 s).
Every universe/variable is explicitly bound (`autoImplicit false`). All lines fit
100 characters. The only postponed theorem is the item's own named theorem; its
full natural-language eight-step proof is in its declaration docstring.

## Second reading by NZ

This is a second pass by the same dispatched worker; no other agent was started,
as the task forbids it. The maintainer supplies the independent delivery review.
I reopened the live node, its eight proof steps, each recorded dependency interface,
and the final Lean file. The report above matches each hypothesis and clause.

The second pass corrected the initially underspecified shift convention: each
`DerivedTensor` now records a shift structure whose counit commutes with shifts, and
the final transformation uses these structures and the existing standard right-derived
shifts. It also added the exactness clauses for literal point evaluation, so the
presentation as `R(ev_* Gamma_G)` has precisely the node's `ev_* R Gamma_G` meaning.
I checked that the coefficient map is forced on ALL sections, eta is forced as a
natural tensor map, and its derived map is constructed with Mathlib's universal
`leftDerivedNatTrans`. The theorem consequently cannot be satisfied by picking an
unrelated isomorphism. All normalization and existence conditions occur in the
conclusion, not as strengthened hypotheses. The statement's functors are ordinary
unbounded derived functors on the recorded internal action category. No continuous
cochain model has been substituted in their definitions.
