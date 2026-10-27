## Worker report

The module Sheaf.RepresentationTheory.TrivialProcyclicRestrictionIsomorphism states
`ContinuousCohomology.TrivialProcyclic.trivial_procyclic_restriction_isomorphism` with
`sorry`. The three helper definitions contain real data: the integer inclusion and
the two displayed propositions collecting the scalar and finite-coefficient clauses.
No dependency interface repair, new definition node, or statement correction is needed.
The statement remains verbatim. Three already landed definition nodes are added to
stmt_deps because their existing declarations bundle the specified coefficients,
provide the lifted p-adic integer group, and realize the continuous tensor coefficients.

Hypotheses and conclusions, clause by clause:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- `(Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[ℓ] Ω]
  [IsAlgClosure ℚ_[ℓ] Ω]` is the algebraic closure with the extended norm. The
  NormedAlgebra structure says that the norm extends the p-adic scalar norm; it is
  not completeness. The intermediate field inherits the subspace norm topology.
- `(E : IntermediateField ℚ_[ℓ] Ω) [FiniteDimensional ℚ_[ℓ] E]` says finite
  intermediate field. The four final conjuncts cover exactly F=E and F=Ω, without
  replacing Ω by its completion or by finite-image functions.
- `continuousScalarRing F` is precisely the existing continuous-map coefficient
  ring bundled in CondensedBar.Ring, with Profinite.{u}, coherent topology,
  abelian coefficients in u+1 and the recorded ordinary derived localizations.
  These compatible universes contain both fields and test objects; arbitrary
  finite-dimensional W is allowed in Type (u+1), not just Type u.
- `IntegerGroup.{u} ℓ` is Multiplicative (ULift ℤ_[ℓ]) with its p-adic topology.
  `integerInclusion` sends k to its actual integer cast, so u(1) is positive additive
  one, not the multiplicative identity (which represents additive zero).
- `TotalModel` and `HasComparison` are the recorded cyclic degrees 0,1 model and
  invariant-normalized lambda. `trivialCyclicMap` is exactly c_A after the canonical
  trivial-residual forgetful and coordinate identifications. `cyclicMap` is c_N in
  the existing relative category with residual group PUnit. Exact conservative
  forgetting identifies its invertibility with invertibility of scalar c_N.
- The quantifiers over K,C range over all compatible cyclic models. They are
  presentations of the already specified construction, not a hypothesis that c is
  invertible. The dependency theorem supplies these models.
- `BarModel`, `barFunctions`, `barDiagram` use the actual free internal module and
  its tensor right adjoint, computed in the second variable on a single compatible
  nonnegative equivariant resolution. For the regular module its sections are all
  C(S x H^q,F): evaluate a generalized natural function on the tautological pair
  over S x H^q, with inverse restriction along (f,g). Thus the underived source
  is U_A, with its trivial-action inhomogeneous differential. `extend` is extension
  from nonnegative degrees by zero to negative degrees.
- `barAugmentation ... I`, extended and mapped by Q, is the actual j_A with (q,0)
  component given by I.ι.f 0 and the total coprojection. This is not a chosen
  isomorphism. The first ScalarAssertion conjunct asserts its `IsIso`.
- `barEta M b ... I` is the invariant-inclusion-normalized derived-bar isomorphism.
  Quantification over `BarNormalization M` retains the specified invariant inclusion;
  the recorded `barNormalizationExist` supplies such data for every compatible model.
- The second ScalarAssertion conjunct is `IsIso (trivialCyclicMap ...)`.
- The third conjunct is exactly the displayed c_A eta^{-1} j_A = Q epsilon:
  Lean composition writes `Q.map (extendMap j) ≫ eta.inv ≫ c = Q.map (extendMap epsilon)`.
  The recorded evaluation has degree-zero identity, degree-one evaluation at u(1),
  and zero components in degrees at least two, with the same zero-differential target.
- In FiniteAssertion, W has AddCommGroup, Module E and FiniteDimensional E and is
  given trivial action by `Representation.trivial`. `Extended E F W` is the existing
  algebraic tensor product with moduleTopology F, which is the finite product norm
  topology. `Realization` identifies every section with C(S,F tensor_E W), including
  pointwise scalar, restriction and generalized group-action formulas. The conclusion
  is IsIso of the recorded canonical `cyclicMap` on that exact object.
- The statement adds no completeness or termwise internal-Hom acyclicity assertion.

Dependency declarations inspected and used:

- Mathlib.CategoryTheory.Monoidal.Mod: CategoryTheory.Mod, Mod.regular; ModObj is
  the internal action law and Mod.Hom the linear morphism, not ModuleCat over a
  section ring.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory, HasDerivedCategory,
  DerivedCategory.Q. The size-convention dependency is metatheoretic and has no
  single Lean definiendum; explicit universe u and recorded localizations implement it.
- Sheaf.CategoryTheory.CondensedActionModule: Profinite.CondensedAction.ActionModule,
  trivial, inflate, sectionModule and the normalized fixed-section invariants.
- Sheaf.Topology.ContinuousMapCondensedRing:
  Profinite.continuousMapRingSheafOfUniverse, continuousMapRingObjOfUniverse and its
  canonical monoid structure, used by continuousScalarRing.
- Sheaf.CategoryTheory.ContinuousScalarRing:
  Profinite.CondensedAction.continuousScalarRing (landed node
  def-sfb-bundled-continuous-scalar-ring, added to stmt_deps).
- Sheaf.Paper.IndUnipotentSystem:
  Profinite.CondensedAction.IndUnipotent.IntegerGroup (landed node
  def-sfb-ind-unipotent-system, added to stmt_deps). No unipotent-system hypothesis
  is imposed.
- Sheaf.Paper.ContinuousRepresentationCondensation: Realization,
  PrimeToEll.Extended, its original tensor module and module topology (landed node
  def-sfb-continuous-representation-condensation, added to stmt_deps).
- Sheaf.CategoryTheory.RelativeCyclicRestrictionModel:
  CategoryTheory.RelativeCyclic.relative_cyclic_restriction_model, barEvaluation,
  and its public dependencies RelativeCyclicTotal (TotalModel, HasComparison,
  cyclicMap), RelativeTrivialCyclicMap (trivialCyclicMap), RelativeBarData
  (BarModel, barFunctions, barDiagram, barAugmentation, barEta, evaluation).
- Sheaf.CategoryTheory.CondensedDerivedInvariantBar:
  CategoryTheory.CondensedBar.condensed_derived_invariant_bar and its recorded
  compatible Model/Assertion. The existing relative BarModel alias retains its
  larger localization then transports canonically to the small-Hom localization.

Proof-only imports cover the recorded scalar evaluation, complete-field column
acyclicity, noncomplete scalar augmentation and first-quadrant total comparison.
The infrastructure proof dependency lem-sfb-condensed-action-injective-infrastructure
has no recorded Lean declaration; its additive ordinary derived-invariants interface
is already imported through the relative cyclic model. No nonexistent module is imported.

Edge cases checked before writing:

- W=0: no Nontrivial W, positive dimension, chosen nonempty basis or nonempty index
  condition appears. Representation.trivial and Extended are defined for zero W;
  the inverse argument in the docstring is an empty sum between zero objects.
- Profinite S empty: all sections are the unique continuous map, and all the
  realization and bar generalized-element interfaces quantify over every S.
- H^0: power H 0 is the point; degree-zero evaluation is the original scalar identity.
- Negative degrees: the bar complex is extended by zero; the cyclic target has only
  degrees zero and one. No cohomology-only replacement of a derived isomorphism occurs.
- Every prime is allowed; no odd-prime restriction or positive characteristic is added.
- The base field E=Q_l is allowed; the two branches are valid also for dimension one.
- Ω is the norm algebraic closure, with no CompleteSpace instance requested.

Searches for an existing statement (msearch, 2026-10-24):

- LeanFinder: "Ordinary condensed derived invariants of the p-adic integers acting
  trivially on a finite dimensional norm topological vector space computed by cyclic
  restriction". Eight hits, including Rep.FiniteCyclicGroup.normHomCompSub and finite
  cyclic resolutions. These concern finite abstract representations, not the ordinary
  internal condensed comparison and its bar identity.
- Loogle: `"Condensed", "invariant"`: no hits.
- Mathlib grep:
  `(procyclic|PadicInt).*(cohomolog|invariant)|(cohomolog|invariant).*(procyclic|PadicInt)`:
  no hits.
- LeanSearch: "Trivial norm topological condensed p adic coefficients derived cyclic
  restriction bar augmentation isomorphism": eight hits concerning p-adic norms,
  completion and unrelated augmentation. None gives this statement.
- rg in WeilConjectures and Sheaf for procyclic, cyclic restriction, the assigned id
  and proposed declaration names: no existing declaration of the assigned statement.
  Found and reused RelativeCyclicRestrictionModel, ContinuousScalarRing,
  ProcyclicScalarCochainEvaluation and NormAlgclBarAugmentation; those assert the
  separate inputs, not scalar c invertibility together with all finite coefficients.
- The supplied CompactObject example module is withdrawn; its node now records the
  upstream WeilConjectures.CategoryTheory.CompactObject. Its full declaration and
  docstring were inspected along with the current module-mode conventions.
- Opened the latest blueprint direct-images proof paragraph (3). It supplies the
  open-direct-image context; the DAG explicitly labels this scalar obligation as
  agent-formulated with an exact external reference wanted. No new source claim is made.

Validation: server scompile.py and deliver2.py dry-run results are recorded below
once complete. No STATEMENT-DISPUTED or source correction.

Server scompile.py passed both sandbox and named-library compilation after making
ULift's identity equality explicit in the concrete integer-inclusion definition.
There are no errors or warnings; the only postponed theorem is the named main
statement. The file has 145 lines, no line over 100 characters, and autoImplicit false.
The node signature matches the theorem text verbatim. Only lean and the three added
landed statement dependencies differ from the read-only node.

The required deliver2.py --no-push dry run passed the server preflight and per-file
compilation (dry-run commit 42f01d7a3a4). No mechanical failures remain. The maintainer's
independent review is the independent reading; this worker did not start another agent.

## Second reading by Q114

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
