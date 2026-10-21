## Worker report

Item: `lem-sfb-admissible-scalar-realization-exact`. The delivery states
`AlgebraicGeometry.ProEtale.AdmissibleScalarRealization.admissible_scalar_realization_exact`
in `Sheaf.Paper.AdmissibleScalarRealizationExact`. Its sole theorem has proof `sorry`.
The eight other declarations are transparent abbreviations or predicates packaging this
node's own constructions and clauses. They contain real data and no postponed proofs;
there is no independent new notion or new DAG node. The original node statement, proof,
and dependency lists are unchanged.

Sources read: Stacks `sites-modules.tex`, `lemma-constant-exact` (093J), lines 8198 onward,
and `lemma-completion-flat` (093M), lines 8261 onward, including both proofs; the current
main-20261015 internal-Hom stability proof, paragraphs 2--3. I also read every statement
dependency's statement and Lean binding, and the bound source declarations/docstrings.
The compact-object example has been withdrawn; I read the live upstream replacement
`WeilConjectures.CategoryTheory.CompactObject` named by its node instead.

Hypothesis and clause correspondence:

- The fixed prime is `(ℓ : ℕ) [Fact ℓ.Prime]`; the arbitrary scheme is
  `(T : Scheme.{u})`, with no nonemptiness, finiteness, or separation assumption.
  Its site is exactly `Scheme.ProEt.topology T`, on `T.ProEt`.
- Finite coefficients are the first universally quantified clause, with
  `(A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [Finite A] [DiscreteTopology A]`. The premise
  `∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0` is exactly annihilation by a power of ell.
  No positive-exponent condition is imposed, so the zero ring is included.
- The finite extension is the third clause's `(E : Type u) [Field E]
  [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]`. `IntegralAssertions` and
  `RationalAssertions` install the recorded spectral absolute value's normed-field
  structure, hence the required ell-adic topology, rather than an arbitrary topology.
  Its valuation ring is the recorded `Padic.coefficientExtensionIntegers ℓ E`.
  Every uniformizer is covered: the integral predicate quantifies `π` with
  `Ideal.span {π} = Padic.coefficientExtensionMaximalIdeal ℓ E`.
- The remaining standard rings are `ULift.{u} ℤ_[ℓ]`, `ULift.{u} ℚ_[ℓ]`, and
  `ULift.{u} (PadicAlgCl ℓ)`. `ULift` has the existing transported ring and induced
  topology, so these are universe transports by the canonical continuous ring
  equivalence `ULift.ringEquiv`, not changed coefficient rings. In particular they
  allow every `Scheme.{u}` without equating site object and morphism universes.
- All six cases use `Profinite.continuousCoefficientRingObj A`, whose sections are
  `ULift C(S,A)`, and the actual `condensedRingObj ... T = p_T^* Λ`. The last case
  uses *all* continuous functions into the algebraic closure. There is no condition
  about landing in a finite subextension. The existing
  `IsLocalizingAdmissibleCoefficient` has a seventh compatibility alternative for
  finite-subextension-valued coefficients; this theorem explicitly lists the six
  inputs specified by this node and makes no assertion about that seventh input.
- Evaluation of the continuous-function ring on the one-point profinite set identifies
  its scalar ring with the displayed `A`: evaluate a function at the unique point,
  with inverse the constant function. The ring operations are pointwise. Thus the
  `IsNoetherianRing A` clause of `ScalarAssertions` is exactly the node's assertion
  about `R = Λ(*)`, transported along this canonical identification.
- `C_T` is precisely the recorded `FiniteConstantModel.modelFunctor A T`. It first
  uses `scalarModules`, applies constant sheafification, extends scalars along
  `scalarToContinuous A`, then uses `(upperStarFromPoint T).mapMod`. The scalar map
  sends `a` to its constant continuous function. Strong monoidality of inverse image
  and `constantSchemeIso` identify this with the displayed ordinary relative tensor
  `B_T ⊗_{constant A} constant M`. No derived tensor or completed tensor is used.
- `ScalarAssertions` states `(modelFunctor A T).Additive`,
  `PreservesFiniteLimits`, and `PreservesFiniteColimits`. For these abelian categories
  this is exactly additivity and preservation of every short exact sequence.
  The source is all `ModuleCat.{u+1} A`, with no finite-generation, presentation,
  freeness, or boundedness restriction on its objects.
- `localizedModel A T U` applies the existing internal/section module equivalence and
  `SheafOfModules.overFunctor _ U` to that same functor. Its coefficient sheaf is
  literally the restriction of the reconstructed ring sheaf of `B_T` to the over site.
  The universal clause over `U : T.ProEt` asserts additivity and both finite limit
  and colimit preservation for these actual localized functors.
- The finite ring identification is
  `IsIso (FiniteDiscreteOrdinary.canonicalAbelianMap A T)`. This is the existing
  normalized map from the constant ring to the actual coefficient ring, not a
  newly selected comparison. Its construction is the canonical monoidal
  `constantSchemeIso` followed by sheafified constant functions. It is a ring map
  (as checked in the existing encoding module), so invertibility is the required
  canonical ring identification. Restricting this specified map gives the finite
  identification on every localized site as well.
- `CompletedIdentification A T p` uses the actual reconstructed commutative ring
  sheaf of `condensedRingObj (continuousCoefficientRingObj A) T` and the existing
  `Scheme.adicLisseCompletedRing T (Ideal.span {ULift.up p})`. That latter object
  is the genuine inverse limit of `adicLisseRingSystem`, whose level `n` is the
  constant ring `ULift A / (p)^(n+1)` and whose arrows are the quotient factor maps.
  Positive exponents are therefore precisely `n ≥ 1` in the node; the zero quotient
  level has not been inserted into the required tower.
- The comparison is normalized at every pro-etale object, scalar, and positive
  quotient projection: the image of the canonical constant scalar `a`, under the
  ring isomorphism and the `n`th projection, equals the sheafification-unit image
  of its residue class modulo `(p)^(n+1)`. The statement records the unique ring
  isomorphism with this normalization. This expresses the canonical identification,
  retaining the constant-scalar algebra structure. Uniqueness follows by reducing
  modulo each power: the source quotient is the constant quotient sheaf, so locally
  every residue lifts to a scalar, and the projections jointly distinguish maps.
  In particular the comparison is not an unnormalized choice of equivalent rings.
- `CompletedAssertions` requires `PreservesFiniteLimits` and
  `PreservesFiniteColimits` for `Mod.extendScalars (scalarMap A T)`, on *all* internal
  modules over the pulled-back constant ring. Here `scalarMap` is exactly
  `(upperStarFromPoint T).map (scalarToContinuous A)`. By `constantSchemeIso` its
  source is canonically the constant scalar ring. Thus this is the full sheaf-module
  flatness clause, stronger in scope than merely exactness on constant modules,
  and exactly the scope required by the node.
- `LocalizedFlatness` restricts the regular `B_T` module, with its scalar action
  restricted by that same `scalarMap`, to every over site. Its predicate is the
  existing `SheafOfModules.IsFlatOnSite`, i.e. exactness of ordinary sheaf tensor
  on *all* module sheaves on that localized site. The coefficient, module, site
  object and site Hom universes are explicitly supplied. Ring identifications
  restrict by the existing sheaf-over functor, so their localized versions are
  included without selecting additional unrelated isomorphisms.
- The second main clause gives the integral assertions for the standard integer ring
  with `p = (ℓ : ULift ℤ_[ℓ])`. The third gives them for every finite extension's
  valuation ring and every uniformizer. Rational assertions for `E`, `ℚ_ℓ`, and
  the actual continuous `Qbar_ℓ` are the three field cases.

Dependencies used:

- `sk-def-localizing-closure`: `Sheaf.Paper.LocalizingAdmissibleCoefficients`, the six
  continuous coefficient alternatives of `IsLocalizingAdmissibleCoefficient`. Its
  extra finite-subextension alternative is not conflated with the continuous one.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `Scheme` and `Scheme.Hom`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `Scheme.ProEt` and its topology (unequal object/Hom universes retained).
- `sk-def-sfb-pulled-back-coefficients`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, `coefficientRing`,
  `coefficientRing_X`, `condensedRingObj`, `upperStarFromPoint`.
- `def-sfb-finite-constant-model-data`: `Sheaf.Paper.FiniteConstantModelResolution`,
  `scalarModules`, `scalarToContinuous`, `modelFunctor`, the canonical integral and
  rational coefficient/model constructions; no duplicate of these is written.
- `def-sfb-modobj-relative-tensor`:
  `WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`, `Mod.monoidalCategory`,
  `tensorObj_X`, `tensorObjπ`, and the ordinary `Mod.extendScalars` construction.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, equivalent to every ideal being finitely generated.
- `def-pur-localized-ringed-site`:
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`,
  `SheafOfModules.overFunctor` and `over`, with `GrothendieckTopology.over`.
- `sk-def-sfb-condensed-ring`: `Sheaf.Topology.ProfiniteCondensedRing`,
  `Profinite.CondensedRing` and the publicly imported continuous-function coefficient
  constructors. The universe-general `continuousCoefficientRingObj` is used.
- `def-weil-pbc-constant-sheaf`: `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `constantSheaf`, `toSheafify`, and the canonical constant-sheaf comparisons.
- The proof-plan imports include the recorded DVR, PID-Noetherian, vector-space-free,
  projective, constant-exact, integral coefficient limit, completed constant sheaf,
  finite normalized encoding and coefficient localization modules. The sole omitted
  proof-only import is `Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence`: importing it
  alongside the current normalized encoding makes the published environment reject
  duplicate `FiniteDiscreteOrdinary.Encoding.ordinary`. The smaller encoding module
  contains the exact canonical finite coefficient map and its normalization needed
  here. This follows the launcher's instruction to import only the usable side of a
  duplicate; no library source or dependency record is modified.

Edge cases checked before and during the second reading: zero finite ring; finite
rings of characteristic ell-squared rather than just fields; exponent zero; zero
module and infinite-dimensional scalar modules; empty scheme and empty site objects;
zero residue at every positive exponent; finite extension of degree one; arbitrary
uniformizers related by a unit; continuous algebraic-closure-valued functions with
image in no finite extension. No condition excludes any of these cases.

Searches actually run using `msearch.py Q90 lem-sfb-admissible-scalar-realization-exact`:

- `leanfinder`: "Admissible condensed coefficients give additive exact scalar realization
  on all modules on the pro etale site". Eight results, including condensed AB4/AB5,
  solid modules and generic condensed module constructions; no exact six-case theorem.
- `loogle`: `ModuleCat.preservesFiniteLimits_extendScalars_of_flat`. One result of
  that name, `Mathlib.Algebra.Category.ModuleCat.Descent`, concerning ordinary ring
  modules along an already-flat ring homomorphism, not the actual sheaf coefficients.
- `grep`: `completion.*flat|constant.*exact|preservesFiniteLimits_extendScalars_of_flat`.
  Five results in `AdicCompletion/AsTensorProduct`, `ModuleCat/Descent` and smooth
  flatness; none supplies the six actual continuous sheaf realizations.
- `leansearch`: "constant module sheaf exact scalar realization of topological adic
  coefficient rings". Eight results on discrete condensed modules and module sheaf
  construction/scalar restriction; no exact statement.
- Project and upstream `rg` for scalar exactness and the proposed namespace/names,
  plus `grep -rn` of the item id in `lean/WeilConjectures`. No existing declaration
  states this item. The private `modelFunctor_exact` in `FiniteConstantModelResolution`
  and `constantToContinuous_preservesFiniteLimits` are related ingredients, not the
  complete finite/integral/field, Noetherian, limit and localized package. A separate
  `ScalarAssertions` in `AdicHeartPullbackFibres` belongs to a different namespace
  and different adic-heart statement; none of this delivery's full names collide.

There is no statement dispute, correction, new node, or dependency replacement.

## Second reading by Q90

I performed a separate second pass with the unchanged JSON statement and the complete
Lean module open. The dispatcher explicitly prohibited starting other agents, so this
section records my second reading, not a claimed independent-worker review; the
maintainer's independent delivery review remains the independent review.

I checked each of the six scalar cases against the main conjunction and expanded all
assertion predicates. The two integral cases include full extension exactness on
arbitrary constant-ring sheaf modules and actual localized flatness, whereas the
three field cases only require scalar realization exactness. Finite coefficients use
the existing normalized canonical map. The completion is a ring-sheaf limit at every
positive exponent, with scalar residue compatibility explicitly recorded. Finite
extension topologies are the spectral topologies, and every uniformizer is quantified.
There are no unbound variables or implicit universe restrictions. The only `sorry`
is the whole proof of the node's named theorem.

Changes made during this reading: removed the conflicting finite-equivalence import
in favor of its smaller normalized encoding; supplied the site/coefficient universe
arguments in localized flatness; made the sheafification value categories explicit
to resolve an otherwise unsolved universe metavariable; and quantified all
uniformizers rather than just the library's chosen one. None changes the JSON
statement or replaces a canonical construction.

Validation uses only the prescribed `scompile.py` and `deliver2.py` wrappers. No global
build, direct repository edit, direct git command, or launcher-tool modification was
performed.
