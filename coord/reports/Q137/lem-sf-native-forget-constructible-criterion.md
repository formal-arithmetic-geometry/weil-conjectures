## Worker report

The module `Sheaf.Paper.NativeForgetConstructibleCriterion` states
`AlgebraicGeometry.ProEtale.NativeEncoding.native_forget_constructible_criterion`.
It has one theorem with proof `sorry` and no definitions. The DAG statement, proof,
source and status are unchanged. Its `stmt_deps` gains only the already-landed
`det-def-sfb-constructible-local-model`, whose recorded scalar-model declarations
are used explicitly in the theorem.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

1. `(k₀ : Type u) [Field k₀] [Finite k₀]` is the finite ground field. The geometric
   algebraic closure is the framework's `AlgebraicClosure k₀`, used inside
   `Scheme.Hom.geometricFiber`. No different algebraic closure is chosen. The node
   fixes the native framework, which already uses this representative.
   `(l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]` is the prime unequal to the
   characteristic; Ω is the existing `PadicAlgCl l`.
2. `(X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]`, together with
   `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact` of its structure map,
   states exactly that T₀ (named X here) is separated and finite type over k₀.
   T is `(X ↘ Spec (CommRingCat.of k₀)).geometricFiber`. Qcqs and Noetherianity are
   consequences, not added hypotheses. Site and module universes are the existing
   framework's `Scheme.{u}`, `Ab.{u+1}` and ordinary derived localizations.
3. B, A, W and WCder are the existing `adicConstantSheaf`, `AdicSheaf`,
   `ProEtaleWeilSheaf` and `WeilComplex.objectProperty`. R is
   `condensedRingObj (Profinite.padicAlgClRingObj l) T`: this is the specified
   finite-subextension-valued coefficient, not all continuous Ω-valued functions.
   E and V are precisely the published `NativeEncoding.encoding l T` and
   `NativeEncoding.realization k₀ l X`. U is `Endofunctor.IsoAlgebra.forget` of
   the actual `WeilSheaf.frobeniusPullback`.
4. The first conjunction quantifies over every native module M and gives both
   `IsAdicConstructibleSheaf M ↔ IsConstantModelConstructible ... (encoding.obj M)`
   and `IsAdicConstructibleSheaf M ↔ IsAdicStratifiedLisseSheaf M`.
   The latter explicitly asserts replacement of local stratifications by one
   finite stratification of all of T. The upstream global predicate requires
   finite strata, immersions, constructible images partitioning T, and lisse
   restrictions on each stratum; the local predicate is its Zariski-local version.
5. The scalar clause uses the recorded `scalarRingObj` in Ab to encode the
   ordinary Ω-vector-space P. Its dimension r is expressed by
   `Nonempty (P ≅ Mod.finiteFree (scalarRingObj ...) r)`, equivalently existence
   of an r-element basis over this field. This is no extra condition beyond
   being finite-dimensional of the specified dimension. The conclusion gives
   both `finiteConstantScalarExtension.obj P ≅ Mod.finiteFree R_U r` and
   `encoding.obj (Mod.finiteFree B_U r) ≅ Mod.finiteFree R_U r`, in Nonempty.
   The extension functor is the actual tensor R_U ⊗_{Ω_U} P_U, constructed by
   the canonical scalar coefficient map. The formula is stated for each scheme
   U, hence applies to every covering member of every stratum; it is independent
   of its map to T. It imposes no finite-type condition on U. The bound r is
   universally quantified separately for each U and P and may equal zero.
6. `∀ n : ℤ, Nonempty (realization ⋙ homologyFunctor _ n ≅
   homologyFunctor _ n ⋙ IsoAlgebra.forget ... ⋙ encoding ...)` states the
   cohomology identification as a natural isomorphism of functors on the entire
   ordinary unbounded derived category, so it includes all objects and arrows.
   Its orientation is Hⁿ(V C) ≅ E U Hⁿ(C).
7. The next clause quantifies over all ambient derived C and integers n and
   states the exact iff between `IsZero (Hⁿ C)` and `IsZero (Hⁿ (V C))`.
8. The next clause quantifies over C and arbitrary integer endpoints a,b and
   states the iff between vanishing of their cohomology outside `[a,b]`.
   There is no boundedness premise, and no ordered-endpoint premise is needed
   for this support-detection assertion.
9. For every C, the next conjunction states two separate iffs:
   `(WeilComplex.objectProperty ... C ↔ constantModelBoundedConstructible ... (V C))`
   and `(constantModelBoundedConstructible ... (V C) ↔
   (constantModelBoundedConstructible ... (V C) ∧ finiteTorAmplitude _ (V C)))`.
   Thus it asserts both arrows of both requested equivalences. Dctf membership
   is its defining predicate, i.e. bounded constructibility and finite Tor
   amplitude; it is the object predicate of `ConstantModelConstructibleFiniteTor`.
   The bounded constructible predicate is the finite constant scalar convention
   of `sk-def-sfb-constructible` and `det-def-sfb-constructible-tor-amplitude`,
   as required by the item's maintainer note. The more general locally finitely
   presented ring-object predicate of `sk-def-sfb-bounded-constructible` is not
   substituted for it; its recorded module is unnecessary to these terms.
10. The last clause assumes a ≤ b, vanishing of Hⁿ(V C) for n < a or b < n,
    and `IsConstantModelConstructible` for Hⁿ(V C) in every degree. It concludes
    `DerivedCategory.torAmplitudeIn _ (a - 1) b (V C)`. The latter tests the
    recorded relative derived tensor against every coefficient module in degree
    zero, exactly as specified by the Tor-amplitude dependency.
11. No equivalence of categories with fixed pairs in a derived category is
    asserted: all C live in `DerivedCategory (ProEtaleWeilSheaf k₀ l X)`.

Recorded dependency declarations read and reused:

- `WeilConjectures.WeilSheaf.LowerShriek` imports the native framework in
  `WeilConjectures.WeilSheaf.Category` and `...Adic.Constructible`: `AdicSheaf`,
  `adicConstantSheaf`, `IsAdicConstructibleSheaf`, `IsAdicStratifiedLisseSheaf`,
  `ProEtaleWeilSheaf`, `WeilSheaf.frobeniusPullback`, `WeilComplex.objectProperty`.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing`, `Profinite.padicAlgClRingObj`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `condensedRingObj` and `coefficientRing`, the actual coefficient inverse image.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`; the finite-free
  specialization is the existing `CategoryTheory.Mod.finiteFree` from
  `WeilConjectures.CategoryTheory.ModuleObjects.Free`.
- `Sheaf.Paper.LocallyFiniteCoefficientRingRealization`:
  `locallyFiniteCoefficientRing_realization`, the normalized ring realization
  used by the recorded native encoding module.
- `Sheaf.Paper.NativeEncodingDerivedOperations`: `coefficientIso`, `encoding`,
  `encoding_isEquivalence`, `encoding_exact_derived`, `derivedEncoding` and
  `realization`. The actual forward functors are reused, not arbitrary choices.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; `DerivedCategory.homologyFunctor` is the recorded
  cohomology factorization through ordinary localization.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `IsConstantModelConstructible`, `constantModelBoundedConstructible` and
  `ConstantModelConstructibleFiniteTor`.
- `Sheaf.Paper.ConstantModelTorAmplitude`:
  `constantModelConstructibleFiniteTor_wellDefined`, exposing the shared
  `DerivedCategory.torAmplitudeIn` and `DerivedCategory.finiteTorAmplitude`.
- `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`: `scalarRingObj`,
  `finiteConstantScalarExtension` and `finiteConstantLocalModel_iff_exists_cover`.
  This is the existing definition node added to the statement dependencies.

Proof-only dependencies with recorded modules are imported without `public`:
`LocalizingClosureCtfEqualsBc`, `ExactDerivedCohomologyCoherence`,
`NativeModuleConstructibilityComparison`, `FiniteConstantStratifiedZariskiLocality`.
The native exact/conservative forgetting interface is already public through
`NativeEncodingDerivedOperations`. The base-change and qcqs proof dependencies
are Mathlib leaves, not missing Lean interfaces.

Sources checked: the local Bhatt--Scholze PDF, Definitions 6.8.3, 6.8.6, 6.8.8
(the intervening paragraph supplies the topologically Noetherian setting);
`literature/blueprint/latest/.../sk-def-sfb-constructible/_section.md` and
`.../sk-def-sfb-constructible-local-model.md`; the complete existing native
constructibility definitions and the recorded encoding, scalar-model and Tor APIs.

Edge cases checked: empty T admits the empty global stratification; zero M and
C are allowed; r = 0 gives the empty sum and scalar zero module; ranks are not
required equal across different members; arbitrary negative degrees and degree-zero
complexes are included; interval support is detected even when a > b (then all
cohomology vanishes), while the stated Tor interval uses a ≤ b; C need not be
bounded to use the natural cohomology, zero or interval comparisons. No nonempty
scheme, nonzero rank or condition on the Frobenius action is added.

Searches performed through the prescribed msearch.py wrapper:

- LeanFinder, query "An exact functor forgetting Frobenius on native adic modules
  detects constructibility bounded cohomology and finite Tor amplitude": eight
  hits (CondensedMod.IsSolid, Condensed.profiniteSolid, AdicCompletion.map_exact,
  localCohomology.ofSelfLERadical, LightCondensed.instIsGrothendieckAbelianLightCondMod,
  localCohomology, CondensedMod, Condensed.instAB4StarCondensedMod). None is this
  native constructibility comparison.
- Loogle, query `CategoryTheory.Functor, DerivedCategory.homologyFunctor`: twelve
  generic cohomology functor, shift and factorization/naturality hits. These give
  the reused cohomology vocabulary, not the native theorem.
- grep, query `IsAdicConstructibleSheaf|native_forget_constructible|constantModelBoundedConstructible`:
  zero Mathlib hits.
- LeanSearch, query "Forgetting Frobenius on complexes of constructible adic
  sheaves detects bounded constructibility and Tor amplitude": eight generic
  sheaf/module forgetful functor hits, none a match.
- Local rg searches in `lean/WeilConjectures` and `lean/Sheaf` identified and read
  the existing encoding, native predicates, finite scalar extension, general
  native module comparison, exact-derived cohomology and coefficient Tor APIs.
  Searches for `native_forget_constructible_criterion|NativeForgetConstructibleCriterion`
  in Mathlib, WeilConjectures and Sheaf, and the prescribed upstream grep for the
  item id, found no existing declaration of this combined criterion.

No statement dispute, statement correction, new notion, or dependency repair was
needed. The scalar-model node is already recorded and is reused as allowed by
brief-stage2 §5 (statement dependencies may gain landed nodes).

Validation: the final module compiled via scompile.py in both sandbox mode and its
actual library module path on 2026-10-24, with no errors and no unexpected warnings.
Every binder is explicit with `autoImplicit false`; every Lean line is ≤100 characters.

## Second reading by Q137

This is a manual self-audit; the dispatched worker was expressly instructed not
to start another agent. The maintainer supplies the independent delivery review.
I reopened the node and complete module and matched the hypotheses and all clauses
as listed above. This reading found three omissions/errors in the initial draft:
the native global stratification was only discussed in prose, the scalar finite-rank
identification was only discussed in prose, and the two derived predicate iffs were
written as one nested iff. The delivered theorem states the global-stratification
iff explicitly, uses the existing scalar-extension and finite-free objects to state
the rank comparison, and separates both predicate iffs with a conjunction. I also
checked that the cohomology comparison is functor-level naturality, both interval
support predicates are fully within the quantified C,a,b clause, and the final
Tor predicate uses exactly `(a - 1)` and b. All changes are confined to the draft
Lean statement and its lean record; the source DAG statement is unchanged.
