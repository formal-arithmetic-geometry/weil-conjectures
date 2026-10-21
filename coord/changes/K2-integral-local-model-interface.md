# Integral completed local model interface

## Reason

Proposition 6.6.11 is a separate input to the cohomology argument in Proposition 6.8.11(3).
Move the existing model interface to a common module so that this separate theorem can use
it without importing its own consumer. The main module publicly reexports the common module.
No definition, statement, universe, attribute, or declaration name changes.

## Old

The following declaration block in `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`:

```lean
/-- The ordinary realization N ↦ A_T ⊗_A N, using the normalized coefficient comparison.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
def integralConstantModule (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) : ModuleCat.{u + 1} A ⥤
      pbcModules T (pbcAdicCompletion T d) :=
  completedKoszulConstant T
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite } ⋙
    pbcRestrict (pbcCompletedComparison T d).inv

/-- Exactness of the ordinary completed-constant realization.
Source: Bhatt--Scholze, Lemma 6.5.8 and Proposition 6.6.11
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization).
Proof: constant module sheafification is exact. The completed ring is flat over
constant A by lem-weil-pbc-completed-constant-sheaf-reduction, since d is Noetherian.
Thus tensoring with it preserves finite limits and colimits. Restriction along the
normalized coefficient isomorphism is an exact equivalence. -/
theorem integralConstantModule_exact (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :
    PreservesFiniteLimits (integralConstantModule T d) ∧
      PreservesFiniteColimits (integralConstantModule T d) := by
  let dd : ProEtaleAdicCoefficientDatum A :=
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite }
  let K := adicLisseConstantModules T A
  let E := completedConstantExtension T (adicDatumScalar T dd)
  let R := pbcRestrict (pbcCompletedComparison T d).inv
  have hK : PreservesFiniteLimits K ∧ PreservesFiniteColimits K := by
    let P : ModuleCat.{u + 1} A ⥤
      _root_.PresheafOfModules.{u + 1}
        ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of A)) :=
      siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
        PresheafOfModules.pushforward₀
          ((Functor.const T.ProEt).obj (Discrete.mk (ULift.up ())))
          ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A))
    have hP : PreservesFiniteLimits P := by
      constructor
      intro J _ _
      constructor
      intro F
      constructor
      intro c hc
      exact ⟨_root_.PresheafOfModules.evaluationJointlyReflectsLimits _ _
        (fun X ↦ hc)⟩
    have hP' : PreservesFiniteColimits P := by
      constructor
      intro J _ _
      constructor
      intro F
      constructor
      intro c hc
      exact ⟨_root_.PresheafOfModules.evaluationJointlyReflectsColimits _ _
        (fun X ↦ hc)⟩
    exact ⟨comp_preservesFiniteLimits P
      (PresheafOfModules.sheafification (adicLisseConstantUnit T A)),
      comp_preservesFiniteColimits P
        (PresheafOfModules.sheafification (adicLisseConstantUnit T A))⟩
  have hE : PreservesFiniteLimits E ∧ PreservesFiniteColimits E := by
    let := dd.toCompleteCoefficientDatum.noetherian
    have h := completed_constant_algebra_flat_quotients T dd.ideal
      _ (Iso.refl _) (adicDatumScalar T dd) (by
        intro n
        exact (adicDatumScalar_exists T dd).exists.choose_spec n)
    have he := (exactFunctor_iff E).1 h.2.1
    exact ⟨he.1, he.2⟩
  let := hK.1
  let := hK.2
  let := hE.1
  let := hE.2
  exact ⟨comp_preservesFiniteLimits (K ⋙ E) R,
    comp_preservesFiniteColimits (K ⋙ E) R⟩

/-- Additivity of completed-constant realization, inherited from its two factors.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
instance integralConstantModule_additive (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) : (integralConstantModule T d).Additive :=
  letI := (integralConstantModule_exact T d).1
  Functor.additive_of_preserves_binary_products _

/-- The derived realization P ↦ A_T ⊗^L_A P, obtained by localizing the exact
ordinary constant-module realization. On bounded finite projective complexes this
is its termwise tensor realization.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
def integralConstantDerived (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) : completedConstantDerived (ModuleCat.{u + 1} A) ⥤
      DerivedCategory (pbcModules T (pbcAdicCompletion T d)) :=
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  letI := (integralConstantModule_exact T d).1
  letI := (integralConstantModule_exact T d).2
  (integralConstantModule T d).mapDerivedCategory

/-- Restrict a derived object first to a stratum and then to a covering site object.
The slice coefficient sheaf is the restriction of the actual inverse-image ring.
Source: Bhatt--Scholze, Proposition 6.6.11; Stacks Tags 0997 and 0998
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
def integralLocalDerived {T S : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (U : S.ProEt)
    (K : DerivedCategory (pbcModules T R)) :
    completedConstantDerived (SheafOfModules.{u + 1}
      (((adicLisseForget S).obj ((adicTowerInverseImage g).obj R)).over U)) :=
  ringedSiteDerivedRestrictionOfUniverses
    ((adicLisseForget S).obj ((adicTowerInverseImage g).obj R)) U
    ((adicTowerPullback g R).obj K)

/-- Condition (ii): finite strata, on each a pro-etale covering sieve, and on each
cover member an actual perfect A-complex whose completed realization is K there.
IsPerfectRingComplex is the recorded bounded finite-projective notion.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
def IsIntegralStratifiedPerfect (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T d))) : Prop :=
  ∃ s : Stratification T, ∀ i : Fin s.n,
    ∃ V : Sieve (⊤_ (s.domain i).ProEt),
      V ∈ ProEt.topology (s.domain i) (⊤_ (s.domain i).ProEt) ∧
        ∀ (U : (s.domain i).ProEt) (f : U ⟶ ⊤_ (s.domain i).ProEt), V f →
          ∃ P : completedConstantDerived (ModuleCat.{u + 1} A),
            @DerivedCategory.IsPerfectRingComplex A _
              (HasDerivedCategory.standard (ModuleCat.{u + 1} A)) P ∧
              Nonempty (integralLocalDerived (s.immersion i) (pbcAdicCompletion T d) U K ≅
                integralLocalDerived (s.immersion i) (pbcAdicCompletion T d) U
                  ((integralConstantDerived T d).obj P))

/-- The constructible integral sheaf condition: finite strata and locally the ordinary
completed realization of a finitely presented A-module, including the zero module.
Source: Bhatt--Scholze, Definition 6.8.10
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
def IsIntegralStratifiedFinitelyPresented (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (F : pbcModules T (pbcAdicCompletion T d)) : Prop :=
  ∃ s : Stratification T, ∀ i : Fin s.n,
    ∃ V : Sieve (⊤_ (s.domain i).ProEt),
      V ∈ ProEt.topology (s.domain i) (⊤_ (s.domain i).ProEt) ∧
        ∀ (U : (s.domain i).ProEt) (f : U ⟶ ⊤_ (s.domain i).ProEt), V f →
          ∃ N : ModuleCat.{u + 1} A, Module.FinitePresentation A N ∧
            Nonempty ((SheafOfModules.overFunctor _ U).obj
              ((proEtaleModuleInverseImage (s.immersion i) (pbcAdicCompletion T d)).obj F) ≅
              (SheafOfModules.overFunctor _ U).obj
                ((proEtaleModuleInverseImage (s.immersion i) (pbcAdicCompletion T d)).obj
                  ((integralConstantModule T d).obj N)))

/-- Condition (iii): boundedness and the stated finitely presented local models for
all cohomology sheaves. The finite stratification may depend on the cohomological degree.
Source: Bhatt--Scholze, Proposition 6.8.11(3)
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
def IsIntegralBoundedConstructibleCohomology (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T d))) : Prop :=
  (∃ a b : ℤ, a ≤ b ∧ K.IsGE a ∧ K.IsLE b) ∧
    ∀ q : ℤ, IsIntegralStratifiedFinitelyPresented T d
      ((DerivedCategory.homologyFunctor (pbcModules T (pbcAdicCompletion T d)) q).obj K)
```

## New

Exactly the same declaration block, verbatim, in `Sheaf.Paper.IntegralStratifiedPerfectModels`.
The old module has `public import Sheaf.Paper.IntegralStratifiedPerfectModels`.
The equality of the two blocks was checked byte for byte. The new separate criterion imports
only the common model interface. It leaves the completion/reduction argument open, while
the cohomology argument, global bounds and finite PID resolutions are proved in the parent.

## Users

`tools/downstream.py` initially found 17 live transitive importers. The table also records
the quarantined consumers identified by preflight. Every importer still sees all old
public names with the identical meaning; no consumer adaptation is required. Current shared
claim records list no holder for these modules.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralStratifiedPerfectCharacterization | K2 | Publicly reexports the unchanged interface. |
| Sheaf.AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias | unclaimed | No change; identical public reexport. |
| Sheaf.Paper.BoundedConstructiblePushforwardRestriction | unclaimed | No change; identical public reexport. |
| Sheaf.Paper.IntegralConstructibleBoundedBelowCompactness | unclaimed | No change; identical public reexport. |
| Sheaf.Paper.SfIntegralStandardTruncations | unclaimed | No change; identical public reexport. |
| Sheaf.Paper.StratifiedPerfectInternalHomCoproducts | unclaimed | No change; identical public reexport. |
| WeilConjectures | unclaimed | No change; identical public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | unclaimed | No change; identical public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | unclaimed | No change; identical public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed | unclaimed | No change; identical public reexport. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | No change; identical public reexport. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | No change; identical public reexport. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | No change; identical public reexport. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | No change; identical public reexport. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | No change; identical public reexport. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | No change; identical public reexport. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | No change; identical public reexport. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | No change; identical public reexport. |

| Sheaf.Paper.ExtensionZeroPerfectModelTransport | unclaimed, quarantined | Public reexport preserves all coefficient realizations, exactness and additivity; archive unchanged. |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | unclaimed, quarantined | Public reexport preserves derived restriction and local-perfect predicate; archive unchanged. |

## Status

landed 20261021T061432-L-1774768 2026-10-21 (merge of deliver/K2/Sheaf.Paper.IntegralStratifiedPerfectCharacterization)
