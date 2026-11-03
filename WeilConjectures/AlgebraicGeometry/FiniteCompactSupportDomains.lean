/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.AlgebraicGeometry.BoundedFlatCoefficientSiteSquare.BoundedFlatCoefficientSiteSquareCurrent
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatConstructibleModel
public import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportTorWindowGeneralField
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
public import WeilConjectures.CategoryTheory.ConcreteCategory.FinitelyGenerated
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ExtendScalars
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
public import WeilConjectures.SmoothPurity.ProEtaleFiniteModelStalks

/-! # Finite compact-support domains with current coefficient extension

Source: Stacks Project, Tags 0GL6, 0E8I, 099R and 09AF; blueprint
sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional,
Charts and Locality (blueprint: lem-sp-finite-compact-support-domains).

The constant-ring module-sheaf presentation is identified with modules over the
pulled-back discrete condensed ring by the recorded finite-discrete ordinary
coefficient equivalence. Scalar extension here is the current K-flat derived
extension, with its target-ring action, on each actual small site.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

private abbrev currentScalar {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (X : Scheme.{u}) :=
  CoefficientScalarRepresentatives.ordinaryExtension X.smallEtaleTopology φ

private abbrev currentScalarAdjunction {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (X : Scheme.{u}) :=
  CoefficientScalarRepresentatives.ordinaryAdjunction X.smallEtaleTopology φ

private def currentScalarCompSheafFiberIso
    (P : X.smallEtaleTopology.Point.{u + 1}) :
    currentScalar φ X ⋙ P.sheafFiber ≅
      P.sheafFiber ⋙ ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ :=
  -- Mathlib's instance is stated for `extendScalars.{u₁, u₂, max u₂ w}`, and unifying
  -- `u + 1 =?= max (u + 1) ?w` gets stuck
  have := (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).isLeftAdjoint
  Functor.isoWhiskerLeft (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ))
    (P.presheafToSheafCompSheafFiberIso (ModuleCat.{u + 1} S)) ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf _ _)
      (P.presheafFiberCompIso (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ))

/-- Extension of scalars of étale sheaves sends constant sheaves to constant sheaves: both
functors are left adjoint to taking global sections viewed as an `R`-module. -/
private def currentScalarConstantIso :
    constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⋙ currentScalar φ X ≅
      ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ ⋙
        constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} S) :=
  ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} R) terminalIsTerminal).comp
    (currentScalarAdjunction φ X)).leftAdjointUniq
    (((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).comp
      (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} S)
        terminalIsTerminal)).ofNatIsoRight
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)))

/-- Extension of scalars of étale sheaves commutes with pullback, `g^*(S ⊗_R F) ≅ S ⊗_R g^* F`:
both functors are left adjoint to `G ↦ g_* G` viewed as a sheaf of `R`-modules. -/
private def currentScalarCompUpperStarIso (g : Y ⟶ X) :
    currentScalar φ X ⋙ Etale.upperStar (ModuleCat.{u + 1} S) g ≅
      Etale.upperStar (ModuleCat.{u + 1} R) g ⋙ currentScalar φ Y :=
  ((currentScalarAdjunction φ X).comp
      (Etale.upperStarLowerStarAdjunction _ g)).leftAdjointUniq
    (((Etale.upperStarLowerStarAdjunction _ g).comp
      (currentScalarAdjunction φ Y)).ofNatIsoRight
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)))

private theorem isFiniteSheaf_currentScalar_obj
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) [hF : IsFiniteSheaf F] :
    IsFiniteSheaf ((currentScalar φ X).obj F) where
  isFinitelyGenerated_sheafFiber Ω _ _ s := by
    let Φ := (pointSmallEtale s).ulift.{u + 1}
    have h := hF.isFinitelyGenerated_sheafFiber Ω s
    rw [← ConcreteCategory.isFinitelyGenerated_iff_of_iso
      (((pointSmallEtale s).uliftSheafFiberIso.{u + 1} _).app F),
      ModuleCat.isFinitelyGenerated_iff] at h
    have := ModuleCat.finite_extendScalars_obj' φ (Φ.sheafFiber.obj F)
    exact ((ModuleCat.isFinitelyGenerated_iff _).2 this).of_iso
      (((currentScalarCompSheafFiberIso φ X Φ).app F).symm ≪≫
        ((pointSmallEtale s).uliftSheafFiberIso.{u + 1} _).app _)

/-- Extension of scalars of étale sheaves preserves locally constant sheaves, trivialised by the
same cover: it commutes with pullbacks and sends constant sheaves to constant sheaves. -/
private theorem isLocallyConstantSheaf_currentScalar_obj
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) [h : IsLocallyConstantSheaf F] :
    IsLocallyConstantSheaf ((currentScalar φ X).obj F) := by
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := h.nonempty_locallyConstantDatum
  refine ⟨⟨⟨𝒰, fun i ↦ ?_⟩⟩⟩
  have := h𝒰 i
  rw [isConstant_over_iff_upperStar] at this ⊢
  obtain ⟨M, ⟨e⟩⟩ := this.1
  exact Sheaf.isConstant_of_iso _ ((currentScalarCompUpperStarIso φ _).app F ≪≫
    (currentScalar φ _).mapIso e.symm ≪≫
    (currentScalarConstantIso φ _).app M)

/-- Extension of scalars of étale sheaves preserves finite locally constant sheaves. -/
private theorem isFiniteLocallyConstantSheaf_currentScalar_obj
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) [IsFiniteLocallyConstantSheaf F] :
    IsFiniteLocallyConstantSheaf ((currentScalar φ X).obj F) where
  toIsFiniteSheaf := isFiniteSheaf_currentScalar_obj φ F

/-- Extension of scalars of étale sheaves preserves constructible sheaves, with the same
stratification: it commutes with the pullbacks to the strata. -/
private theorem isConstructibleSheaf_currentScalar_obj
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) [h : IsConstructibleSheaf F] :
    IsConstructibleSheaf ((currentScalar φ X).obj F) := by
  obtain ⟨T, hT⟩ := h.exists_stratification
  refine ⟨T, fun i ↦ ?_⟩
  have := hT i
  exact IsFiniteLocallyConstantSheaf.of_iso (F := (currentScalar φ _).obj
      ((Etale.upperStar _ (T.immersion i)).obj F))
    ((currentScalarCompUpperStarIso φ (T.immersion i)).app F).symm

private theorem boundedConstructible_of_bounded
    (R : Type (u + 1)) [CommRing R] [Finite R] (X : Scheme.{u})
    (K : Etale.DerivedCategoryModule R X)
    (hb : _root_.DerivedCategory.TStructure.t.bounded K)
    (hc : ∀ q : ℤ, IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) :
    Etale.DerivedCategory.isBoundedConstructible R X K := by
  obtain ⟨a, ha⟩ := hb.1
  obtain ⟨b, hb⟩ := hb.2
  exact ⟨hc, min a b, b, min_le_right _ _, fun q hq ↦ hq.elim
    (fun h ↦ (_root_.DerivedCategory.isGE_iff K a).1 ha q
      (lt_of_lt_of_le h (min_le_left _ _)))
    (fun h ↦ (_root_.DerivedCategory.isLE_iff K b).1 hb q h)⟩

private theorem bounded_of_boundedConstructible
    (R : Type (u + 1)) [CommRing R] [Finite R] (X : Scheme.{u})
    (K : Etale.DerivedCategoryModule R X)
    (h : Etale.DerivedCategory.isBoundedConstructible R X K) :
    _root_.DerivedCategory.TStructure.t.bounded K := by
  obtain ⟨_, a, b, _, hz⟩ := h
  exact ⟨⟨a, (_root_.DerivedCategory.isGE_iff K a).2
    (fun q hq ↦ hz q (.inl hq))⟩,
    ⟨b, (_root_.DerivedCategory.isLE_iff K b).2 (fun q hq ↦ hz q (.inr hq))⟩⟩

private theorem proConstructible_iso
    (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R] [Finite R]
    {F G : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)} (e : F ≅ G)
    (h : IsConstructibleProEtaleFixedModuleSheaf X R G) :
    IsConstructibleProEtaleFixedModuleSheaf X R F := by
  obtain ⟨S, hn, hs, hG⟩ := h
  refine ⟨S, hn, hs, fun i ↦ ?_⟩
  let d := (upperStar (ModuleCat.{u + 1} R) (S.immersion i)).mapIso e
  obtain ⟨hl, hf⟩ := hG i
  obtain ⟨I, U, f, hc, hm⟩ := hl
  refine ⟨⟨I, U, f, hc, fun j ↦ ?_⟩, fun Ω _ _ y ↦ ?_⟩
  · obtain ⟨M, ⟨m⟩⟩ := hm j
    exact ⟨M, ⟨((ProEt.topology (S.domain i)).overPullback
      (ModuleCat.{u + 1} R) (U j)).mapIso d ≪≫ m⟩⟩
  · let t := colim.mapIso (Functor.isoWhiskerLeft
      (proEtaleGeometricNeighbourhoodForget y).op
      ((sheafToPresheaf _ _).mapIso d))
    let := hf Ω y
    exact Finite.of_equiv
      (proEtaleGeometricFixedModuleStalk y R
        ((upperStar (ModuleCat.{u + 1} R) (S.immersion i)).obj G))
      (Equiv.ofBijective t.hom (ConcreteCategory.bijective_of_isIso t.hom)).symm

private theorem inputDomains
    (X : Scheme.{u}) [IsNoetherian X]
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (a b : ℤ) (hab : a ≤ b) (K : Etale.DerivedCategoryModule A X)
    (hc : Etale.DerivedCategory.isBoundedConstructible A X K)
    (ht : Etale.DerivedCategory.hasTorAmplitudeIn A X a b K) :
    Etale.DerivedCategory.isBoundedConstructible B X
      ((Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).obj K) ∧
    Etale.DerivedCategory.hasTorAmplitudeIn B X a b
      ((Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).obj K) ∧
    _root_.DerivedCategory.TStructure.t.bounded
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K) ∧
    (∀ q : ℤ, IsConstructibleProEtaleFixedModuleSheaf X A
      ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K))) ∧
    _root_.DerivedCategory.torAmplitudeIn _ a b
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K) ∧
    _root_.DerivedCategory.TStructure.t.bounded
      ((Sheaf.fixedCoefficientDerivedScalarExtension (ProEt.topology X) φ).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K)) := by
  let N := comparisonUpperStar (ModuleCat.{u + 1} A) X
  obtain ⟨P, hf, hp, hz, ⟨eP⟩⟩ :=
    (Etale.hasTorAmplitudeIn_iff_exists_finiteValueConstructibleModel
      A X a b hab K hc).1 ht
  let P' : (BoundedFlatCoefficientSiteSquare.inputs X A a b).FullSubcategory :=
    ⟨P, hf, hz⟩
  obtain ⟨χ, e, p, h⟩ :=
    BoundedFlatCoefficientSiteSquare.boundedFlat_coefficient_site_square X φ a b hab
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, htE, htN, htNE, _⟩ := h P'
  let eE : (Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).obj K ≅
      _root_.DerivedCategory.Q.obj
        ((BoundedFlatCoefficientSiteSquare.scalarComplex X.smallEtaleTopology φ).obj P) :=
    (CoefficientScalarRepresentatives.extension X.smallEtaleTopology φ).mapIso eP.symm ≪≫
      (e.app P').symm
  let eN := N.mapDerivedCategory.mapIso eP.symm ≪≫ N.mapDerivedCategoryFactors.app P
  let eNE :=
    (CoefficientScalarRepresentatives.extension (ProEt.topology X) φ).mapIso
      (N.mapDerivedCategory.mapIso eP.symm) ≪≫ (p.app P').symm
  have tE := (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso eE.symm
    (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 htE)
  have tN := (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso eN.symm htN.2
  have tNE := (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso eNE.symm htNE.2
  have bN := _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn tN
  have bNE := _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn tNE
  have bE := _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn tE
  let SP := (BoundedFlatCoefficientSiteSquare.scalarComplex X.smallEtaleTopology φ).obj P
  have hcSP (q : ℤ) : IsConstructibleEtaleModuleSheaf (SP.X q) := by
    have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hp q)
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      (isConstructibleSheaf_currentScalar_obj φ (P.X q))
  refine ⟨⟨fun q ↦ ?_, a, b, hab, fun q hq ↦ hq.elim
      (fun h ↦ (_root_.DerivedCategory.isGE_iff _ a).1 bE.1 q h)
      (fun h ↦ (_root_.DerivedCategory.isLE_iff _ b).1 bE.2 q h)⟩,
    Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2 tE,
    ⟨⟨a, bN.1⟩, ⟨b, bN.2⟩⟩, fun q ↦ ?_, tN,
    ⟨⟨a, bNE.1⟩, ⟨b, bNE.2⟩⟩⟩
  · have h := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1
      (etaleHomology_constructible X B SP hcSP q)
    have : Scheme.IsConstructibleSheaf
        ((HomologicalComplex.homologyFunctor _ (.up ℤ) q).obj SP) := h
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      (IsConstructibleSheaf.of_iso
        (((_root_.DerivedCategory.homologyFunctor _ q).mapIso eE) ≪≫
          (_root_.DerivedCategory.homologyFunctorFactors _ q).app SP).symm)
  · have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1
      (etaleHomology_constructible X A P hp q)
    exact proConstructible_iso X A
      (((_root_.DerivedCategory.homologyFunctor _ q).mapIso eN) ≪≫
        (_root_.DerivedCategory.homologyFunctorFactors _ q).app _ ≪≫
        (P.sc q).mapHomologyIso N)
      (fixedConstructible_of_models X A _
        (isConstructible_comparisonUpperStar_obj (P.homology q)))

/-- All finite compact-support and scalar/site outputs have their required domains.
Source: Stacks 0GL6 and 0E8I; blueprint Charts and Locality of
`det-sp-reduction-exceptional` (blueprint: lem-sp-finite-compact-support-domains).

Proof:
1. Finite type over the field makes U and V Noetherian and h quasi-compact.
   The characteristic calculation using hchar makes each finite primary coefficient
   ring have invertible exponent on V, including the zero ring and empty schemes.
2. Choose a bounded flat constructible model for L. Apply the ordinary etale
   compact-support Tor-window theorem at this compactification: open extension
   preserves flatness and proper direct image supplies a uniform fibre bound.
   This gives bounded constructible finite Tor amplitude for F_A L. The same
   argument over B will apply to L_B after step 3.
3. Apply the bounded-flat coefficient/site square to flat models for L and F_A L.
   The ordinary scalar adjunction preserves finite locally constant sheaves and
   strata. Exact site comparison preserves constructible cohomology. These give
   bounded constructibility and the uniform Tor
   interval for site pullback, actual derived scalar extension, and actual
   pro-etale scalar extension. Apply it over B with the identity map to each
   B-output to obtain its intrinsic site-pullback properties. These are universal
   degree-zero module tests and finite-stratification constructibility.
4. Apply step 2 over B to L_B, then step 3 to this output. All listed etale
   outputs and their site pullbacks are bounded, hence bounded below. Exact
   pro-etale open extension and left t-exact derived direct image supply lower
   bounds for the actual pro-etale compact-support outputs. Step 3 supplies the
   bounds for both actual pro-etale scalar outputs. Assemble the finite lists.
No flatness or finite projective dimension of B over A is used. -/
theorem finiteCompactSupportDomains_current
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    (hchar : ringChar k ≠ ℓ)
    {U V : Scheme.{u}} [U.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))]
    (h : U ⟶ V) [h.IsOver (Spec (.of k))] (c : Compactification h)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    (L : Etale.DerivedCategoryModule A U)
    (hb : _root_.DerivedCategory.TStructure.t.bounded L)
    (hc : ∀ q : ℤ, IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ q).obj L))
    (ht : ∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A U a b L) :
    (∀ (K : Etale.DerivedCategoryModule A V),
      K ∈ [(Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) c).obj L] →
      _root_.DerivedCategory.TStructure.t.bounded K ∧
      (∀ q : ℤ, IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) ∧
      (∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A V a b K) ∧
      (∃ a : ℤ, K.IsGE a) ∧
      _root_.DerivedCategory.TStructure.t.bounded
        ((comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategory.obj K) ∧
      (∀ q : ℤ, IsConstructibleProEtaleFixedModuleSheaf V A
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategory.obj K))) ∧
      (∃ a b : ℤ, a ≤ b ∧ _root_.DerivedCategory.torAmplitudeIn
        (Sheaf (ProEt.topology V) (ModuleCat.{u + 1} A)) a b
        ((comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategory.obj K)) ∧
      (∃ a : ℤ,
        ((comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategory.obj K).IsGE a)) ∧
    (∀ P : Σ T : Scheme.{u}, Etale.DerivedCategoryModule B T,
      P ∈ [⟨U, (Sheaf.fixedCoefficientDerivedScalarExtension U.smallEtaleTopology φ).obj L⟩,
        ⟨V, (Sheaf.fixedCoefficientDerivedScalarExtension V.smallEtaleTopology φ).obj
          ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj L)⟩,
        ⟨V, (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).obj
          ((Sheaf.fixedCoefficientDerivedScalarExtension U.smallEtaleTopology φ).obj L)⟩] →
      _root_.DerivedCategory.TStructure.t.bounded P.2 ∧
      (∀ q : ℤ, IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ q).obj P.2)) ∧
      (∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn B P.1 a b P.2) ∧
      (∃ a : ℤ, P.2.IsGE a) ∧
      _root_.DerivedCategory.TStructure.t.bounded
        ((comparisonUpperStar (ModuleCat.{u + 1} B) P.1).mapDerivedCategory.obj P.2) ∧
      (∀ q : ℤ, IsConstructibleProEtaleFixedModuleSheaf P.1 B
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} B) P.1).mapDerivedCategory.obj P.2))) ∧
      (∃ a b : ℤ, a ≤ b ∧ _root_.DerivedCategory.torAmplitudeIn
        (Sheaf (ProEt.topology P.1) (ModuleCat.{u + 1} B)) a b
        ((comparisonUpperStar (ModuleCat.{u + 1} B) P.1).mapDerivedCategory.obj P.2)) ∧
      (∃ a : ℤ,
        ((comparisonUpperStar (ModuleCat.{u + 1} B) P.1).mapDerivedCategory.obj P.2).IsGE a)) ∧
    (∃ a : ℤ,
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.obj L)).IsGE a) ∧
    (∃ a : ℤ,
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} B) U).mapDerivedCategory.obj
          ((Sheaf.fixedCoefficientDerivedScalarExtension U.smallEtaleTopology φ).obj L))).IsGE a) ∧
    (∀ P : Σ T : Scheme.{u}, Etale.DerivedCategoryModule A T,
      P ∈ [⟨U, L⟩,
        ⟨V, (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj L⟩] →
      ∃ a : ℤ, ((Sheaf.fixedCoefficientDerivedScalarExtension (ProEt.topology P.1) φ).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) P.1).mapDerivedCategory.obj P.2)).IsGE a) := by
  let : c.Z.Over (Spec (.of k)) := ⟨c.g ≫ V ↘ Spec (.of k)⟩
  let : c.g.IsOver (Spec (.of k)) := ⟨rfl⟩
  let : c.i.IsOver (Spec (.of k)) := ⟨by
    change c.i ≫ (c.g ≫ V ↘ Spec (.of k)) = U ↘ Spec (.of k)
    rw [← Category.assoc, ← c.comm]
    exact CategoryTheory.comp_over h _⟩
  have : LocallyOfFiniteType (c.Z ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (c.g ≫ V ↘ Spec (.of k))
    infer_instance
  have : QuasiCompact (c.Z ↘ Spec (.of k)) := by
    change QuasiCompact (c.g ≫ V ↘ Spec (.of k))
    infer_instance
  have : IsSeparated (c.Z ↘ Spec (.of k)) := by
    change IsSeparated (c.g ≫ V ↘ Spec (.of k))
    infer_instance
  have : IsLocallyNoetherian U :=
    LocallyOfFiniteType.isLocallyNoetherian (U ↘ Spec (.of k))
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace
    (U ↘ Spec (.of k))
  have : IsNoetherian U := {}
  have : IsLocallyNoetherian V :=
    LocallyOfFiniteType.isLocallyNoetherian (V ↘ Spec (.of k))
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace
    (V ↘ Spec (.of k))
  have : IsNoetherian V := {}
  obtain ⟨e, _, hwindow⟩ :=
    Etale.exists_etaleCompactSupport_torWindow_of_finite_or_isAlgClosed
      k ℓ (Fact.out : ℓ.Prime) hk hchar c.g
  have preserve (R : Type (u + 1)) [CommRing R] [Finite R]
      (hR : ∃ n : ℕ, ∀ x : R, (ℓ ^ n) • x = 0)
      (K : Etale.DerivedCategoryModule R U)
      (hcK : Etale.DerivedCategory.isBoundedConstructible R U K)
      (htK : ∃ a b : ℤ, a ≤ b ∧
        Etale.DerivedCategory.hasTorAmplitudeIn R U a b K) :
      Etale.DerivedCategory.isBoundedConstructible R V
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).obj K) ∧
      (∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn R V a b
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} R) c).obj K)) := by
    obtain ⟨a, b, hab, htK⟩ := htK
    obtain ⟨P, hf, hp, hz, he⟩ :=
      (Etale.hasTorAmplitudeIn_iff_exists_finiteValueConstructibleModel
        R U a b hab K hcK).1 htK
    have kill : ∃ n : ℕ, 1 ≤ n ∧ (ℓ ^ n : ℕ) • (1 : R) = 0 := by
      obtain ⟨n, hn⟩ := hR
      exact ⟨n + 1, Nat.le_add_left 1 n, by
        rw [pow_succ', mul_smul, hn, smul_zero]⟩
    obtain ⟨_, _, _, _, _, _, _, hcF, htF⟩ :=
      hwindow U c.i R kill a b hab K hcK htK P he (fun q ↦ (hf q).2) hp hz
    exact ⟨hcF, a, b + 2 * (e : ℤ), by omega, htF⟩
  have hL := boundedConstructible_of_bounded A U L hb hc
  obtain ⟨hcFA, aA, bA, habA, htFA⟩ := preserve A hA L hL ht
  obtain ⟨a, b, hab, htL⟩ := ht
  obtain ⟨hcLB, htLB, hbNL, _, _, hbSL⟩ := inputDomains U φ a b hab L hL htL
  obtain ⟨hcSFA, htSFA, _, _, _, hbSFA⟩ := inputDomains V φ aA bA habA _ hcFA htFA
  obtain ⟨hcFB, aB, bB, habB, htFB⟩ := preserve B hB _ hcLB ⟨a, b, hab, htLB⟩
  have assemble (R : Type (u + 1)) [CommRing R] [Finite R]
      (X : Scheme.{u}) [IsNoetherian X] (K : Etale.DerivedCategoryModule R X)
      (hcK : Etale.DerivedCategory.isBoundedConstructible R X K)
      (a b : ℤ) (hab : a ≤ b) (htK : Etale.DerivedCategory.hasTorAmplitudeIn R X a b K) :
      _root_.DerivedCategory.TStructure.t.bounded K ∧
      (∀ q : ℤ, IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) ∧
      (∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn R X a b K) ∧
      (∃ a : ℤ, K.IsGE a) ∧
      _root_.DerivedCategory.TStructure.t.bounded
        ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.obj K) ∧
      (∀ q : ℤ, IsConstructibleProEtaleFixedModuleSheaf X R
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.obj K))) ∧
      (∃ a b : ℤ, a ≤ b ∧ _root_.DerivedCategory.torAmplitudeIn
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) a b
        ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.obj K)) ∧
      (∃ a : ℤ,
        ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.obj K).IsGE a) := by
    obtain ⟨_, _, hbN, hcN, htN, _⟩ := inputDomains X (RingHom.id R) a b hab K hcK htK
    exact And.intro (bounded_of_boundedConstructible R X K hcK)
      ⟨hcK.1, ⟨a, b, hab, htK⟩,
        (bounded_of_boundedConstructible R X K hcK).1, hbN, hcN,
        ⟨a, b, hab, htN⟩, hbN.1⟩
  have proSupport (R : Type (u + 1)) [CommRing R]
      (K : _root_.DerivedCategory (Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R)))
      (hK : ∃ a : ℤ, K.IsGE a) :
      ∃ a : ℤ,
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).obj K).IsGE a := by
    let KP : _root_.DerivedCategory.Plus
        (Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R)) := ⟨K, hK⟩
    let FP := (rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} R) c).obj KP
    exact (_root_.DerivedCategory.TStructure.t.plus).prop_of_iso
      ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} R) c).app KP) FP.property
  have hbNLB := (inputDomains U (RingHom.id B) a b hab _ hcLB htLB).2.2.1
  refine ⟨?_, ?_, proSupport A _ hbNL.1, proSupport B _ hbNLB.1, ?_⟩
  · intro K hK
    simp only [List.mem_singleton] at hK
    subst K
    exact assemble A V _ hcFA aA bA habA htFA
  · intro P hP
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl | rfl
    · exact assemble B U _ hcLB a b hab htLB
    · exact assemble B V _ hcSFA aA bA habA htSFA
    · exact assemble B V _ hcFB aB bB habB htFB
  · intro P hP
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl
    · exact hbSL.1
    · exact hbSFA.1

/-- The specified compact-support comparison is invertible for every D+ input.
Source: Stacks 099R and 09AF; blueprint Charts and Locality of
`det-sp-reduction-exceptional` (blueprint: lem-sp-finite-compact-support-domains).

Proof: the proper map c.g is qcqs. Exact open extension puts j_!E in D+.
Apply the recorded invertibility theorem to the named proper counit mate at
j_!E. The second factor is the proper derived image of the canonical open
comparison isomorphism, so is invertible as well. Their composite is invertible.
The standard D+ compatibility identifies the displayed endpoints with the
restrictions of the unbounded compact-support functors in the preceding theorem.
Both arrows are the specified comparisons, with no independently chosen map. -/
theorem finiteCompactSupportDomains_current_comparison_isIso
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    (hchar : ringChar k ≠ ℓ)
    {U V : Scheme.{u}} [U.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))]
    (h : U ⟶ V) [h.IsOver (Spec (.of k))] (c : Compactification h)
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (hR : ∃ n : ℕ, ∀ x : R, (ℓ ^ n) • x = 0)
    (E : _root_.DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    IsIso
      ((fixedComparisonDirectImageMatePlus R c.g).app
          ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} R) c.i).mapDerivedCategoryPlus.obj E) ≫
        (lowerStar (ModuleCat.{u + 1} R) c.g).rightDerivedFunctorPlus.map
          (((Functor.mapDerivedCategoryPlusCompIso
              (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i)
              (comparisonUpperStar (ModuleCat.{u + 1} R) c.Z)).symm ≪≫
            Functor.mapDerivedCategoryPlusNatIso
              (openImmersionLowerShriekComparisonUpperStarIso
                (ModuleCat.{u + 1} R) c.i) ≪≫
            Functor.mapDerivedCategoryPlusCompIso
              (comparisonUpperStar (ModuleCat.{u + 1} R) U)
              (openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i)).hom.app E)) := by
  have _ := hk
  have _ := hchar
  have _ := hR
  let := isIso_fixedComparisonDirectImageMatePlus R c.g
  infer_instance

end AlgebraicGeometry.ProEtale
