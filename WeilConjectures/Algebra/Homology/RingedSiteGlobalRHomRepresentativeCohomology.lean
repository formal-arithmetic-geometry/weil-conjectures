/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedSiteGlobalRHomModel
public import WeilConjectures.Algebra.Homology.DerivedInternalHomSectionsModel
public import Mathlib.Algebra.Category.ModuleCat.Ulift
import WeilConjectures.Algebra.Homology.RingedSiteGlobalRHomRepresentativeForget
import WeilConjectures.Algebra.Homology.RingedSiteGlobalRHomCohomologyNaturality
import all WeilConjectures.Algebra.Homology.KInjectiveHomScalarTelescope
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear

/-! Linear cohomology comparisons for the module-valued global Hom representative. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v r a w z

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RingedSiteGlobalRHom

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max c v r})
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w} (Modules.{c, v, max c v r} R)]
  (A : Type a) [CommRing A] (φ : A →+* Scalars.{c, v, max c v r} R)
  [HasDerivedCategory.{z} (ModuleCat.{max c v r} A)]

attribute [local irreducible] homComplexFunctor derivedInternalHomOfUniverses
  Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit

private def representativeGroupComparison
    (L : CochainComplex (Modules.{c, v, max c v r} R) ℤ) (q : ℤ) :
    representative.{c, v, r, a} R A φ L ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{max c v r} A) (.up ℤ) q ⋙
        forget₂ (ModuleCat.{max c v r} A) AddCommGrpCat.{max c v r} ≅
      ordinaryHomFunctor.{c, v, r} R L ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{max c v r} (.up ℤ) q :=
  Functor.isoWhiskerLeft (representative.{c, v, r, a} R A φ L)
      (((forget₂ (ModuleCat.{max c v r} A)
        AddCommGrpCat.{max c v r}).mapHomologicalComplexHomologyIso
        (.up ℤ) q).symm) ≪≫
    Functor.isoWhiskerRight
      (Classical.choice (representative_forget_comparison.{c, v, r, a} R A φ L))
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{max c v r} (.up ℤ) q)

attribute [local irreducible] representativeGroupComparison

private def representativeGroupIso
    (L I : CochainComplex (Modules.{c, v, max c v r} R) ℤ) (q : ℤ) :
    (forget₂ (ModuleCat.{max c v r} A) AddCommGrpCat.{max c v r}).obj
      (((representative.{c, v, r, a} R A φ L).obj I).homology q) ≅
        (CochainComplex.HomComplex L I).homology q :=
  (representativeGroupComparison.{c, v, r, a} R A φ L q).app I

attribute [local irreducible] representativeGroupIso

omit [HasDerivedCategory.{w} (Modules.{c, v, max c v r} R)]
  [HasDerivedCategory.{z} (ModuleCat.{max c v r} A)] in
private theorem representativeGroupIso_naturality
    (L : CochainComplex (Modules.{c, v, max c v r} R) ℤ)
    {I I' : CochainComplex (Modules.{c, v, max c v r} R) ℤ}
    (f : I ⟶ I') (q : ℤ) :
    (forget₂ (ModuleCat.{max c v r} A) AddCommGrpCat.{max c v r}).map
        (HomologicalComplex.homologyMap ((representative.{c, v, r, a} R A φ L).map f) q) ≫
      (representativeGroupIso.{c, v, r, a} R A φ L I' q).hom =
    (representativeGroupIso.{c, v, r, a} R A φ L I q).hom ≫
      HomologicalComplex.homologyMap (externalHomMap (𝟙 L) f) q := by
  unfold representativeGroupIso
  exact (representativeGroupComparison.{c, v, r, a} R A φ L q).hom.naturality f

private def representativeDerivedEquiv
    (L I : CochainComplex (Modules.{c, v, max c v r} R) ℤ) [I.IsKInjective] (q : ℤ) :
    ((representative.{c, v, r, a} R A φ L).obj I).homology q ≃+
      (DerivedCategory.Q.{w}.obj L ⟶ (DerivedCategory.Q.{w}.obj I)⟦q⟧) :=
  (representativeGroupIso.{c, v, r, a} R A φ L I q).addCommGroupIsoToAddEquiv.trans
    (externalHomDerivedEquiv L I q)

attribute [local irreducible] representativeDerivedEquiv

omit [HasDerivedCategory.{z} (ModuleCat.{max c v r} A)] in
private theorem representativeDerivedEquiv_naturality
    (L : CochainComplex (Modules.{c, v, max c v r} R) ℤ)
    {I I' : CochainComplex (Modules.{c, v, max c v r} R) ℤ}
    [I.IsKInjective] [I'.IsKInjective] (f : I ⟶ I') (q : ℤ)
    (x : ((representative.{c, v, r, a} R A φ L).obj I).homology q) :
    representativeDerivedEquiv.{c, v, r, a, w} R A φ L I' q
      (HomologicalComplex.homologyMap ((representative.{c, v, r, a} R A φ L).map f) q x) =
    representativeDerivedEquiv.{c, v, r, a, w} R A φ L I q x ≫
      (DerivedCategory.Q.map f)⟦q⟧' := by
  have h := ConcreteCategory.congr_hom
    (representativeGroupIso_naturality.{c, v, r, a} R A φ L f q) x
  unfold representativeDerivedEquiv
  simp only [AddEquiv.trans_apply]
  change (externalHomDerivedEquiv L I' q)
    ((representativeGroupIso.{c, v, r, a} R A φ L I' q).hom _) = _
  rw [show (representativeGroupIso.{c, v, r, a} R A φ L I' q).hom
      (HomologicalComplex.homologyMap ((representative.{c, v, r, a} R A φ L).map f) q x) = _
    from h]
  exact externalDerivedEquiv_naturality f q _

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w} (Modules.{c, v, max c v r} R)]
  [HasDerivedCategory.{z} (ModuleCat.{max c v r} A)] in
private theorem representative_map_scalar
    (L I : CochainComplex (Modules.{c, v, max c v r} R) ℤ) (b : A) :
    (representative.{c, v, r, a} R A φ L).map ((φ b) • 𝟙 I) =
      b • 𝟙 ((representative.{c, v, r, a} R A φ L).obj I) := by
  have h := CategoryTheory.homComplex_map_scalar.{c, v, r} J R (φ b) L I
  dsimp only [kInjectiveHomScalarEndomorphism, homComplex] at h
  dsimp only [representative, Functor.comp_map]
  rw [h]
  ext n x
  change x ≫ ((φ b) • 𝟙 _) = _
  rw [Linear.comp_smul, Category.comp_id]
  rfl

omit [HasDerivedCategory.{z} (ModuleCat.{max c v r} A)] in
private theorem representativeDerivedEquiv_scalar
    (L I : CochainComplex (Modules.{c, v, max c v r} R) ℤ) [I.IsKInjective]
    (q : ℤ) (b : A)
    (x : ((representative.{c, v, r, a} R A φ L).obj I).homology q) :
    representativeDerivedEquiv.{c, v, r, a, w} R A φ L I q (b • x) =
      (φ b) • representativeDerivedEquiv.{c, v, r, a, w} R A φ L I q x := by
  have h := representativeDerivedEquiv_naturality.{c, v, r, a, w}
    R A φ L ((φ b) • 𝟙 I) q x
  rw [representative_map_scalar.{c, v, r, a} R A φ L I b] at h
  change representativeDerivedEquiv.{c, v, r, a, w} R A φ L I q
    ((HomologicalComplex.homologyFunctor (ModuleCat.{max c v r} A) (.up ℤ) q).map
      (b • 𝟙 _) x) = _ at h
  simp only [Functor.map_smul, Functor.map_id, Linear.comp_smul, Category.comp_id] at h
  exact h

/-- Shifted derived Hom with its restricted coefficient action and a common universe lift.
Source: Stacks Project, Tags 0B6E and 08JA.
(blueprint: lem-sfb-global-rhom-representative-cohomology-comparison). -/
def shiftedHomFunctor
    (E : DerivedCategory (Modules.{c, v, max c v r} R)) (q : ℤ) :
    DerivedCategory (Modules.{c, v, max c v r} R) ⥤ ModuleCat.{max c v r w} A :=
  shiftFunctor _ q ⋙
    (linearCoyoneda (Scalars.{c, v, max c v r} R) _).obj (op E) ⋙
      ModuleCat.restrictScalars φ ⋙ ModuleCat.uliftFunctor.{max c v r} A

universe u₁ u₂

private def liftLinearEquiv
    {S : Type*} [CommRing S] {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] [Module S M] [Module S N]
    (e : M ≃+ N) (h : ∀ (b : S) (x : M), e (b • x) = b • e x) :
    ULift.{u₁} M ≃ₗ[S] ULift.{u₂} N where
  toEquiv := ((ULift.moduleEquiv (R := S)).toEquiv.trans e.toEquiv).trans
    (ULift.moduleEquiv (R := S)).symm.toEquiv
  map_add' := by intros; exact congrArg ULift.up (e.map_add _ _)
  map_smul' := by intro b x; exact congrArg ULift.up (h b x.down)

omit [HasDerivedCategory.{z} (ModuleCat.{max c v r} A)] in
/-- Cohomology of the section representative is naturally the shifted derived Hom module.
Source: Stacks Project, Tags 0B6E, 08JA and 070I.
(blueprint: lem-sfb-global-rhom-representative-cohomology-comparison).

Proof: forget coefficients and identify the section representative with the ordinary
Hom complex. Its cohomology consists of homotopy classes of shifted maps. The
K-injective localization bijection identifies these with derived maps, naturally
under postcomposition. Apply naturality to scalar multiplication on the target:
the chain-level scalar formula identifies its action on sections with the given
coefficient action. Thus the additive comparison is linear. Lift both modules to
a common universe and assemble the comparisons into a natural isomorphism. -/
theorem representative_cohomology_comparison
    (L : CochainComplex (Modules.{c, v, max c v r} R) ℤ) (q : ℤ) :
    Nonempty ((DerivedInternalHomSectionsModel.injectiveProperty.{c, v, r} R).ι ⋙
      representative.{c, v, r, a} R A φ L ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{max c v r} A) (.up ℤ) q ⋙
      ModuleCat.uliftFunctor.{w} A ≅
    (DerivedInternalHomSectionsModel.injectiveProperty.{c, v, r} R).ι ⋙ DerivedCategory.Q.{w} ⋙
      shiftedHomFunctor.{c, v, r, a, w} R A φ (DerivedCategory.Q.obj L) q) := by
  refine ⟨?_⟩
  refine NatIso.ofComponents (fun I ↦ ?_) ?_
  · have : I.obj.IsKInjective := I.property
    letI : Module A (DerivedCategory.Q.{w}.obj L ⟶
        (DerivedCategory.Q.{w}.obj I.obj)⟦q⟧) := Module.compHom _ φ
    let e := representativeDerivedEquiv.{c, v, r, a, w} R A φ L I.obj q
    exact (liftLinearEquiv e (fun b x ↦
      representativeDerivedEquiv_scalar.{c, v, r, a, w} R A φ L I.obj q b x)).toModuleIso
  · intro I I' f
    have : I.obj.IsKInjective := I.property
    have : I'.obj.IsKInjective := I'.property
    ext x
    exact congrArg ULift.up
      (representativeDerivedEquiv_naturality.{c, v, r, a, w} R A φ L f.hom q x.down)

end CategoryTheory.RingedSiteGlobalRHom
