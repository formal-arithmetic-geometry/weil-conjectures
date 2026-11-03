module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectRingEquiv
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumCompletedSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

private local instance fixedSmall (T : AlgebraicGeometry.Scheme.{u}) :
    CategoryTheory.EssentiallySmall.{u + 1} T.ProEt :=
  CategoryTheory.essentiallySmallSelf.{0} _

private noncomputable local instance fixedSheafify (T : AlgebraicGeometry.Scheme.{u}) :
    CategoryTheory.HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, 0} T

private local instance fixedLocallyBijective (T : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

theorem pbcLevelConstantComparison_hom_eq (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (pbcLevelConstantComparison T d n).hom =
      AdicCoefficients.constantComparison T (A ⧸ d.ideal ^ (n + 1)) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ ((pbcAdicRings T d).obj (op n)).property
  change toSheafify _ _ ≫ (pbcLevelConstantComparison T d n).hom.hom =
    toSheafify _ _ ≫ sheafifyMap _ _
  rw [← toSheafify_naturality]
  ext U b
  exact (pbcLevelConstantComparison_exists T d n).exists.choose_spec U b

theorem pbcLevelConstantComparison_naturality (T : Scheme.{u})
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (dA : AdicCoefficientDatum A) (dB : AdicCoefficientDatum B) (n : ℕ)
    (q : (A ⧸ dA.ideal ^ (n + 1)) →+* (B ⧸ dB.ideal ^ (n + 1))) :
    (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map (CommRingCat.ofHom q) ≫
        (pbcLevelConstantComparison T dB n).hom =
      (pbcLevelConstantComparison T dA n).hom ≫ AdicCoefficients.coefficientMap T q := by
  rw [pbcLevelConstantComparison_hom_eq, pbcLevelConstantComparison_hom_eq]
  change (presheafToSheaf _ CommRingCat).map _ ≫
      (presheafToSheaf _ CommRingCat).map _ =
    (presheafToSheaf _ CommRingCat).map _ ≫
      (presheafToSheaf _ CommRingCat).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

theorem pbcCompletedScalar_projection (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    pbcCompletedScalar T d ≫ pbcAdicProjection T d n =
      (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) ≫
        (pbcLevelConstantComparison T d n).hom := by
  dsimp only [pbcCompletedScalar, pbcAdicProjection, pbcCompletedComparison]
  rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc]
  change (adicDatumScalar T
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
      quotientFinite := d.quotientFinite } ≫ _) ≫ _ = _
  congr 1
  exact (adicDatumScalar_exists T
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
      quotientFinite := d.quotientFinite }).exists.choose_spec n

section RingEquiv

variable {A A' : Type (u + 1)} [CommRing A] [CommRing A']
  (d : AdicCoefficientDatum A) (d' : AdicCoefficientDatum A')
  (φ : A ≃+* A') (hφ : d.ideal.map φ = d'.ideal)

theorem AdicCoefficientDatum.completionIso_scalar (T : Scheme.{u}) :
    pbcCompletedScalar T d ≫ (d.completionIso d' φ hφ T).hom =
      (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom φ.toRingHom) ≫ pbcCompletedScalar T d' := by
  apply limit.hom_ext
  intro j
  obtain ⟨n⟩ := j
  change _ ≫ pbcAdicProjection T d' n = _ ≫ pbcAdicProjection T d' n
  rw [Category.assoc, d.completionIso_hom_projection d' φ hφ T n, ← Category.assoc,
    pbcCompletedScalar_projection, Category.assoc, Category.assoc,
    pbcCompletedScalar_projection, ← Category.assoc _ _ (pbcLevelConstantComparison T d' n).hom,
    ← Functor.map_comp]
  letI := d.quotientFinite
  letI := d'.quotientFinite
  change _ ≫ _ ≫ AdicCoefficients.coefficientMap T (d.quotientRingEquiv d' φ hφ n).toRingHom = _
  rw [← pbcLevelConstantComparison_naturality, ← Category.assoc, ← Functor.map_comp]
  rfl

end RingEquiv
section Adjunctions

/-- Restriction along the identity, normalized on underlying sections. -/
def pbcRestrictIdIso {T : Scheme.{u}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    pbcRestrict (𝟙 R) ≅ 𝟭 (pbcModules T R) :=
  NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        ModuleCat.restrictScalarsId'App _ rfl (M.val.obj U))
        (fun {U V} f ↦ by ext x; rfl)))
      (fun f ↦ by ext U x; rfl)

/-- Restriction along a ring sheaf isomorphism is an equivalence. -/
def pbcRestrictEquivalence {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (e : R ≅ S) :
    pbcModules T S ≌ pbcModules T R :=
  CategoryTheory.Equivalence.mk (pbcRestrict e.hom) (pbcRestrict e.inv)
    (pbcRestrictComp e.inv e.hom (𝟙 S) e.inv_hom_id ≪≫ pbcRestrictIdIso S).symm
    (pbcRestrictComp e.hom e.inv (𝟙 R) e.hom_inv_id ≪≫ pbcRestrictIdIso R)

private def constantPF (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
    PresheafOfModules.pushforward₀
      ((Functor.const X.ProEt).obj (Discrete.mk (ULift.up ())))
      ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A))

private def constantPresheafHomEquiv (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (T : X.ProEt) (hT : IsTerminal T) (M : ModuleCat.{u + 1} A)
    (F : _root_.PresheafOfModules.{u + 1} ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A))) :
    ((constantPF X A).obj M ⟶ F) ≃ (M ⟶ F.obj (op T)) where
  toFun f := f.app (op T)
  invFun q :=
    { app U := q ≫ F.map (hT.from U.unop).op
      naturality := by
        intro U V a
        ext x
        symm
        change F.map a (F.map (hT.from U.unop).op (q x)) =
          F.map (hT.from V.unop).op (q x)
        rw [← F.map_comp_apply]
        have h : (hT.from U.unop).op ≫ a = (hT.from V.unop).op := by
          exact congrArg Quiver.Hom.op (hT.hom_ext _ _)
        rw [h] }
  left_inv f := by
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    exact (PresheafOfModules.naturality_apply f (hT.from U.unop).op x).symm
  right_inv q := by
    have h : hT.from T = 𝟙 T := hT.hom_ext _ _
    ext x
    change F.map (hT.from T).op (q x) = q x
    rw [h]
    simp
    rfl

private def constantPFAdj (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (T : X.ProEt) (hT : IsTerminal T) :
    constantPF X A ⊣ PresheafOfModules.evaluation _ (op T) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := constantPresheafHomEquiv X A T hT
      homEquiv_naturality_left_symm := by
        intros
        apply PresheafOfModules.hom_ext
        intro U
        rfl
      homEquiv_naturality_right := by intros; rfl }

/-- Global sections over a terminal object, with the constant scalar action. -/
private def constantGlobalSections (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (T : X.ProEt) :=
  SheafOfModules.forget (adicLisseRing X A) ⋙
    PresheafOfModules.restrictScalars (adicLisseConstantUnit X A) ⋙
      PresheafOfModules.evaluation _ (op T)

private def constantAdj (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (T : X.ProEt) (hT : IsTerminal T) :
    adicLisseConstantModules X A ⊣ constantGlobalSections X A T :=
  (constantPFAdj X A T hT).comp
    (PresheafOfModules.sheafificationAdjunction (adicLisseConstantUnit X A))

/-- Global sections of completed modules, with the constant scalar action. -/
private def integralGlobalSections {A : Type (u + 1)} [CommRing A]
    (X : Scheme.{u}) (d : AdicCoefficientDatum A) (T : X.ProEt) :=
  pbcRestrict (pbcCompletedScalar X d) ⋙ constantGlobalSections X A T

/-- The completed constant realization is left adjoint to global sections. -/
private def integralConstantAdjunction {A : Type (u + 1)} [CommRing A]
    (X : Scheme.{u}) (d : AdicCoefficientDatum A) (T : X.ProEt) (hT : IsTerminal T) :
    integralConstantModule X d ⊣ integralGlobalSections X d T := by
  let pd : ProEtaleAdicCoefficientDatum A :=
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite }
  let e := proEtaleScalarEquivalence X
    ((adicLisseForget X).mapIso (pbcCompletedComparison X d).symm)
  let adj := ((constantAdj X A T hT).comp
    (adicDatumOrdinaryAdjunction X (adicDatumScalar X pd))).comp e.toAdjunction
  exact adj

end Adjunctions
section ConstantTransport

variable {A A' : Type (u + 1)} [CommRing A] [CommRing A']
  (d : AdicCoefficientDatum A) (d' : AdicCoefficientDatum A')
  (φ : A ≃+* A') (hφ : d.ideal.map φ = d'.ideal)

private theorem completionIso_scalar_apply (T : Scheme.{u}) (U : T.ProEtᵒᵖ) (a : A') :
    (d.completionIso d' φ hφ T).hom.hom.app U ((pbcCompletedScalar T d).hom.app U
      ((toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A))).app U (φ.symm a))) =
    (pbcCompletedScalar T d').hom.app U
      ((toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A'))).app U a) := by
  have h := congrArg (fun f ↦ f.hom.app U ((toSheafify (ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A))).app U (φ.symm a)))
    (d.completionIso_scalar d' φ hφ T)
  refine h.trans ?_
  have hn := ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_naturality
    (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).map (CommRingCat.ofHom φ.toRingHom))) U)
    (φ.symm a)
  simp only [NatTrans.comp_app, CategoryTheory.comp_apply] at hn
  exact congrArg (ConcreteCategory.hom ((pbcCompletedScalar T d').hom.app U))
    (hn.symm.trans (congrArg _ (φ.apply_symm_apply a)))

private theorem smul_congr' {T : Scheme.{u}} {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (N : pbcModules T R) (U : T.ProEtᵒᵖ) {r s : ((adicLisseForget T).obj R).obj.obj U}
    (h : r = s) (x : N.val.obj U) : r • x = s • x := by rw [h]

private def globalSectionsIso (T : Scheme.{u}) (Tm : T.ProEt) :
    integralGlobalSections T d' Tm ≅
      pbcRestrict (d.completionIso d' φ hφ T).hom ⋙ integralGlobalSections T d Tm ⋙
        ModuleCat.restrictScalars φ.symm.toRingHom :=
  NatIso.ofComponents (fun N ↦
    { hom := ModuleCat.ofHom (X := (integralGlobalSections T d' Tm).obj N)
        (Y := (pbcRestrict (d.completionIso d' φ hφ T).hom ⋙ integralGlobalSections T d Tm ⋙
          ModuleCat.restrictScalars φ.symm.toRingHom).obj N)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun a x ↦ by
            exact smul_congr' N (op Tm) (completionIso_scalar_apply d d' φ hφ T (op Tm) a).symm x }
      inv := ModuleCat.ofHom (Y := (integralGlobalSections T d' Tm).obj N)
        (X := (pbcRestrict (d.completionIso d' φ hφ T).hom ⋙ integralGlobalSections T d Tm ⋙
          ModuleCat.restrictScalars φ.symm.toRingHom).obj N)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun a x ↦ by
            exact smul_congr' N (op Tm) (completionIso_scalar_apply d d' φ hφ T (op Tm) a) x } })
    (fun f ↦ by
      ext x
      rfl)

private def constantModuleTransportIso (T : Scheme.{u}) (Tm : T.ProEt) (hT : IsTerminal Tm) :
    integralConstantModule T d' ≅
      ModuleCat.restrictScalars φ.toRingHom ⋙ integralConstantModule T d ⋙
        pbcRestrict (d.completionIso d' φ hφ T).inv :=
  let adj₁ := (ModuleCat.restrictScalarsEquivalenceOfRingEquiv φ).toAdjunction
  let adjG := integralConstantAdjunction T d Tm hT
  let adj₃ := (pbcRestrictEquivalence (d.completionIso d' φ hφ T).symm).toAdjunction
  let adjG' := integralConstantAdjunction T d' Tm hT
  (conjugateIsoEquiv (adj₁.comp (adjG.comp adj₃)) adjG').symm
    (globalSectionsIso d d' φ hφ T Tm).symm

/-- The completed constant realization commutes with the transport of coefficient data. -/
theorem integralConstantDerived_transport (T : Scheme.{u})
    (P : completedConstantDerived (ModuleCat.{u + 1} A')) :
    letI := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
    letI := HasDerivedCategory.standard (ModuleCat.{u + 1} A')
    Nonempty ((integralConstantDerived T d').obj P ≅
      (d.transportDerived d' φ hφ T).obj ((integralConstantDerived T d).obj
        ((ModuleCat.restrictScalars φ.toRingHom).mapDerivedCategory.obj P))) := by
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} A')
  let e := constantModuleTransportIso d d' φ hφ T (⊤_ T.ProEt) terminalIsTerminal
  let := (integralConstantModule_exact T d).1
  let := (integralConstantModule_exact T d).2
  let := (integralConstantModule_exact T d').1
  let := (integralConstantModule_exact T d').2
  exact ⟨((Functor.mapDerivedCategoryNatIso e) ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _)).app P⟩

end ConstantTransport

end AlgebraicGeometry.Scheme
