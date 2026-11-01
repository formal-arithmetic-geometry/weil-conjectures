/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCohomologyHom
public import WeilConjectures.CategoryTheory.Sites.SmoothPurity.SupportLongExact
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedHomCocycleNormalization

/-! # The specified supported-Hom identification

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an,
lem-pur-supported-hom.md and its proof; used in sk-lem-sp-reduction,
lem-pur-gysin-structure.proof.md, step 4
(blueprint: lem-pur-supported-hom).

The older existence theorem forgets which natural isomorphism is meant. Here the
cocycle formula determines a unique natural isomorphism. Choosing that uniquely
specified isomorphism postpones only its existence proof, not its mathematical data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

namespace AlgebraicGeometry.ProEtale

/-- The canonical comparison of the recorded coefficient unit with the constant
module on the small pro-etale site. Source: purity conventions, comparison pullback
of constants (blueprint: lem-pur-supported-hom). -/
def supportedHomConstantIso (P : WeilConjectures.PurityFiniteSetting.{u}) (Z : Scheme.{u}) :
    P.constant Z ≅ (constantSheaf (Scheme.ProEt.topology Z)
      (ModuleCat.{u + 1} P.Coefficient)).obj (ModuleCat.of P.Coefficient P.Coefficient) :=
  ((Functor.isoWhiskerLeft
      (constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
      (Functor.sheafPullbackConstruction.sheafPullbackIso (Scheme.toProEt Z)
        (ModuleCat.{u + 1} P.Coefficient) Z.smallEtaleTopology
        (Scheme.ProEt.topology Z)).symm ≪≫
    (Scheme.toProEt Z).constantSheafsheafPullbackIso (ModuleCat.{u + 1} P.Coefficient)
      Z.smallEtaleTopology (Scheme.ProEt.topology Z)
      (terminalIsTerminal : IsTerminal (⊤_ Z.Etale))
      (terminalIsTerminal.isTerminalObj (Scheme.toProEt Z))).app
        (ModuleCat.of P.Coefficient P.Coefficient))

/-- The supported coefficient object is the underived direct image in degree zero.
Source: lem-pur-supported-hom (blueprint: lem-pur-supported-hom). -/
abbrev supportedHomSource (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) :=
  (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z)

/-- The two additive-group-valued functors in the supported-Hom statement.
Source: lem-pur-supported-hom, displayed identification
(blueprint: lem-pur-supported-hom). -/
abbrev SupportedHomIdentification (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (a : ℤ) :=
  (derivedSupportSections i P.Coefficient ⋙
    DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) a ⋙
    forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}) ≅
  (DerivedCategory.Plus.ι ⋙
    shiftFunctor (ModuleDerivedCategory X P.Coefficient) a ⋙
    preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) 0).obj
        (supportedHomSource P i))))

/-- Evaluation on the quotient of the coefficient unit specifies the cocycle map.
A supported cycle is sent to the chain map from i_*A_Z in degree zero, shifted
with the cochain convention, then localized. Source: lem-pur-supported-hom,
proof steps 4--6 (blueprint: lem-pur-supported-hom). -/
def SupportedHomCocycleNormalization (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (a : ℤ)
    (χ : SupportedHomIdentification P i a) : Prop :=
  ∀ (I : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (_hi : ∀ r : ℤ, Injective (I.obj.X r))
    (f : supportedHomSource P i ⟶ I.obj.X a)
    (hf : f ≫ I.obj.d a (a + 1) = 0)
    (s : (((supportSections i P.Coefficient).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I.obj).cycles a),
    kernel.ι ((I.obj.X a).obj.map (supportRestrictionArrow i).op)
        ((((supportSections i P.Coefficient).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I.obj).iCycles a s) =
      f.hom.app (op (Scheme.ProEt.mk (𝟙 X)))
        ((Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} P.Coefficient)
            (ModuleCat.of P.Coefficient P.Coefficient) ≫
          (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).map
            (supportedHomConstantIso P Z).inv).hom.app
              (op (Scheme.ProEt.mk (𝟙 X)))
                ((toSheafify (Scheme.ProEt.topology X)
                  ((Functor.const X.ProEtᵒᵖ).obj
                    (ModuleCat.of P.Coefficient P.Coefficient))).app
                      (op (Scheme.ProEt.mk (𝟙 X))) (1 : P.Coefficient))) →
    χ.hom.app (DerivedCategory.Plus.Q.obj I)
        ((Sheaf.supportSequenceModelIso (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} P.Coefficient) (supportSections i P.Coefficient)
          I (DerivedCategory.Plus.Q.obj I) (Iso.refl _) a).hom
            ((((supportSections i P.Coefficient).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I.obj).homologyπ a s)) =
      (DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app (supportedHomSource P i) ≫
        ShiftedHom.map (Cocycle.equivHomShift.symm
          (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf)) DerivedCategory.Q ≫
        ((DerivedCategory.quotientCompQhIso _).inv.app I.obj)⟦a⟧'

section
variable {A : Type (u + 1)} [CommRing A]
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J (ModuleCat.{u + 1} A)]
    [IsGrothendieckAbelian.{u + 1} (Sheaf J (ModuleCat.{u + 1} A))]
    {T W : C} (hT : IsTerminal T) (j : W ⟶ T)
    (B₀ : Sheaf J (ModuleCat.{u + 1} A))
    (rho₀ : (constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ B₀)
    (B : Sheaf J (ModuleCat.{u + 1} A)) (d : B₀ ≅ B)
omit [HasSheafify J (ModuleCat.{u + 1} A)]
  [IsGrothendieckAbelian.{u + 1} (Sheaf J (ModuleCat.{u + 1} A))] in
end

private def supportHomNormalizationChangeSupportedGeneric
    {A : Type (u + 1)} [CommRing A]
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J (ModuleCat.{u + 1} A)]
    [IsGrothendieckAbelian.{u + 1} (Sheaf J (ModuleCat.{u + 1} A))]
    {T W : C} (hT : IsTerminal T) (j : W ⟶ T)
    (B₀ : Sheaf J (ModuleCat.{u + 1} A))
    (rho₀ : (constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ B₀)
    (B : Sheaf J (ModuleCat.{u + 1} A))
    (rho : (constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ B)
    (d : B₀ ≅ B) (hd : rho₀ ≫ d.hom = rho)
    (N : AlgebraicGeometry.SupportedHomCocycleNormalization J A hT j B rho) :
    AlgebraicGeometry.SupportedHomCocycleNormalization J A hT j
      B₀ rho₀ := by
  exact
    { theta := supportHomChangeTheta J j B₀ B d N.theta
      evaluation := by
        intro M f
        rw [supportHomChangeTheta_apply, N.evaluation]
        have hr : rho ≫ d.inv ≫ f = rho₀ ≫ f := by
          rw [← hd, Category.assoc, Iso.hom_inv_id_assoc]
        rw [hr]
      chi := supportHomChangeChi J j B₀ B d N.chi
      naturality := by
        intro K M b a x
        rw [supportHomChangeChi_apply, supportHomChangeChi_apply, N.naturality]
        exact (Category.assoc _ _ _).symm
      cocycle := supportHomChangeCocycle J j B₀ B d N.theta N.chi N.cocycle }


private abbrev shs_rho (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) :=
  Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} P.Coefficient)
    (ModuleCat.of P.Coefficient P.Coefficient) ≫
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).map (supportedHomConstantIso P Z).inv

private def shs_normalization (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (N : AlgebraicGeometry.ProEtale.supportedHomNormalization P i) :
    AlgebraicGeometry.SupportedHomCocycleNormalization (Scheme.ProEt.topology X)
      P.Coefficient (MorphismProperty.Over.mkIdTerminal _ _) (supportRestrictionArrow i)
      (supportedHomSource P i) (shs_rho P i) := by
  refine supportHomNormalizationChangeSupportedGeneric (Scheme.ProEt.topology X)
    (MorphismProperty.Over.mkIdTerminal _ _) (supportRestrictionArrow i)
    (supportedHomSource P i) (shs_rho P i) _ _
    ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).mapIso
      (supportedHomConstantIso P Z)) ?_ N
  simp only [shs_rho, Functor.mapIso_hom, Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id]
  simp

private theorem shs_resolution_id
    {A : Type (u + 1)} [CommRing A] {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{u + 1} A)]
    [IsGrothendieckAbelian.{u + 1} (Sheaf J (ModuleCat.{u + 1} A))]
    (I : CochainComplex.Plus (Sheaf J (ModuleCat.{u + 1} A))) :
    supportedHomResolutionIso J A I I (𝟙 I) = Iso.refl _ := by
  apply Iso.ext
  apply DerivedCategory.Plus.ι.map_injective
  change DerivedCategory.Plus.ι.map (DerivedCategory.Plus.ι.preimage _) = _
  rw [Functor.map_preimage]
  simp
  rfl

private theorem shs_injective_cocycle
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (N : AlgebraicGeometry.ProEtale.supportedHomNormalization P i)
    (I : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    [∀ n : ℤ, Injective (I.obj.X n)] (a : ℤ)
    (x : (((supportSections i P.Coefficient).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I.obj).cycles a) :
    ∃ f : supportedHomSource P i ⟶ I.obj.X a,
      (shs_normalization P i N).theta.hom.app (I.obj.X a) f =
        (((supportSections i P.Coefficient).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I.obj).iCycles a x ∧
      ∃ hf : f ≫ I.obj.d a (a + 1) = 0,
        (shs_normalization P i N).chi (DerivedCategory.Plus.Q.obj I) a
          ((Sheaf.supportSequenceModelIso (Scheme.ProEt.topology X)
            (ModuleCat.{u + 1} P.Coefficient) (supportSections i P.Coefficient) I
            (DerivedCategory.Plus.Q.obj I) (Iso.refl _) a).hom
              ((((supportSections i P.Coefficient).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj I.obj).homologyπ a x)) =
          supportedHomLocalizedCocycle I.obj a f hf := by
  obtain ⟨f, ⟨hf, hfn⟩, _⟩ := (shs_normalization P i N).cocycle I I (𝟙 I) a x
  obtain ⟨hd, hchi⟩ := hfn
  refine ⟨f, hf, hd, ?_⟩
  exact supportHomIdentityRoof DerivedCategory.Plus.ι
    (shiftFunctor (ModuleDerivedCategory X P.Coefficient) a)
    (fun d ↦ (shs_normalization P i N).chi (DerivedCategory.Plus.Q.obj I) a
      ((Sheaf.supportSequenceModelIso (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} P.Coefficient) (supportSections i P.Coefficient) I
        (DerivedCategory.Plus.Q.obj I) d a).hom
          ((((supportSections i P.Coefficient).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I.obj).homologyπ a x)))
    (supportedHomLocalizedCocycle I.obj a f hd)
    (supportedHomLocalizedCocycle I.obj a f hd) rfl
    (supportedHomResolutionIso _ P.Coefficient I I (𝟙 I))
    ((DerivedCategory.quotientCompQhIso _).inv.app I.obj)
    (shs_resolution_id _ I) (by rfl) hchi

private theorem shs_evaluation
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (N : AlgebraicGeometry.ProEtale.supportedHomNormalization P i)
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))
    (f : supportedHomSource P i ⟶ M) :
    kernel.ι (M.obj.map (supportRestrictionArrow i).op)
      ((shs_normalization P i N).theta.hom.app M f) =
      f.hom.app (op (Scheme.ProEt.mk (𝟙 X)))
        ((shs_rho P i).hom.app (op (Scheme.ProEt.mk (𝟙 X)))
          ((toSheafify (Scheme.ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj
              (ModuleCat.of P.Coefficient P.Coefficient))).app
                (op (Scheme.ProEt.mk (𝟙 X))) (1 : P.Coefficient))) := by
  exact (shs_normalization P i N).evaluation M f

private theorem shs_comp_map_id
    {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {X : C} {Y : D} (f : Y ⟶ G.obj X) : f = f ≫ G.map (𝟙 X) := by
  rw [G.map_id, Category.comp_id]

private theorem shs_roof_eq
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (I : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (a : ℤ) (f : supportedHomSource P i ⟶ I.obj.X a)
    (hf : f ≫ I.obj.d a (a + 1) = 0) :
    supportedHomLocalizedCocycle I.obj a f hf =
      (DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app (supportedHomSource P i) ≫
        ShiftedHom.map (Cocycle.equivHomShift.symm
          (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf)) DerivedCategory.Q ≫
        ((DerivedCategory.quotientCompQhIso _).inv.app I.obj)⟦a⟧' := by
  rw [supportedHomLocalizedCocycle_eq]
  change _ = 𝟙 _ ≫ _ ≫ (shiftFunctor _ a).map (𝟙 _)
  rw [Category.id_comp]
  exact shs_comp_map_id (shiftFunctor (ModuleDerivedCategory X P.Coefficient) a) _

/-- The concrete normalization record supplies the derived comparison. The proof transports
its injective-cocycle field through the derived roof construction. Source: the
normalization theorem and lem-pur-supported-hom-specified-existence.
(blueprint: lem-pur-supported-hom-specified-record-existence). -/
theorem normalized_comparison_exists_from_record
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (a : ℤ)
    (N : AlgebraicGeometry.ProEtale.supportedHomNormalization P i) :
    ∃ χ : SupportedHomIdentification P i a, SupportedHomCocycleNormalization P i a χ := by
  let M := shs_normalization P i N
  let χ : SupportedHomIdentification P i a :=
    NatIso.ofComponents (fun F ↦ (M.chi F a).toAddCommGrpIso) (by
      intro F G f
      ext x
      exact M.naturality F G f a x)
  refine ⟨χ, ?_⟩
  intro I hi f hf s hs
  have := hi
  obtain ⟨g, hg, hgd, hchi⟩ := shs_injective_cocycle P i N I a s
  have hfg : f = g := by
    apply (AddCommGrpCat.mono_iff_injective (M.theta.hom.app (I.obj.X a))).mp
      inferInstance
    apply (ModuleCat.mono_iff_injective
      (kernel.ι ((I.obj.X a).obj.map (supportRestrictionArrow i).op))).mp inferInstance
    exact (shs_evaluation P i N _ f).trans (hs.symm.trans
      (congrArg (kernel.ι ((I.obj.X a).obj.map (supportRestrictionArrow i).op)) hg).symm)
  subst g
  change M.chi _ a _ = _
  exact hchi.trans (shs_roof_eq P i I a f hf)

/-- Existence of a supported-Hom comparison satisfying the cocycle formula.
Source: lem-pur-supported-hom and its proof (latest blueprint, sk-prop-an),
used in lem-pur-gysin-structure.proof.md, step 4
(blueprint: lem-pur-supported-hom-specified-existence).

Proof: identify constant-coefficient sections with locally constant functions.
The restriction A_X to i_*A_Z is epic and its kernel is extension by zero of
A_U. Hence Hom(i_*A_Z,M) is the support kernel, with the identification fixed
by evaluation on the image of 1 (lem-pur-supported-sections-hom). Exact scalar
forgetting commutes with bounded-below right derived functors, so this additive
identification derives on bounded-below injective complexes
(lem-weil-pbc-right-derived-plus-injective). The derived-Hom roof formula
(lem-sc-p1-rhom-hom-derived-roof) sends each cycle to exactly the displayed
localized chain map, which gives a natural isomorphism satisfying the formula.
No constructibility, Tor bound, or locally Noetherian assumption is used. -/
theorem exists_supportedCohomologyHom (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (a : ℤ) :
    ∃ χ : SupportedHomIdentification P i a, SupportedHomCocycleNormalization P i a χ := by
  obtain ⟨_, ⟨N⟩, _, _, _⟩ := AlgebraicGeometry.supportedHom_cocycle_normalization P i
  exact normalized_comparison_exists_from_record P i a N


private theorem shs_surjective_cycleClass.{v, w}
    {R : Type w} [Ring R] (K : CochainComplex (ModuleCat.{v} R) ℤ) (a : ℤ)
    {M : ModuleCat.{v} R} (e : K.homology a ≅ M) (x : M) :
    ∃ s : K.cycles a, e.hom (K.homologyπ a s) = x := by
  obtain ⟨s, hs⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ a)).mp
    inferInstance (e.inv x)
  refine ⟨s, ?_⟩
  rw [hs]
  exact e.inv_hom_id_apply x

/-- A fixed normalization record makes the cocycle comparison unique. The proof compares
all derived components through injective representatives. Source: the normalization theorem
and lem-pur-supported-hom-specified-uniqueness.
(blueprint: lem-pur-supported-hom-specified-record-uniqueness). -/
theorem normalized_comparison_unique_from_record
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (a : ℤ)
    (N : AlgebraicGeometry.ProEtale.supportedHomNormalization P i)
    (χ₁ χ₂ : SupportedHomIdentification P i a)
    (h₁ : SupportedHomCocycleNormalization P i a χ₁)
    (h₂ : SupportedHomCocycleNormalization P i a χ₂) : χ₁ = χ₂ := by
  have hQ (I : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
      (hi : ∀ r : ℤ, Injective (I.obj.X r)) :
      χ₁.hom.app (DerivedCategory.Plus.Q.obj I) =
        χ₂.hom.app (DerivedCategory.Plus.Q.obj I) := by
    have := hi
    ext x
    let K := ((supportSections i P.Coefficient).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I.obj
    let EI : K.homology a ≅
        ((derivedSupportSections i P.Coefficient ⋙
          DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) a).obj
            (DerivedCategory.Plus.Q.obj I)) :=
      Sheaf.supportSequenceModelIso (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} P.Coefficient) (supportSections i P.Coefficient) I
        (DerivedCategory.Plus.Q.obj I) (Iso.refl _) a
    obtain ⟨s, hx⟩ := shs_surjective_cycleClass K a EI x
    obtain ⟨f, hf, hfd, _⟩ := shs_injective_cocycle P i N I a s
    have heval := (congrArg
      (kernel.ι ((I.obj.X a).obj.map (supportRestrictionArrow i).op)) hf).symm.trans
        (shs_evaluation P i N _ f)
    have heq := (h₁ I hi f hfd s heval).trans (h₂ I hi f hfd s heval).symm
    rw [← hx]
    exact heq
  apply Iso.ext
  apply NatTrans.ext
  funext F
  obtain ⟨m, hm⟩ := F.2
  have : F.IsGE m := (F.isGE_ι_obj_iff m).mp hm
  obtain ⟨J, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso F m
  let I := (InjectiveObject.ι
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))).mapCochainComplexPlus.obj J
  have hi (n : ℤ) : Injective (I.obj.X n) := (J.obj.X n).2
  apply (cancel_epi ((derivedSupportSections i P.Coefficient ⋙
    DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) a ⋙
    forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}).map e.hom)).mp
  rw [χ₁.hom.naturality, χ₂.hom.naturality, hQ I hi]

/-- Uniqueness of a supported-Hom comparison satisfying the cocycle formula.
Source: lem-pur-supported-hom and its proof (latest blueprint, sk-prop-an)
(blueprint: lem-pur-supported-hom-specified-uniqueness).

Proof: by naturality it suffices to compare the components of χ₁ and χ₂ at
Q(I) for I a bounded-below complex of injectives, since every bounded-below
object is isomorphic to such a Q(I) (K-injective resolutions exist). Every
class in H^a_Z(X,I) is the image of a cycle s of Γ_Z(X,I). By the underived
identification Hom(i_*A_Z,I^a) ≅ Γ_Z(X,I^a), natural in I^a, there is a map
f : i_*A_Z → I^a whose value on the image of 1 is s, and f ≫ d = 0 because s is a
cycle. The normalizations h₁ and h₂ then give χ₁ and χ₂ the same value on the
class of s, so the components agree and χ₁ = χ₂. -/
theorem unique_supportedCohomologyHom (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (a : ℤ)
    (χ₁ χ₂ : SupportedHomIdentification P i a)
    (h₁ : SupportedHomCocycleNormalization P i a χ₁)
    (h₂ : SupportedHomCocycleNormalization P i a χ₂) : χ₁ = χ₂ := by
  obtain ⟨_, ⟨N⟩, _, _, _⟩ := AlgebraicGeometry.supportedHom_cocycle_normalization P i
  exact normalized_comparison_unique_from_record P i a N χ₁ χ₂ h₁ h₂
/-- The supported-Hom isomorphism is uniquely determined by the cocycle formula.
Source: lem-pur-supported-hom and its proof, used in the latest
lem-pur-gysin-structure.proof.md, step 4 (blueprint: lem-pur-supported-hom).

Proof: existence is `exists_supportedCohomologyHom`; any second normalized
comparison equals it by `unique_supportedCohomologyHom`. -/
theorem existsUnique_supportedCohomologyHom (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (a : ℤ) :
    ∃! χ : SupportedHomIdentification P i a, SupportedHomCocycleNormalization P i a χ := by
  obtain ⟨χ, hχ⟩ := exists_supportedCohomologyHom P i a
  refine ⟨χ, hχ, ?_⟩
  intro χ' hχ'
  exact unique_supportedCohomologyHom P i a χ' χ hχ' hχ

/-- The specified natural supported-Hom isomorphism. Its data are determined uniquely
by evaluation on injective cycles, not by a bare Nonempty choice.
Source: lem-pur-supported-hom (blueprint: lem-pur-supported-hom). -/
def supportedCohomologyHom (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (a : ℤ) :
    SupportedHomIdentification P i a :=
  (existsUnique_supportedCohomologyHom P i a).exists.choose

end AlgebraicGeometry.ProEtale
