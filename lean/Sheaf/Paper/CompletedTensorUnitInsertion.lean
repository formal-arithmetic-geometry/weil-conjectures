/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Sheaf.Paper.CompletedTensorUnitInsertionData
import Sheaf.Paper.ReflectiveCompletedMonoidal
import Sheaf.Paper.ReflectiveCompletedPullbackCoherence
import Sheaf.Paper.ConstantNativePullbackMonoidal
import Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction
import Sheaf.Algebra.Homology.RingedInternalHomDerivedComplete

/-! # Completion-unit insertions and coherent completed inverse image

Source: Stacks Project, algebraization.tex, Tags 099A and 099G; proetale.tex,
Tags 099M and 099N; sites-cohomology.tex, Tags 07A4 and 0FPT
(blueprint: lem-pur-completed-tensor-unit-insertion).

The helpers only spell out the constraints in proof steps 5 and 7--9. The theorem
uses the published constant-coefficient derived categories, quotient-tower completion,
and completion units. Ordinary tensor and its signed constraints are the published
native derived tensor structure. Its inverse-image tensor comparison is specified
on flat-term K-flat representatives, rather than replaced by an arbitrary isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u vB uB vE uE

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.ConstantCompletion

section Constraints

variable {B : Type uB} [Category.{vB} B] [MonoidalCategory B] [SymmetricCategory B]
variable {E : Type uE} [Category.{vE} E] [MonoidalCategory E] [SymmetricCategory E]

omit [MonoidalCategory B] [SymmetricCategory B] in
private theorem iso_of_complete_precomp
    (P : ObjectProperty B) {X Y : B} (f : X ⟶ Y) (hX : P X) (hY : P Y)
    (h : ∀ Z : B, P Z → Function.Bijective (fun g : Y ⟶ Z ↦ f ≫ g)) : IsIso f := by
  obtain ⟨g, hg⟩ := (h X hX).2 (𝟙 X)
  refine ⟨⟨g, hg, ?_⟩⟩
  apply (h Y hY).1
  simp only [← Category.assoc, hg, Category.id_comp, Category.comp_id]

omit [MonoidalCategory B] [SymmetricCategory B] in
private theorem reflector_map_iso
    (P : ObjectProperty B) (T : B ⥤ B) (η : 𝟭 B ⟶ T)
    (hT : ∀ X, P (T.obj X))
    (hη : ∀ (X Z : B), P Z →
      Function.Bijective (fun g : T.obj X ⟶ Z ↦ η.app X ≫ g))
    {X Y : B} (f : X ⟶ Y)
    (hf : ∀ Z : B, P Z → Function.Bijective (fun g : Y ⟶ Z ↦ f ≫ g)) :
    IsIso (T.map f) := by
  apply iso_of_complete_precomp P _ (hT X) (hT Y)
  intro Z hZ
  let ex := Equiv.ofBijective _ (hη X Z hZ)
  let ey := Equiv.ofBijective _ (hη Y Z hZ)
  let ef := Equiv.ofBijective _ (hf Z hZ)
  convert (ey.trans ef |>.trans ex.symm).bijective using 1
  funext g
  apply ex.injective
  change η.app X ≫ T.map f ≫ g = ex ((ey.trans ef |>.trans ex.symm) g)
  change η.app X ≫ T.map f ≫ g = ex (ex.symm (ef (ey g)))
  rw [ex.apply_symm_apply]
  exact (η.naturality_assoc f g).symm

omit [SymmetricCategory B] in
private theorem reflector_tensor_left_iso
    (P : ObjectProperty B) (T : B ⥤ B) (η : 𝟭 B ⟶ T)
    (hT : ∀ X, P (T.obj X))
    (hη : ∀ (X Z : B), P Z →
      Function.Bijective (fun g : T.obj X ⟶ Z ↦ η.app X ≫ g))
    (H : B → B ⥤ B) (a : ∀ W : B, tensorRight W ⊣ H W)
    (hH : ∀ W Z : B, P Z → P ((H W).obj Z)) (X W : B) :
    IsIso (tensorInsertLeft T η X W) := by
  apply reflector_map_iso P T η hT hη
  intro Z hZ
  let ex := (a W).homEquiv X Z
  let ey := (a W).homEquiv (T.obj X) Z
  let eη := Equiv.ofBijective _ (hη X ((H W).obj Z) (hH W Z hZ))
  convert (ey.trans eη |>.trans ex.symm).bijective using 1 <;> try rfl
  funext g
  apply ex.injective
  simp only [tensorHom_id]
  change ex (((tensorRight W).map (η.app X)) ≫ g) =
    ex (ex.symm (eη (ey g)))
  rw [ex.apply_symm_apply]
  exact (a W).homEquiv_naturality_left (η.app X) g

private theorem reflector_tensor_right_iso
    (T : B ⥤ B) (η : 𝟭 B ⟶ T)
    (hLeft : ∀ X W : B, IsIso (tensorInsertLeft T η X W)) (X W : B) :
    IsIso (tensorInsertRight T η X W) := by
  have : IsIso (T.map (η.app W ⊗ₘ 𝟙 X)) := hLeft W X
  have he : 𝟙 X ⊗ₘ η.app W =
      (β_ X W).hom ≫ (η.app W ⊗ₘ 𝟙 X) ≫ (β_ (T.obj W) X).hom := by
    rw [← BraidedCategory.braiding_naturality_assoc]
    simp only [SymmetricCategory.symmetry, Category.comp_id]
  dsimp only [tensorInsertRight]
  rw [he, T.map_comp, T.map_comp]
  infer_instance

omit [MonoidalCategory B] [SymmetricCategory B]
  [MonoidalCategory E] [SymmetricCategory E] in
private theorem reflector_pullback_unit_iso
    (P : ObjectProperty B) (P' : ObjectProperty E)
    (T : B ⥤ B) (T' : E ⥤ E) (η : 𝟭 B ⟶ T) (η' : 𝟭 E ⟶ T')
    (hT' : ∀ X, P' (T'.obj X))
    (hη : ∀ (X Z : B), P Z →
      Function.Bijective (fun g : T.obj X ⟶ Z ↦ η.app X ≫ g))
    (hη' : ∀ (X Z : E), P' Z →
      Function.Bijective (fun g : T'.obj X ⟶ Z ↦ η'.app X ≫ g))
    (L : B ⥤ E) (R : E ⥤ B) (a : L ⊣ R)
    (hR : ∀ Z, P' Z → P (R.obj Z)) (X : B) :
    IsIso (T'.map (L.map (η.app X))) := by
  apply reflector_map_iso P' T' η' hT' hη'
  intro Z hZ
  let ex := a.homEquiv X Z
  let ey := a.homEquiv (T.obj X) Z
  let eη := Equiv.ofBijective _ (hη X (R.obj Z) (hR Z hZ))
  convert (ey.trans eη |>.trans ex.symm).bijective using 1 <;> try rfl
  funext g
  apply ex.injective
  change ex (L.map (η.app X) ≫ g) = ex (ex.symm (eη (ey g)))
  rw [ex.apply_symm_apply]
  exact a.homEquiv_naturality_left (η.app X) g

omit [SymmetricCategory E] in
private theorem tensor_both_iso
    (T : E ⥤ E) (η : 𝟭 E ⟶ T)
    (hLeft : ∀ X W : E, IsIso (tensorInsertLeft T η X W))
    (hRight : ∀ X W : E, IsIso (tensorInsertRight T η X W)) (X W : E) :
    IsIso (T.map (η.app X ⊗ₘ η.app W)) := by
  have : IsIso (T.map (η.app X ⊗ₘ 𝟙 W)) := hLeft X W
  have : IsIso (T.map (𝟙 (T.obj X) ⊗ₘ η.app W)) := hRight (T.obj X) W
  have he : η.app X ⊗ₘ η.app W =
      (η.app X ⊗ₘ 𝟙 W) ≫ (𝟙 (T.obj X) ⊗ₘ η.app W) := by
    rw [tensorHom_comp_tensorHom]
    simp only [Category.comp_id, Category.id_comp]
  rw [he, T.map_comp]
  infer_instance

omit [SymmetricCategory B] [SymmetricCategory E] in
private theorem completed_comparison_exists
    (L : B ⥤ E) (T : B ⥤ B) (T' : E ⥤ E)
    (η : 𝟭 B ⟶ T) (η' : 𝟭 E ⟶ T')
    (μ : tensor B ⋙ L ≅ (L.prod L) ⋙ tensor E)
    (hLeft' : ∀ X W : E, IsIso (tensorInsertLeft T' η' X W))
    (hRight' : ∀ X W : E, IsIso (tensorInsertRight T' η' X W))
    (hPull : ∀ X : B, IsIso (T'.map (L.map (η.app X)))) :
    ∃ μc : tensor B ⋙ T ⋙ L ⋙ T' ≅ ((L ⋙ T').prod (L ⋙ T')) ⋙ tensor E ⋙ T',
      (∀ X W : B,
        T'.map (L.map (η.app (X ⊗ W))) ≫ μc.hom.app (X, W) =
          T'.map (μ.hom.app (X, W) ≫
            (η'.app (L.obj X) ⊗ₘ η'.app (L.obj W)))) ∧
      (∀ ν : tensor B ⋙ T ⋙ L ⋙ T' ≅ ((L ⋙ T').prod (L ⋙ T')) ⋙ tensor E ⋙ T',
        (∀ X W : B,
          T'.map (L.map (η.app (X ⊗ W))) ≫ ν.hom.app (X, W) =
            T'.map (μ.hom.app (X, W) ≫
              (η'.app (L.obj X) ⊗ₘ η'.app (L.obj W)))) → ν = μc) := by
  let a : tensor B ⋙ L ⋙ T' ⟶ tensor B ⋙ T ⋙ L ⋙ T' :=
    Functor.whiskerLeft (tensor B) (Functor.whiskerRight η (L ⋙ T'))
  have : IsIso a := by
    rw [NatTrans.isIso_iff_isIso_app]
    rintro ⟨X, W⟩
    exact hPull (X ⊗ W)
  let t : tensor E ⟶ (T'.prod T') ⋙ tensor E := {
    app X := η'.app X.1 ⊗ₘ η'.app X.2
    naturality := by
      rintro ⟨X, W⟩ ⟨Y, Z⟩ ⟨f, g⟩
      change (f ⊗ₘ g) ≫ (η'.app Y ⊗ₘ η'.app Z) =
        (η'.app X ⊗ₘ η'.app W) ≫ (T'.map f ⊗ₘ T'.map g)
      rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
      congr 1
      · exact η'.naturality f
      · exact η'.naturality g }
  let b : tensor B ⋙ L ⋙ T' ⟶ ((L ⋙ T').prod (L ⋙ T')) ⋙ tensor E ⋙ T' :=
    Functor.whiskerRight μ.hom T' ≫
      Functor.whiskerLeft (L.prod L) (Functor.whiskerRight t T')
  have : IsIso b := by
    rw [NatTrans.isIso_iff_isIso_app]
    rintro ⟨X, W⟩
    have := tensor_both_iso T' η' hLeft' hRight' (L.obj X) (L.obj W)
    change IsIso (T'.map (μ.hom.app (X, W)) ≫
      T'.map (η'.app (L.obj X) ⊗ₘ η'.app (L.obj W)))
    infer_instance
  let c := (asIso a).symm ≪≫ asIso b
  have hc (X W : B) :
      T'.map (L.map (η.app (X ⊗ W))) ≫ c.hom.app (X, W) =
        T'.map (μ.hom.app (X, W) ≫
          (η'.app (L.obj X) ⊗ₘ η'.app (L.obj W))) := by
    change a.app (X, W) ≫ (inv a ≫ b).app (X, W) = _
    rw [NatTrans.comp_app, NatIso.isIso_inv_app, ← Category.assoc, IsIso.hom_inv_id,
      Category.id_comp, T'.map_comp]
    rfl
  refine ⟨c, hc, ?_⟩
  intro ν hν
  apply Iso.ext
  apply NatTrans.ext
  funext X
  obtain ⟨X, W⟩ := X
  have := hPull (X ⊗ W)
  apply (cancel_epi (T'.map (L.map (η.app (X ⊗ W))))).1
  exact (hν X W).trans (hc X W).symm

omit [SymmetricCategory B] [SymmetricCategory E] in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem ordinary_action_units (L : B ⥤ E)
    (μ : tensor B ⋙ L ≅ (L.prod L) ⋙ tensor E)
    (e : L.obj (𝟙_ B) ≅ 𝟙_ E) (o : L.OplaxMonoidal)
    (ho : ∀ X W : B, o.δ X W = μ.hom.app (X, W)) (he : o.η = e.hom) :
    (∀ X : B, μ.hom.app (𝟙_ B, X) ≫ (e.hom ⊗ₘ 𝟙 (L.obj X)) ≫
      (λ_ (L.obj X)).hom = L.map (λ_ X).hom) ∧
    (∀ X : B, μ.hom.app (X, 𝟙_ B) ≫ (𝟙 (L.obj X) ⊗ₘ e.hom) ≫
      (ρ_ (L.obj X)).hom = L.map (ρ_ X).hom) := by
  let := o
  constructor
  · intro X
    have h := Functor.OplaxMonoidal.left_unitality_hom L X
    rw [ho, he] at h
    simpa only [← tensorHom_id] using h
  · intro X
    have h := Functor.OplaxMonoidal.right_unitality_hom L X
    rw [ho, he] at h
    simpa only [← id_tensorHom] using h

end Constraints

/-- Completion units become tensor and pullback isomorphisms, and determine the
unique coherent completed tensor comparison. There is no perfectness assumption on
any positive quotient A/I^(n+1), and both derived inputs are unbounded and arbitrary.

Source: Stacks Project, algebraization.tex, Tags 099A and 099G; proetale.tex,
Tags 099M and 099N; sites-cohomology.tex, Tags 07A4 and 0FPT
(blueprint: lem-pur-completed-tensor-unit-insertion).

Proof (the node's nine steps):
1. For complete Z, RHom(W,Z) is complete by lem-sf-ringed-rhom-derived-complete.
   The tensor-Hom bijections of lem-sf-ringed-derived-closed-symmetric-monoidal
   and reflection from lem-sp-completed-pullback-adjunction identify precomposition
   by C(eta_V tensor 1) with the bijection Hom(CV,RHom(W,Z)) -> Hom(V,RHom(W,Z)).
   Testing Z at source and target gives a two-sided inverse.
2. The same argument applies to every arrow inverted by C, even after tensoring
   with an arbitrary object. Symmetry gives the other tensor insertion. Naturality
   follows from eta and tensor; both units can therefore be inserted together.
3. Put F=C_X L. Direct image preserves completeness by
   lem-sp-completed-pullback-adjunction. The ordinary and completed adjunctions
   identify Hom(F C_Y V,Z) -> Hom(FV,Z) with the reflection bijection into RZ.
   Hence F(eta_V) is invertible, and F inverts all C_Y equivalences.
4. Use constantNativePullbackMonoidal for the published native tensor models.
   Descend the actual complex-level left-derived counit to the homotopy category.
   The canonical flat-term K-flat comparison gives ConstantTensorNormalization,
   and the existing derived tensor lift supplies ordinary symmetric coherence.
5. On the full complete subcategory define tensor by C(V tensor W) and unit by C1.
   Define the associator as inverse left insertion, C of the ordinary associator,
   then right insertion. Symmetry is C of the ordinary symmetry. Each unitor is
   inverse unit insertion, C of the ordinary unitor, then inverse eta of the
   complete input. These are exactly CompletedConstraintModel's formulas.
6. Insert eta at every internal vertex of a parenthesized tensor expression. All
   such insertions are invertible by step 2. After precomposition by these maps,
   the completed pentagon, triangle, involution and hexagons become C of the
   ordinary equations. Cancel the insertion isomorphisms.
7. Set a_V=F(eta_V) and b=C_X(mu followed by eta_LV tensor eta_LW).
   Both are invertible, so mu_c=b a_(V tensor W)^(-1) is a natural isomorphism.
   Its normalization is mu_c a=b; this equation forces uniqueness.
8. For associativity precompose with the two insertion isomorphisms from the
   ordinary threefold tensor. Substitute mu_c a=b and the completed associator
   formula. Naturality of eta cancels the insertions and leaves ordinary
   associativity of mu from step 4. Cancel the source isomorphism.
9. The same substitution for symmetry leaves the ordinary signed symmetry square.
   Define e_c=C_X(e) a_1^(-1). For each unit equation precompose with F of the
   ordinary unit insertion followed by a. Substitution of the completed unitor
   formula and mu_c a=b cancels eta, leaving the ordinary left or right unit
   equation of step 4. No limit is pulled through inverse image, and no quotient
   is required to be perfect. -/
theorem completedTensorUnitInsertion
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology E)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (V : Sheaf JD (Type u) ⥤ Sheaf JC (Type u))
    (adj : L ⊣ V) [PreservesFiniteLimits L] :
    ∃ (F : InverseImageData L) (k : ConstantTensorData F A)
      (μ : constantDerivedTensor JC A ⋙ (derivedPull F V adj (constantMap F A)).functor ≅
        (((derivedPull F V adj (constantMap F A)).functor).prod
          ((derivedPull F V adj (constantMap F A)).functor)) ⋙ constantDerivedTensor JD A),
      ConstantTensorNormalization F V adj A k μ ∧
      @CompletedTensorAssertions (D (constant JC A)) _
        (constantDerivedMonoidal JC A) (constantDerivedSymmetric JC A)
        (D (constant JD A)) _
        (constantDerivedMonoidal JD A) (constantDerivedSymmetric JD A)
        (IsComplete (quotient JC A I 0)) (IsComplete (quotient JD A I 0))
        (derivedPull F V adj (constantMap F A)).functor
        (completion JC A I false) (completion JD A I false)
        (completionUnit JC A I false) (completionUnit JD A I false) μ := by
  classical
  let := HasDerivedCategory.standard (Mod (constant JC A))
  let := HasDerivedCategory.standard (Mod (constant JD A))
  let : MonoidalCategory (D (constant JC A)) := constantDerivedMonoidal JC A
  let : SymmetricCategory (D (constant JC A)) := constantDerivedSymmetric JC A
  let : MonoidalCategory (D (constant JD A)) := constantDerivedMonoidal JD A
  let : SymmetricCategory (D (constant JD A)) := constantDerivedSymmetric JD A
  obtain ⟨F, G, eG, aM, haM, hlim, hcol, RF, ηG, hRF, hηG,
    aD, haD, hC, hD, hG, aC, aDComp, haC, haDComp, aComplete, haComp⟩ :=
    completedPullbackAdjunction JC JD A I L V adj
  let PC : ObjectProperty (D (constant JC A)) := IsComplete (quotient JC A I 0)
  let PD : ObjectProperty (D (constant JD A)) := IsComplete (quotient JD A I 0)
  let TC : D (constant JC A) ⥤ D (constant JC A) := completion JC A I false
  let TD : D (constant JD A) ⥤ D (constant JD A) := completion JD A I false
  let ηC : 𝟭 (D (constant JC A)) ⟶ TC := completionUnit JC A I false
  let ηD : 𝟭 (D (constant JD A)) ⟶ TD := completionUnit JD A I false
  have hbijC (X Z : D (constant JC A)) (hZ : PC Z) :
      Function.Bijective (fun f : TC.obj X ⟶ Z ↦ ηC.app X ≫ f) := by
    convert (PC.fullyFaithfulι.homEquiv.symm.trans
      (aC.homEquiv X ⟨Z, hZ⟩)).bijective using 1
    funext f
    exact (haC X ⟨Z, hZ⟩ (ObjectProperty.homMk f)).symm
  have hbijD (X Z : D (constant JD A)) (hZ : PD Z) :
      Function.Bijective (fun f : TD.obj X ⟶ Z ↦ ηD.app X ≫ f) := by
    convert (PD.fullyFaithfulι.homEquiv.symm.trans
      (aDComp.homEquiv X ⟨Z, hZ⟩)).bijective using 1
    funext f
    exact (haDComp X ⟨Z, hZ⟩ (ObjectProperty.homMk f)).symm
  have hηC (X : PC.FullSubcategory) : IsIso (ηC.app X.obj) :=
    iso_of_complete_precomp PC _ X.property (hC X.obj) (hbijC X.obj)
  have hηD (X : PD.FullSubcategory) : IsIso (ηD.app X.obj) :=
    iso_of_complete_precomp PD _ X.property (hD X.obj) (hbijD X.obj)
  have hPull (X : D (constant JC A)) :
      IsIso (TD.map ((derivedPull F V adj (constantMap F A)).functor.map (ηC.app X))) :=
    reflector_pullback_unit_iso PC PD TC TD ηC ηD hD hbijC hbijD _ RF aD hG X
  let : ∀ U : C, HasDerivedCategory
      (ringedSiteModules.{u} ((sheafCompose (JC.over U)
        (forget₂ CommRingCat RingCat)).obj ((constant JC A).over U))) :=
    fun _ ↦ HasDerivedCategory.standard _
  let : ∀ U : E, HasDerivedCategory
      (ringedSiteModules.{u} ((sheafCompose (JD.over U)
        (forget₂ CommRingCat RingCat)).obj ((constant JD A).over U))) :=
    fun _ ↦ HasDerivedCategory.standard _
  have hmono {S : Type u} [SmallCategory S] {J : GrothendieckTopology S}
      {R : Sheaf J CommRingCat.{u}} (K : RingedSiteIdeal R) : Mono K.inclusion := by
    constructor
    intro M f g h
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (congrArg (fun k ↦ k.val.app U) h) x
  let : Mono (kernelIdeal (quotient JC A I 0)).inclusion := hmono _
  let : Mono (kernelIdeal (quotient JD A I 0)).inclusion := hmono _
  have hLeftC (X W : D (constant JC A)) : IsIso (tensorInsertLeft TC ηC X W) := by
    obtain ⟨⟨m, aH, ev⟩, hm, _⟩ :=
      RingedDerivedNative.closedAdjunction.{u, u, u} JC (constant JC A)
    dsimp only [WeilConjectures.CoefficientClosedStructure.monoidal] at hm
    subst m
    apply reflector_tensor_left_iso PC TC ηC hC hbijC
      (fun W ↦ Prod.sectR (Opposite.op W) _ ⋙
        derivedInternalHomOfUniverses.{u, u, u} JC (constant JC A)) aH
    intro W Z hZ
    exact isLocallyDerivedRingedIdealComplete_derivedInternalHom JC (constant JC A)
      (kernelIdeal (quotient JC A I 0)).module
      (kernelIdeal (quotient JC A I 0)).inclusion W Z hZ
  have hLeftD (X W : D (constant JD A)) : IsIso (tensorInsertLeft TD ηD X W) := by
    obtain ⟨⟨m, aH, ev⟩, hm, _⟩ :=
      RingedDerivedNative.closedAdjunction.{u, u, u} JD (constant JD A)
    dsimp only [WeilConjectures.CoefficientClosedStructure.monoidal] at hm
    subst m
    apply reflector_tensor_left_iso PD TD ηD hD hbijD
      (fun W ↦ Prod.sectR (Opposite.op W) _ ⋙
        derivedInternalHomOfUniverses.{u, u, u} JD (constant JD A)) aH
    intro W Z hZ
    exact isLocallyDerivedRingedIdealComplete_derivedInternalHom JD (constant JD A)
      (kernelIdeal (quotient JD A I 0)).module
      (kernelIdeal (quotient JD A I 0)).inclusion W Z hZ
  have hRightC := reflector_tensor_right_iso TC ηC hLeftC
  have hRightD := reflector_tensor_right_iso TD ηD hLeftD
  obtain ⟨k, μ, e, o, hnorm, ho, he, hβ⟩ := constantNativePullbackMonoidal F V adj A G.obj aM RF aD
  obtain ⟨μc, hμc, huniq⟩ := completed_comparison_exists
    (derivedPull F V adj (constantMap F A)).functor TC TD ηC ηD μ hLeftD hRightD hPull
  let LF := (derivedPull F V adj (constantMap F A)).functor
  let : IsIso (TD.map (LF.map (ηC.app (𝟙_ (D (constant JC A)))))) := hPull _
  let ec : TD.obj (LF.obj (TC.obj (𝟙_ (D (constant JC A))))) ≅
      TD.obj (𝟙_ (D (constant JD A))) :=
    (asIso (TD.map (LF.map (ηC.app (𝟙_ (D (constant JC A))))))).symm ≪≫ TD.mapIso e
  have hec : TD.map (LF.map (ηC.app (𝟙_ (D (constant JC A))))) ≫ ec.hom =
      TD.map e.hom := by simp [ec]
  obtain ⟨hl, hr⟩ := ordinary_action_units LF μ e o ho he
  obtain ⟨m, s, hm, rm, hrm⟩ := reflectiveCompletedMonoidal PC TC ηC hC hbijC hηC hLeftC hRightC
  obtain ⟨m', s', hm', rm', hrm'⟩ :=
    reflectiveCompletedMonoidal PD TD ηD hD hbijD hηD hLeftD hRightD
  refine ⟨F, k, μ, hnorm, hC, hD, hηC, hηD, hLeftC, hRightC, hLeftD, hRightD,
    hPull, e, μc, ec, hl, hr, hμc, huniq, hec, m, m', s, s', hm, hm', ?_⟩
  exact reflectiveCompletedPullbackCoherence PC PD LF TC TD ηC ηD hC hD hbijC hbijD
    hηC hηD hLeftC hRightC hLeftD hRightD hPull μ e o ho he hβ μc hμc ec hec
    m m' s s' hm hm' rm rm' hrm hrm'

end CategoryTheory.ConstantCompletion
