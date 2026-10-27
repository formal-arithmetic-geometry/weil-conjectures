/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # A tensor-counit transpose under an adjunction mate

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-factors.proof.md, Proof (2)
(blueprint: lem-sp-tensor-counit-exchange-calculus).
-/

@[expose] public section
set_option autoImplicit false

universe uC vC uD vD uC' vC' uD' vD'

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
  {C' : Type uC'} [Category.{vC'} C'] [MonoidalCategory C']
  {D' : Type uD'} [Category.{vD'} D'] [MonoidalCategory D']

/-- The source comparison `H'VK ⊗ UM ≅ U(HK ⊗ M)`.
Source: smooth-purity base-change factors, Proof (2), tensor comparisons
(blueprint: lem-sp-tensor-counit-exchange-calculus). -/
def tensorCounitSourceIso (H : D ⥤ C) (H' : D' ⥤ C')
    (U : C ⥤ C') (V : D ⥤ D') [U.Monoidal]
    (θ : H ⋙ U ≅ V ⋙ H') (K : D) (M : C) :
    H'.obj (V.obj K) ⊗ U.obj M ≅ U.obj (H.obj K ⊗ M) :=
  tensorIso (θ.app K).symm (Iso.refl _) ≪≫ Functor.Monoidal.μIso U _ _

/-- The tensor map transposed from the inverse projection and the unit counit.
Source: smooth-purity base-change factors, Proof (2)
(blueprint: lem-sp-tensor-counit-exchange-calculus). -/
noncomputable def tensorCounitTranspose {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) (H : D ⥤ C) (K : D)
    (P : K ⊗ F.obj (G.obj (𝟙_ D)) ⟶ F.obj (H.obj K ⊗ G.obj (𝟙_ D)))
    [IsIso P] : H.obj K ⊗ G.obj (𝟙_ D) ⟶ G.obj K :=
  adj.homEquiv _ _ (inv P ≫ (K ◁ adj.counit.app (𝟙_ D)) ≫ (ρ_ K).hom)

/-- The unit component of the adjunction mate, with `V1 ≅ 1` included.
Source: smooth-purity base-change factors, Proof (2)
(blueprint: lem-sp-tensor-counit-exchange-calculus). -/
def tensorCounitMateUnit {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {F' : C' ⥤ D'} {G' : D' ⥤ C'} (adj' : F' ⊣ G')
    {U : C ⥤ C'} {V : D ⥤ D'} [V.Monoidal] (β : F ⋙ V ≅ U ⋙ F') :
    U.obj (G.obj (𝟙_ D)) ⟶ G'.obj (𝟙_ D') :=
  (mateEquiv adj adj' β.inv).app (𝟙_ D) ≫
    G'.map (Functor.Monoidal.εIso V).inv

/-- The common inverse transpose, with the tensor unit comparison included.
Source: smooth-purity base-change factors, Proof (2)
(blueprint: lem-sp-tensor-counit-exchange-calculus). -/
noncomputable def tensorCounitCommonTranspose {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) (F' : C' ⥤ D') (H' : D' ⥤ C')
    {U : C ⥤ C'} {V : D ⥤ D'} [V.Monoidal]
    (β : F ⋙ V ≅ U ⋙ F') (K : D)
    (P' : V.obj K ⊗ F'.obj (U.obj (G.obj (𝟙_ D))) ⟶
      F'.obj (H'.obj (V.obj K) ⊗ U.obj (G.obj (𝟙_ D)))) [IsIso P'] :
    F'.obj (H'.obj (V.obj K) ⊗ U.obj (G.obj (𝟙_ D))) ⟶ V.obj K :=
  inv P' ≫ (V.obj K ◁ (β.inv.app (G.obj (𝟙_ D)) ≫
    V.map (adj.counit.app (𝟙_ D)) ≫ (Functor.Monoidal.εIso V).inv)) ≫
    (ρ_ (V.obj K)).hom

/-- Tensorator naturality and right unit compatibility, with the unit comparison explicit. -/
private theorem tensorCounit_map_unit (V : D ⥤ D') [V.Monoidal]
    (K X : D) (c : X ⟶ 𝟙_ D) :
    V.map ((K ◁ c) ≫ (ρ_ K).hom) =
      (Functor.Monoidal.μIso V K X).inv ≫
        (V.obj K ◁ (V.map c ≫ (Functor.Monoidal.εIso V).inv)) ≫
        (ρ_ (V.obj K)).hom := by
  rw [Functor.map_comp, Functor.Monoidal.map_whiskerLeft,
    Functor.Monoidal.map_rightUnitor]
  simp only [Category.assoc, Functor.Monoidal.μIso_inv,
    Functor.Monoidal.εIso_inv, Functor.Monoidal.μ_δ_assoc, whiskerLeft_comp]

omit [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalCategory C'] [MonoidalCategory D'] in
/-- Transport a counit composite across a natural comparison of left adjoints. -/
private theorem tensorCounit_transport
    (F : C ⥤ D) (F' : C' ⥤ D') (U : C ⥤ C') (V : D ⥤ D')
    (β : F ⋙ V ≅ U ⋙ F') {A N : C} {B N' : C'} {K : D}
    (s : B ⟶ U.obj A) (t : A ⟶ N) (e : U.obj N ⟶ N')
    (c : F.obj N ⟶ K) (c' : F'.obj N' ⟶ V.obj K)
    (he : F'.map e ≫ c' = β.inv.app N ≫ V.map c) :
    F'.map (s ≫ U.map t ≫ e) ≫ c' =
      F'.map s ≫ β.inv.app A ≫ V.map (F.map t ≫ c) := by
  simp only [Functor.map_comp, Category.assoc, he]
  have hn := β.inv.naturality t
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc (F'.map (U.map t)), hn]
  simp only [Category.assoc]

/-- Move a morphism in the coefficient through the inverse projection isomorphisms. -/
private theorem tensorCounit_projection
    (F' : C' ⥤ D') (H' : D' ⥤ C')
    (P' : ∀ (K : D') (M : C'), K ⊗ F'.obj M ⟶ F'.obj (H'.obj K ⊗ M))
    (hP' : ∀ {K K' : D'} {M M' : C'} (f : K ⟶ K') (g : M ⟶ M'),
      (f ⊗ₘ F'.map g) ≫ P' K' M' = P' K M ≫ F'.map (H'.map f ⊗ₘ g))
    (K : D') {M M' N : C'} [IsIso (P' K M)] [IsIso (P' K M')]
    (e : M ⟶ M') (t : H'.obj K ⊗ M' ⟶ N) (c : F'.obj N ⟶ K)
    (c1 : F'.obj M' ⟶ 𝟙_ D')
    (ht : F'.map t ≫ c = inv (P' K M') ≫ (K ◁ c1) ≫ (ρ_ K).hom) :
    F'.map ((H'.obj K ◁ e) ≫ t) ≫ c =
      inv (P' K M) ≫ (K ◁ (F'.map e ≫ c1)) ≫ (ρ_ K).hom := by
  have hn := hP' (𝟙 K) e
  simp only [Functor.map_id, id_tensorHom] at hn
  have hi : F'.map (H'.obj K ◁ e) ≫ inv (P' K M') =
      inv (P' K M) ≫ (K ◁ F'.map e) := by
    apply (cancel_epi (P' K M)).mp
    rw [← Category.assoc, ← hn, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
    simp
  simp only [Functor.map_comp, Category.assoc, ht]
  rw [← Category.assoc _ (inv (P' K M')), hi]
  simp only [Category.assoc, whiskerLeft_comp]

/-- A projection/exchange equation intertwines the two tensor-counit transposes.
Source: smooth-purity base-change factors, Proof (2)
(blueprint: lem-sp-tensor-counit-exchange-calculus).

Proof: Put A = HK ⊗ G1 and B = H'VK ⊗ UG1. Expand the inverse Hom transposes
as F(t) followed by the counit (lem-weil-pbc-adjunction-of-natural-bijection).
The mate counit equation (lem-amb-mate-unit-counit) and naturality of beta
identify the left transpose with V(a) after beta inverse and the source comparison.
Tensorator naturality and unit compatibility (def-sfb-strong-monoidal-functor),
then the exchange hypothesis, give `tensorCounitCommonTranspose`.
Naturality of P' at e1, multiplied by the two specified inverses, moves e1
through the inverse projection. The mate counit equation at 1 and counit
naturality for V1 -> 1 identify the right transpose with the same arrow.
Injectivity of the inverse Hom bijection gives equality. No inverse of e1
and no evaluation functor occurs.
-/
theorem tensorCounitExchangeCalculus
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    (F' : C' ⥤ D') (G' : D' ⥤ C') (adj' : F' ⊣ G')
    (H : D ⥤ C) (H' : D' ⥤ C') (U : C ⥤ C') (V : D ⥤ D')
    [H.Monoidal] [H'.Monoidal] [U.Monoidal] [V.Monoidal]
    (θ : H ⋙ U ≅ V ⋙ H') [NatTrans.IsMonoidal θ.hom]
    (β : F ⋙ V ≅ U ⋙ F')
    (P : ∀ (K : D) (M : C), K ⊗ F.obj M ⟶ F.obj (H.obj K ⊗ M))
    (P' : ∀ (K : D') (M : C'), K ⊗ F'.obj M ⟶ F'.obj (H'.obj K ⊗ M))
    (hP : ∀ {K K' : D} {M M' : C} (f : K ⟶ K') (g : M ⟶ M'),
      (f ⊗ₘ F.map g) ≫ P K' M' = P K M ≫ F.map (H.map f ⊗ₘ g))
    (hP' : ∀ {K K' : D'} {M M' : C'} (f : K ⟶ K') (g : M ⟶ M'),
      (f ⊗ₘ F'.map g) ≫ P' K' M' = P' K M ≫ F'.map (H'.map f ⊗ₘ g))
    (K : D) [IsIso (P K (G.obj (𝟙_ D)))]
    [IsIso (P' (V.obj K) (U.obj (G.obj (𝟙_ D))))]
    [IsIso (P' (V.obj K) (G'.obj (𝟙_ D')))]
    (hEx :
      F'.map (tensorCounitSourceIso H H' U V θ K (G.obj (𝟙_ D))).hom ≫
          β.inv.app (H.obj K ⊗ G.obj (𝟙_ D)) ≫
          V.map (inv (P K (G.obj (𝟙_ D)))) ≫
          (Functor.Monoidal.μIso V K (F.obj (G.obj (𝟙_ D)))).inv ≫
          (V.obj K ◁ β.hom.app (G.obj (𝟙_ D))) =
        inv (P' (V.obj K) (U.obj (G.obj (𝟙_ D))))) :
    ((tensorCounitSourceIso H H' U V θ K (G.obj (𝟙_ D))).hom ≫
        U.map (tensorCounitTranspose adj H K (P K (G.obj (𝟙_ D)))) ≫
        (mateEquiv adj adj' β.inv).app K =
      (H'.obj (V.obj K) ◁ tensorCounitMateUnit adj adj' β) ≫
        tensorCounitTranspose adj' H' (V.obj K) (P' (V.obj K) (G'.obj (𝟙_ D')))) ∧
    ((adj'.homEquiv _ _).symm
        ((tensorCounitSourceIso H H' U V θ K (G.obj (𝟙_ D))).hom ≫
          U.map (tensorCounitTranspose adj H K (P K (G.obj (𝟙_ D)))) ≫
          (mateEquiv adj adj' β.inv).app K) =
      tensorCounitCommonTranspose adj F' H' β K
        (P' (V.obj K) (U.obj (G.obj (𝟙_ D))))) ∧
    ((adj'.homEquiv _ _).symm
        ((H'.obj (V.obj K) ◁ tensorCounitMateUnit adj adj' β) ≫
          tensorCounitTranspose adj' H' (V.obj K) (P' (V.obj K) (G'.obj (𝟙_ D')))) =
      tensorCounitCommonTranspose adj F' H' β K
        (P' (V.obj K) (U.obj (G.obj (𝟙_ D))))) := by
  have _ := @hP
  let s := (tensorCounitSourceIso H H' U V θ K (G.obj (𝟙_ D))).hom
  let t := tensorCounitTranspose adj H K (P K (G.obj (𝟙_ D)))
  let e := (mateEquiv adj adj' β.inv).app K
  let c := tensorCounitCommonTranspose adj F' H' β K
    (P' (V.obj K) (U.obj (G.obj (𝟙_ D))))
  have ht : F.map t ≫ adj.counit.app K =
      inv (P K (G.obj (𝟙_ D))) ≫
        (K ◁ adj.counit.app (𝟙_ D)) ≫ (ρ_ K).hom := by
    exact (adj.homEquiv _ _).symm_apply_apply _
  have hl : (adj'.homEquiv _ _).symm (s ≫ U.map t ≫ e) = c := by
    rw [adj'.homEquiv_counit]
    rw [tensorCounit_transport F F' U V β s t e
      (adj.counit.app K) (adj'.counit.app (V.obj K))
      (mateEquiv_counit adj adj' β.inv K), ht]
    dsimp only [c, tensorCounitCommonTranspose]
    rw [Functor.map_comp, tensorCounit_map_unit V K _ _]
    dsimp only [s] at *
    rw [← hEx]
    simp only [whiskerLeft_comp, Category.assoc]
    rw [← whiskerLeft_comp_assoc (V.obj K) (β.hom.app (G.obj (𝟙_ D)))
      (β.inv.app (G.obj (𝟙_ D))), Iso.hom_inv_id_app]
    simp only [whiskerLeft_id, Category.id_comp]
  have he1 : F'.map (tensorCounitMateUnit adj adj' β) ≫
      adj'.counit.app (𝟙_ D') =
      β.inv.app (G.obj (𝟙_ D)) ≫ V.map (adj.counit.app (𝟙_ D)) ≫
        (Functor.Monoidal.εIso V).inv := by
    simp only [tensorCounitMateUnit, Functor.map_comp, Category.assoc]
    rw [show F'.map (G'.map (Functor.Monoidal.εIso V).inv) ≫
      adj'.counit.app (𝟙_ D') = adj'.counit.app (V.obj (𝟙_ D)) ≫
        (Functor.Monoidal.εIso V).inv from
          adj'.counit_naturality (Functor.Monoidal.εIso V).inv,
      ← Category.assoc, mateEquiv_counit adj adj' β.inv (𝟙_ D)]
    rw [Category.assoc]
  have hr : (adj'.homEquiv _ _).symm
      ((H'.obj (V.obj K) ◁ tensorCounitMateUnit adj adj' β) ≫
        tensorCounitTranspose adj' H' (V.obj K)
          (P' (V.obj K) (G'.obj (𝟙_ D')))) = c := by
    rw [adj'.homEquiv_counit]
    have ht'c : F'.map (tensorCounitTranspose adj' H' (V.obj K)
        (P' (V.obj K) (G'.obj (𝟙_ D')))) ≫ adj'.counit.app (V.obj K) =
        inv (P' (V.obj K) (G'.obj (𝟙_ D'))) ≫
          (V.obj K ◁ adj'.counit.app (𝟙_ D')) ≫ (ρ_ (V.obj K)).hom :=
      (adj'.homEquiv _ _).symm_apply_apply _
    rw [tensorCounit_projection F' H' P' hP' (V.obj K)
      (tensorCounitMateUnit adj adj' β) _ _ (adj'.counit.app (𝟙_ D')) ht'c, he1]
    rfl
  exact ⟨(adj'.homEquiv _ _).symm.injective (hl.trans hr.symm), hl, hr⟩

section Restricted

variable {F : C ⥤ D} {G : D ⥤ C}
  {PC : ObjectProperty C} {PD : ObjectProperty D}
  {hF : ∀ X : C, PC X → PD (F.obj X)}
  {hG : ∀ Y : D, PD Y → PC (G.obj Y)}

/-- The ambient Hom bijection of an adjunction restricted to full subcategories.
No monoidal closure of either full subcategory is required.
Source: smooth-purity base-change factors, Proof (2), restricted Hom domains
(blueprint: lem-sp-tensor-counit-exchange-calculus). -/
def tensorCounitRestrictedHomEquiv
    (adj : PD.lift (PC.ι ⋙ F) (fun X ↦ hF X.obj X.property) ⊣
      PC.lift (PD.ι ⋙ G) (fun Y ↦ hG Y.obj Y.property))
    (X : PC.FullSubcategory) (Y : PD.FullSubcategory) :
    (F.obj X.obj ⟶ Y.obj) ≃ (X.obj ⟶ G.obj Y.obj) :=
  PD.fullyFaithfulι.homEquiv.symm.trans
    ((adj.homEquiv X Y).trans PC.fullyFaithfulι.homEquiv)

omit [MonoidalCategory C] [MonoidalCategory D] in
/-- The inverse restricted Hom bijection is the ambient functor map followed by counit. -/
private theorem tensorCounitRestrictedHomEquiv_symm
    (adj : PD.lift (PC.ι ⋙ F) (fun X ↦ hF X.obj X.property) ⊣
      PC.lift (PD.ι ⋙ G) (fun Y ↦ hG Y.obj Y.property))
    (X : PC.FullSubcategory) (Y : PD.FullSubcategory) (f : X.obj ⟶ G.obj Y.obj) :
    (tensorCounitRestrictedHomEquiv adj X Y).symm f =
      F.map f ≫ (adj.counit.app Y).hom := by
  change ((adj.homEquiv X Y).symm (ObjectProperty.homMk f)).hom = _
  rw [adj.homEquiv_counit]
  rfl

variable {F' : C' ⥤ D'} {G' : D' ⥤ C'}
  {PC' : ObjectProperty C'} {PD' : ObjectProperty D'}
  {hF' : ∀ X : C', PC' X → PD' (F'.obj X)}
  {hG' : ∀ Y : D', PD' Y → PC' (G'.obj Y)}

/-- The same calculation using adjunctions only on specified full subcategories.
The four arrows are fixed by their displayed Hom-transpose equations. Domain
membership is assumed only for objects occurring in these equations and their
naturality squares; tensor closure of the full subcategories is not assumed.

Source: smooth-purity base-change factors, Proof (2), restricted adjunctions
(blueprint: lem-sp-tensor-counit-exchange-calculus).

Proof: expand the two restricted inverse Hom bijections by their counits, as
in lem-weil-pbc-adjunction-of-natural-bijection. The defining equations for eK
and e1 give the mate counit equations (lem-amb-mate-unit-counit) at K and at 1.
Restricted Hom naturality and beta naturality give the transpose of the left
composite. Tensorator naturality, unit compatibility and hEx turn it into c.
Apply P' naturality to e1 and cancel the two specified projection isomorphisms.
Counit naturality at V1 -> 1 makes the right transpose c as well. Injectivity
of the restricted Hom bijection gives the equality. Every naturality square
has its endpoints among the explicitly listed domain objects.
-/
theorem tensorCounitExchangeCalculus_restricted
    (adj : PD.lift (PC.ι ⋙ F) (fun X ↦ hF X.obj X.property) ⊣
      PC.lift (PD.ι ⋙ G) (fun Y ↦ hG Y.obj Y.property))
    (adj' : PD'.lift (PC'.ι ⋙ F') (fun X ↦ hF' X.obj X.property) ⊣
      PC'.lift (PD'.ι ⋙ G') (fun Y ↦ hG' Y.obj Y.property))
    (H : D ⥤ C) (H' : D' ⥤ C') (U : C ⥤ C') (V : D ⥤ D')
    [H.Monoidal] [H'.Monoidal] [U.Monoidal] [V.Monoidal]
    (θ : H ⋙ U ≅ V ⋙ H') [NatTrans.IsMonoidal θ.hom]
    (β : F ⋙ V ≅ U ⋙ F')
    (P : ∀ (K : D) (M : C), K ⊗ F.obj M ⟶ F.obj (H.obj K ⊗ M))
    (P' : ∀ (K : D') (M : C'), K ⊗ F'.obj M ⟶ F'.obj (H'.obj K ⊗ M))
    (hP : ∀ {K K' : D} {M M' : C} (f : K ⟶ K') (g : M ⟶ M'),
      (f ⊗ₘ F.map g) ≫ P K' M' = P K M ≫ F.map (H.map f ⊗ₘ g))
    (hP' : ∀ {K K' : D'} {M M' : C'} (f : K ⟶ K') (g : M ⟶ M'),
      (f ⊗ₘ F'.map g) ≫ P' K' M' = P' K M ≫ F'.map (H'.map f ⊗ₘ g))
    (K : D) (hK : PD K) (h1 : PD (𝟙_ D)) (h1' : PD' (𝟙_ D'))
    (hA : PC (H.obj K ⊗ G.obj (𝟙_ D)))
    (hB : PC' (H'.obj (V.obj K) ⊗ U.obj (G.obj (𝟙_ D))))
    (hA' : PC' (H'.obj (V.obj K) ⊗ G'.obj (𝟙_ D')))
    (hUA : PC' (U.obj (H.obj K ⊗ G.obj (𝟙_ D))))
    (hUGK : PC' (U.obj (G.obj K))) (hU1 : PC' (U.obj (G.obj (𝟙_ D))))
    (hVK : PD' (V.obj K)) (hV1 : PD' (V.obj (𝟙_ D)))
    [IsIso (P K (G.obj (𝟙_ D)))]
    [IsIso (P' (V.obj K) (U.obj (G.obj (𝟙_ D))))]
    [IsIso (P' (V.obj K) (G'.obj (𝟙_ D')))]
    (hEx :
      F'.map (tensorCounitSourceIso H H' U V θ K (G.obj (𝟙_ D))).hom ≫
          β.inv.app (H.obj K ⊗ G.obj (𝟙_ D)) ≫
          V.map (inv (P K (G.obj (𝟙_ D)))) ≫
          (Functor.Monoidal.μIso V K (F.obj (G.obj (𝟙_ D)))).inv ≫
          (V.obj K ◁ β.hom.app (G.obj (𝟙_ D))) =
        inv (P' (V.obj K) (U.obj (G.obj (𝟙_ D)))))
    (t : H.obj K ⊗ G.obj (𝟙_ D) ⟶ G.obj K)
    (ht : t = tensorCounitRestrictedHomEquiv adj ⟨_, hA⟩ ⟨K, hK⟩
      (inv (P K (G.obj (𝟙_ D))) ≫
        (K ◁ (adj.counit.app ⟨𝟙_ D, h1⟩).hom) ≫ (ρ_ K).hom))
    (t' : H'.obj (V.obj K) ⊗ G'.obj (𝟙_ D') ⟶ G'.obj (V.obj K))
    (ht' : t' = tensorCounitRestrictedHomEquiv adj' ⟨_, hA'⟩ ⟨_, hVK⟩
      (inv (P' (V.obj K) (G'.obj (𝟙_ D'))) ≫
        (V.obj K ◁ (adj'.counit.app ⟨𝟙_ D', h1'⟩).hom) ≫ (ρ_ (V.obj K)).hom))
    (eK : U.obj (G.obj K) ⟶ G'.obj (V.obj K))
    (heK : eK = tensorCounitRestrictedHomEquiv adj' ⟨_, hUGK⟩ ⟨_, hVK⟩
      (β.inv.app (G.obj K) ≫ V.map (adj.counit.app ⟨K, hK⟩).hom))
    (e1 : U.obj (G.obj (𝟙_ D)) ⟶ G'.obj (𝟙_ D'))
    (he1 : e1 = tensorCounitRestrictedHomEquiv adj' ⟨_, hU1⟩ ⟨_, hV1⟩
      (β.inv.app (G.obj (𝟙_ D)) ≫ V.map (adj.counit.app ⟨𝟙_ D, h1⟩).hom) ≫
        G'.map (Functor.Monoidal.εIso V).inv) :
    ((tensorCounitSourceIso H H' U V θ K (G.obj (𝟙_ D))).hom ≫ U.map t ≫ eK =
      (H'.obj (V.obj K) ◁ e1) ≫ t') ∧
    ((tensorCounitRestrictedHomEquiv adj' ⟨_, hB⟩ ⟨_, hVK⟩).symm
        ((tensorCounitSourceIso H H' U V θ K (G.obj (𝟙_ D))).hom ≫ U.map t ≫ eK) =
      inv (P' (V.obj K) (U.obj (G.obj (𝟙_ D)))) ≫
        (V.obj K ◁ (β.inv.app (G.obj (𝟙_ D)) ≫
          V.map (adj.counit.app ⟨𝟙_ D, h1⟩).hom ≫ (Functor.Monoidal.εIso V).inv)) ≫
        (ρ_ (V.obj K)).hom) ∧
    ((tensorCounitRestrictedHomEquiv adj' ⟨_, hB⟩ ⟨_, hVK⟩).symm
        ((H'.obj (V.obj K) ◁ e1) ≫ t') =
      inv (P' (V.obj K) (U.obj (G.obj (𝟙_ D)))) ≫
        (V.obj K ◁ (β.inv.app (G.obj (𝟙_ D)) ≫
          V.map (adj.counit.app ⟨𝟙_ D, h1⟩).hom ≫ (Functor.Monoidal.εIso V).inv)) ≫
        (ρ_ (V.obj K)).hom) := by
  have _ := @hP
  have _ := hUA
  let s := (tensorCounitSourceIso H H' U V θ K (G.obj (𝟙_ D))).hom
  let c := inv (P' (V.obj K) (U.obj (G.obj (𝟙_ D)))) ≫
    (V.obj K ◁ (β.inv.app (G.obj (𝟙_ D)) ≫
      V.map (adj.counit.app ⟨𝟙_ D, h1⟩).hom ≫
      (Functor.Monoidal.εIso V).inv)) ≫ (ρ_ (V.obj K)).hom
  have htc : F.map t ≫ (adj.counit.app ⟨K, hK⟩).hom =
      inv (P K (G.obj (𝟙_ D))) ≫
        (K ◁ (adj.counit.app ⟨𝟙_ D, h1⟩).hom) ≫ (ρ_ K).hom := by
    rw [← tensorCounitRestrictedHomEquiv_symm adj ⟨_, hA⟩ ⟨K, hK⟩, ht]
    exact (tensorCounitRestrictedHomEquiv adj ⟨_, hA⟩ ⟨K, hK⟩).symm_apply_apply _
  have heKc : F'.map eK ≫ (adj'.counit.app ⟨_, hVK⟩).hom =
      β.inv.app (G.obj K) ≫ V.map (adj.counit.app ⟨K, hK⟩).hom := by
    rw [← tensorCounitRestrictedHomEquiv_symm adj' ⟨_, hUGK⟩ ⟨_, hVK⟩, heK]
    exact (tensorCounitRestrictedHomEquiv adj' ⟨_, hUGK⟩ ⟨_, hVK⟩).symm_apply_apply _
  have hl : (tensorCounitRestrictedHomEquiv adj' ⟨_, hB⟩ ⟨_, hVK⟩).symm
      (s ≫ U.map t ≫ eK) = c := by
    rw [tensorCounitRestrictedHomEquiv_symm]
    rw [tensorCounit_transport F F' U V β s t eK _ _ heKc, htc]
    dsimp only [c]
    rw [Functor.map_comp, tensorCounit_map_unit V K _ _]
    dsimp only [s] at *
    rw [← hEx]
    simp only [whiskerLeft_comp, Category.assoc]
    rw [← whiskerLeft_comp_assoc (V.obj K) (β.hom.app (G.obj (𝟙_ D)))
      (β.inv.app (G.obj (𝟙_ D))), Iso.hom_inv_id_app]
    simp only [whiskerLeft_id, Category.id_comp]
  have he1c : F'.map e1 ≫ (adj'.counit.app ⟨_, h1'⟩).hom =
      β.inv.app (G.obj (𝟙_ D)) ≫ V.map (adj.counit.app ⟨𝟙_ D, h1⟩).hom ≫
        (Functor.Monoidal.εIso V).inv := by
    have hn := congrArg (fun f ↦ f.hom) (adj'.counit.naturality
      (ObjectProperty.homMk (X := ⟨_, hV1⟩) (Y := ⟨_, h1'⟩)
        (Functor.Monoidal.εIso V).inv))
    change F'.map (G'.map (Functor.Monoidal.εIso V).inv) ≫
      (adj'.counit.app ⟨_, h1'⟩).hom =
      (adj'.counit.app ⟨_, hV1⟩).hom ≫ (Functor.Monoidal.εIso V).inv at hn
    rw [he1, Functor.map_comp, Category.assoc, hn, ← Category.assoc,
      ← tensorCounitRestrictedHomEquiv_symm adj' ⟨_, hU1⟩ ⟨_, hV1⟩,
      Equiv.symm_apply_apply]
    rw [Category.assoc]
  have ht'c : F'.map t' ≫ (adj'.counit.app ⟨_, hVK⟩).hom =
      inv (P' (V.obj K) (G'.obj (𝟙_ D'))) ≫
        (V.obj K ◁ (adj'.counit.app ⟨_, h1'⟩).hom) ≫ (ρ_ (V.obj K)).hom := by
    rw [← tensorCounitRestrictedHomEquiv_symm adj' ⟨_, hA'⟩ ⟨_, hVK⟩, ht']
    exact (tensorCounitRestrictedHomEquiv adj' ⟨_, hA'⟩ ⟨_, hVK⟩).symm_apply_apply _
  have hr : (tensorCounitRestrictedHomEquiv adj' ⟨_, hB⟩ ⟨_, hVK⟩).symm
      ((H'.obj (V.obj K) ◁ e1) ≫ t') = c := by
    rw [tensorCounitRestrictedHomEquiv_symm]
    rw [tensorCounit_projection F' H' P' hP' (V.obj K) e1 t'
      _ (adj'.counit.app ⟨_, h1'⟩).hom ht'c, he1c]
  exact ⟨(tensorCounitRestrictedHomEquiv adj' ⟨_, hB⟩ ⟨_, hVK⟩).symm.injective
    (hl.trans hr.symm), hl, hr⟩

end Restricted

end CategoryTheory
