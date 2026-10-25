/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.ProjectionCoherence
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.PoincareDuality.ProperProjectionComp
public import WeilConjectures.PoincareDuality.RefinementProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeFormalism
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek

/-!

# The projection formula of an open immersion

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace CategoryTheory.Adjunction

section Restriction

variable {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
  {Pi : C₀ ⥤ C₁} {Si : C₁ ⥤ C₀} {Pi₁ : C₀ ⥤ C₂} {Si₁ : C₂ ⥤ C₀} {Fh : C₂ ⥤ C₁}
  (bi : Pi ⊣ Si) (bi₁ : Pi₁ ⊣ Si₁) (e : Si₁ ≅ Fh ⋙ Si)

/-- The restriction comparison `i_! ⟶ h^* i₁_!` is natural. -/
@[reassoc]
lemma restrictionComparison_naturality {M M' : C₀} (φ : M ⟶ M') :
    Pi.map φ ≫ restrictionComparison bi bi₁ e M' =
      restrictionComparison bi bi₁ e M ≫ Fh.map (Pi₁.map φ) := by
  have he := e.hom.naturality (Pi₁.map φ)
  simp only [Functor.comp_map] at he
  rw [restrictionComparison, restrictionComparison, ← Pi.map_comp_assoc,
    ← bi₁.unit_naturality_assoc, he, Category.assoc, Pi.map_comp_assoc, Pi.map_comp_assoc,
    Pi.map_comp_assoc, bi.counit_naturality]

end Restriction

section RefinementProjection

variable {C₀ C₁ C₂ C₃ : Type*} [Category C₀] [Category C₁] [Category C₂] [Category C₃]
  {_ : MonoidalCategory C₀} {_ : MonoidalCategory C₁} {_ : MonoidalCategory C₂}
  {_ : MonoidalCategory C₃}
  {Pi : C₀ ⥤ C₁} {Si : C₁ ⥤ C₀} {Pi₁ : C₀ ⥤ C₂} {Si₁ : C₂ ⥤ C₀} {Fh : C₂ ⥤ C₁} {Gh : C₁ ⥤ C₂}
  {Fp₁ : C₃ ⥤ C₂} {Gp₁ : C₂ ⥤ C₃} {Fp : C₃ ⥤ C₁} {Gp : C₁ ⥤ C₃} {Ff : C₃ ⥤ C₀}
  {_ : Si.LaxMonoidal} {_ : Si₁.LaxMonoidal} {_ : Fh.Monoidal} {_ : Fp₁.OplaxMonoidal}
  {_ : Fp.OplaxMonoidal}
  (bi : Pi ⊣ Si) (bi₁ : Pi₁ ⊣ Si₁) (ah : Fh ⊣ Gh) (ap₁ : Fp₁ ⊣ Gp₁) (ap : Fp ⊣ Gp)
  (e : Si₁ ≅ Fh ⋙ Si)

open Functor.LaxMonoidal in
/-- **The exceptional projection morphism is compatible with refinements of compactifications**,
for abstract functors: for compactifications `X ⟶[i] Z ⟶[p] Y` and `X ⟶[i₁] Z₁ ⟶[p₁] Y` and a
refinement `h : Z ⟶ Z₁` with `i ≫ h = i₁` and `h ≫ p₁ = p`, the exceptional projection
morphisms `p_* (q_i⁻¹) ∘ PF^*_p` and `p₁_* (q_{i₁}⁻¹) ∘ PF^*_{p₁}` are intertwined by the
comparison `p₁_* i₁_! ⟶ p₁_* h_* i_! ≅ p_* i_!` (the unit of `h^* ⊣ h_*` followed by the inverse
of the restriction comparison and the conjugate of `cp : p^* ≅ p₁^* ⋙ h^*`). -/
lemma projectionMorphism_comp_refinement
    [∀ M, IsIso (restrictionComparison bi bi₁ e M)]
    [∀ M N, IsIso (bi.projectionComparison M N)] [∀ M N, IsIso (bi₁.projectionComparison M N)]
    (he : ∀ X Y, μ Si₁ X Y ≫ e.hom.app (X ⊗ Y) =
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫ μ (Fh ⋙ Si) X Y)
    (cp : Fp ≅ Fp₁ ⋙ Fh)
    (hcp : ∀ X Y, δ Fp X Y ≫ (cp.hom.app X ⊗ₘ cp.hom.app Y) =
      cp.hom.app (X ⊗ Y) ≫ δ (Fp₁ ⋙ Fh) X Y)
    (ec : Ff ≅ Fp ⋙ Si) (ec₁ : Ff ≅ Fp₁ ⋙ Si₁)
    (hec : ∀ B, e.hom.app (Fp₁.obj B) ≫ Si.map (cp.inv.app B) ≫ ec.inv.app B = ec₁.inv.app B)
    (K : C₀) (B : C₃) :
    (ap₁.projectionMorphism (Pi₁.obj K) B ≫
        Gp₁.map (inv (bi₁.projectionComparison K (Fp₁.obj B)) ≫
          Pi₁.map (K ◁ ec₁.inv.app B))) ≫
      Gp₁.map (ah.unit.app (Pi₁.obj (K ⊗ Ff.obj B)) ≫
          Gh.map (inv (restrictionComparison bi bi₁ e (K ⊗ Ff.obj B)))) ≫
        (conjugateIsoEquiv ap (ap₁.comp ah) cp.symm).symm.hom.app (Pi.obj (K ⊗ Ff.obj B)) =
    (Gp₁.map (ah.unit.app (Pi₁.obj K) ≫ Gh.map (inv (restrictionComparison bi bi₁ e K))) ≫
        (conjugateIsoEquiv ap (ap₁.comp ah) cp.symm).symm.hom.app (Pi.obj K)) ▷ B ≫
      ap.projectionMorphism (Pi.obj K) B ≫
        Gp.map (inv (bi.projectionComparison K (Fp.obj B)) ≫ Pi.map (K ◁ ec.inv.app B)) := by
  have hconj : (conjugateIsoEquiv ap (ap₁.comp ah) cp.symm).symm =
      conjugateIsoEquiv (ap₁.comp ah) ap cp := Iso.ext rfl
  rw [hconj]
  set θ : ∀ M, Pi₁.obj M ⟶ Gh.obj (Pi.obj M) := fun M ↦
    ah.unit.app (Pi₁.obj M) ≫ Gh.map (inv (restrictionComparison bi bi₁ e M)) with hθ
  have hθ' (M : C₀) : ah.unit.app (Pi₁.obj M) ≫ Gh.map (inv (restrictionComparison bi bi₁ e M)) =
      θ M := rfl
  have hθnat {M M' : C₀} (φ : M ⟶ M') : Pi₁.map φ ≫ θ M' = θ M ≫ Gh.map (Pi.map φ) := by
    have h1 := restrictionComparison_naturality bi bi₁ e φ
    have h2 : inv (restrictionComparison bi bi₁ e M) ≫ Pi.map φ =
        Fh.map (Pi₁.map φ) ≫ inv (restrictionComparison bi bi₁ e M') := by
      rw [IsIso.inv_comp_eq, ← reassoc_of% h1, IsIso.hom_inv_id, Category.comp_id]
    simp only [hθ]
    rw [← ah.unit_naturality_assoc, ← Gh.map_comp, ← h2, Gh.map_comp]
    simp only [Category.assoc]
  have hq : bi₁.projectionComparison K (Fp₁.obj B) ≫ θ K ▷ Fp₁.obj B ≫
      ah.projectionMorphism (Pi.obj K) (Fp₁.obj B) =
      θ (K ⊗ Si₁.obj (Fp₁.obj B)) ≫ Gh.map (Pi.map (K ◁ e.hom.app (Fp₁.obj B)) ≫
        bi.projectionComparison K (Fh.obj (Fp₁.obj B))) :=
    projectionComparison_comp_refinement bi bi₁ e ah he K (Fp₁.obj B)
  have hq' : θ K ▷ Fp₁.obj B ≫ ah.projectionMorphism (Pi.obj K) (Fp₁.obj B) =
      inv (bi₁.projectionComparison K (Fp₁.obj B)) ≫ θ (K ⊗ Si₁.obj (Fp₁.obj B)) ≫
        Gh.map (Pi.map (K ◁ e.hom.app (Fp₁.obj B)) ≫
          bi.projectionComparison K (Fh.obj (Fp₁.obj B))) := by
    rw [IsIso.eq_inv_comp, hq]
  have hkey : Pi.map (K ◁ e.hom.app (Fp₁.obj B)) ≫
      bi.projectionComparison K (Fh.obj (Fp₁.obj B)) ≫ Pi.obj K ◁ cp.inv.app B ≫
        inv (bi.projectionComparison K (Fp.obj B)) ≫ Pi.map (K ◁ ec.inv.app B) =
      Pi.map (K ◁ ec₁.inv.app B) := by
    have hn := bi.projectionComparison_natural_right K (cp.inv.app B)
    rw [← reassoc_of% hn, IsIso.hom_inv_id_assoc, ← Pi.map_comp_assoc, ← Pi.map_comp,
      ← whiskerLeft_comp, ← whiskerLeft_comp, Category.assoc, hec]
  rw [projectionMorphism_eq_of_iso ap (ap₁.comp ah) cp hcp, projectionMorphism_comp]
  simp only [Category.assoc]
  rw [← comp_whiskerRight_assoc, Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  rw [hθ' K,
    ap₁.projectionMorphism_natural_left_assoc, ← Gp₁.map_comp_assoc (θ K ▷ Fp₁.obj B), hq', hθ' (K ⊗ Ff.obj B)]
  have hc := (conjugateIsoEquiv (ap₁.comp ah) ap cp).hom.naturality
    (Pi.map (K ◁ e.hom.app (Fp₁.obj B)) ≫ bi.projectionComparison K (Fh.obj (Fp₁.obj B)))
  have hc' := (conjugateIsoEquiv (ap₁.comp ah) ap cp).hom.naturality
    (Pi.map (K ◁ ec₁.inv.app B))
  simp only [Functor.comp_map, Functor.comp_obj] at hc hc' ⊢
  simp only [Gp₁.map_comp, Category.assoc]
  rw [reassoc_of% hc, ← Gp₁.map_comp_assoc (Pi₁.map _), hθnat, Gp₁.map_comp_assoc,
    hc', ← hkey]
  simp only [Gp.map_comp, Category.assoc]
  rfl

end RefinementProjection

section Identity

variable {C₀ C₁ : Type*} [Category C₀] [Category C₁] [MonoidalCategory C₀] [MonoidalCategory C₁]
  {Pf : C₀ ⥤ C₁} {Sf : C₁ ⥤ C₀} {F₁ G₁ : C₁ ⥤ C₁} [Sf.LaxMonoidal] [F₁.OplaxMonoidal]
  (bf : Pf ⊣ Sf) (a₁ : F₁ ⊣ G₁)

/-- The projection morphism of `Adjunction.id` is the identity. -/
lemma id_projectionMorphism (A B : C₁) :
    (Adjunction.id (C := C₁)).projectionMorphism A B = 𝟙 (A ⊗ B) := by
  rw [projectionMorphism, Adjunction.homEquiv_unit]
  simp

/-- **The exceptional projection morphism of the trivial compactification**, for abstract
functors: for an open immersion `f` compactified by `X ⟶[f] Y ⟶[𝟙] Y`, through
`u : (𝟙 Y)^* ≅ 𝟭` and its conjugate `(𝟙 Y)_* ≅ 𝟭`, the exceptional projection morphism
`(𝟙 Y)_* (q_f⁻¹) ∘ PF^*_{𝟙 Y}` is the inverse of the projection comparison `q_f`. -/
lemma projectionMorphism_comp_projectionComparison_of_iso_id
    [∀ M N, IsIso (bf.projectionComparison M N)] (u : F₁ ≅ 𝟭 C₁)
    (hu : ∀ X Y, δ F₁ X Y ≫ (u.hom.app X ⊗ₘ u.hom.app Y) = u.hom.app (X ⊗ Y))
    (ec : Sf ≅ F₁ ⋙ Sf) (hec : ∀ B, ec.hom.app B ≫ Sf.map (u.hom.app B) = 𝟙 _) (K : C₀)
    (B : C₁) :
    (a₁.projectionMorphism (Pf.obj K) B ≫
        G₁.map (inv (bf.projectionComparison K (F₁.obj B)) ≫ Pf.map (K ◁ ec.inv.app B))) ≫
      (conjugateIsoEquiv a₁ Adjunction.id u.symm).hom.app (Pf.obj (K ⊗ Sf.obj B)) ≫
        bf.projectionComparison K B =
    (conjugateIsoEquiv a₁ Adjunction.id u.symm).hom.app (Pf.obj K) ▷ B := by
  have hl : conjugateIsoEquiv Adjunction.id a₁ u =
      (conjugateIsoEquiv a₁ Adjunction.id u.symm).symm := Iso.ext rfl
  have hec' : Sf.map (u.inv.app B) ≫ ec.inv.app B = 𝟙 _ := by
    have h1 : ec.inv.app B = Sf.map (u.hom.app B) := by
      rw [← cancel_epi (ec.hom.app B), Iso.hom_inv_id_app, hec]
    rw [h1, ← Sf.map_comp, Iso.inv_hom_id_app]
    simp
  have hn := bf.inv_projectionComparison_natural_right K (u.inv.app B)
  set l := conjugateIsoEquiv a₁ Adjunction.id u.symm
  rw [projectionMorphism_eq_of_iso a₁ Adjunction.id u (fun X Y ↦ by simpa using hu X Y), hl,
    id_projectionMorphism]
  have hln {X Y : C₁} (x : X ⟶ Y) : G₁.map x ≫ l.hom.app Y = l.hom.app X ≫ x :=
    l.hom.naturality x
  simp only [Iso.symm_inv, Iso.symm_hom, Category.assoc, ← G₁.map_comp_assoc]
  rw [reassoc_of% hn, ← Pf.map_comp, ← whiskerLeft_comp, hec']
  erw [MonoidalCategory.whiskerLeft_id, Pf.map_id, Category.comp_id]
  rw [reassoc_of% (hln (inv (bf.projectionComparison K B)))]
  simp

end Identity

end CategoryTheory.Adjunction

namespace CategoryTheory.ObjectProperty

/-- A composite `pm ≫ G' (iq ≫ I' (K ◁ e))` of morphisms between objects of full monoidal
subcategories, with `G'` and `I'` the restrictions of functors `G` and `I`, is computed in the
ambient categories. -/
lemma homMk_comp_lift_map_comp_lift_map {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂]
    [Category C₃] {_ : MonoidalCategory C₁} {P₁ : ObjectProperty C₁} {P₂ : ObjectProperty C₂}
    {P₃ : ObjectProperty C₃} {_ : P₁.IsMonoidal} (I : C₁ ⥤ C₂)
    (hI : ∀ X : P₁.FullSubcategory, P₂ (I.obj X.obj)) (G : C₂ ⥤ C₃)
    (hG : ∀ X : P₂.FullSubcategory, P₃ (G.obj X.obj)) {W : P₃.FullSubcategory}
    {V : P₂.FullSubcategory} {K M₁ M₂ : P₁.FullSubcategory}
    (pm : W ⟶ (P₃.lift (P₂.ι ⋙ G) hG).obj V)
    (iq : V ⟶ (P₂.lift (P₁.ι ⋙ I) hI).obj (K ⊗ M₁)) (e : M₁ ⟶ M₂)
    (a : W.obj ⟶ G.obj V.obj) (ha : pm.hom = a) (b : V.obj ⟶ I.obj (K.obj ⊗ M₁.obj))
    (hb : iq.hom = b) (c : M₁.obj ⟶ M₂.obj) (hc : e.hom = c) :
    homMk (Y := (P₃.lift (P₂.ι ⋙ G) hG).obj ((P₂.lift (P₁.ι ⋙ I) hI).obj (K ⊗ M₂)))
        (a ≫ G.map (b ≫ I.map (K.obj ◁ c))) =
      pm ≫ (P₃.lift (P₂.ι ⋙ G) hG).map (iq ≫ (P₂.lift (P₁.ι ⋙ I) hI).map (K ◁ e)) := by
  subst ha hb hc
  rfl

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

open scoped CategoryTheory.Functor CategoryTheory.Obj

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] [IsEllAdicFinitenessCoefficient ℓ Λ] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

-- the tensor products of bounded constructible complexes are elaborated through the projection of
-- the monoidal category instance, as in the abstract lemmas (see the implementation notes of
-- `WeilConjectures.TraceFormula.KunnethVerdierOpen`)
attribute [local instance 2000] MonoidalCategory.toMonoidalCategoryStruct

section Bridge

variable {X Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom]

omit [IsEllAdicFinitenessCoefficient ℓ Λ] in
variable [IsFinitenessCoefficient ℓ Λ] in
@[simp]
lemma boundedConstructibleLowerStar_map_hom (p : Z ⟶ Y) {A A' : Dᵇc(Z.left)⟦Λ⟧} (φ : A ⟶ A') :
    ((boundedConstructibleLowerStar Λ ℓ p).map φ).hom = (R((p.left)_*⟦Λ⟧)).map φ.hom :=
  rfl

omit [IsEllAdicFinitenessCoefficient ℓ Λ] in
@[simp]
lemma boundedConstructibleOpenImmersionLowerShriek_map_hom (i : X ⟶ Z) [IsOpenImmersion i.left]
    {K K' : Dᵇc(X.left)⟦Λ⟧} (φ : K ⟶ K') :
    ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i).map φ).hom =
      (D((i.left)_!open⟦Λ⟧)).map φ.hom :=
  rfl

lemma μ_boundedConstructibleUpperStar_hom (p : Z ⟶ Y) (K M : Dᵇc(Y.left)⟦Λ⟧) :
    (Functor.LaxMonoidal.μ (boundedConstructibleUpperStar Λ ℓ p) K M).hom =
      Functor.LaxMonoidal.μ L((p.left)^*⟦Λ⟧) K.obj M.obj :=
  rfl

omit [IsEllAdicFinitenessCoefficient ℓ Λ] in
variable [IsFinitenessCoefficient ℓ Λ] in
/-- The unit of `Lp^* ⊣ Rp_*` on bounded constructible complexes is the derived unit. -/
lemma boundedConstructibleUpperStarLowerStarAdjunction_unit_app_hom (p : Z ⟶ Y)
    (B : Dᵇc(Y.left)⟦Λ⟧) :
    ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p).unit.app B).hom =
      (derivedUpperStarLowerStarAdjunction Λ p.left).unit.app B.obj := by
  have := Adjunction.map_restrictFullyFaithful_unit_app (derivedUpperStarLowerStarAdjunction Λ p.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility Λ ℓ p).symm
    (boundedConstructibleLowerStarCompatibility Λ ℓ p).symm B
  refine this.trans ?_
  simp [boundedConstructibleUpperStarCompatibility, boundedConstructibleLowerStarCompatibility,
    ObjectProperty.liftCompιIso]

omit [IsEllAdicFinitenessCoefficient ℓ Λ] in
variable [IsFinitenessCoefficient ℓ Λ] in
/-- The counit of `Lp^* ⊣ Rp_*` on bounded constructible complexes is the derived counit. -/
lemma boundedConstructibleUpperStarLowerStarAdjunction_counit_app_hom (p : Z ⟶ Y)
    (A : Dᵇc(Z.left)⟦Λ⟧) :
    ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p).counit.app A).hom =
      (derivedUpperStarLowerStarAdjunction Λ p.left).counit.app A.obj := by
  have := Adjunction.map_restrictFullyFaithful_counit_app
    (derivedUpperStarLowerStarAdjunction Λ p.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility Λ ℓ p).symm
    (boundedConstructibleLowerStarCompatibility Λ ℓ p).symm A
  refine this.trans ?_
  simp [boundedConstructibleUpperStarCompatibility, boundedConstructibleLowerStarCompatibility,
    ObjectProperty.liftCompιIso]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

omit [IsEllAdicFinitenessCoefficient ℓ Λ] in
/-- The unit of `i_! ⊣ Li^*` on bounded constructible complexes is the derived unit. -/
lemma boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_unit_app_hom (i : X ⟶ Z)
    [IsOpenImmersion i.left] (K : Dᵇc(X.left)⟦Λ⟧) :
    ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i).unit.app K).hom =
      (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ i.left).unit.app K.obj := by
  have := Adjunction.map_restrictFullyFaithful_unit_app
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i.left).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ i.left).symm)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ i).symm
    (boundedConstructibleUpperStarCompatibility Λ ℓ i).symm K
  refine this.trans ?_
  simp [boundedConstructibleUpperStarCompatibility,
    boundedConstructibleOpenImmersionLowerShriekCompatibility, ObjectProperty.liftCompιIso]
  rfl

omit [IsEllAdicFinitenessCoefficient ℓ Λ] in
/-- The counit of `i_! ⊣ Li^*` on bounded constructible complexes is the derived counit. -/
lemma boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_counit_app_hom
    (i : X ⟶ Z) [IsOpenImmersion i.left] (N : Dᵇc(Z.left)⟦Λ⟧) :
    ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i).counit.app N).hom =
      (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ i.left).counit.app
        N.obj := by
  have := Adjunction.map_restrictFullyFaithful_counit_app
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i.left).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ i.left).symm)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ i).symm
    (boundedConstructibleUpperStarCompatibility Λ ℓ i).symm N
  refine this.trans ?_
  simp only [boundedConstructibleUpperStarCompatibility,
    boundedConstructibleOpenImmersionLowerShriekCompatibility, ObjectProperty.liftCompιIso,
    Iso.refl_symm, Iso.refl_inv, NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  rfl

/-- The projection morphism of `Lp^* ⊣ Rp_*` on bounded constructible complexes is the derived
projection morphism `properProjectionMorphism`. -/
lemma boundedConstructibleUpperStarLowerStarAdjunction_projectionMorphism_hom (p : Z ⟶ Y)
    (A : Dᵇc(Z.left)⟦Λ⟧) (B : Dᵇc(Y.left)⟦Λ⟧) :
    ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p).projectionMorphism A B).hom =
      properProjectionMorphism Λ p.left A.obj B.obj := by
  rw [Adjunction.projectionMorphism, Adjunction.homEquiv_unit, properProjectionMorphism,
    Adjunction.projectionMorphism, Adjunction.homEquiv_unit]
  simp [boundedConstructibleUpperStarLowerStarAdjunction_unit_app_hom,
    boundedConstructibleUpperStarLowerStarAdjunction_counit_app_hom, δ_boundedConstructibleUpperStar_hom,
    δ_leftDerivedUpperStar]
  rfl

/-- The projection comparison of `i_! ⊣ Li^*` on bounded constructible complexes is the derived
projection comparison `openImmersionProjectionComparison`. -/
lemma boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_projectionComparison_hom
    (i : X ⟶ Z) [IsOpenImmersion i.left] (K : Dᵇc(X.left)⟦Λ⟧) (N : Dᵇc(Z.left)⟦Λ⟧) :
    ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i).projectionComparison
      K N).hom = openImmersionProjectionComparison Λ i.left K.obj N.obj := by
  rw [Adjunction.projectionComparison, Adjunction.homEquiv_counit, openImmersionProjectionComparison,
    Adjunction.projectionComparison, Adjunction.homEquiv_counit]
  simp [boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_unit_app_hom,
    boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_counit_app_hom,
    μ_boundedConstructibleUpperStar_hom]
  rfl

/-- The projection comparison of `i_! ⊣ Li^*` on bounded constructible complexes is an
isomorphism, as on the ambient derived categories (`isIso_openImmersionProjectionComparison`). -/
instance isIso_boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_projectionComparison
    (i : X ⟶ Z) [IsOpenImmersion i.left] (K : Dᵇc(X.left)⟦Λ⟧) (N : Dᵇc(Z.left)⟦Λ⟧) :
    IsIso ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i).projectionComparison
      K N) := by
  have : IsIso ((boundedConstructible _).ι.map
      ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i).projectionComparison
        K N)) := by
    rw [ObjectProperty.ι_map,
      boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_projectionComparison_hom]
    infer_instance
  exact isIso_of_reflects_iso _ (boundedConstructible _).ι

end Bridge

section Factorization

variable {X Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom]

/-- The exceptional projection morphism `PF^!_{f,K,B} : p_* i_! K ⊗ B ⟶ p_* i_! (K ⊗ Lf^* B)` of
a factorization `f = i ≫ p` with `i` an open immersion, on bounded constructible complexes: the
projection morphism of `Lp^* ⊣ Rp_*`, the inverse of the projection comparison of `i_! ⊣ Li^*`,
and the identification `Li^* Lp^* B ≅ Lf^* B`. -/
noncomputable def boundedConstructibleExceptionalProjectionMorphismOfFactorization (i : X ⟶ Z)
    [IsOpenImmersion i.left] (p : Z ⟶ Y) {f : X ⟶ Y} (w : i ≫ p = f) (K : Dᵇc(X.left)⟦Λ⟧)
    (B : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructibleLowerStar Λ ℓ p).obj
        ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i).obj K) ⊗ B ⟶
      (boundedConstructibleLowerStar Λ ℓ p).obj
        ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i).obj
          (K ⊗ (boundedConstructibleUpperStar Λ ℓ f).obj B)) :=
  (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p).projectionMorphism _ B ≫
    (boundedConstructibleLowerStar Λ ℓ p).map
      (inv ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i).projectionComparison
          K ((boundedConstructibleUpperStar Λ ℓ p).obj B)) ≫
        (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i).map
          (K ◁ (eqToIso (congrArg (boundedConstructibleUpperStar Λ ℓ) w.symm) ≪≫
            boundedConstructibleUpperStarComp Λ ℓ i p).inv.app B))

/-- Whiskering on the left of bounded constructible complexes is computed in the derived
category. -/
lemma whiskerLeft_hom_boundedConstructible (K : Dᵇc(X.left)⟦Λ⟧) {M N : Dᵇc(X.left)⟦Λ⟧}
    (g : M ⟶ N) : (K ◁ g).hom = K.obj ◁ g.hom :=
  rfl

/-- On the ambient derived category, the inverse of the composition isomorphism
`Lf^* ≅ L(c.overI ≫ c.overG)^* ≅ Lc.overG^* ⋙ Lc.overI^*` of a compactification `c` is that of
`leftDerivedUpperStarCompactificationIso`. -/
lemma boundedConstructibleUpperStarComp_overI_overG_inv_app_hom {f : X ⟶ Y}
    (c : Compactification f.left) (B : Dᵇc(Y.left)⟦Λ⟧) :
    ((eqToIso (congrArg (boundedConstructibleUpperStar Λ ℓ) c.overI_overG.symm) ≪≫
      boundedConstructibleUpperStarComp Λ ℓ c.overI c.overG).inv.app B).hom =
      (leftDerivedUpperStarCompactificationIso Λ c).inv.app B.obj := by
  have hc : ((boundedConstructibleUpperStarComp Λ ℓ c.overI c.overG).inv.app B).hom =
      (leftDerivedUpperStarComp Λ c.i c.g).inv.app B.obj := by
    simp [boundedConstructibleUpperStarComp, boundedConstructibleUpperStarCompatibility,
      ObjectProperty.liftCompιIso]
  rw [Iso.trans_inv, NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom, hc]
  clear hc
  obtain ⟨fl, fr, fw⟩ := f
  cases c with
  | mk Z g i comm hg hi =>
  cases comm
  simp only [leftDerivedUpperStarCompactificationIso, eqToIso_refl, Iso.refl_trans, Iso.refl_inv,
    NatTrans.id_app, ObjectProperty.FullSubcategory.id_hom]
  exact Category.comp_id _

set_option maxHeartbeats 1000000 in
-- unfolding the bounded constructible functors to the derived ones
/-- The exceptional projection morphism of a compactification `c`, restricted to bounded
constructible complexes, is the exceptional projection morphism of the factorization
`f = c.overI ≫ c.overG`. -/
lemma homMk_exceptionalProjectionMorphismOfCompactification {f : X ⟶ Y}
    (c : Compactification f.left) (K : Dᵇc(X.left)⟦Λ⟧) (B : Dᵇc(Y.left)⟦Λ⟧) :
    ObjectProperty.homMk
        (X := (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).obj K ⊗ B)
        (Y := (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).obj
          (K ⊗ (boundedConstructibleUpperStar Λ ℓ f).obj B))
        (exceptionalProjectionMorphismOfCompactification Λ c K.obj B.obj) =
      boundedConstructibleExceptionalProjectionMorphismOfFactorization Λ ℓ c.overI c.overG
        c.overI_overG K B := by
  have he := boundedConstructibleUpperStarComp_overI_overG_inv_app_hom Λ ℓ c B
  have hinv : inv ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ
      c.overI).projectionComparison K ((boundedConstructibleUpperStar Λ ℓ c.overG).obj B)).hom =
      inv (openImmersionProjectionComparison Λ c.i K.obj (L((c.g)^*⟦Λ⟧).obj B.obj)) :=
    IsIso.inv_eq_of_hom_inv_id (by
      rw [boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_projectionComparison_hom]
      exact IsIso.hom_inv_id _)
  have h3 : ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ c.overI).map
      (K ◁ (eqToIso (congrArg (boundedConstructibleUpperStar Λ ℓ) c.overI_overG.symm) ≪≫
        boundedConstructibleUpperStarComp Λ ℓ c.overI c.overG).inv.app B)).hom =
      D((c.i)_!open⟦Λ⟧).map (K.obj ◁ (leftDerivedUpperStarCompactificationIso Λ c).inv.app B.obj) := by
    rw [← he]
    rfl
  obtain ⟨fl, fr, fw⟩ := f
  cases c with
  | mk Z g i comm hg hi =>
  cases comm
  refine ObjectProperty.hom_ext (P := boundedConstructible _) ?_
  unfold boundedConstructibleExceptionalProjectionMorphismOfFactorization
    exceptionalProjectionMorphismOfCompactification
  simp only [ObjectProperty.homMk_hom, ObjectProperty.FullSubcategory.comp_hom,
    boundedConstructibleUpperStarLowerStarAdjunction_projectionMorphism_hom,
    boundedConstructibleLowerStar_map_hom, ObjectProperty.hom_inv, hinv, h3]
  rfl


end Factorization
section MonoidalComp

variable {W₁ W₂ W₃ : Over (Spec (.of k))}
  [LocallyOfFiniteType W₁.hom] [QuasiCompact W₁.hom] [IsSeparated W₁.hom]
  [LocallyOfFiniteType W₂.hom] [QuasiCompact W₂.hom] [IsSeparated W₂.hom]
  [LocallyOfFiniteType W₃.hom] [QuasiCompact W₃.hom] [IsSeparated W₃.hom]

/-- `boundedConstructibleUpperStarComp_hom_app_tensor_δ`, for the tensor products elaborated
through the monoidal category instance, with the comultiplication of the composite. -/
lemma boundedConstructibleUpperStarComp_hom_app_tensor_δ' (a : W₁ ⟶ W₂) (b : W₂ ⟶ W₃)
    (K M : Dᵇc(W₃.left)⟦Λ⟧) :
    δ (boundedConstructibleUpperStar Λ ℓ (a ≫ b)) K M ≫
        ((boundedConstructibleUpperStarComp Λ ℓ a b).hom.app K ⊗ₘ
          (boundedConstructibleUpperStarComp Λ ℓ a b).hom.app M) =
      (boundedConstructibleUpperStarComp Λ ℓ a b).hom.app (K ⊗ M) ≫
        δ (boundedConstructibleUpperStar Λ ℓ b ⋙ boundedConstructibleUpperStar Λ ℓ a) K M := by
  refine ObjectProperty.hom_ext (P := boundedConstructible _) ?_
  have key := congrArg InducedCategory.Hom.hom
    (boundedConstructibleUpperStarComp_hom_app_tensor_δ Λ ℓ a b K M)
  rw [Functor.OplaxMonoidal.comp_δ]
  exact key

end MonoidalComp

section Refinement

variable {X Z Z₁ Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
  [IsSeparated Z₁.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {i : X ⟶ Z} {i₁ : X ⟶ Z₁} {h : Z ⟶ Z₁} [IsOpenImmersion i.left] [IsOpenImmersion i₁.left]

omit [IsEllAdicFinitenessCoefficient ℓ Λ] in
/-- The restriction comparison of a refinement is an isomorphism. -/
lemma isIso_restrictionComparison_of_isPullback (sq : IsPullback (𝟙 X) i i₁ h)
    (M : Dᵇc(X.left)⟦Λ⟧) :
    IsIso (Adjunction.restrictionComparison
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i)
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i₁)
      (boundedConstructibleUpperStarTriangleComparison Λ ℓ sq.toCommSq.snd_comp_eq_of_fst_eq_id)
      M) := by
  rw [← boundedConstructibleOpenImmersionLowerShriekRefinement_app]
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ sq
  infer_instance

omit [IsEllAdicFinitenessCoefficient ℓ Λ] in
variable [IsFinitenessCoefficient ℓ Λ] in
/-- The comparison `i₁_! ⋙ Rp₁_* ≅ i_! ⋙ Rp_*` along a refinement, in terms of the unit of
`Lh^* ⊣ Rh_*` and the inverse of the abstract restriction comparison. -/
lemma boundedConstructibleLowerShriekRefinementIso_hom_app (sq : IsPullback (𝟙 X) i i₁ h)
    {p₁ : Z₁ ⟶ Y} (K : Dᵇc(X.left)⟦Λ⟧)
    [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward Λ ℓ sq)] :
    haveI := isIso_restrictionComparison_of_isPullback Λ ℓ sq
    (boundedConstructibleLowerShriekRefinementIso Λ ℓ sq (rfl : h ≫ p₁ = h ≫ p₁)).hom.app K =
      (boundedConstructibleLowerStar Λ ℓ p₁).map
        ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ h).unit.app
            ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K) ≫
          (boundedConstructibleLowerStar Λ ℓ h).map (inv (Adjunction.restrictionComparison
            (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i)
            (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i₁)
            (boundedConstructibleUpperStarTriangleComparison Λ ℓ
              sq.toCommSq.snd_comp_eq_of_fst_eq_id) K))) ≫
        (boundedConstructibleLowerStarComp Λ ℓ h p₁).hom.app _ := by
  simp only [boundedConstructibleLowerShriekRefinementIso,
    boundedConstructibleOpenImmersionLowerShriekRefinementPushforward, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, asIso_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, eqToIso_refl, Iso.refl_hom,
    Category.id_comp, Category.comp_id, Functor.map_comp, NatIso.isIso_inv_app,
    boundedConstructibleOpenImmersionLowerShriekRefinement_app, Functor.map_id, Category.assoc]

omit [IsEllAdicFinitenessCoefficient ℓ Λ] [IsOpenImmersion i₁.left] in
/-- The cocycle condition for the composition isomorphisms of the pullbacks along
`X ⟶[i] Z ⟶[h] Z₁ ⟶[p₁] Y`, in the form used by the compatibility of the exceptional
projection morphism with refinements. -/
lemma boundedConstructibleUpperStarComp_refinement_cocycle (h : Z ⟶ Z₁) (p₁ : Z₁ ⟶ Y)
    {f : X ⟶ Y} (w : i ≫ h ≫ p₁ = f) (w₁ : (i ≫ h) ≫ p₁ = f) (hw : i ≫ h = i ≫ h)
    (B : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructibleUpperStarTriangleComparison Λ ℓ hw).hom.app
        ((boundedConstructibleUpperStar Λ ℓ p₁).obj B) ≫
      (boundedConstructibleUpperStar Λ ℓ i).map
        ((boundedConstructibleUpperStarComp Λ ℓ h p₁).inv.app B) ≫
      (eqToIso (congrArg (boundedConstructibleUpperStar Λ ℓ) w.symm) ≪≫
        boundedConstructibleUpperStarComp Λ ℓ i (h ≫ p₁)).inv.app B =
    (eqToIso (congrArg (boundedConstructibleUpperStar Λ ℓ) w₁.symm) ≪≫
      boundedConstructibleUpperStarComp Λ ℓ (i ≫ h) p₁).inv.app B := by
  subst w
  have ha := boundedConstructibleUpperStarComp_assoc_app Λ ℓ i h p₁ B
  simp only [boundedConstructibleUpperStarTriangleComparison, Iso.trans_hom, Iso.trans_inv,
    eqToIso_refl, Iso.refl_hom, Iso.refl_inv, NatTrans.comp_app, NatTrans.id_app,
    Category.id_comp, Category.comp_id, eqToHom_app]
  rw [← cancel_epi ((boundedConstructibleUpperStarComp Λ ℓ (i ≫ h) p₁).hom.app B),
    Iso.hom_inv_id_app_assoc, reassoc_of% ha]
  simp [← Functor.map_comp_assoc]
  rfl

omit [IsOpenImmersion i.left] [IsOpenImmersion i₁.left] in
open Functor.LaxMonoidal in
/-- The triangle comparison `Li₁^* ≅ Lh^* ⋙ Li^*` is compatible with the multiplications. -/
lemma boundedConstructibleUpperStarTriangleComparison_μ' (w : i ≫ h = i₁) (K M : Dᵇc(Z₁.left)⟦Λ⟧) :
    μ (boundedConstructibleUpperStar Λ ℓ i₁) K M ≫
        (boundedConstructibleUpperStarTriangleComparison Λ ℓ w).hom.app (K ⊗ M) =
      ((boundedConstructibleUpperStarTriangleComparison Λ ℓ w).hom.app K ⊗ₘ
          (boundedConstructibleUpperStarTriangleComparison Λ ℓ w).hom.app M) ≫
        μ (boundedConstructibleUpperStar Λ ℓ h ⋙ boundedConstructibleUpperStar Λ ℓ i) K M := by
  subst w
  refine Adjunction.μ_comp_hom_app_eq_of_δ _ (fun K M ↦ ?_) K M
  simp only [boundedConstructibleUpperStarTriangleComparison, Iso.trans_hom, eqToIso_refl,
    Iso.refl_hom, Category.id_comp]
  exact boundedConstructibleUpperStarComp_hom_app_tensor_δ' Λ ℓ i h K M

omit [IsEllAdicFinitenessCoefficient ℓ Λ] [IsOpenImmersion i.left] [IsOpenImmersion i₁.left] in
variable [IsFinitenessCoefficient ℓ Λ] in
/-- `boundedConstructibleLowerStarComp`, unfolded. -/
lemma boundedConstructibleLowerStarComp_eq_conjugateIsoEquiv (h : Z ⟶ Z₁) (p₁ : Z₁ ⟶ Y) :
    boundedConstructibleLowerStarComp Λ ℓ h p₁ =
      (conjugateIsoEquiv (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ (h ≫ p₁))
        ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p₁).comp
          (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ h))
        (boundedConstructibleUpperStarComp Λ ℓ h p₁).symm).symm :=
  rfl

set_option maxHeartbeats 1000000 in
-- the kernel unfolds the bounded constructible functors
/-- **The exceptional projection morphism is compatible with refinements**: along a refinement
`h` of factorizations `f = i₁ ≫ p₁` by `f = i ≫ p`, the comparison
`i₁_! ⋙ Rp₁_* ≅ i_! ⋙ Rp_*` intertwines the exceptional projection morphisms. -/
theorem boundedConstructibleExceptionalProjectionMorphismOfFactorization_comp_refinementIso
    (sq : IsPullback (𝟙 X) i i₁ h) {p₁ : Z₁ ⟶ Y} {p : Z ⟶ Y} (wp : h ≫ p₁ = p) {f : X ⟶ Y}
    (w : i ≫ p = f) (w₁ : i₁ ≫ p₁ = f)
    [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward Λ ℓ sq)]
    (K : Dᵇc(X.left)⟦Λ⟧) (B : Dᵇc(Y.left)⟦Λ⟧) :
    boundedConstructibleExceptionalProjectionMorphismOfFactorization Λ ℓ i₁ p₁ w₁ K B ≫
        (boundedConstructibleLowerShriekRefinementIso Λ ℓ sq wp).hom.app
          (K ⊗ (boundedConstructibleUpperStar Λ ℓ f).obj B) =
      (boundedConstructibleLowerShriekRefinementIso Λ ℓ sq wp).hom.app K ▷ B ≫
        boundedConstructibleExceptionalProjectionMorphismOfFactorization Λ ℓ i p w K B := by
  obtain rfl := sq.toCommSq.snd_comp_eq_of_fst_eq_id
  subst wp
  have := isIso_restrictionComparison_of_isPullback Λ ℓ sq
  rw [boundedConstructibleLowerShriekRefinementIso_hom_app,
    boundedConstructibleLowerShriekRefinementIso_hom_app]
  unfold boundedConstructibleExceptionalProjectionMorphismOfFactorization
  rw [boundedConstructibleLowerStarComp_eq_conjugateIsoEquiv]
  have key := Adjunction.projectionMorphism_comp_refinement
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ (i ≫ h))
    (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ h)
    (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p₁)
    (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ (h ≫ p₁))
    (boundedConstructibleUpperStarTriangleComparison Λ ℓ sq.toCommSq.snd_comp_eq_of_fst_eq_id)
    (boundedConstructibleUpperStarTriangleComparison_μ' Λ ℓ _)
    (boundedConstructibleUpperStarComp Λ ℓ h p₁)
    (boundedConstructibleUpperStarComp_hom_app_tensor_δ' Λ ℓ h p₁)
    (eqToIso (congrArg (boundedConstructibleUpperStar Λ ℓ) w.symm) ≪≫
      boundedConstructibleUpperStarComp Λ ℓ i (h ≫ p₁))
    (eqToIso (congrArg (boundedConstructibleUpperStar Λ ℓ) w₁.symm) ≪≫
      boundedConstructibleUpperStarComp Λ ℓ (i ≫ h) p₁)
    (boundedConstructibleUpperStarComp_refinement_cocycle Λ ℓ h p₁ w w₁ _) K B
  -- TODO: `key` and the goal differ only by `Functor.comp_obj` unfoldings (checked with a
  -- structural Expr diff: after `dsimp only [Functor.comp_obj, Functor.comp_map,
  -- Functor.id_obj] at key ⊢` they are syntactically equal), but closing the goal with
  -- `exact key` then loops in `whnf`, and `convert key using 0` runs out of memory in the
  -- kernel. Likely fix: restate this theorem in exactly the form produced by `key`.
  sorry

end Refinement

end AlgebraicGeometry.ProEtale.CondensedRing
