/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# A lifting criterion for K-injectivity

We show that a cochain complex `L` in an abelian category which has the right lifting
property with respect to all monomorphic quasi-isomorphisms is K-injective.

## Main results

* `CochainComplex.isKInjective_of_forall_exists_lift`: if every morphism `A ⟶ L` extends
  along every monomorphic quasi-isomorphism `A ⟶ B`, then `L` is K-injective.
* `CochainComplex.isKInjective_of_rlp`: if `p : L ⟶ Z` has the right lifting property with
  respect to the monomorphic quasi-isomorphisms and `Z` is a zero object, then `L` is
  K-injective. This is the form in which the small object argument produces K-injective
  complexes.

The proof of the first statement applies the lifting property to the inclusion
`CochainComplex.mappingCone.inr (𝟙 K) : K ⟶ mappingCone (𝟙 K)`, which is a monomorphism,
and a quasi-isomorphism as soon as `K` is acyclic, since the mapping cone of an identity
is contractible. The resulting lift produces the required null-homotopy.
-/

@[expose] public section

namespace CochainComplex

open CategoryTheory Category Limits HomComplex

variable {C : Type*} [Category* C] [Abelian C]

namespace mappingCone

variable {F G K : CochainComplex C ℤ}

instance (φ : F ⟶ G) : Mono (mappingCone.inr φ) :=
  HomologicalComplex.mono_of_mono_f _
    (fun n ↦ mono_of_mono_fac (mappingCone.inr_f_snd_v φ n))

/-- The mapping cone of an identity is contractible. -/
noncomputable def homotopyIdZeroOfId : Homotopy (𝟙 (mappingCone (𝟙 K))) 0 :=
  mappingCone.liftHomotopy _ _ _ (mappingCone.snd _) 0 (by simp) (by simp)

lemma acyclic_of_id (K : CochainComplex C ℤ) : (mappingCone (𝟙 K)).Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero,
    ← HomologicalComplex.homologyMap_id, homotopyIdZeroOfId.homologyMap_eq,
    HomologicalComplex.homologyMap_zero]

lemma quasiIso_inr_id (hK : K.Acyclic) : QuasiIso (mappingCone.inr (𝟙 K)) where
  quasiIsoAt n := by
    rw [quasiIsoAt_iff_exactAt _ _ (hK n)]
    exact acyclic_of_id K n

end mappingCone

/-- A cochain complex which has the right lifting property with respect to all monomorphic
quasi-isomorphisms is K-injective. -/
theorem isKInjective_of_forall_exists_lift (L : CochainComplex C ℤ)
    (hL : ∀ {A B : CochainComplex C ℤ} (i : A ⟶ B), Mono i → QuasiIso i →
      ∀ (f : A ⟶ L), ∃ g : B ⟶ L, i ≫ g = f) :
    L.IsKInjective where
  nonempty_homotopy_zero {K} f hK := by
    obtain ⟨g, hg⟩ := hL (mappingCone.inr (𝟙 K)) inferInstance
      (mappingCone.quasiIso_inr_id hK) f
    refine ⟨(Cochain.equivHomotopy f 0).symm
      ⟨(mappingCone.inl (𝟙 K)).comp (Cochain.ofHom g) (add_zero (-1)), ?_⟩⟩
    rw [δ_comp_zero_cochain _ _ _ (by omega), δ_ofHom, Cochain.comp_zero,
      mappingCone.δ_inl, ← Cochain.ofHom_comp, assoc, hg]
    simp

/-- A cochain complex `L` which admits a morphism `p : L ⟶ Z` to a zero object which has the
right lifting property with respect to the monomorphic quasi-isomorphisms is K-injective. -/
theorem isKInjective_of_rlp {L Z : CochainComplex C ℤ} (p : L ⟶ Z) (hZ : IsZero Z)
    (hp : MorphismProperty.rlp (MorphismProperty.monomorphisms (CochainComplex C ℤ) ⊓
      HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) p) :
    L.IsKInjective := by
  refine isKInjective_of_forall_exists_lift L (fun {A B} i hi hi' f ↦ ?_)
  have := hp i ⟨hi, hi'⟩
  have sq : CommSq f i p (0 : B ⟶ Z) := ⟨hZ.eq_of_tgt _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

end CochainComplex

namespace CochainComplex

open CategoryTheory Category Limits

section

variable {C : Type*} [Category* C] [Abelian C]

/-- The mapping cone of a morphism between K-injective cochain complexes is K-injective. -/
instance isKInjective_mappingCone {K L : CochainComplex C ℤ} (φ : K ⟶ L) [K.IsKInjective]
    [L.IsKInjective] : (mappingCone φ).IsKInjective := by
  rw [isKInjective_iff_rightOrthogonal]
  exact (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal.ext_of_isTriangulatedClosed₃ _
    (HomotopyCategory.mappingCone_triangleh_distinguished φ)
    (IsKInjective.rightOrthogonal K) (IsKInjective.rightOrthogonal L)

/-- A quasi-isomorphism between K-injective cochain complexes is an isomorphism in the homotopy
category. -/
lemma isIso_quotient_map_of_isKInjective {K L : CochainComplex C ℤ} (φ : K ⟶ L) [QuasiIso φ]
    [K.IsKInjective] [L.IsKInjective] :
    IsIso ((HomotopyCategory.quotient C (.up ℤ)).map φ) := by
  have hφ := (mappingCone.quasiIso_iff_acyclic φ).1 inferInstance
  have hZ : IsZero ((HomotopyCategory.quotient C (.up ℤ)).obj (mappingCone φ)) := by
    rw [IsZero.iff_id_eq_zero, ← (HomotopyCategory.quotient C (.up ℤ)).map_id,
      ← (HomotopyCategory.quotient C (.up ℤ)).map_zero]
    exact HomotopyCategory.eq_of_homotopy _ _ (IsKInjective.homotopyZero _ hφ)
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
    (HomotopyCategory.mappingCone_triangleh_distinguished φ)).1 hZ

end

section

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]

set_option backward.isDefEq.respectTransparency false in
/-- If `F ⊣ G` is an adjunction between abelian categories whose left adjoint `F` sends acyclic
complexes to acyclic complexes, then `G` sends K-injective complexes to K-injective complexes:
a morphism `K ⟶ G(L)` corresponds to a morphism `F(K) ⟶ L`, and a null-homotopy of the latter
transports to a null-homotopy of the former. -/
lemma _root_.CategoryTheory.Adjunction.isKInjective_mapHomologicalComplex (adj : F ⊣ G)
    (hF : ∀ K : CochainComplex C ℤ, K.Acyclic →
      ((F.mapHomologicalComplex (.up ℤ)).obj K).Acyclic)
    (L : CochainComplex D ℤ) [L.IsKInjective] :
    IsKInjective ((G.mapHomologicalComplex (.up ℤ)).obj L) where
  nonempty_homotopy_zero {K} f hK := by
    let f₀ (p : ℤ) : K.X p ⟶ G.obj (L.X p) := f.f p
    have hf₀ (p q : ℤ) : f₀ p ≫ G.map (L.d p q) = K.d p q ≫ f₀ q := f.comm p q
    let f' : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L :=
      { f p := F.map (f₀ p) ≫ adj.counit.app (L.X p)
        comm' p q _ := by
          change (F.map (f₀ p) ≫ adj.counit.app (L.X p)) ≫ L.d p q =
            F.map (K.d p q) ≫ F.map (f₀ q) ≫ adj.counit.app (L.X q)
          have := adj.counit_naturality (L.d p q)
          erw [Category.assoc, ← this, ← F.map_comp_assoc, hf₀, F.map_comp_assoc] }
    let h := IsKInjective.homotopyZero f' (hF K hK)
    let h₀ (p q : ℤ) : F.obj (K.X p) ⟶ L.X q := h.hom p q
    refine ⟨{ hom p q := adj.unit.app (K.X p) ≫ G.map (h₀ p q)
              zero p q hpq := by
                change _ ≫ G.map (h.hom p q) = 0
                rw [h.zero p q hpq, G.map_zero, comp_zero]
              comm p := ?_ }⟩
    have h₁ : f₀ p = adj.unit.app (K.X p) ≫ G.map (F.map (f₀ p) ≫ adj.counit.app (L.X p)) := by
      have := adj.unit_naturality (f₀ p)
      erw [G.map_comp, reassoc_of% this, adj.right_triangle_components, Category.comp_id]
    have h₂ : F.map (f₀ p) ≫ adj.counit.app (L.X p) =
        F.map (K.d p (p + 1)) ≫ h₀ (p + 1) p + h₀ p (p - 1) ≫ L.d (p - 1) p := by
      have := h.comm p
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (p - 1) p by simp)] at this
      simpa using this
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (p - 1) p by simp)]
    refine h₁.trans ?_
    rw [h₂, G.map_add, G.map_comp, G.map_comp, Preadditive.comp_add]
    have := adj.unit_naturality (K.d p (p + 1))
    erw [reassoc_of% this]
    simp

end

end CochainComplex
