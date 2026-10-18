/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Abelian.Injective.ExtHomology
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.ResolutionMap
public import WeilConjectures.SixFunctors.ProEtale.Adic.GlobalSectionsExt
public import WeilConjectures.WeilSheaf.CohomologyResolution

/-!
# Weil cohomology of the constant sheaf as pro-étale `Ext`

The cohomology `Hʳ(Y ⊗ k̄, ℚ̄_ℓ)` of the constant Weil sheaf is the pro-étale cohomology
`Hʳ(Ȳ_proét, ℚ̄_ℓ) = Ext^r(ℤ, ℚ̄_ℓ,Ȳ)` of the underlying abelian sheaf, computed through an
injective resolution `I` of `ℚ̄_ℓ` by pro-étale Weil sheaves, whose underlying abelian sheaves
form an injective resolution of `ℚ̄_ℓ,Ȳ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor Opposite Abelian

namespace AlgebraicGeometry

attribute [local instance 2000] CategoryWithHomology.hasHomology

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

namespace ProEtaleWeilSheaf

variable (k₀ l) (Y : Scheme.{u}) [Y.Over (Spec (CommRingCat.of k₀))]

/-- The underlying abelian sheaf of a pro-étale Weil sheaf. -/
noncomputable abbrev forgetAb :
    ProEtaleWeilSheaf k₀ l Y ⥤
      Sheaf (Scheme.ProEt.topology (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        AddCommGrpCat.{u + 1} :=
  IsoAlgebra.forget _ ⋙ AdicSheaf.forget _ ⋙ sheafForget₂ (ULift.{u + 1} (PadicAlgCl l)) _


instance preservesInjectiveObjects_adicSheafForget (X : Scheme.{u}) :
    (AdicSheaf.forget (l := l) X).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Mod.freeForgetAdjunction (adicConstantSheaf l X))

instance preservesInjectiveObjects_forgetAb : (forgetAb k₀ l Y).PreservesInjectiveObjects := by
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsoAlgebra.preservesInjectiveObjects_forget (F := WeilSheaf.frobeniusPullback k₀ l Y)
  infer_instance

end ProEtaleWeilSheaf

namespace ProEtaleWeilSheaf

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]

/-- Morphisms `ℤ ⟶ M` out of the constant abelian sheaf, for a pro-étale Weil sheaf `M`, are the
global sections `Γ(Ȳ, M)`. -/
noncomputable def sectionsAddEquiv (M : ProEtaleWeilSheaf k₀ l Y) :
    (constantIntSheaf _ ⟶ (forgetAb k₀ l Y).obj M) ≃+ (globalSectionsWeilFunctor k₀ l Y).obj M :=
  constantIntHomAddEquivΓ _ M.carrier.X

lemma sectionsAddEquiv_comp {M M' : ProEtaleWeilSheaf k₀ l Y}
    (f : constantIntSheaf _ ⟶ (forgetAb k₀ l Y).obj M) (φ : M ⟶ M') :
    sectionsAddEquiv M' (f ≫ (forgetAb k₀ l Y).map φ) =
      (globalSectionsWeilFunctor k₀ l Y).map φ (sectionsAddEquiv M f) :=
  constantIntHomAddEquivΓ_comp f _

/-- `sectionsAddEquiv` after an isomorphism of the target. -/
noncomputable def sectionsAddEquivOfIso {M M' : ProEtaleWeilSheaf k₀ l Y} (e : M ≅ M') :
    (constantIntSheaf _ ⟶ (forgetAb k₀ l Y).obj M) ≃+ (globalSectionsWeilFunctor k₀ l Y).obj M' :=
  (AddEquiv.mk' ((Iso.refl _).homCongr ((forgetAb k₀ l Y).mapIso e)) fun f g ↦ by simp).trans
    (sectionsAddEquiv M')

lemma sectionsAddEquivOfIso_apply {M M' : ProEtaleWeilSheaf k₀ l Y} (e : M ≅ M')
    (f : constantIntSheaf _ ⟶ (forgetAb k₀ l Y).obj M) :
    sectionsAddEquivOfIso e f = sectionsAddEquiv M' (f ≫ (forgetAb k₀ l Y).map e.hom) := by
  rw [sectionsAddEquivOfIso, AddEquiv.trans_apply]
  congr 1

variable {K : ProEtaleWeilSheaf k₀ l Y} (I : InjectiveResolution K) (r : ℕ)

lemma sc_g_sectionsAddEquiv (f : constantIntSheaf _ ⟶ (forgetAb k₀ l Y).obj (I.cocomplex.X r)) :
    ((I.cocomplex.sc r).map (globalSectionsWeilFunctor k₀ l Y)).g (sectionsAddEquiv _ f) =
      sectionsAddEquivOfIso (I.cocomplex.XIsoOfEq (CochainComplex.next ℕ r).symm)
        (f ≫ ((I.map (forgetAb k₀ l Y)).cocomplex.d r (r + 1))) := by
  rw [sectionsAddEquivOfIso_apply, Category.assoc]
  rw [InjectiveResolution.map_cocomplex_d,
    ← (forgetAb k₀ l Y).map_comp, HomologicalComplex.d_comp_XIsoOfEq_hom,
    sectionsAddEquiv_comp]
  rfl

set_option maxHeartbeats 1000000 in
-- unifying the terms of the image of a resolution with the images of its terms is slow
lemma extMk_eq_zero_iff_sectionsAddEquiv
    (f : constantIntSheaf _ ⟶ (I.map (forgetAb k₀ l Y)).cocomplex.X r)
    (hf : f ≫ (I.map (forgetAb k₀ l Y)).cocomplex.d r (r + 1) = 0) :
    (I.map (forgetAb k₀ l Y)).extMk f (r + 1) rfl hf = 0 ↔
      ∃ x : ((I.cocomplex.sc r).map (globalSectionsWeilFunctor k₀ l Y)).X₁,
        ((I.cocomplex.sc r).map (globalSectionsWeilFunctor k₀ l Y)).f x = sectionsAddEquiv _ f := by
  rw [InjectiveResolution.extMk_eq_zero_iff_exists]
  cases r with
  | zero =>
    have h0 : I.cocomplex.d ((ComplexShape.up ℕ).prev 0) 0 = 0 :=
      I.cocomplex.shape _ _ (by simp)
    simp only [true_and, Nat.add_eq_zero_iff, one_ne_zero, and_false, IsEmpty.exists_iff,
      exists_const, or_false]
    refine ⟨fun h ↦ ⟨0, ?_⟩, fun ⟨x, hx⟩ ↦ ?_⟩
    · rw [map_zero, h, map_zero]
    · refine (sectionsAddEquiv _).injective ?_
      rw [map_zero, ← hx]
      exact ConcreteCategory.congr_hom ((ShortComplex.map_f _ _).trans
        ((congrArg (globalSectionsWeilFunctor k₀ l Y).map h0).trans
          ((globalSectionsWeilFunctor k₀ l Y).map_zero _ _))) x
  | succ p =>
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, false_and, false_or,
      Nat.add_right_cancel_iff, exists_prop, exists_eq_left]
    rw [InjectiveResolution.map_cocomplex_d]
    have key (g : constantIntSheaf _ ⟶ (forgetAb k₀ l Y).obj (I.cocomplex.X p)) :
        ((I.cocomplex.sc (p + 1)).map (globalSectionsWeilFunctor k₀ l Y)).f
          (sectionsAddEquivOfIso (I.cocomplex.XIsoOfEq (CochainComplex.prev_nat_succ p).symm) g) =
          sectionsAddEquiv _ (g ≫ (forgetAb k₀ l Y).map (I.cocomplex.d p (p + 1))) := by
      rw [sectionsAddEquivOfIso_apply]
      refine (sectionsAddEquiv_comp _ (I.cocomplex.d _ (p + 1))).symm.trans ?_
      have hd := congrArg (forgetAb k₀ l Y).map
        (I.cocomplex.XIsoOfEq_hom_comp_d (CochainComplex.prev_nat_succ p).symm (p + 1))
      rw [Functor.map_comp] at hd
      rw [Category.assoc, hd]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨sectionsAddEquivOfIso (I.cocomplex.XIsoOfEq (CochainComplex.prev_nat_succ p).symm) g,
        by rw [key, hg]⟩
    · rintro ⟨x, hx⟩
      refine ⟨(sectionsAddEquivOfIso
        (I.cocomplex.XIsoOfEq (CochainComplex.prev_nat_succ p).symm)).symm x,
        (sectionsAddEquiv _).injective ?_⟩
      rw [← key, AddEquiv.apply_symm_apply, hx]

/-- The `r`-th pro-étale `Ext` of `ℤ` into the underlying abelian sheaf of a pro-étale Weil sheaf
`K` is the `r`-th homology of the complex of global sections of an injective resolution of `K`. -/
noncomputable def extAddEquivHomology :
    Ext (constantIntSheaf _) ((forgetAb k₀ l Y).obj K) r ≃+
      ((I.cocomplex.sc r).map (globalSectionsWeilFunctor k₀ l Y)).homology :=
  InjectiveResolution.extAddEquivHomology (I.map (forgetAb k₀ l Y)) _ (sectionsAddEquiv _)
    (sectionsAddEquivOfIso (I.cocomplex.XIsoOfEq (CochainComplex.next ℕ r).symm))
    (sc_g_sectionsAddEquiv I r) (extMk_eq_zero_iff_sectionsAddEquiv I r)

/-- The Frobenius on the cocycles `ℤ ⟶ Iⁿ` of the complex computing `Ext(ℤ, K)`: the Frobenius of
the global sections `Γ(Ȳ, Iⁿ)`. -/
noncomputable def cocycleFrobenius (n : ℕ) :
    (constantIntSheaf _ ⟶ (I.map (forgetAb k₀ l Y)).cocomplex.X n) →+
      (constantIntSheaf _ ⟶ (I.map (forgetAb k₀ l Y)).cocomplex.X n) :=
  ((sectionsAddEquiv (I.cocomplex.X n)).symm.toAddMonoidHom.comp
    ((globalSectionsFrobeniusNatTrans k₀ l Y).app (I.cocomplex.X n)).hom.toAddMonoidHom).comp
      (sectionsAddEquiv (I.cocomplex.X n)).toAddMonoidHom

lemma sectionsAddEquiv_cocycleFrobenius (n : ℕ)
    (f : constantIntSheaf _ ⟶ (I.map (forgetAb k₀ l Y)).cocomplex.X n) :
    sectionsAddEquiv _ (cocycleFrobenius I n f) =
      (globalSectionsFrobeniusNatTrans k₀ l Y).app (I.cocomplex.X n) (sectionsAddEquiv _ f) :=
  AddEquiv.apply_symm_apply _ _

lemma cocycleFrobenius_comp_d (n m : ℕ)
    (f : constantIntSheaf _ ⟶ (I.map (forgetAb k₀ l Y)).cocomplex.X n) :
    cocycleFrobenius I m (f ≫ (I.map (forgetAb k₀ l Y)).cocomplex.d n m) =
      cocycleFrobenius I n f ≫ (I.map (forgetAb k₀ l Y)).cocomplex.d n m := by
  refine (sectionsAddEquiv _).injective ?_
  rw [sectionsAddEquiv_cocycleFrobenius, InjectiveResolution.map_cocomplex_d,
    sectionsAddEquiv_comp, sectionsAddEquiv_comp, sectionsAddEquiv_cocycleFrobenius]
  have h := ConcreteCategory.congr_hom
    ((globalSectionsFrobeniusNatTrans k₀ l Y).naturality (I.cocomplex.d n m)) (sectionsAddEquiv _ f)
  simp only [ConcreteCategory.comp_apply] at h
  exact h

end ProEtaleWeilSheaf

end AlgebraicGeometry
