/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.FiniteNativeTensorComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality
import WeilConjectures.AlgebraicGeometry.FiniteCondensedRealizationHomDomain
import WeilConjectures.AlgebraicGeometry.FiniteCondensedCtfEquivalence
import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual
import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-! # Canonical closed comparison for normalized finite realization

Source: latest blueprint, `det-pd-biduality-coefficients.proof.md`, paragraph (i).
The comparison is the evaluation transpose for the fixed normalized tensorator.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.scalarReductionSiteSmall
universe u c d v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace CategoryTheory

private theorem finiteClosedTest
    {C : Type c} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {D : Type d} [Category.{w} D] [MonoidalCategory D] [MonoidalClosed D]
    (F : C ⥤ D) [F.Monoidal] (K L W : C)
    (h₁ : Function.Bijective (F.map : (L ⟶ (ihom K).obj W) → _))
    (h₂ : Function.Bijective (F.map : (K ⊗ L ⟶ W) → _)) :
    Function.Bijective (fun f : F.obj L ⟶ F.obj ((ihom K).obj W) ↦
      f ≫ (Functor.LaxMonoidal.ihomComparison F K).natTrans.app W) := by
  let e₁ := Equiv.ofBijective _ h₁
  let e₂ := Equiv.ofBijective _ h₂
  let E := (((e₁.symm.trans ((ihom.adjunction K).homEquiv L W).symm).trans e₂).trans
    (Functor.Monoidal.μIso F K L).symm.homFromEquiv).trans
      ((ihom.adjunction (F.obj K)).homEquiv (F.obj L) (F.obj W))
  have he : (fun f : F.obj L ⟶ F.obj ((ihom K).obj W) ↦
      f ≫ (Functor.LaxMonoidal.ihomComparison F K).natTrans.app W) = E := by
    funext f
    obtain ⟨g, rfl⟩ := h₁.surjective f
    have hE : E (F.map g) = MonoidalClosed.curry
        ((Functor.Monoidal.μIso F K L).hom ≫ F.map (MonoidalClosed.uncurry g)) := by
      change MonoidalClosed.curry ((Functor.Monoidal.μIso F K L).hom ≫
        F.map (MonoidalClosed.uncurry (e₁.symm (e₁ g)))) = _
      rw [e₁.symm_apply_apply]
    rw [hE]
    apply MonoidalClosed.uncurry_injective
    rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_natural_left,
      MonoidalClosed.uncurry_eq, Functor.LaxMonoidal.ihomComparison_ev,
      Functor.LaxMonoidal.μ_natural_right_assoc, ← F.map_comp,
      MonoidalClosed.uncurry_eq, Functor.Monoidal.μIso_hom]
  rw [he]
  exact E.bijective
private theorem finiteClosedRestrictionTest
    {C : Type c} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {D : Type d} [Category.{w} D] [MonoidalCategory D] [MonoidalClosed D]
    (F : C ⥤ D) [F.Monoidal] (P : ObjectProperty C) (Q : ObjectProperty D)
    (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))
    [(Q.lift (P.ι ⋙ F) hF).IsEquivalence]
    (K W : C) (hW : P W)
    (htensor : ∀ L, P L → P (K ⊗ L))
    (hsource : P ((ihom K).obj W))
    (htarget : Q ((ihom (F.obj K)).obj (F.obj W))) :
    IsIso ((Functor.LaxMonoidal.ihomComparison F K).natTrans.app W) := by
  let R := Q.lift (P.ι ⋙ F) hF
  have hf (X Y : C) (hX : P X) (hY : P Y) :
      Function.Bijective (F.map : (X ⟶ Y) → _) := by
    constructor
    · intro f g h
      have hh : R.map (ObjectProperty.homMk f :
          (⟨X, hX⟩ : P.FullSubcategory) ⟶ ⟨Y, hY⟩) =
          R.map (ObjectProperty.homMk g) := by
        apply Q.hom_ext
        exact h
      exact P.ι.congr_map (R.map_injective hh)
    · intro f
      obtain ⟨g, hg⟩ := R.map_surjective
        (ObjectProperty.homMk f : R.obj ⟨X, hX⟩ ⟶ R.obj ⟨Y, hY⟩)
      exact ⟨g.hom, Q.ι.congr_map hg⟩
  let X : Q.FullSubcategory := ⟨F.obj ((ihom K).obj W), hF ⟨_, hsource⟩⟩
  let Y : Q.FullSubcategory := ⟨(ihom (F.obj K)).obj (F.obj W), htarget⟩
  let b : X ⟶ Y := ObjectProperty.homMk
    ((Functor.LaxMonoidal.ihomComparison F K).natTrans.app W)
  have hb : IsIso b := by
    apply isIso_of_yoneda_map_bijective
    intro T
    let L := R.objPreimage T
    let q := Q.ι.mapIso (R.objObjPreimageIso T)
    have hL := finiteClosedTest F K L.obj W
      (hf _ _ L.property hsource) (hf _ _ (htensor _ L.property) hW)
    constructor
    · intro f g h
      have hh : q.hom ≫ f.hom = q.hom ≫ g.hom :=
        hL.injective (by
          simpa only [b, ObjectProperty.homMk_hom,
              ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
            using congrArg (fun k ↦ q.hom ≫ k.hom) h)
      apply Q.hom_ext
      exact (cancel_epi q.hom).mp hh
    · intro f
      obtain ⟨g, hg⟩ := hL.surjective (q.hom ≫ f.hom)
      refine ⟨ObjectProperty.homMk (q.inv ≫ g), ?_⟩
      apply Q.hom_ext
      change (q.inv ≫ g) ≫
        (Functor.LaxMonoidal.ihomComparison F K).natTrans.app W = f.hom
      dsimp only at hg
      rw [Category.assoc, hg, Iso.inv_hom_id_assoc]
  exact inferInstanceAs (IsIso (Q.ι.map b))

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

private theorem boundedConstructible_iff_source
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (K : Etale.DerivedCategoryModule A X) :
    Etale.DerivedCategory.isBoundedConstructible A X K ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X K := by
  constructor
  · rintro ⟨hc, a, b, -, hz⟩
    refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun i ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)⟩
    · exact (_root_.DerivedCategory.isGE_iff K a).2 (fun i hi ↦ hz i (.inl hi))
    · exact (_root_.DerivedCategory.isLE_iff K b).2 (fun i hi ↦ hz i (.inr hi))
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun i ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc i),
      min a b, b, min_le_right _ _, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff K a).1 ha i
        (hi.trans_le (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff K b).1 hb i hi

/-- The canonical internal-Hom mate of normalized finite realization is invertible
on pairs of finite-Tor constructible etale objects. No dualizing object occurs here.

Source: latest blueprint, `det-pd-biduality-coefficients.proof.md`, paragraph (i),
tensor compatibility and internal Hom
(blueprint: lem-sf-finite-condensed-realization-closed).

Proof:
1. Finite constructible descent with Tor intervals gives an equivalence of the two full
   finite-Tor constructible subcategories. Their tensor products remain in these domains.
   Finite etale internal Hom and actual-module internal Hom preserve these domains.
2. For K and W in the source domain and any target object P in the target domain, choose
   an etale preimage Q. The full faithfulness on bounded-below inputs, followed by the
   two tensor-Hom adjunctions and the specified tensorator, identifies
   Hom(P,F[ K,W ]) with Hom(P,[ FK,FW ]). In the middle use full faithfulness on
   K tensor Q and W, which are bounded below. This is natural in P.
3. Untransposition identifies this bijection with postcomposition by the canonical
   ihomComparison: its untranspose is the tensorator followed by the image of evaluation.
   Both its source and target are in the full target domain by step 1. Restricted Yoneda
   therefore proves the stated IsIso. Zero rings, the empty scheme and zero objects
   require no additional hypotheses. -/
theorem finiteCondensedRealizationClosed
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    [HasInvertibleExponent (ULift.{u + 1} A) (Spec (.of k))]
    (hA : ∃ m : ℕ, ((ℓ ^ m : ℕ) : A) = 0)
    (enc : ∀ X : Scheme.{u}, Encoding A X)
    (T : Scheme.{u}) (a : T ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    let F := internalEtaleRealization A T (enc T)
    letI := FiniteNativeTensor.realizationMonoidal A T (enc T)
    ∀ K W : Etale.DerivedCategoryModule (ULift.{u + 1} A) T,
      (Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) T K ∧
        _root_.DerivedCategory.finiteTorAmplitude _ K) →
      (Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) T W ∧
        _root_.DerivedCategory.finiteTorAmplitude _ W) →
      IsIso ((Functor.LaxMonoidal.ihomComparison F K).natTrans.app W) := by
  dsimp only
  let F := internalEtaleRealization A T (enc T)
  let : F.Monoidal := FiniteNativeTensor.realizationMonoidal A T (enc T)
  let P := Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) T ⊓
    _root_.DerivedCategory.finiteTorAmplitude _
  let Q := constantModelBoundedConstructible (coefficient A) T ⊓
    _root_.DerivedCategory.finiteTorAmplitude _
  obtain ⟨hF, hR⟩ := finiteCondensedCtfEquivalence p ℓ hpℓ k A enc T a
  let R := Q.lift (P.ι ⋙ F) hF
  have : R.IsEquivalence := hR
  let : HasInvertibleExponent (ULift.{u + 1} A) T := .of_hom a
  have hP (K : Etale.DerivedCategoryModule (ULift.{u + 1} A) T) :
      P K ↔ Etale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) T K :=
    and_congr (boundedConstructible_iff_source (ULift.{u + 1} A) T K) Iff.rfl
  have htensor (K L : Etale.DerivedCategoryModule (ULift.{u + 1} A) T)
      (hK : P K) (hL : P L) : P (K ⊗ L) :=
    (hP _).mpr (Etale.constructibleFiniteTor_tensor (ULift.{u + 1} A) T
      ((hP _).mp hK) ((hP _).mp hL))
  have hsource (K W : Etale.DerivedCategoryModule (ULift.{u + 1} A) T)
      (hK : P K) (hW : P W) : P ((ihom K).obj W) :=
    (hP _).mpr (Etale.constructibleFiniteTor_derivedHom (ULift.{u + 1} A) a
      ((hP _).mp hK) ((hP _).mp hW))
  intro K W hK hW
  exact CategoryTheory.finiteClosedRestrictionTest F P Q hF K W hW
    (fun L hL ↦ htensor K L hK hL) (hsource K W hK hW)
    (finiteCondensedRealizationHomDomain p ℓ hpℓ k A hA enc T a K W hK hW)

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
