/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import Mathlib.CategoryTheory.Generator.Basic

/-!
# Grothendieck abelianness of constant-coefficient etale module sheaves

## References

* Stacks Project, Tags 03DA, 03DB, 03DI, 03EW, 021A, 021B and 04HR
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- The module sheaves over the constant ring sheaf on the small etale site are
Grothendieck abelian. The last conjunct states the abelian-sheaf case, with integer
coefficients (Stacks, Tags 03DA, 03DB, 03DI, 03EW, 021B and 04HR). -/
theorem etaleModuleSheaves_grothendieckAbelian (T : Scheme.{u})
    (Λ : Type u) [CommRing Λ] :
    IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1}
      ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1, u} Λ)))) ∧
      (∃ (I : Type (u + 1)) (U : I → T.Etale),
        (∀ i : I, IsAffine (U i).left) ∧
        (∀ V : T.Etale, ∃ (K : Type (u + 1)) (i : K → I)
          (f : ∀ k : K, U (i k) ⟶ V),
          Sieve.ofArrows (fun k : K ↦ U (i k)) f ∈ T.smallEtaleTopology V) ∧
        ∃ c : Cofan (fun i : I ↦
          (PresheafOfModules.sheafification.{u + 1}
            (𝟙 ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
              (RingCat.of (ULift.{u + 1, u} Λ))).obj)).obj
            ((PresheafOfModules.free ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
              (RingCat.of (ULift.{u + 1, u} Λ))).obj).obj (uliftYoneda.{u + 1}.obj (U i)))),
          Nonempty (IsColimit c) ∧ IsSeparator c.pt) ∧
      IsGrothendieckAbelian.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) := by
  have := etaleConstantModuleFunctor_isEquivalence T (ULift.{u + 1, u} Λ)
  let R := (constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
    (RingCat.of (ULift.{u + 1, u} Λ))
  have hG : IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1} R) :=
    IsGrothendieckAbelian.of_equivalence
      (etaleConstantModuleFunctor T (ULift.{u + 1, u} Λ)).asEquivalence
  have := hG
  have : HasColimitsOfSize.{u + 1, u + 1} (SheafOfModules.{u + 1} R) :=
    IsGrothendieckAbelian.hasColimits _
  refine ⟨hG, ?_, inferInstance⟩
  let U : T.AffineEtale → T.Etale := (AffineEtale.Spec T).obj
  refine ⟨T.AffineEtale, U, ?_, ?_, ?_⟩
  · intro i
    change IsAffine ((Scheme.Spec).obj _)
    infer_instance
  · intro V
    refine ⟨(Σ i : T.AffineEtale, U i ⟶ V), Sigma.fst, fun k ↦ k.2, ?_⟩
    apply T.smallEtaleTopology.superset_covering ?_
      ((AffineEtale.Spec T).is_cover_of_isCoverDense T.smallEtaleTopology V)
    rintro W f ⟨l⟩
    rw [Sieve.mem_ofArrows_iff]
    exact ⟨⟨l.obj, l.map⟩, l.lift, l.fac.symm⟩
  · let Q := fun i : T.AffineEtale ↦
      (PresheafOfModules.sheafification.{u + 1} (𝟙 R.obj)).obj
        ((PresheafOfModules.free R.obj).obj (uliftYoneda.{u + 1}.obj (U i)))
    have hs : ObjectProperty.IsSeparating (.ofObj Q) := by
      intro M N f g h
      apply (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj).map_injective
      apply (Functor.whiskerLeft_obj_map_bijective_of_isCoverDense
        T.smallEtaleTopology (AffineEtale.Spec T)
        M.val.presheaf N.val.presheaf N.isSheaf).injective
      ext ⟨i⟩ x
      let adj := PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 R.obj)
      let e (M : SheafOfModules.{u + 1} R) :=
        (adj.homEquiv
          ((PresheafOfModules.free R.obj).obj (uliftYoneda.{u + 1}.obj (U i))) M).trans
          (PresheafOfModules.freeHomEquiv.trans uliftYonedaEquiv)
      have hn (a : Q i ⟶ M) (k : M ⟶ N) :
          (e N) (a ≫ k) = k.val.app (.op (U i)) ((e M) a) := by
        dsimp only [e, Equiv.trans_apply]
        rw [adj.homEquiv_naturality_right]
        let a' := (adj.homEquiv _ _) a
        let k' := (SheafOfModules.forget R ⋙
          PresheafOfModules.restrictScalars (𝟙 R.obj)).map k
        change uliftYonedaEquiv (PresheafOfModules.freeHomEquiv (a' ≫ k')) = _
        have hfree := (PresheafOfModules.freeAdjunction R.obj).homEquiv_naturality_right a' k'
        rw [PresheafOfModules.freeAdjunction_homEquiv,
          PresheafOfModules.freeAdjunction_homEquiv] at hfree
        erw [hfree, uliftYonedaEquiv_comp]
      have hh := h _ (ObjectProperty.ofObj_apply Q i) ((e M).symm x)
      have he := congrArg (e N) hh
      rw [hn, hn, Equiv.apply_symm_apply] at he
      exact he
    exact ⟨_, ⟨colimit.isColimit (Discrete.functor Q)⟩, hs.isSeparator_coproduct⟩

end AlgebraicGeometry.Scheme
