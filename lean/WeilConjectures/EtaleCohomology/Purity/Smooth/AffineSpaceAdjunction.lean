/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.Affine
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
import Sheaf.SmoothPurity.NormalizedProjectiveLineAdjunction
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso
import WeilConjectures.SixFunctors.Etale.Derived.TensorRightUnitor

/-!
# The affine-space ambient adjunction

For the projection `p_d : 𝔸^d_S ⟶ S` of relative affine space, the direct image with compact
support `Rp_{d!}` is left adjoint to the twisted pullback `p_d^*(d)[2d]` on the entire derived
categories of étale sheaves of `Λ`-modules (blueprint `cor-amb-affine-space-adjunction`, of the
subsection `sk-prop-sf-cbc`). Its proof composes the extension by zero along `𝔸¹_S ⊆ ℙ¹_S` with
the projective-line adjunction `Rq_* ⊣ q^*(1)[2]` (`thm-amb-p1-adjunction`), which is built from
the projective-line trace; neither is available yet, so the statement is recorded here with
`sorry`.

Since `Rp_d^!` is *defined* as the right adjoint of `Rp_{d!}`, the adjunction identifies
`Rp_d^!` with `p_d^*(d)[2d]`: this is how affine-line purity
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineLine`) is deduced.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]

@[irreducible] private noncomputable def lowerShriekCongr {X Y : Scheme.{u}}
    {f g : X ⟶ Y} [HasCompactification f] [HasCompactification g] (h : f = g) :
    rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f ≅
      rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) g := by
  subst g
  exact Iso.refl _

@[irreducible] private noncomputable def twistZero (X : Scheme.{u}) [HasInvertibleExponent Λ X] :
    twistShift Λ X 0 ≅ 𝟭 _ :=
  Functor.isoWhiskerLeft _ (shiftFunctorZero' _ (2 * (0 : ℤ)) (by simp)) ≪≫
    Functor.rightUnitor _ ≪≫
    (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.mapIso
      (HasTateTwist.twistObjectZeroIso X) ≪≫
    derivedTensorRightUnitorNatIso _ X

@[irreducible] private noncomputable def pullTwist {X Y : Scheme.{u}}
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]
    (f : X ⟶ Y) (m : ℤ) :
    twistShift Λ Y m ⋙ L((f)^*[ModuleCat.{u + 1} Λ]) ≅
      L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ twistShift Λ X m :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((L((f)^*[ModuleCat.{u + 1} Λ])).commShiftIso (2 * m)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (derivedTensorRightCompLeftDerivedUpperStarIso _ f (tateObject Λ Y m) ≪≫
        Functor.isoWhiskerLeft _
          ((derivedTensor (ModuleCat.{u + 1} Λ) X).flip.mapIso
            (leftDerivedUpperStarTateObjectIso f m))) _ ≪≫
    Functor.associator _ _ _

private theorem affineLineAdjunction [HasTateTwist.IsNormalized Λ]
    (S : Scheme.{u}) [HasInvertibleExponent Λ S] :
    Nonempty (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ)
        (𝔸(ULift.{u} (Fin 1); S) ↘ S) ⊣
      L((𝔸(ULift.{u} (Fin 1); S) ↘ S)^*[ModuleCat.{u + 1} Λ]) ⋙
        twistShift Λ 𝔸(ULift.{u} (Fin 1); S) 1) := by
  let P := ℙ(Option (ULift.{u} (Fin 1)); S)
  let j := AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S
  let q : P ⟶ S := P ↘ S
  let c : Compactification (𝔸(ULift.{u} (Fin 1); S) ↘ S) := {
    Z := P
    i := j
    g := q
    comm := (AffineSpace.toRelativeProjectiveSpace_over (ULift.{u} (Fin 1)) S).symm
    isProper := inferInstance
    isOpenImmersion := inferInstance
  }
  have : HasInvertibleExponent Λ P := .of_hom q
  obtain ⟨a⟩ := nonempty_normalizedProjectiveLineAdjunction Λ S
  let b := (derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} Λ) j).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory _ j).symm
  let r := Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (pullTwist Λ j 1) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) j q
        (𝔸(ULift.{u} (Fin 1); S) ↘ S)
        (AffineSpace.toRelativeProjectiveSpace_over (ULift.{u} (Fin 1)) S).symm).symm _
  exact ⟨((b.comp a).ofNatIsoRight r).ofNatIsoLeft (rightDerivedLowerShriekIso Λ c)⟩

@[irreducible] private noncomputable def addTwist (X : Scheme.{u}) [HasInvertibleExponent Λ X]
    (m n : ℤ) : twistShift Λ X m ⋙ twistShift Λ X n ≅ twistShift Λ X (m + n) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (((derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj
        (tateObject Λ X n)).commShiftIso (2 * m)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (shiftFunctorAdd' _ (2 * m) (2 * n)
        (2 * (m + n)) (by ring)).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((CategoryTheory.MonoidalCategory.tensorRightTensor
        (tateObject Λ X m) (tateObject Λ X n)).symm ≪≫
        (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.mapIso
          (HasTateTwist.twistObjectAddIso X m n)) _

@[irreducible] private noncomputable def composeTwist {X Y Z : Scheme.{u}}
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]
    (f : X ⟶ Y) (g : Y ⟶ Z) (m n : ℤ)
    (fg : X ⟶ Z := f ≫ g) (hfg : fg = f ≫ g := by cat_disch) :
    (L((g)^*[ModuleCat.{u + 1} Λ]) ⋙ twistShift Λ Y m) ⋙
        (L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ twistShift Λ X n) ≅
      L((fg)^*[ModuleCat.{u + 1} Λ]) ⋙ twistShift Λ X (m + n) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pullTwist Λ f m) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (addTwist Λ X m n)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarComp _ f g fg hfg).symm _

@[irreducible] private noncomputable def successorIso (d : ℕ) (S : Scheme.{u}) :
    𝔸(ULift.{u} (Fin (d + 1)); S) ≅ 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); S)) :=
  AffineSpace.reindexIso S
      ((Equiv.sumCongr Equiv.ulift Equiv.ulift).trans (finSumFinEquiv.trans Equiv.ulift.symm)) ≪≫
    AffineSpace.sumIso S

private lemma successorIso_over (d : ℕ) (S : Scheme.{u}) :
    (successorIso d S).hom ≫
        𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); S)) ↘ 𝔸(ULift.{u} (Fin d); S) ≫
          𝔸(ULift.{u} (Fin d); S) ↘ S = 𝔸(ULift.{u} (Fin (d + 1)); S) ↘ S := by
  rw [successorIso, Iso.trans_hom, Category.assoc, AffineSpace.sumIso_hom_over_over,
    AffineSpace.reindexIso_hom, AffineSpace.reindex_over]

/-- Blueprint `cor-amb-affine-space-adjunction`: affine-space ambient adjunction.

For the projection `p_d : 𝔸^d_S ⟶ S` of relative affine space over a scheme `S` on which the
exponent of `Λ` is invertible, on the entire derived categories of étale sheaves of
`Λ`-modules,

`Rp_{d!} ⊣ p_d^*(d)[2d]`. -/
theorem nonempty_rightDerivedLowerShriek_adjunction_affineSpace [HasTateTwist.IsNormalized Λ]
    (d : ℕ) (S : Scheme.{u}) [HasInvertibleExponent Λ S] :
    Nonempty (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) (𝔸(ULift.{u} (Fin d); S) ↘ S) ⊣
      L(((𝔸(ULift.{u} (Fin d); S) ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙
        twistShift Λ 𝔸(ULift.{u} (Fin d); S) d) := by
  induction d with
  | zero =>
    let p := 𝔸(ULift.{u} (Fin 0); S) ↘ S
    let a := (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) p).ofNatIsoRight
      (rightDerivedUpperShriekIsoOfIso _ (asIso p))
    exact ⟨a.ofNatIsoRight ((Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft _ (twistZero Λ _).symm)⟩
  | succ d ih =>
    rw [Nat.cast_succ]
    let e := successorIso d S
    let q := 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); S)) ↘
      𝔸(ULift.{u} (Fin d); S)
    let p := 𝔸(ULift.{u} (Fin d); S) ↘ S
    obtain ⟨a⟩ := ih
    obtain ⟨b⟩ := affineLineAdjunction Λ 𝔸(ULift.{u} (Fin d); S)
    have : HasCompactification (e.hom ≫ q) :=
      HasCompactification.comp_of_isOpenImmersion q e.hom
    have h : (e.hom ≫ q) ≫ p = 𝔸(ULift.{u} (Fin (d + 1)); S) ↘ S := by
      rw [Category.assoc]
      exact successorIso_over d S
    have : HasCompactification ((e.hom ≫ q) ≫ p) := .of_eq h.symm
    obtain ⟨c₁⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ e.hom q
    obtain ⟨c₂⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ (e.hom ≫ q) p
    let ae := (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) e.hom).ofNatIsoRight
      (rightDerivedUpperShriekIsoOfIso _ e)
    let b' := (ae.comp b).ofNatIsoLeft c₁.symm
    let a' := (b'.comp a).ofNatIsoLeft (c₂.symm ≪≫ lowerShriekCongr Λ h)
    let r : (L((q)^*[ModuleCat.{u + 1} Λ]) ⋙
        twistShift Λ 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); S)) 1) ⋙
          L((e.hom)^*[ModuleCat.{u + 1} Λ]) ≅
        L((e.hom ≫ q)^*[ModuleCat.{u + 1} Λ]) ⋙
          twistShift Λ 𝔸(ULift.{u} (Fin (d + 1)); S) 1 :=
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (pullTwist Λ e.hom 1) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) e.hom q).symm _
    exact ⟨a'.ofNatIsoRight
      (Functor.isoWhiskerLeft _ r ≪≫ composeTwist Λ (e.hom ≫ q) p d 1
        (𝔸(ULift.{u} (Fin (d + 1)); S) ↘ S) h.symm)⟩


end Etale

end AlgebraicGeometry
