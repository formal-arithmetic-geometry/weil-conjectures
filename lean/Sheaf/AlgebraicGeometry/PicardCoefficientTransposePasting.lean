/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
public import Sheaf.AlgebraicGeometry.SchemeDerivedMateEvaluation
public import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackSquare

/-! # Pasting of the coefficient transpose

Source: Stacks Project, Tags 08HY and 0D5S.
(blueprint: lem-sc-picard-coefficient-transpose-pasting)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

/-- The coefficient transpose, constructed from the fixed base-change mate.
Source: Stacks Project, Tag 08HY.
(blueprint: def-sc-picard-coefficient-transpose) -/
@[irreducible]
def picardCoefficientTranspose {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S) :
  ∀ {V : Scheme.{v}} (r : V ⟶ W),
    (derivedPullback (pullback.snd f (r ≫ k))).obj
      ((derivedPullback r).obj
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
              ((Modules.tensorPullback (pullback.fst f k)).obj L)))) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f (r ≫ k)).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f (r ≫ k))).obj L) :=
  fun {V : Scheme.{v}} (r : V ⟶ W) ↦ by
    let M := (Modules.tensorPullback (pullback.fst f k)).obj L
    let N := (Modules.tensorPullback (pullback.fst f (r ≫ k))).obj L
    let a : pullback f (r ≫ k) ⟶ pullback f k :=
      pullback.lift (pullback.fst f (r ≫ k)) (pullback.snd f (r ≫ k) ≫ r)
        (by rw [Category.assoc]; exact pullback.condition)
    have ha : a ≫ pullback.fst f k = pullback.fst f (r ≫ k) := pullback.lift_fst ..
    have hb : a ≫ pullback.snd f k = pullback.snd f (r ≫ k) ≫ r := pullback.lift_snd ..
    let c := (conjugateIsoEquiv
      ((Classical.choose (Modules.exists_tensorPullbackAdjunction (pullback.fst f k))).comp
        (Classical.choose (Modules.exists_tensorPullbackAdjunction a)))
      (Classical.choose (Modules.exists_tensorPullbackAdjunction
        (pullback.fst f (r ≫ k))))).symm
      (Modules.pushforwardComp a (pullback.fst f k) ≪≫ Modules.pushforwardCongr ha)
    let d : (Modules.pullback a).obj M ≅ N :=
      ((Classical.choose (Modules.exists_tensorPullbackAdjunction a)).leftAdjointUniq
        (Modules.pullbackPushforwardAdjunction a)).symm.app M ≪≫ (c.app L).symm
    let B := schemeDerivedBaseChangeMap (pullback.snd f k) (pullback.snd f (r ≫ k))
      r a hb ((DerivedCategory.singleFunctor _ 0).obj M) ≫
        (schemeDerivedDirectImage (pullback.snd f (r ≫ k))).map
          (Modules.canonicalSinglePullbackMap a M ≫
            (DerivedCategory.singleFunctor _ 0).map d.hom)
    let p := pullback.snd f (r ≫ k)
    let adj := Classical.choose (exists_schemeDerivedAdjunction p
      (hAdd := (Classical.choose exists_derivedPullbackComposition) p)
      ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) p)
      ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) p))
    exact (adj.homEquiv _ _).symm B

/-- Coefficient pasting for the transposes of base change, with no structure-sheaf
normalization and no test section.
Source: Stacks Project, Tags 08HY and 0D5S.
(blueprint: lem-sc-picard-coefficient-transpose-pasting)

Proof: Write a and a' for the displayed lifts to X_W. Pullback.hom_ext and the
projection equations give j followed by a equal to a'. Expand τ using the
counit formula for the pinned derived adjunction and evaluate the defining
base-change mate. Naturality moves the coefficient comparison through the
counit and the triangle identity cancels the intervening unit. The derived
composition associativity law identifies the two paths around the resulting
rectangle. Evaluate the left-derived composition factorization on L[0];
canonicalSinglePullbackSquare identifies its coefficient comparison with
successive single-pullback comparisons. Uniqueness of left adjoints identifies
the tensor comparison with the conjugate of pushforward composition. These
give exactly d. No single-pullback coefficient map is inverted, so the argument
also applies to zero modules, identity maps and empty schemes. -/
theorem picardCoefficientTranspose_pasting
    {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    {T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
    (h : i ≫ t = t')
    (j : pullback f (t' ≫ k) ⟶ pullback f (t ≫ k))
    (hj₁ : j ≫ pullback.fst f (t ≫ k) = pullback.fst f (t' ≫ k))
    (hj₂ : j ≫ pullback.snd f (t ≫ k) = pullback.snd f (t' ≫ k) ≫ i)
 :
  let τ : ∀ {V : Scheme.{v}} (r : V ⟶ W),
    (derivedPullback (pullback.snd f (r ≫ k))).obj
      ((derivedPullback r).obj
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
              ((Modules.tensorPullback (pullback.fst f k)).obj L)))) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f (r ≫ k)).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f (r ≫ k))).obj L) :=
    picardCoefficientTranspose f L W k
  let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
        ((Modules.tensorPullback (pullback.fst f k)).obj L))
  let C := canonicalDerivedPullbackComposition i t ≪≫
    eqToIso (congrArg (fun q : T' ⟶ W ↦ derivedPullback q) h)
  let N := (Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L
  let c := (conjugateIsoEquiv
    ((Classical.choose (Modules.exists_tensorPullbackAdjunction
      (pullback.fst f (t ≫ k)))).comp
        (Classical.choose (Modules.exists_tensorPullbackAdjunction j)))
    (Classical.choose (Modules.exists_tensorPullbackAdjunction
      (pullback.fst f (t' ≫ k))))).symm
    (Modules.pushforwardComp j (pullback.fst f (t ≫ k)) ≪≫
      Modules.pushforwardCongr hj₁)
  let d := ((Classical.choose (Modules.exists_tensorPullbackAdjunction j)).leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction j)).symm.app N ≪≫ (c.app L).symm
  canonicalDerivedSquareComparison (pullback.snd f (t ≫ k))
      (pullback.snd f (t' ≫ k)) i j hj₂ ((derivedPullback t).obj E) ≫
    (derivedPullback j).map (τ t) ≫ Modules.canonicalSinglePullbackMap j N ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f (t' ≫ k)).toRingedSpace)) 0).map
          d.hom =
    (derivedPullback (pullback.snd f (t' ≫ k))).map (C.hom.app E) ≫ τ t' := by sorry

end
end AlgebraicGeometry.Scheme
