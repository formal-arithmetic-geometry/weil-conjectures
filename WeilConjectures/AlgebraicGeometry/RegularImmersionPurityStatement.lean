/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalTateCoprojectionCoherence
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import Mathlib.FieldTheory.Perfect
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteExceptionalComposition
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionIso
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionProduct
public import WeilConjectures.EtaleCohomology.TateTwist.Normalized
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.RegularDualizingTwistCancellation

/-! # Signed and canonical regular-immersion purity

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/
sec-the-trace-map-in-top-degree/sk-cor-trace/sk-thm-regular/_section.md, clauses (b)--(c),
and sk-thm-regular.proof.md in the same directory, Steps 1--4
(blueprint: sk-thm-regular).

The existing proved declarations supply concentration, unique frame gluing, generation,
etale restriction, and exterior products. Only the missing signed and canonical parts
are stated here. The smooth orientations satisfy the published diagonal/Rees normalization;
they are not arbitrary choices of rank-one isomorphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [NeZero (ringChar Λ)]

/-- The canonical rank-one root-line comparison, shifted by two. Both sides are scalar
extension of the same roots-of-unity sheaf. No trivialization is chosen.
Source: the coefficient convention in Step 1 (blueprint: sk-thm-regular). -/
noncomputable def regularTateLineComparison (T : Scheme.{u}) [HasInvertibleExponent Λ T] :
    shiftedTateObject Λ T 1 ≅
      (ordinaryFiniteLine Λ (ringChar Λ) ringChar.Nat.cast_ringChar T)⟦(2 : ℤ)⟧ := by
  let N := ringChar Λ
  let hA : (N : Λ) = 0 := ringChar.Nat.cast_ringChar
  let scalarIso : ModuleCat.extendScalars (Scheme.finiteEtaleTwistScalar N Λ hA) ≅
      forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat ⋙
        ModuleCat.extendScalarsAddCommGrp Λ := by
    let f := Scheme.finiteEtaleTwistScalar N Λ hA
    let adj := ModuleCat.extendScalarsAddCommGrpAdj Λ
    let e (M : ModuleCat.{u + 1} (ZMod N)) (P : ModuleCat.{u + 1} Λ) :
        ((forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat).obj M ⟶
            (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat).obj P) ≃
          (M ⟶ (ModuleCat.restrictScalars f).obj P) :=
      { toFun := fun g ↦ ModuleCat.ofHom (X := M) (Y := (ModuleCat.restrictScalars f).obj P)
          (AddMonoidHom.toZModLinearMap N (M := M)
            (M₁ := (ModuleCat.restrictScalars f).obj P) g.hom)
        invFun := fun g ↦ AddCommGrpCat.ofHom g.hom.toAddMonoidHom
        left_inv := fun g ↦ rfl
        right_inv := fun g ↦ by ext; rfl }
    let adj' : (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat ⋙
        ModuleCat.extendScalarsAddCommGrp Λ) ⊣ ModuleCat.restrictScalars f :=
      Adjunction.mkOfHomEquiv
        { homEquiv := fun M P ↦ (adj.homEquiv _ _).trans (e M P)
          homEquiv_naturality_left_symm := by
            intro M' M P g k
            change (adj.homEquiv _ _).symm
              ((forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat).map g ≫
                (e M P).symm k) = _
            exact adj.homEquiv_naturality_left_symm _ _
          homEquiv_naturality_right := by
            intro M P P' g k
            change e M P' (adj.homEquiv _ _ (g ≫ k)) = _
            rw [adj.homEquiv_naturality_right]
            rfl }
    exact (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} f).leftAdjointUniq adj'
  let lineIso : Scheme.finiteEtaleTateLine T N Λ hA ≅
      (extendScalars Λ T).obj (T.rootsOfUnitySheaf N) :=
    (presheafToSheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapIso
      (Functor.isoWhiskerLeft (Scheme.finiteEtaleMuModulePresheaf T N) scalarIso)
  let e : tateObject Λ T 1 ≅
      ordinaryFiniteLine Λ (ringChar Λ) ringChar.Nat.cast_ringChar T :=
    tateTwistObjectIsoSingleFunctor Λ T 1 ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso
        (tateTwistSheafOneIso T Λ ≪≫
          lineIso.symm)
  exact (shiftFunctor _ (2 : ℤ)).mapIso e

/-- The ordered tensor comparison from the Tate datum to the published finite root model.
The empty product is the coefficient unit; successors use Tate addition and the canonical
rank-one root comparison. This fixes every scalar in the orientation normalization.
Source: the coefficient convention in Steps 1--2 (blueprint: sk-thm-regular). -/
noncomputable def regularTatePowerComparison (T : Scheme.{u}) [HasInvertibleExponent Λ T] :
    (d : ℕ) → shiftedTateObject Λ T d ≅
      FiniteSmoothPurity.line Λ (ringChar Λ) ringChar.Nat.cast_ringChar T d
  | 0 => shiftedTateZeroIso Λ T ≪≫
      (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) T).symm
  | d + 1 =>
      eqToIso (by simp only [shiftedTateObject, Nat.cast_add, Nat.cast_one]) ≪≫
        (shiftTateObjectAddIso Λ T (d : ℤ) 1).symm ≪≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) T).mapIso
          (regularTatePowerComparison T d)).app _ ≪≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) T).obj _).mapIso
          (regularTateLineComparison Λ T)

/-- The existing diagonal/Rees normalization expressed in the upstream Tate datum.
The transport is the canonical ordered root comparison, not a free coefficient isomorphism.
Source: Step 1, the specified smooth-purity orientations (blueprint: sk-thm-regular). -/
def regularSmoothOrientationNormalized {k : Type u} [Field k]
    (T : Scheme.{u}) [HasInvertibleExponent Λ T]
    (aT : T ⟶ Spec (.of k)) [Smooth aT] [IsSeparated aT] [QuasiCompact aT]
    [HasCompactification aT] (d : ℕ)
    (P : dualizingComplex Λ aT ≅ shiftedTateObject Λ T d) : Prop :=
  letI : IsNoetherian T := isNoetherian_of_locallyOfFiniteType aT
  ∃ G : FiniteRingSectionDeformation.Geometry d
      (pullback.fst aT aT) (pullback.diagonal aT),
    ∃ hT : IsUnit (ringChar Λ : Γ(T, ⊤)),
      FiniteSmoothPurity.OrientationNormalized Λ (ringChar Λ)
        (Nat.pos_of_ne_zero (NeZero.ne (ringChar Λ))) ringChar.Nat.cast_ringChar
        aT d G hT (P ≪≫ regularTatePowerComparison Λ T d)

/-- The specified untwisted class is invertible, not merely isomorphic to some object.
Together with the proved `isIso_homology_zero_map_fundamentalClassMap` (generation), this
states the canonical untwisted part of clauses (b)--(c).
Source: sk-thm-regular.md, clause (c) (blueprint: sk-thm-regular).
Proof: the glued frame-class map is invertible by the coordinate comparison in Step 4.
Tensor it with the inverse shifted Tate object. Co-projection, associativity, evaluation,
and unitors identify the resulting map with `regularImmersionUntwistedClass`. Each factor
is invertible. Its inverse is precisely the canonical untwisted purity map. -/
theorem isIso_regularImmersionUntwistedClass {X Z : Scheme.{u}}
    [HasInvertibleExponent Λ X] (c : ℕ) (i : Z ⟶ X) [IsRegularImmersion c i]
    {k : Type u} [Field k] [PerfectField k]
    (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    IsIso (regularImmersionUntwistedClass Λ c i aX hZ) := by
  let : HasInvertibleExponent Λ Z := .of_hom i
  have := isIso_fundamentalClassMap Λ c i aX hZ
  have : IsIso (shiftedTateEvaluation Λ Z (c : ℤ)) := by
    unfold shiftedTateEvaluation
    infer_instance
  unfold regularImmersionUntwistedClass
  infer_instance

end AlgebraicGeometry.Etale
