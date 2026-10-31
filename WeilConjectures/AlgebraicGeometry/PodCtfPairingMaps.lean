/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PodCtfAdjunctions

/-! # Canonical projection and fixed-left Hom on the recorded finite-Tor domains

Source: main-20261015, fix-lem-tensor-adjunction.proof.md, Step 1;
thm-pod-identification-of-the-comparison, third paragraph
(blueprint: def-pod-ctf-pairing-maps).

These definitions expose the specified projection and internal Hom independently
of the downstream Hom-chain theorems. All data come from the recorded operations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry Opposite

namespace WeilConjectures.PodCtfPairing
open AlgebraicGeometry.Scheme

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
  (S : SixFunctorOperationDatum D C E n hn) (s : PodCoefficientStage)
  {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
  (R : PodCtfAdjunctionData (PodCoefficientStage.operations S s)
    (PodCoefficientStage.domain S s) (PodCoefficientStage.homPairs (S := S) s)
    (PodCoefficientStage.internalHom (S := S) s) (PodCoefficientStage.tensor S s) f c)

/-- The canonical projection at the four coefficient stages, in the actual partial
finite-Tor tensor coordinates. Source: the fourth bijection of the Hom chain
(blueprint: def-pod-ctf-pairing-maps). -/
def rawProjection
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (T : (PodCoefficientStage.domain S s Y).FullSubcategory) :
    ((PodCoefficientStage.tensor S s Y).obj (R.support.obj M).obj).obj T ⟶
      ((PodCoefficientStage.operations S s).support f c).obj
        (((PodCoefficientStage.tensor S s X).obj M.obj).obj (R.pull.obj T)) := by
  cases s with
  | finite =>
    exact CompactSupportFiniteProjection.component S.toSixFunctorFiniteOperations f c M.obj
      ⟨T.obj.obj, T.property⟩
  | integral =>
    exact compactSupportProjectionComponent S.higher.integralExchange f c M.obj T.obj
  | rational =>
    exact compactSupportProjectionComponent S.higher.rationalExchange f c M.obj T.obj
  | common =>
    exact compactSupportProjectionComponent S.closure.commonStageExchange f c M.obj T.obj

/-- The actual projection isomorphism, supplied by the recorded projection theorem.
Source: fix-prop-projection-formula at the four stages
(blueprint: def-pod-ctf-pairing-maps). -/
def rawProjectionIso
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (T : (PodCoefficientStage.domain S s Y).FullSubcategory) :
    ((PodCoefficientStage.tensor S s Y).obj (R.support.obj M).obj).obj T ≅
      ((PodCoefficientStage.operations S s).support f c).obj
        (((PodCoefficientStage.tensor S s X).obj M.obj).obj (R.pull.obj T)) := by
  cases s with
  | finite =>
    have h := (compactSupportProjectionFormula S).1.isIso f c M.obj
      ⟨T.obj.obj, T.property⟩
    exact @asIso _ _ _ _ (rawProjection S .finite f c R M T) h
  | integral =>
    have h := (compactSupportProjectionFormula S).2.1.isIso f c M.obj T.obj T.property
    exact @asIso _ _ _ _ (rawProjection S .integral f c R M T) h
  | rational =>
    have h := (compactSupportProjectionFormula S).2.2.1.isIso f c M.obj T.obj trivial
    exact @asIso _ _ _ _ (rawProjection S .rational f c R M T) h
  | common =>
    have h := (compactSupportProjectionFormula S).2.2.2.1.isIso f c M.obj T.obj trivial
    exact @asIso _ _ _ _ (rawProjection S .common f c R M T) h

/-- Projection transported through the specified tensor comparisons and full inclusion.
Its direction is C tensor T to f_!(M tensor f^*T).
Source: the fourth bijection and P_T (blueprint: def-pod-ctf-pairing-maps). -/
def projectionIso
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (T : (PodCoefficientStage.domain S s Y).FullSubcategory) :
    (@MonoidalCategory.tensorLeft _ _ R.closedY.closed.monoidal (R.support.obj M)).obj T ≅
      R.support.obj
        ((@MonoidalCategory.tensorLeft _ _ R.closedX.closed.monoidal M).obj
          (R.pull.obj T)) :=
  (PodCoefficientStage.domain S s Y).ι.preimageIso
    ((R.tensorY (R.support.obj M)).app T ≪≫ rawProjectionIso S s f c R M T ≪≫
      ((PodCoefficientStage.operations S s).support f c).mapIso
        ((R.tensorX M).app (R.pull.obj T)).symm)

/-- The specified forward projection map, rather than its inverse.
Source: P_T in the node (blueprint: def-pod-ctf-pairing-maps). -/
def projection
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (T : (PodCoefficientStage.domain S s Y).FullSubcategory) :=
  (projectionIso S s f c R M T).hom

/-- Internal Hom with left input M, using the dependency's restricted Hom functor.
Source: L_N in the Hom chain (blueprint: def-pod-ctf-pairing-maps). -/
def homX (M : (PodCoefficientStage.domain S s X).FullSubcategory) :=
  Prod.sectR (op M) _ ⋙ sixFunctorDomainHom _ _ _
    R.closedX.homPermitted R.closedX.homDomain

/-- Internal Hom on Y with left input C, using the same closed restriction.
Source: B_N in the Hom chain (blueprint: def-pod-ctf-pairing-maps). -/
def homY (K : (PodCoefficientStage.domain S s Y).FullSubcategory) :=
  Prod.sectR (op K) _ ⋙ sixFunctorDomainHom _ _ _
    R.closedY.homPermitted R.closedY.homDomain

end WeilConjectures.PodCtfPairing
