/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q99
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
import WeilConjectures.AlgebraicGeometry.AmpleIso

/-! # Restriction of an invertible pullback twist to an open subscheme

Source: Stacks Project, Morphisms, Tag 0C4K; Modules, Tags 01CD, 0B8L, 01CT;
Sheaves, Tag 0097 (blueprint: lem-sfb-invertible-twist-open-restriction).

The existing tensor powers and canonical tensor/power comparisons are used throughout.
The library represents powers by `M tensor (M tensor (... tensor O))`; associators and
unitors identify this with the positive-power convention in the node.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Restrict the twist using, in order, the tensor comparison, the successive-pullback
comparison around the open square, and the power comparison. No choice of an arbitrary
isomorphism is made. The power comparison has the canonical structure-module comparison
in degree zero.
Source: Stacks, Tags 0C4K, 01CD, 0097
(blueprint: lem-sfb-invertible-twist-open-restriction). -/
noncomputable def invertibleTwistOpenRestrictionIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : X.Modules) (M : Y.Modules) (a : ℕ) (U : Y.Opens) :
    (tensorPullback (f ⁻¹ᵁ U).ι).obj (L ⊗ (tensorPullback f).obj (M.tensorPow a)) ≅
      (tensorPullback (f ⁻¹ᵁ U).ι).obj L ⊗
        (tensorPullback (f ∣_ U)).obj (((tensorPullback U.ι).obj M).tensorPow a) :=
  boundaryPullbackTensorIso (f ⁻¹ᵁ U).ι L ((tensorPullback f).obj (M.tensorPow a)) ≪≫
    (Iso.refl _ ⊗ᵢ
      (((tensorPullbackSectionComp (f ⁻¹ᵁ U).ι f).app (M.tensorPow a)).symm ≪≫
        eqToIso (congrArg (fun h => (tensorPullback h).obj (M.tensorPow a))
          (morphismRestrict_ι f U).symm) ≪≫
        (tensorPullbackSectionComp (f ∣_ U) U.ι).app (M.tensorPow a) ≪≫
        (tensorPullback (f ∣_ U)).mapIso (boundaryPullbackPowIso U.ι M a)))

/-- The degree-zero power comparison is the map adjoint to the structure-sheaf map.
In the tensor description it is `b tensor c` mapping to `b * h sharp(c)`;
its inverse sends `b` to `b tensor 1`, also for `h = f |_ U` and `h = U.ι`.
Source: Stacks, Tags 0096, 0097 and 01CD
(blueprint: lem-sfb-invertible-twist-open-restriction).

Proof: expand the degree-zero branch of `boundaryPullbackPowIso`. The comparison with
Mathlib pullback is the unique isomorphism compatible with the normalized adjunction
units, so the composite is adjoint to the same structure map as
`tensorPullbackObjUnitToUnit`. The adjunction bijection identifies the maps. In the tensor
formula the map multiplies `b` by the image of `c`; insertion of one is its inverse
because the balancing relation identifies `b * h sharp(c) tensor 1` with `b tensor c`.
These formulas commute with restriction and hence descend through sheafification. -/
theorem invertibleTwistOpenRestriction_power_zero {V W : Scheme.{u}} (h : V ⟶ W)
    (M : W.Modules) :
    (boundaryPullbackPowIso h M 0).hom = tensorPullbackObjUnitToUnit h := by
  let adj := Classical.choose (exists_tensorPullbackAdjunction h)
  change ((boundaryPullbackComparison h).app _).hom ≫ (pullbackObjUnitIso h).hom = _
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_right]
  rw [show ((boundaryPullbackComparison h).app _).hom =
    (adj.leftAdjointUniq (pullbackPushforwardAdjunction h)).hom.app _ from rfl]
  rw [adj.homEquiv_leftAdjointUniq_hom_app]
  exact (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    h.toRingCatSheafHom).trans ((adj.homEquiv _ _).apply_symm_apply _).symm

/-- Tensor powers, their pullbacks and the twists are invertible. On every inverse-image
open, the specified restriction isomorphism identifies the two twists, and they are ample
simultaneously. There are no quasi-compactness, affineness, finite-type or ampleness
assumptions on the morphism or open.
Source: Stacks, Tags 0C4K, 01CD, 0B8L, 01CT, 0097 and 01PS
(blueprint: lem-sfb-invertible-twist-open-restriction).

Proof: induct on the exponent, using invertibility of the structure module in degree
zero and the tensor clause of `lem-weil-pbc-invertible-pullback-tensor` at each successor.
Its pullback clause then gives invertibility of the pulled-back power and of its tensor
with L, and likewise of the two restricted modules. The structure comparison is
multiplication with inverse insertion of one, as in
`lem-weil-pbc-module-pullback-structure-sheaf` and the preceding zero-degree statement.
Inductively the power comparison is the pullback tensor comparison followed by the
identity on the first factor tensored with the previous power comparison. Compose the
tensor comparison along j, the inverse successive-pullback comparison along j and f,
the equality j followed by f = f_U followed by k, the successive-pullback comparison
along f_U and k, and the pullback of the power comparison along k. This is exactly
`invertibleTwistOpenRestrictionIso`. Finally apply `lem-sc-ample-iso` to this isomorphism
on the single scheme f inverse U. No preservation of ampleness by arbitrary restriction
is used. The construction includes exponent zero and empty opens or schemes. -/
theorem invertible_twist_open_restriction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : X.Modules) (M : Y.Modules) [L.IsInvertible] [M.IsInvertible] (a : ℕ) :
    (M.tensorPow a).IsInvertible ∧
      ((tensorPullback f).obj (M.tensorPow a)).IsInvertible ∧
      (L ⊗ (tensorPullback f).obj (M.tensorPow a)).IsInvertible ∧
      ∀ U : Y.Opens,
        ∃ hleft : ((tensorPullback (f ⁻¹ᵁ U).ι).obj
            (L ⊗ (tensorPullback f).obj (M.tensorPow a))).IsInvertible,
        ∃ hright : ((tensorPullback (f ⁻¹ᵁ U).ι).obj L ⊗
            (tensorPullback (f ∣_ U)).obj
              (((tensorPullback U.ι).obj M).tensorPow a)).IsInvertible,
        ∃ e : (tensorPullback (f ⁻¹ᵁ U).ι).obj
            (L ⊗ (tensorPullback f).obj (M.tensorPow a)) ≅
          (tensorPullback (f ⁻¹ᵁ U).ι).obj L ⊗
            (tensorPullback (f ∣_ U)).obj (((tensorPullback U.ι).obj M).tensorPow a),
          e = invertibleTwistOpenRestrictionIso f L M a U ∧
          (@IsAmple (f ⁻¹ᵁ U).toScheme
              ((tensorPullback (f ⁻¹ᵁ U).ι).obj
                (L ⊗ (tensorPullback f).obj (M.tensorPow a))) hleft ↔
            @IsAmple (f ⁻¹ᵁ U).toScheme
              ((tensorPullback (f ⁻¹ᵁ U).ι).obj L ⊗
                (tensorPullback (f ∣_ U)).obj
                  (((tensorPullback U.ι).obj M).tensorPow a)) hright) := by
  have hpull : ∀ {V W : Scheme.{u}} (h : V ⟶ W) (N : W.Modules)
      [N.IsInvertible], ((tensorPullback h).obj N).IsInvertible := by
    intro V W h N _
    exact IsInvertible.of_iso ((boundaryPullbackComparison h).app N).symm
  have hpow : (M.tensorPow a).IsInvertible := inferInstance
  have hp : ((tensorPullback f).obj (M.tensorPow a)).IsInvertible :=
    hpull f (M.tensorPow a)
  have htwist : (L ⊗ (tensorPullback f).obj (M.tensorPow a)).IsInvertible :=
    inferInstance
  refine ⟨hpow, hp, htwist, ?_⟩
  intro U
  have hleft : ((tensorPullback (f ⁻¹ᵁ U).ι).obj
      (L ⊗ (tensorPullback f).obj (M.tensorPow a))).IsInvertible := hpull _ _
  have hright : ((tensorPullback (f ⁻¹ᵁ U).ι).obj L ⊗
      (tensorPullback (f ∣_ U)).obj
        (((tensorPullback U.ι).obj M).tensorPow a)).IsInvertible :=
    IsInvertible.of_iso (invertibleTwistOpenRestrictionIso f L M a U)
  exact ⟨hleft, hright, invertibleTwistOpenRestrictionIso f L M a U, rfl,
    isAmple_iff_of_iso (invertibleTwistOpenRestrictionIso f L M a U)⟩

end AlgebraicGeometry.Scheme.Modules
