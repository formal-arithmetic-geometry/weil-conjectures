/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.PicardOrdinaryModelCycles
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.PicardDerivedModelSections
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf

/-! # Raw scalar coordinates and differential formulas

Source: Stacks Project, Tags 0BF2, 01I7, 01IB and 0096.
(blueprint: lem-sc-picard-ordinary-raw-coordinates)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Affine bases give raw morphism coordinates compatible with residue restriction.
Unlike cycle lifting, this calculation does not assume that the coefficients vanish
at the residue point or that a scalar annihilates them.
Source: Stacks Project, Tag 0BF2, degree-zero calculation; Tags 01I7, 01IB and 0096.
(blueprint: lem-sc-picard-ordinary-raw-coordinates)

Proof: Strict perfectness makes the two terms retracts of finite free sheaves,
hence quasi-coherent. The affine tilde/Gamma equivalence on U sheafifies e0 and e1.
Faithfulness identifies the differential in these bases with multiplication by d,
because its map on sections is hd. Restrict these bases to V and tensor them to
Spec κ(w). The tensor-unit comparison identifies the pulled-back source with the
structure sheaf. Maps from that sheaf are global sections, giving additive
coordinates c and c1 on V and b and b1 at the residue point. In the target basis,
postcomposition
by the differential has coordinates c(f) times d restricted to V, or b(f) times
the evaluated vector d at the residue point. Since the target basis is injective,
the differential formulas follow. Finally the structure-sheaf map of the residue
lift is evaluation. Naturality of tensor pullback, the unit
comparison and the conjugate composition comparisons in the pinned adjunction
therefore gives hres. None of this needs V affine: the bases are sheaf bases
restricted from U. For m=0 the target sheaf and the coordinate vector are both
zero, so the same kernel formulas apply. -/
theorem picard_ordinary_raw_coordinates
    (W : Scheme.{v}) (w : W)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (m : ℕ) (d : Fin m → Γ(W, U))
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (e0 : (K.X 0).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] Γ(W, U))
    (e1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] (Fin m → Γ(W, U)))
    (hd : ∀ a : Γ(W, U), e1 ((K.d 0 1).val.app (.op (Over.mk (𝟙 U))) (e0.symm a)) = a • d) :
    let p := picardResidueLift W w U hwU
    ∃ (b : ((Modules.tensorPullback (W.fromSpecResidueField w)).obj
        (SheafOfModules.unit (moduleRings W.toRingedSpace)) ⟶
          (Modules.tensorPullback p).obj ((Modules.overEquiv U).functor.obj (K.X 0))) ≃+
            W.residueField w)
      (b1 : ((Modules.tensorPullback (W.fromSpecResidueField w)).obj
        (SheafOfModules.unit (moduleRings W.toRingedSpace)) ⟶
          (Modules.tensorPullback p).obj ((Modules.overEquiv U).functor.obj (K.X 1))) ≃+
            (Fin m → W.residueField w))
      (c : ∀ (V : W.Opens) (hVU : V ≤ U),
        ((Modules.tensorPullback V.ι).obj
          (SheafOfModules.unit (moduleRings W.toRingedSpace)) ⟶
            (Modules.tensorPullback (W.homOfLE hVU)).obj
              ((Modules.overEquiv U).functor.obj (K.X 0))) ≃+ Γ(W, V))
      (c1 : ∀ (V : W.Opens) (hVU : V ≤ U),
        ((Modules.tensorPullback V.ι).obj
          (SheafOfModules.unit (moduleRings W.toRingedSpace)) ⟶
            (Modules.tensorPullback (W.homOfLE hVU)).obj
              ((Modules.overEquiv U).functor.obj (K.X 1))) ≃+ (Fin m → Γ(W, V))),
      (∀ f, b1 (f ≫ (Modules.tensorPullback p).map
          ((Modules.overEquiv U).functor.map (K.d 0 1))) =
        b f • (fun i ↦ W.evaluation U w hwU (d i))) ∧
      (∀ (V : W.Opens) (hVU : V ≤ U) f,
        c1 V hVU (f ≫ (Modules.tensorPullback (W.homOfLE hVU)).map
          ((Modules.overEquiv U).functor.map (K.d 0 1))) =
        c V hVU f • (fun i ↦ W.presheaf.map (homOfLE hVU).op (d i))) ∧
      ∀ (V : W.Opens) (hwV : w ∈ V) (hVU : V ≤ U)
        (hs : picardResidueLift W w V hwV ≫ W.homOfLE hVU = p) f,
        b (picardOrdinaryModelRestriction W U K (picardResidueLift W w V hwV)
          V.ι (W.fromSpecResidueField w) (W.homOfLE hVU) p
          (picardResidueLift_comp W w V hwV) hs f) =
            W.evaluation V w hwV (c V hVU f) := by sorry

end AlgebraicGeometry.Scheme
