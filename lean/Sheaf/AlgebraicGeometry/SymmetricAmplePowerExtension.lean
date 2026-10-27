/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q157
-/
module

public import Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import Sheaf.AlgebraicGeometry.SchemeRelativeAmpleBaseChange

/-! # Ample extensions of powers of symmetric lines

Source: Raynaud, Faisceaux amples, XI Theorem 1.13; Moret-Bailly, Pinceaux de
varietes abeliennes, VI Proposition 3.1, connected-fibre case. The normal semiabelian
formulation and local rigidification are the agent formulation in the DAG; the local
originals are WANTED. (blueprint: lem-sfb-symmetric-ample-power-extension)

The auxiliary maps spell out the induced rigidifications of tensor powers and open
restrictions. The extension is existential, and is not supplied as input.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj

namespace AlgebraicGeometry

/-- The rigidification on a tensor power, using tensor pullback and unit multiplication.
Source: Raynaud XI 1.13, rigidified power in the local extension assertion
(blueprint: lem-sfb-symmetric-ample-power-extension). -/
def amplePowerRigidification {X S : Scheme.{u}} (e : S ⟶ X) (M : X.Modules)
    (r : (Scheme.Modules.tensorPullback e).obj M ≅ 𝟙_ S.Modules) :
    (n : ℕ) → (Scheme.Modules.tensorPullback e).obj (M.tensorPow n) ≅ 𝟙_ S.Modules
  | 0 => Scheme.Modules.boundaryPullbackPowIso e M 0
  | n + 1 => Scheme.Modules.boundaryPullbackTensorIso e M (M.tensorPow n) ≪≫
      (r ⊗ᵢ amplePowerRigidification e M r n) ≪≫ (λ_ _)

/-- The canonical restriction from the group over V to the group over U, for U contained
in V. Source: Raynaud XI 1.13, overlap in the local extension assertion
(blueprint: lem-sfb-symmetric-ample-power-extension). -/
abbrev amplePowerOpenMap {X S : Scheme.{u}} (f : X ⟶ S) {U V : S.Opens} (h : U ≤ V) :
    pullback f U.ι ⟶ pullback f V.ι :=
  baseChangeMap f (Over.homMk (U := Over.mk U.ι) (V := Over.mk V.ι)
    (S.homOfLE h) (S.homOfLE_ι h))

/-- Restrict the specified rigidification using the canonical composition comparisons
and the compatibility of base-changed identity sections. Source: Raynaud XI 1.13,
rigidification-preserving comparison on the overlap
(blueprint: lem-sfb-symmetric-ample-power-extension). -/
def amplePowerOpenRigidification {X S : Scheme.{u}} (f : X ⟶ S)
    (e : S ⟶ X) (he : e ≫ f = 𝟙 S) {U V : S.Opens} (h : U ≤ V)
    (L : (pullback f V.ι).Modules)
    (r : (Scheme.Modules.tensorPullback
      (sectionBaseChange f e he (Over.mk V.ι))).obj L ≅ 𝟙_ V.toScheme.Modules) :
    (Scheme.Modules.tensorPullback (sectionBaseChange f e he (Over.mk U.ι))).obj
      ((Scheme.Modules.tensorPullback (amplePowerOpenMap f h)).obj L) ≅
        𝟙_ U.toScheme.Modules :=
  ((Scheme.Modules.tensorPullbackSectionComp
    (sectionBaseChange f e he (Over.mk U.ι)) (amplePowerOpenMap f h)).app L).symm ≪≫
  eqToIso (congrArg (fun a ↦ (Scheme.Modules.tensorPullback a).obj L)
    (sectionBaseChange_comp_baseChangeMap f e he
      (Over.homMk (U := Over.mk U.ι) (V := Over.mk V.ι)
        (S.homOfLE h) (S.homOfLE_ι h)))) ≪≫
  (Scheme.Modules.tensorPullbackSectionComp (S.homOfLE h)
    (sectionBaseChange f e he (Over.mk V.ι))).app L ≪≫
  (Scheme.Modules.tensorPullback (S.homOfLE h)).mapIso r ≪≫
  Scheme.Modules.boundaryPullbackPowIso (S.homOfLE h) (𝟙_ V.toScheme.Modules) 0

/-- A positive tensor power of a symmetric rigidified relatively ample line on the
abelian dense open extends, on an affine open covering of the normal integral Noetherian
affine base, to a relatively ample rigidified line. The overlap isomorphism preserves
exactly the input rigidification, raised to that tensor power. Each extension is also
absolutely ample because its base is affine.

Source: Raynaud XI Theorem 1.13; Moret-Bailly VI Proposition 3.1, connected-fibre case;
normal semiabelian formulation and local rigidification as in the DAG (originals WANTED).
(blueprint: lem-sfb-symmetric-ample-power-extension)

Proof plan:
1. Apply lem-sfb-semiabelian-cubical-rigidification(a) on the proper abelian open
   to give M its unique cubical structure compatible with the prescribed rigidification.
2. Apply lem-sfb-normal-symmetric-cubical-extension over T. Normality, integrality,
   Noetherianity, semiabelian fibres, density and symmetry are exactly the hypotheses.
   Obtain a cubical rigidified line B on H and a rigidified comparison with M.
3. The generic point lies in V. Apply lem-trf-scheme-relative-ample-base-change to
   the generic point to get ampleness of M there. The comparison identifies this
   with B on the generic fibre. The fibre is proper by lem-weil-pbc-proper-base-change.
4. Apply lem-sfb-normal-cubical-generic-ampleness to B: it is relatively ample.
5. Use the one-member affine cover T, exponent 1 and B. Tensor-unit and restriction
   comparisons give the displayed rigidified overlap isomorphism. Relative ampleness
   on the affine open T itself gives absolute ampleness. -/
theorem symmetricAmplePowerExtension
    {T : Scheme.{u}} [IsAffine T] [IsIntegral T] [IsLocallyNoetherian T]
    (hT : ∀ t : T, IsDomain (T.presheaf.stalk t) ∧
      IsIntegrallyClosed (T.presheaf.stalk t))
    (H : Grp (Over T)) [IsCommMonObj H.X]
    [Smooth H.X.hom] [IsSeparated H.X.hom]
    [LocallyOfFinitePresentation H.X.hom] [QuasiCompact H.X.hom]
    (hH : HasSemiabelianGeometricFibres H)
    (V : T.Opens) (hV : Dense (V : Set T))
    [IsProper (pullback.snd H.X.hom V.ι)]
    (M : (pullback H.X.hom V.ι).Modules) [M.IsInvertible]
    (r : (Scheme.Modules.tensorPullback
      (sectionBaseChange H.X.hom η[H.X].left (Over.w η[H.X]) (Over.mk V.ι))).obj M ≅
        𝟙_ V.toScheme.Modules)
    (symmetry : (Scheme.Modules.tensorPullback
      ι[((Over.pullback V.ι).mapGrp.obj H).X].left).obj M ≅ M)
    (hM : ∀ A : V.toScheme.Opens, IsAffineOpen A →
      ∃ h : ((Scheme.Modules.tensorPullback
          ((pullback.snd H.X.hom V.ι) ⁻¹ᵁ A).ι).obj M).IsInvertible,
        @Scheme.Modules.IsAmple _ ((Scheme.Modules.tensorPullback
          ((pullback.snd H.X.hom V.ι) ⁻¹ᵁ A).ι).obj M) h) :
    ∃ (I : Type u) (W : I → T.Opens), (⨆ i, W i) = ⊤ ∧
      (∀ i, IsAffineOpen (W i)) ∧
      ∀ i, Nonempty (W i) → ∃ n : ℕ, 1 ≤ n ∧
        ∃ (B : (pullback H.X.hom (W i).ι).Modules) (hB : B.IsInvertible),
          (∀ A : (W i).toScheme.Opens, IsAffineOpen A →
            ∃ h : ((Scheme.Modules.tensorPullback
                ((pullback.snd H.X.hom (W i).ι) ⁻¹ᵁ A).ι).obj B).IsInvertible,
              @Scheme.Modules.IsAmple _ ((Scheme.Modules.tensorPullback
                ((pullback.snd H.X.hom (W i).ι) ⁻¹ᵁ A).ι).obj B) h) ∧
          @Scheme.Modules.IsAmple _ B hB ∧
          ∃ rB : (Scheme.Modules.tensorPullback
              (sectionBaseChange H.X.hom η[H.X].left (Over.w η[H.X])
                (Over.mk (W i).ι))).obj B ≅ 𝟙_ (W i).toScheme.Modules,
          ∃ α : (Scheme.Modules.tensorPullback
              (amplePowerOpenMap H.X.hom (inf_le_right : V ⊓ W i ≤ W i))).obj B ≅
            (Scheme.Modules.tensorPullback
              (amplePowerOpenMap H.X.hom (inf_le_left : V ⊓ W i ≤ V))).obj
                (M.tensorPow n),
            (Scheme.Modules.tensorPullback
                (sectionBaseChange H.X.hom η[H.X].left (Over.w η[H.X])
                  (Over.mk (V ⊓ W i).ι))).map α.hom ≫
              (amplePowerOpenRigidification H.X.hom η[H.X].left (Over.w η[H.X])
                (inf_le_left : V ⊓ W i ≤ V) (M.tensorPow n)
                (amplePowerRigidification
                  (sectionBaseChange H.X.hom η[H.X].left (Over.w η[H.X]) (Over.mk V.ι))
                  M r n)).hom =
              (amplePowerOpenRigidification H.X.hom η[H.X].left (Over.w η[H.X])
                (inf_le_right : V ⊓ W i ≤ W i) B rB).hom := by
  sorry

end AlgebraicGeometry
