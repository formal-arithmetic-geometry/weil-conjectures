/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteOpenProductOperations

/-! # Restriction calculation for finite open product comparisons

Source: Stacks 0GL1, and the open-product signed-symmetry argument of
`lem-sf-kunneth-coherence.proof.md`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization
namespace WeilConjectures.FiniteOpenProduct

/-- The signed conjugate of the transported reversed comparison has the normalized
open restriction. This is a restriction calculation and asserts no equality of
ambient arrows.

Source: Stacks Tag 0GL1 and the agent-formulated signed open-product reduction of
blueprint lem-sf-kunneth-coherence.proof.md.
(blueprint: lem-pur-finite-open-product-swap-restriction).

Proof: Apply the two-open restriction calculation to comparison(b,a,k,j,N,M).
The actual fibre-product symmetries interchange both projections and give the
Cartesian square swapSquare. Expand transportedReverse: inverse swapFactors,
pullback of that reversed comparison, beta for swapSquare, and extension of the
interior swapFactors. Restrict this composite along u. The normalized beta
unit equation moves the reversed open unit through the square to the u-unit.
Naturality of pullComp and tensorPullIso, and their composition compatibility,
cancel the inverse ambient swapFactors with the pullbacks of the reversed
source identifications; the interior swapFactors identify the reversed
projection factors with q-star N and p-star M. Thus this restriction is the
u-unit after the reversed tensor of the same two unit identifications used in
restrictionSource. Pullback respects the signed braiding. Move the exterior
sigma through tensorPullIso and those identifications by naturality, and move
the interior sigma through the u-unit by unit naturality. The two braidings on
the interior tensor are inverse by the symmetric Koszul rule: in degrees r,s
the sign is (-1)^(rs+sr)=1. After cancellation the source identification is
exactly restrictionSource, followed by the u-unit on p-star M tensor q-star N,
which is the displayed equation. All comparisons descend from the same K-flat
maps, so the calculation applies without boundedness or parity restrictions. -/
theorem finiteOpenProductSwapRestriction (S : PurityFiniteSetting.{u})
    (Xb Zb B X Z : Over (Spec (CommRingCat.of S.field.k)))
    [IsSeparated Xb.hom] [LocallyOfFiniteType Xb.hom] [QuasiCompact Xb.hom]
    [IsSeparated Zb.hom] [LocallyOfFiniteType Zb.hom] [QuasiCompact Zb.hom]
    [IsSeparated B.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (a : Xb ⟶ B) (b : Zb ⟶ B)
    [IsSeparated a.left] [LocallyOfFiniteType a.left] [QuasiCompact a.left]
    [IsSeparated b.left] [LocallyOfFiniteType b.left] [QuasiCompact b.left]
    (j : X ⟶ Xb) (k : Z ⟶ Zb) [IsOpenImmersion j.left] [IsOpenImmersion k.left]
    (M : FiniteD S.Coefficient X.left) (N : FiniteD S.Coefficient Z.left) :
    (restrictionSource S.Coefficient a.left b.left j.left k.left M N ≫
      (pull S.Coefficient (productOpen a.left b.left j.left k.left)).map
        (sigma S.Coefficient _ _ _ ≫
        transportedReverse S.Coefficient a.left b.left j.left k.left M N ≫
          (finiteShriek S.Coefficient (productOpen a.left b.left j.left k.left)).map
            (sigma S.Coefficient _ ((pull S.Coefficient
                (second (j.left ≫ a.left) (k.left ≫ b.left))).obj N)
              ((pull S.Coefficient
                (first (j.left ≫ a.left) (k.left ≫ b.left))).obj M))) =
      (adj S.Coefficient (productOpen a.left b.left j.left k.left)).unit.app
        (tensor S.Coefficient (product (j.left ≫ a.left) (k.left ≫ b.left))
          ((pull S.Coefficient (first (j.left ≫ a.left) (k.left ≫ b.left))).obj M)
          ((pull S.Coefficient (second (j.left ≫ a.left) (k.left ≫ b.left))).obj N))) := by
  sorry

end WeilConjectures.FiniteOpenProduct
