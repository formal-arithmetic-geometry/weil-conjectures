/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.Paper.FiniteOpenProductOperations

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

/-- The two specified external-product chains have the open adjunction unit as
restriction. This asserts only the restriction calculation, not invertibility,
uniqueness, or the signed-swap equality.

Source: Stacks Tag 0GL1, lemma-j-shriek-and-tensor, and the agent-formulated
open-product reduction of blueprint lem-sf-kunneth-coherence.proof.md.
(blueprint: lem-pur-finite-open-product-restriction).

Proof: Write v for leftOpen(a,b,j), w for rightOpen(j a,b,k), and u=w v.
The defining pullback squares identify the restrictions of the first and second
ambient factors with p-star M and q-star N by exactly the two units appearing in
restrictionSource. The normalized beta equation identifies restriction of each
base-change factor with this unit identification. The normalized gamma equation
identifies restriction of each extension-first projection factor with the
corresponding open unit after the inverse unit on its extended argument.
For rho expand its two signed braidings; pullback/braiding compatibility puts
the two braidings next to each other after the gamma equation, and their
composite is identity, so the same normalization holds in extension-second order.
Apply these equations to each factor of comparison. Naturality moves the outer
unit past the inner factor; compatibility of tensorPullIso with pullComp combines
the two tensor comparisons. The defining leftAdjointUniq equation for comp gives
the unit of the composite adjunction after pullComp. The equality w v=u then
identifies this with adj(u).unit. The remaining source identification is precisely
restrictionSource, giving the first displayed equation. Repeat with the other
factorization, v=rightOpen(a,b,k) and w=leftOpen(a,k b,j), using rho first and
gamma second. The same two original open units give exactly the same
restrictionSource, and the compositor equation gives the second displayed
equation. The argument is natural in arbitrary unbounded objects and imposes
no support condition on a single ambient tensor factor. -/
theorem finiteOpenProductRestriction (S : PurityFiniteSetting.{u})
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
        (comparison S.Coefficient a.left b.left j.left k.left M N) =
      (adj S.Coefficient (productOpen a.left b.left j.left k.left)).unit.app
        (tensor S.Coefficient (product (j.left ≫ a.left) (k.left ≫ b.left))
          ((pull S.Coefficient (first (j.left ≫ a.left) (k.left ≫ b.left))).obj M)
          ((pull S.Coefficient (second (j.left ≫ a.left) (k.left ≫ b.left))).obj N))) ∧
    (restrictionSource S.Coefficient a.left b.left j.left k.left M N ≫
      (pull S.Coefficient (productOpen a.left b.left j.left k.left)).map
        (comparisonOp S.Coefficient a.left b.left j.left k.left M N) =
      (adj S.Coefficient (productOpen a.left b.left j.left k.left)).unit.app
        (tensor S.Coefficient (product (j.left ≫ a.left) (k.left ≫ b.left))
          ((pull S.Coefficient (first (j.left ≫ a.left) (k.left ≫ b.left))).obj M)
          ((pull S.Coefficient (second (j.left ≫ a.left) (k.left ≫ b.left))).obj N))) := by
  sorry

end WeilConjectures.FiniteOpenProduct
