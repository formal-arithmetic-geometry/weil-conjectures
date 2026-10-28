/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.VectorTraceGeometry
public import Sheaf.AlgebraicGeometry.AffineLinearTraceAction

/-! # Comparing two vector-bundle frames after arbitrary base change

(blueprint: lem-pur-vector-integration-base-change-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The two inverse frames over a common base differ by an invertible linear map.
This is an equality of scheme maps, with no coefficient ring, compact support,
Tate transport, projective-line datum, or counit.
Source: blueprint sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md,
paragraph 2, base change and independence of the frame; the symmetric-algebra
construction and coordinate convention of def-asd-vector-bundle-zero-section.
(blueprint: lem-pur-vector-integration-base-change-coordinates).

Proof: pull the source frame along g and the target frame along a, using the free
module comparison for tensor pullback. The equality j f = g V.ι and a U.ι = j,
together with composition of module pullback, identify their modules over W.
Their composite is an automorphism of the rank-r free module. Its images of the
standard basis, and those of its inverse, give inverse matrices over Gamma(W,O_W).
This requires no affine hypothesis: maps out of the free sheaf are determined by
its standard global basis sections. In the convention e'_j = sum_i G_ij e_i,
the forward coordinate change is the transpose of G; take its inverse for the
inverse charts. Check the asserted equality on each degree-one generator of Sym(F).
The baseChange map takes generators to the module pullback unit, so both composites
have exactly the prescribed linear image. The symmetric-algebra universal property
and relative Spec identify the scheme maps. The coordinate-tower comparison converts
the polynomial substitution to affineTraceLinearMap. At rank zero the matrices
are empty and the equality is the equality of structural maps; for empty W the
same free-module and generator argument applies without a nonemptiness assumption.
-/
theorem vectorIntegration_baseChange_coordinates
    {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (f : T ⟶ S) (r : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank r]
    (V : S.Opens) (eS : VectorBundleZeroSection.Trivialization S r F V)
    (U : T.Opens)
    (eT : VectorBundleZeroSection.Trivialization T r
      ((Scheme.Modules.tensorPullback f).obj F) U)
    (W : Scheme.{u}) (j : W ⟶ T) (a : W ⟶ U.toScheme) (g : W ⟶ V.toScheme)
    (ha : a ≫ U.ι = j) (hg : j ≫ f = g ≫ V.ι) :
    ∃ H : Matrix.GeneralLinearGroup (Fin r) Γ(W, ⊤),
      (affineTraceMap a r ≫ vectorIntegrationChart T r
        ((Scheme.Modules.tensorPullback f).obj F) U eT) ≫
          VectorTraceGeometry.baseChange f r F =
        affineTraceLinearMap W r H ≫
          (affineTraceMap g r ≫ vectorIntegrationChart S r F V eS) := by sorry

end AlgebraicGeometry.Etale
