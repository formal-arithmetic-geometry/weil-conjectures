/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

/-!
# Exterior pairing induced by a linear map on an open

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph,
exterior and tensor universal properties (blueprint: lem-sc-exterior-tensor-local-pairing).
-/

@[expose] public section

universe v
open CategoryTheory Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- A natural family of linear maps on subopens induces a natural exterior tensor pairing.
Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph, construction
before independence of lifts (blueprint: lem-sc-exterior-tensor-local-pairing).

Proof: Write j for the inclusion of U, V(W)=j(image)(j(preimage)(W))=U ∩ W,
and H=j_*(exteriorSheaf B (r+s)|U). Its sections on W are the exterior-sheaf
sections on V(W), with scalars restricted from W. The equality
j.app W followed by (j.appIso (j(preimage)(W))).inv = O_X(W → V(W))
identifies this scalar action with ordinary restriction.

On V contained in U, multiply exterior-algebra elements after applying
exteriorPower.map to f in the first factor and to t in the second factor.
Products of degree r and degree s lie in degree r+s by pow_add and
Submodule.mul_mem_mul. Compose with the target exterior sheafification unit.
This gives an O_X(V)-bilinear map beta_V from the two exterior presheaf sections.
On pure wedges the formula follows from exteriorPower.map_apply_ιMulti and
ExteriorAlgebra.ιMulti_mul_ιMulti. Check naturality on two pure wedges using
naturality of f, t, and the unit, then extend to both exterior presheaf factors
by span induction using exteriorPower.ιMulti_span.

For any W, first restrict both exterior presheaf inputs to V(W) and apply
beta_V(W). The scalar identity above makes this an O_X(W)-bilinear map into H(W).
It is natural: for Z contained in W, V(Z) is contained in V(W), and the two
composites from V(Z) to W are equal; beta's naturality gives the required equation.
Apply the bilinear sheafification extension theorem and then the sheaf tensor
universal property to obtain phi: exteriorSheaf A r tensor exteriorSheaf C s → H.
For W contained in U the open-restriction adjunction unit from exteriorSheaf B n
has bijective component, since V(W)=W and its component is restriction along
that equality. Compose phi_W with the inverse of this linear equivalence to
get d_W. Naturality of phi and the unit gives naturality of d. Their equations
on the exterior and tensor sheafification units give the displayed formula.
No splitting, exactness, rank, or local freeness is used. Empty blocks give
scalar multiplication in degree zero; empty opens and zero rings obey the
same universal properties. -/
theorem exteriorTensor_local_pairing {X : Scheme.{v}} {A B C : X.Modules}
    (f : A ⟶ B) (r n s : ℕ) (hr : n = r + s) (U : X.Opens)
    (t : ∀ W : X.Opens, W ≤ U →
      C.val.obj (op W) →ₗ[X.presheaf.obj (op W)] B.val.obj (op W))
    (ht : ∀ (W Z : X.Opens) (hW : W ≤ U) (hZW : Z ≤ W) b,
      B.val.map (homOfLE hZW).op (t W hW b) =
        t Z (hZW.trans hW) (C.val.map (homOfLE hZW).op b)) :
    ∃ d : ∀ W : X.Opens, W ≤ U →
      (exteriorSheaf A r ⊗ exteriorSheaf C s).val.obj (op W)
        →ₗ[X.presheaf.obj (op W)] (exteriorSheaf B n).val.obj (op W),
      (∀ W hW (a : Fin r → A.val.obj (op W)) (b : Fin s → C.val.obj (op W)),
        d W hW (tmulSection (exteriorSheafSection A r W a)
          (exteriorSheafSection C s W b)) =
        exteriorSheafSection B n W
          (fun i ↦ Fin.append (fun j ↦ f.val.app (op W) (a j))
            (fun j ↦ t W hW (b j)) (Fin.cast hr i))) ∧
      (∀ (W Z : X.Opens) (hW : W ≤ U) (hZW : Z ≤ W) y,
        (exteriorSheaf B n).val.map (homOfLE hZW).op (d W hW y) =
          d Z (hZW.trans hW)
            ((exteriorSheaf A r ⊗ exteriorSheaf C s).val.map (homOfLE hZW).op y)) := by sorry

end AlgebraicGeometry.Scheme.Modules
