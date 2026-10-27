/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Connected.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Rigidity of connected algebraic group actions on tori

Source: Milne, Algebraic Groups (2017), Theorem 12.36 and Corollary 12.37,
printed pp.243--244 (blueprint: lem-sfb-connected-action-torus-rigidity).

The action is an internal action on the underlying scheme of the torus.
Multiplication preservation is tested on all algebra-valued points. Together with
its action laws this says that each group element acts by a group automorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped MonObj

namespace AlgebraicGeometry

/-- An action by group automorphisms of a smooth geometrically connected affine
algebraic group on a torus is the second projection.

Source: Milne, Algebraic Groups (2017), Theorem 12.36 and Corollary 12.37,
printed pp.243--244 (blueprint: lem-sfb-connected-action-torus-rigidity).

Proof:
1. Extend scalars to the algebraic closure. Equality descends because
   lem-sfb-field-extension-tensor-injective makes the coefficient extension
   injective; def-weil-affine-spectrum and
   lem-weil-pbc-fibre-product-affine-spectra translate this into equality of
   the original affine morphisms. Use the torus splitting to identify the
   target with a product of copies of G_m. The parameter scheme is connected
   and has the identity as a rational point.
2. Restrict the action to every finite subgroup (mu_n)^d. By
   lem-sfb-finite-torsion-hom-parameter its family of homomorphisms is classified
   by a map to a finite constant scheme. Connectedness forces this map into
   one component, and its value at the identity forces it to classify the
   inclusion. Thus the restricted action is the projection, including when
   the characteristic divides n.
3. Write B for the parameter scheme's coordinate ring. By
   lem-weil-pbc-fibre-product-affine-spectra and
   lem-weil-pbc-algebra-tensor-pushout-universal-property the source ring is
   B[t_1^{+-1},...,t_d^{+-1}], and the torsion restrictions are its quotients
   by (t_1^n-1,...,t_d^n-1). The coordinate identifications send each pure
   tensor b tensor t^v to b t^v; their inverses send a finite sum to the sum
   of the corresponding pure tensors. The pullbacks of every target function
   agree in all these quotients by step 2.
4. Apply lem-sfb-torus-torsion-joint-injectivity to deduce equality of the two
   coordinate maps. The affine spectrum correspondence gives equality of
   the action and projection after scalar extension, and step 1 descends it.
   Evaluating this equality gives a(g,t)=t for every algebra and every pair
   of algebra-valued points. -/
theorem connected_action_torus_rigidity {k : Type u} [Field k]
    (G T : Grp (Over (Spec (.of k))))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [IsAffine T.X.left] [LocallyOfFiniteType T.X.hom] [QuasiCompact T.X.hom]
    [Smooth G.X.hom]
    (hG : ConnectedSpace
      ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj G).X.left)
    (hT : MultiplicativeType.IsTorus T) [a : ModObj G.X T.X]
    (hhom : ∀ (A : CommAlgCat.{u} k)
      (g : (algSpec (.of k)).obj (op A) ⟶ G.X)
      (t₁ t₂ : (algSpec (.of k)).obj (op A) ⟶ T.X),
      g • (t₁ * t₂) = (g • t₁) * (g • t₂)) :
    a.smul = CartesianMonoidalCategory.snd G.X T.X := by
  sorry

end AlgebraicGeometry
