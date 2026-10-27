/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q102
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
public import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LineEvaluationInversePair
import Sheaf.AlgebraicGeometry.SpaceFinitePresentationModuleLimit
import Sheaf.CategoryTheory.ModulePullbackTensorIso

/-!
# Line modules descend along affine limits of algebraic spaces

Source: Stacks Project, spaces-limits.tex, Tag 0D2X,
lemma-descend-invertible-modules, clause (2), with the hypotheses of Tag 07SK
(blueprint: lem-sfb-space-invertible-limit-descent).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A line module on a directed affine limit of qcqs algebraic spaces descends to a stage.
Quasi-separatedness is expressed by the quasi-compact scheme fibre products of any two
maps from affine schemes, equivalently quasi-compactness of the representable diagonal.
The base scheme need not be quasi-separated. Pullback is the canonical tensor pullback
on the small etale ringed topoi; the scheme comparison identifies lines with ordinary
Zariski invertible modules.

Source: Stacks Project, spaces-limits.tex, Tag 0D2X, clause (2), and Tag 07SK
(blueprint: lem-sfb-space-invertible-limit-descent).

Proof:
1. Let N be the module dual of L. By lem-pur-sheaf-line-evaluation-inverse-pair,
   N is a line and evaluation identifies L tensor N with the structure module.
   Both modules are finitely presented, since locally they are free of rank one.
   Apply the object clause of lem-sfb-space-fp-module-limit-category to L and N,
   then use directedness to obtain finitely presented models A_i and B_i at one stage.
2. The tensor P_i = A_i tensor B_i is finitely presented: presentations with n,m
   generators and r,s relations give nm generators and rm+ns tensor relations.
   The structure module is finitely presented as well. Apply
   lem-weil-pbc-ringed-topoi-module-pullback-tensor on the canonical ringed etale
   topoi. Its comparison sends c tensor (a tensor b) to
   (c tensor a) tensor (1 tensor b); the inverse sends
   (c tensor a) tensor (d tensor b) to cd tensor (a tensor b).
   Balancing and sheafification, as in def-pur-sheaf-tensor-product, give the inverse
   maps. The unit comparison similarly identifies pullback of the structure module
   with the structure module. Thus evaluation gives an isomorphism between the
   pullbacks of P_i and the structure module.
3. Descend this isomorphism and its inverse by the map clause of
   lem-sfb-space-fp-module-limit-category. Descend the two inverse equations by
   its eventual-equality clause. At a common later stage k the descended maps are
   inverse isomorphisms. All sources and targets here are finitely presented;
   the tails remain nonempty and directed.
4. Pull A_i and B_i to k, obtaining L_k and N_k. Use
   lem-weil-pbc-ringed-topoi-module-pullback-tensor again to identify
   L_k tensor N_k with the structure module. By lem-sfb-space-tensor-inverse-line,
   L_k is a line. The canonical composition comparisons from
   lem-sfb-space-fp-module-limit-category identify its pullback with L.
-/
theorem lineModule_descent_affineLimit {S : Scheme.{u}}
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ AlgebraicSpace S)
    (hqc : ∀ i : Iᵒᵖ, ∃ (U : Over S) (a : yoneda.obj U ⟶ (D.obj i).obj.obj),
      CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a)
    (hqs : ∀ (i : Iᵒᵖ) (U V : Over S), IsAffine U.left → IsAffine V.left →
      ∀ (a : yoneda.obj U ⟶ (D.obj i).obj.obj) (b : yoneda.obj V ⟶ (D.obj i).obj.obj),
        ∃ (W : Over S) (p : W ⟶ U) (q : W ⟶ V),
          IsPullback (yoneda.map p) (yoneda.map q) a b ∧ CompactSpace W.left)
    (haff : ∀ {i j : Iᵒᵖ} (f : i ⟶ j),
      IsRepresentableWith (fun _ _ p ↦ IsAffineHom p.left) (D.map f).hom.hom)
    (c : Cone D) (hc : IsLimit c) (L : c.pt.Modules) (hL : c.pt.IsLineModule L) :
    ∃ (i : I) (L_i : (D.obj (op i)).Modules), (D.obj (op i)).IsLineModule L_i ∧
      Nonempty ((moduleTensorPullback (c.π.app (op i))).obj L_i ≅ L) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
