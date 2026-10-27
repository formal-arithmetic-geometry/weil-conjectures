module

public import Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-! # Trivial special fibre of a closed subgroup of a split torus

Source: Conrad, Reductive group schemes (2014), Exercise 2.4.3(iii), printed p.76,
and the final torsion argument of Theorem B.3.2(2), printed pp.289--290.
(blueprint: lem-sfb-local-torus-subgroup-special-trivial).

The base change is along the residue-field quotient, and the maps in the hypothesis
and conclusion are the actual identity sections. No flatness or completeness is imposed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonObj

namespace AlgebraicGeometry

/-- A closed subgroup of a split torus over a Noetherian local ring is trivial if its
special fibre is trivial, as detected by the identity section itself.

Source: Conrad, Reductive group schemes (2014), Exercise 2.4.3(iii), printed p.76;
Theorem B.3.2(2), final torsion argument, printed pp.289--290.
(blueprint: lem-sfb-local-torus-subgroup-special-trivial).

Proof, following the six steps of the accepted DAG split:
1. The closed immersion into the affine Laurent torus writes K as Spec B, with B a
   quotient of A[x_i,y_i]/(x_i*y_i-1) (def-weil-closed-immersion,
   def-weil-affine-spectrum). Its augmentation epsilon splits B = A direct_sum J.
   The ideal J = ker epsilon is generated over B by x_i-1 and y_i-1, hence finite
   over B. For rank zero this already gives J = 0.
2. For every n > 1 the n-torsion H_n has coordinate algebra
   C_n = B/(x_i^n-1,y_i^n-1). Monomials with each x_i exponent less than n span
   C_n over A, since y_i = x_i^(n-1). Its augmentation kernel L_n is finite over A
   and splits C_n = A direct_sum L_n. Its special fibre is trivial by the hypothesis
   and the affine fibre-product formula (lem-weil-pbc-fibre-product-affine-spectra).
   Thus L_n/m L_n = 0, and Nakayama (lem-weil-pbc-nakayama-jacobson) gives L_n = 0.
3. At any prime p, extend kappa(p) to an algebraic closure Omega
   (def-weil-pbc-localization-at-prime, def-weil-algebraic-closure).
   The immersion stays closed (lem-weil-pbc-closed-immersion-base-change), so
   lem-sfb-split-torus-subgroups-diagonalizable identifies K_Omega with D(M),
   M finitely generated abelian. Its n-torsion has algebra Omega[M/nM]: send a
   basis element to its coset, with inverse using any representative. Step 2
   forces M/nM = 0 for every n > 1. The structure theorem
   (lem-sbc-finitely-generated-abelian-group-structure) now gives M = 0: a free
   summand survives modulo 2, and a prime-power summand survives modulo its prime.
   This uses scheme-theoretic torsion, including characteristic-p infinitesimals.
4. The augmentation B tensor_A kappa(p) -> kappa(p) becomes an isomorphism over
   Omega. Field-extension tensor injectivity (lem-sfb-field-extension-tensor-injective)
   kills its kernel, while its scalar section gives surjectivity. The split
   decomposition from Step 1 therefore gives J tensor_A kappa(p) = 0 for all p
   (lem-weil-pbc-fibre-product-affine-spectra).
5. For q prime in B above p, the fraction maps identify J tensor_A kappa(p) with
   S_p^{-1}J / p S_p^{-1}J (def-weil-pbc-localization-at-prime,
   def-weil-pbc-module-localization). Localizing further at q gives
   J_q = p J_q. This is a finite B_q-module by Step 1, and p maps into the maximal
   ideal of B_q. Nakayama over B_q gives J_q = 0.
6. If j in J were nonzero, its proper annihilator would lie in a maximal ideal q.
   The localization zero criterion (def-weil-pbc-module-localization) gives some
   s outside q with s*j = 0, a contradiction. Hence J = 0; epsilon and A -> B are
   inverse. Taking spectra shows that the identity section itself is an isomorphism
   (def-weil-affine-spectrum), without flatness or completeness assumptions. -/
theorem isIso_unit_of_splitTorus_closed_specialFiber
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (r : ℕ) (K : Grp (Over (Spec (.of A))))
    (j : K ⟶ RingGroupSchemes.splitTorus A r) [IsClosedImmersion j.hom.hom.left]
    (hspecial : IsIso (η[((Over.pullback
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).mapGrp.obj K).X]).left) :
    IsIso (η[K.X]).left := by
  sorry

end AlgebraicGeometry
