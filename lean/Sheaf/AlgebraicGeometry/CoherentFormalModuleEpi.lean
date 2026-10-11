/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian

/-! # Epimorphisms of coherent formal modules

Source: Stacks Project, Cohomology of Schemes, Lemma 087Y
(blueprint: lem-weil-pbc-formal-systems-surjective).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- A morphism in Coh(X,I) is an epimorphism exactly when its first component is an
 epimorphism of O_X-modules. In the shared indexing convention, `op 0` denotes level 1.

Source: Stacks Project, Cohomology of Schemes, Lemma 087Y
(blueprint: lem-weil-pbc-formal-systems-surjective).

Proof (the four steps of the node):
1. By lem-weil-pbc-coherent-formal-modules-abelian the category is abelian and cokernels
are termwise. By lem-weil-pbc-preadditive-epi-iff-cokernel-zero, the system map is epi
iff all its component cokernels C_n vanish, whereas its first component is epi iff C_1=0.
2. Assume C_1=0. Cover X by Noetherian affine opens U=Spec A. Restriction and the affine
formal-module equivalence (lem-weil-pbc-coherent-formal-modules-local-exactness and
lem-weil-pbc-coherent-formal-modules-affine) identify the map with f:M -> N of finite
modules over the I-adic completion of A, with components its reductions modulo I^n.
The quotient projections are surjective, and the first component is surjective on affine
sections by lem-weil-pbc-quasi-coherent-module-cokernel-image. Thus N=f(M)+IN.
3. The finite quotient Q=N/f(M) satisfies JQ=Q for J=I times the completed ring.
By lem-weil-pbc-adic-completion-mod-ideal the completed ring is J-adically complete;
lem-weil-pbc-adic-complete-jacobson-radical places J in its Jacobson radical.
Then lem-weil-pbc-nakayama-jacobson gives Q=0, so f is surjective.
4. Every reduction of f is surjective, hence each C_n has zero sections on these affine
opens. The quasi-coherent affine tilde-Gamma equivalence
(lem-weil-pbc-affine-tilde-gamma-adjunction) makes each restriction zero; the sheaf axiom
makes C_n zero globally. Step 1 proves the converse; the forward direction takes n=1.
-/
theorem coherentFormalModule_epi_iff_first_component {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) {F G : CoherentFormalModule X I} (α : F ⟶ G) :
    Epi α ↔ Epi (α.hom.app (op 0)) := by
  sorry

end AlgebraicGeometry
