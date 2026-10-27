/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.AlgebraicGeometry.StackLqcCoherator
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
import Sheaf.AlgebraicGeometry.AlgebraicSpace
import Sheaf.AlgebraicGeometry.StackQuasiCoherentSchemeRestriction
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus

/-! # The quasi-coherator counit on flat scheme tests

Source: Stacks Project, stacks-cohomology.tex, Tag 0GQK, lemma-flat-object-and-Q;
Tags 0778 and 0779 (blueprint: lem-sfb-stack-coherator-flat-test-restriction).

The adjunction is the one supplied by `exists_moduliLqcCoherator`, or any choice of
that right adjunction. The statement concerns its actual counit, restricted by the
existing small étale restriction functor, and its evaluation at the test object.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry Opposite

namespace CategoryTheory

/-- On a chartwise-flat scheme test the quasi-coherator counit is invertible on the
small étale site, and hence on sections at the test object. No quasi-compactness,
quasi-separatedness, finite-presentation or Noetherian condition is imposed.
Source: Stacks Project, stacks-cohomology.tex, Tag 0GQK, lemma-flat-object-and-Q,
with Tags 0778 and 0779 (blueprint: lem-sfb-stack-coherator-flat-test-restriction).

Proof:
1. Choose a smooth surjective scheme atlas a:U → F. Its relation and triple relation
   are algebraic spaces. On étale charts of the relation the two maps to U are flat,
   by lem-sfb-stack-chartwise-smooth-etale-calculus. Flat compatibility of H identifies
   their pullbacks of H_U with the same restricted module. The comparisons define
   delta = c_2^{-1} c_1. Their tensor formula makes delta natural on charts. Full
   faithfulness in lem-sfb-space-fppf-qcoh-descent glues delta to the relation; the
   equality c_3^{-1} c_2 c_2^{-1} c_1 = c_3^{-1} c_1 gives the cocycle and the identity
   comparison gives its unit condition.
2. By lem-sfb-smooth-atlas-module-descent this datum descends to a quasi-coherent M
   with eta:M_U ≅ H_U. By lem-sfb-smooth-atlas-quasicoherent-source-maps, eta extends
   uniquely to phi:M → H. These same descent and source-map statements identify
   Hom(A,M) with Hom(A,H) by composition with phi for every quasi-coherent A.
3. The adjunction of lem-sfb-stack-lqc-coherator gives the same universal property
   for q_H. Its uniqueness gives b:M → QH and c:QH → M with q_H b = phi and phi c = q_H.
   Injectivity of the two Hom bijections gives cb = 1 and bc = 1. Restriction to U
   gives (q_H)_U b_U = eta, so the counit is invertible on the atlas.
4. For the flat test z:T → F, form the algebraic space W = T ×_F U. Choose a surjective
   étale scheme chart V → W. The maps g:V → T and h:V → U are respectively smooth
   surjective and flat. The two composites to F are identified by the fibre product.
5. Naturality of the tensor comparisons identifies g^*(q_H)_T and h^*(q_H)_U after
   conjugation by these comparisons. For H they are invertible by flat compatibility;
   for QH use lem-sfb-stack-quasi-coherent-scheme-restriction. Thus g^*(q_H)_T is an
   isomorphism, since (q_H)_U is one by step 3.
6. Both endpoints on T are quasi-coherent. The smooth surjection g is an fppf cover
   by lem-sfb-space-fppf-covering-calculus. Full faithfulness of fppf descent descends
   the inverse of g^*(q_H)_T; its compatibility follows by inverting the descent
   equation, and faithfulness gives both inverse equations on T.
7. Evaluate at the final étale test. The lifted final test is canonically isomorphic
   to the original object z, by the counit of moduliTestSlice's equivalence. Naturality
   transports the evaluated inverse to q_H(z). No finiteness assumption was used. -/
theorem moduliLqcCoherator_counit_flatTest_isIso {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsAlgebraicModuliStack F)
    (h : SheafOfModules.isQuasicoherent (moduliModuleRings F hF.1.1) ≤
      locallyQuasicoherentFlatCompatible F hF.1.1)
    (Q : (locallyQuasicoherentFlatCompatible F hF.1.1).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent (moduliModuleRings F hF.1.1)).FullSubcategory)
    (adj : ObjectProperty.ιOfLE h ⊣ Q)
    (H : (locallyQuasicoherentFlatCompatible F hF.1.1).FullSubcategory)
    (T : Over S) (z : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (hz : ModuliSpaceTest @Flat z) :
    IsIso ((moduliEtaleRestriction F hF.1.1
      (z.obj (CostructuredArrow.mk (𝟙 (yoneda.obj T))))).map (adj.counit.app H).hom) ∧
    IsIso ((SheafOfModules.evaluation (moduliModuleRings F hF.1.1)
      (op (z.obj (CostructuredArrow.mk (𝟙 (yoneda.obj T)))))).map
        (adj.counit.app H).hom) := by
  sorry

end CategoryTheory
