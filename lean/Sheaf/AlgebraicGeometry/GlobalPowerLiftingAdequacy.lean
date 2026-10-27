/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.AlgebraicGeometry.AdequateModuliSpace
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.RelativeModuliInertia
public import Mathlib.AlgebraicGeometry.Scheme
import Sheaf.AlgebraicGeometry.AdequateModuliEtaleLocality

/-! # Global power lifting gives an adequate moduli space

Source: Alper, arXiv:1005.2398v3, Lemma 4.1.8(3) implies (2), Remarks 4.1.3 and
5.1.2, and Definition 5.1.1 (blueprint: lem-sfb-global-power-lifting-adequacy).

The canonical map on functions is expressed by its values on every scheme object,
as in the existing affine criterion. The second conclusion spells out the tests
on arbitrary quasi-coherent algebras on every affine etale base change.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

namespace CategoryTheory

/-- Global positive-power lifting and the canonical isomorphism on functions make
an affine-target morphism an adequate moduli space, including the tests on all
quasi-coherent algebras on each affine etale base change.
Source: Alper, arXiv:1005.2398v3, Lemma 4.1.8(3) implies (2), Remarks 4.1.3 and
5.1.2, and Definition 5.1.1 (blueprint: lem-sfb-global-power-lifting-adequacy).

Proof:
1. Apply `adequateModuliSpace_iff_affine_global_power` from
   lem-sfb-adequate-moduli-etale-locality with source F and affine ring A. The
   morphism's quasi-compactness and quasi-separatedness are the hypotheses hqc
   and hqs. The canonical function-ring isomorphism is exactly hfunctions: every
   compatible family has a unique scalar preimage under the actual pullback map.
   For any quasi-coherent algebra surjection B -> C and global section t, hpower
   supplies the positive exponent and lifting section. These are precisely the
   two conditions in the criterion, so its reverse implication gives adequacy.
2. Unpack the last conjunct of `IsAdequateModuliSpace` from
   def-sfb-adequate-moduli-space. For each affine etale test W, it applies to every
   quasi-coherent algebra surjection on the actual 2-base change, including those
   not descending from F, and yields the stated positive-power lift. No
   Noetherian or finite-generation hypothesis is used in either step.
-/
theorem adequateModuliSpace_of_global_power_lifting
    {k : Type u} [Field k] (A : Type u) [CommRing A] [Algebra k A]
    (F : BasedCategory.{v, w} (Over (Spec (CommRingCat.of k))))
    (hF : IsAlgebraicModuliStack F)
    (_hFqc : IsQuasiCompactModuli F)
    (_hFqs : IsQuasiSeparatedAlgebraicModuliMap (moduliBaseStructure F))
    (φ : BasedFunctor F (discreteModuli (yoneda.obj
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))))))
    (hqc : IsQuasiCompactAlgebraicModuliMap.{u, v, w, u, u + 1, 0, 0} φ)
    (hqs : IsQuasiSeparatedAlgebraicModuliMap φ)
    (hfunctions : ∀ t : moduliGlobalSectionsRing (moduliStructureSheaf F hF.1.1),
      ∃! r : A, ∀ x : F.obj,
        t.1 (op x) = ULift.up ((Scheme.Γ.map
          (eqToHom (congrArg (fun T : Over (Spec (CommRingCat.of k)) ↦ T.left)
              (φ.w_obj x)).symm ≫
            (yoneda.preimage (φ.obj x).hom).left).op)
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv r)))
    (hpower : ∀ (B C : ModuliAlgebraSheaf F hF.1.1),
      IsQuasicoherentModuliAlgebra B → IsQuasicoherentModuliAlgebra C →
      ∀ (q : B ⟶ C), IsSurjectiveModuliAlgebra q →
        ∀ t : moduliGlobalSectionsRing C.right,
          ∃ N : ℕ, 0 < N ∧ ∃ s : moduliGlobalSectionsRing B.right,
            ∀ x : F.objᵒᵖ, (q.right.hom.app x) (s.1 x) = (t.1 x) ^ N) :
    IsAdequateModuliSpace F hF
      (schemeSpace (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))))) φ ∧
      ∀ W : (schemeSpace
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))))).EtaleSite,
        IsAffine ((etaleForget (schemeSpace
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))))).obj W) →
        ∀ (B C : ModuliAlgebraSheaf
            (moduliSpaceBaseChange (schemeSpace
              (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))))) φ W)
            (moduliSpaceBaseChange_isFibred hF.1.1 (schemeSpace
              (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))))) φ W)),
          IsQuasicoherentModuliAlgebra B → IsQuasicoherentModuliAlgebra C →
          ∀ (q : B ⟶ C), IsSurjectiveModuliAlgebra q →
            ∀ t : moduliGlobalSectionsRing C.right,
              ∃ N : ℕ, 0 < N ∧ ∃ s : moduliGlobalSectionsRing B.right,
                ∀ x : (moduliSpaceBaseChange (schemeSpace
                    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))))) φ W).objᵒᵖ,
                  (q.right.hom.app x) (s.1 x) = (t.1 x) ^ N := by
  sorry

end CategoryTheory
