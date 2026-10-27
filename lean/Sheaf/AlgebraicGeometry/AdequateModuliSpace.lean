/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra

/-! # Adequate moduli spaces

Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
arXiv:1005.2398v3, Definition 5.1.1, Lemma 4.1.8(3), Remark 4.1.3 and
Proposition 4.2.1(3)--(4) (blueprint: def-sfb-adequate-moduli-space).

The power-lifting test ranges over all quasi-coherent algebras on each affine
étale 2-base change. The structure-sheaf isomorphism is a separate condition.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory Opposite

namespace CategoryTheory

/-- An adequate moduli space is a qcqs morphism with the canonical structure-sheaf
isomorphism and power lifting for every surjection of quasi-coherent algebras on
all affine étale 2-base changes. Equality of global sections is expressed on every
object of the total site; both sections are compatible families.
Source: Alper, arXiv:1005.2398v3, Definition 5.1.1; the affine-chart formulation is
Lemma 4.1.8(3), Remark 4.1.3 and Proposition 4.2.1(3)--(4)
(blueprint: def-sfb-adequate-moduli-space). -/
def IsAdequateModuliSpace {k : Type u} [Field k]
    (F : BasedCategory.{v, w} (Over (AlgebraicGeometry.Spec (CommRingCat.of k))))
    (hF : IsAlgebraicModuliStack F)
    (Y : AlgebraicGeometry.AlgebraicSpace (AlgebraicGeometry.Spec (CommRingCat.of k)))
    (φ : BasedFunctor F (discreteModuli Y.obj.obj)) : Prop :=
  IsQuasiCompactAlgebraicModuliMap.{u, v, w, u, u + 1, 0, 0} φ ∧
    IsQuasiSeparatedAlgebraicModuliMap φ ∧
    IsIso (moduliStructureMap hF.1.1 Y φ) ∧
    ∀ (W : Y.EtaleSite),
      AlgebraicGeometry.IsAffine ((AlgebraicGeometry.AlgebraicSpace.etaleForget Y).obj W) →
      ∀ (A B : ModuliAlgebraSheaf (moduliSpaceBaseChange Y φ W)
          (moduliSpaceBaseChange_isFibred hF.1.1 Y φ W)),
        IsQuasicoherentModuliAlgebra A → IsQuasicoherentModuliAlgebra B →
        ∀ (f : A ⟶ B), IsSurjectiveModuliAlgebra f →
          ∀ (t : moduliGlobalSectionsRing B.right),
            ∃ (N : ℕ), 0 < N ∧ ∃ (s : moduliGlobalSectionsRing A.right),
              ∀ (x : (moduliSpaceBaseChange Y φ W).objᵒᵖ),
                (f.right.hom.app x) (s.1 x) = (t.1 x) ^ N

end CategoryTheory
