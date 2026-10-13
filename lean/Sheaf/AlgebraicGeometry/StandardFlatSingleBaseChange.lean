/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic

/-! # Standard flat single base change for the canonical pullback

Source: Stacks Project, Tag 0A1D, lemma-base-change-tensor.
(blueprint: lem-pc-standard-flat-single-base-change).

The standard-localization degree-zero flat comparison is the intermediate result
needed by the localized cartesian comparison. Its proof follows the stalkwise
K-flat comparison and qcqs single-complex induction described in the DAG node.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Standard-localization degree-zero flat base change.

Source: Stacks Project, Tag 0A1D, lemma-base-change-tensor, specialized to
E = O_Y[0] and G = M[0].
(blueprint: lem-pc-standard-flat-single-base-change).

Proof: M[0] is bounded above, and every term is quasi-coherent and flat over B:
the degree-zero term is M and all other terms are zero. The structure sheaf
O_Y[0] has quasi-coherent cohomology, so Tag 0A1D applies with E = O_Y[0].
Its conclusion is Lg^* Rp_*(O_Y[0] tensor^L M[0]) isomorphic to
Rr_*(Lq^* O_Y[0] tensor^L q^*(M[0])). Derived pullback takes the tensor
unit O_Y[0] to O_(Y x_B A)[0]. Cancel the tensor units, and use the
termwise identification q^*(M[0]) = (q^*M)[0]. Invert the resulting
isomorphism to obtain the displayed orientation. For the stalk calculation
underlying Tag 0A1D, M_x[0] is K-flat over O_(B,b), and the fibre-product
stalk is flat over O_(Y,x) tensor_(O_(B,b)) O_(A,a), since it is a
localization of that tensor product. These are not flatness assertions over
O_(Y,x) or of A over B. Zero modules and empty schemes satisfy the same
argument. -/
theorem standard_flat_single_baseChange
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    (M : Y.Modules) [M.IsQuasicoherent] (hM : M.IsFlatOver p) (g : A ⟶ B) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    Nonempty ((schemeDerivedDirectImage (pullback.snd p g)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings (pullback p g).toRingedSpace)) 0).obj
          (Scheme.Modules.tensorPullbackObj (pullback.fst p g) M)) ≅
      (derivedPullback g).obj ((schemeDerivedDirectImage p).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M))) := by
  sorry

end AlgebraicGeometry
