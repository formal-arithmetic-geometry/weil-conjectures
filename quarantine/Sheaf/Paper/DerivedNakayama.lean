/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

import Sheaf.Paper.DerivedNakayamaResolution
import Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
import Sheaf.Paper.DerivedNakayamaFirstReduction

/-!
# Reduction and derived Nakayama

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-lem-pe-derived-nakayama/_section.md` (blueprint: sk-lem-pe-derived-nakayama).

The perfect resolution is stated by its bounded rank-one free representative, its
specified differential, and its quasi-isomorphic augmentation to the finite coefficient.
The natural cone comparison uses the existing localized mapping-cone functor.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.DerivedNakayama

/-- The finite coefficient has the two-term perfect resolution, derived reduction is its
natural cone, and first reduction detects zero objects and isomorphisms among complete objects.
Source: blueprint main-20261015, Reduction and derived Nakayama, statement and proof
(blueprint: sk-lem-pe-derived-nakayama).

Proof:
1. Apply lem-weil-pbc-standard-quotients-perfect with the chosen uniformizer pi_E.
   The exact inverse image from the point gives the coefficient exact sequence of
   det-pe-derived-nakayama-resolution. Put its two regular modules in degrees -1 and 0,
   and augment by the quotient map. The kernel and cokernel calculation shows that the
   augmentation is a quasi-isomorphism. The terms are free of rank one in those degrees
   and zero elsewhere. This is a perfect resolution: the identity covering and the
   identity rank-one splittings give def-weil-pbc-strict-perfect-coefficient-package.
   The natural cone identification is det-pe-derived-nakayama-resolution, computed by
   tensoring this bounded flat resolution with a K-flat representative of K.
2. If K_1 vanishes, use the quotient-power triangles with m=1 inductively to show all
   positive reductions vanish. Completeness identifies K with their derived inverse
   limit, which is zero (det-pe-derived-nakayama-first-reduction, Vanishing).
3. Complete complexes are closed under cones: reduction and the derived inverse limit
   are exact, and their canonical comparison is natural. The cone of f therefore is
   complete and its first reduction is zero when f_1 is invertible. Step 2 kills the
   cone, so f is invertible (det-pe-derived-nakayama-first-reduction, Isomorphisms).
No boundedness or constructibility of K or L, or invertibility of l on X, is required. -/
theorem reduction_and_derived_nakayama (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    (∃ d : End (Mod.regular (integerRing l E)),
      (∀ (S : Profinite.{u}ᵒᵖ) (f : (integerRing l E).obj.obj S) (s : S.unop),
        ((d.hom.hom.app S) f).down s =
          Padic.coefficientExtensionUniformizer l E * f.down s) ∧
      ∀ (X : Scheme.{u}) (n : ℕ),
        (∃ (P : CochainComplex (AdicCompletion.Modules l E X) ℤ),
          P.IsStrictlyGE (-1) ∧ P.IsStrictlyLE 0 ∧
          ∃ (em : P.X (-1) ≅ Mod.regular (AdicCompletion.ring l E X))
            (e0 : P.X 0 ≅ Mod.regular (AdicCompletion.ring l E X)),
            P.d (-1) 0 = em.hom ≫ (regularPullbackIso l E X).inv ≫
              (pullback l E X).map (d ^ (n + 1)) ≫
                (regularPullbackIso l E X).hom ≫ e0.inv ∧
            ∃ ε : P ⟶ (CochainComplex.singleFunctor (AdicCompletion.Modules l E X) 0).obj
                (AdicCompletion.finiteModule l E X n),
              QuasiIso ε ∧ ε.f 0 = e0.hom ≫ AdicCompletion.finiteUnit l E X n) ∧
        Nonempty (DerivedCategory.Q ⋙ reductionFunctor l E X (n + 1) ≅
          coneFunctor l E X (d ^ (n + 1)))) ∧
    (∀ (X : Scheme.{u}) (K : Derived l E X),
      IsDerivedComplete l E X K →
      IsZero ((reductionFunctor l E X 1).obj K) → IsZero K) ∧
    (∀ (X : Scheme.{u}) (K L : Derived l E X) (f : K ⟶ L),
      IsDerivedComplete l E X K → IsDerivedComplete l E X L →
      IsIso ((reductionFunctor l E X 1).map f) → IsIso f) := by
  sorry

end AlgebraicGeometry.ProEtale.DerivedNakayama
