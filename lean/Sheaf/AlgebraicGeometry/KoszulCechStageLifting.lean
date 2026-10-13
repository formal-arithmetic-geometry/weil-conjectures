/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import Sheaf.AlgebraicGeometry.KoszulCechComparisonConstruction

/-! # Finite-stage lifting for the Koszul-to-Čech cocone

Source: Stacks, Tags 08D0 and 08D1.
(blueprint: lem-sc-koszul-cech-stage-lifting)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Every total Čech cochain is the image of a cochain at one positive Koszul exponent.
Source: Stacks, Tag 08D0, proof's localization description, and Tag 08D1,
finite total-degree diagonals (blueprint: lem-sc-koszul-cech-stage-lifting).

Proof: Transport the target through principalCechObjIso. For each nonempty subset J,
put p = card(J)-1 and q = n-p. Quasi-coherence on Spec(A) identifies its section on
D(g_J), where g_J is the product of the f_j, with the localization of global
sections of F.X q. Write that section, after multiplication by the inverse of
Int.negOnePow(p*q+p*(p-1)/2), as m_J/g_J^d_J. There are finitely many J, so choose
E >= 1 and E >= d_J for all J. Replace m_J by g_J^(E-d_J) m_J. At stage e = E-1,
define each linear map on the ordered exterior basis by these numerators. Terms
outside the tail's finite support are zero. The free exterior bases therefore give
a homogeneous module Hom cochain, and koszulCechHomObjIso transports it to the
specified diagram. The cocone formula gives exactly the chosen sections: g_J is
invertible on D(g_J), so the formula can be divided by g_J^E. Transport back through
principalCechObjIso. For r=0 the target has no coordinates, and the zero cochain at
stage 0 suffices; for zero or nilpotent g_J its localized section module is zero.
This argument uses cochains, with no cycle or boundedness condition on F. -/
theorem koszulCechCocone_stage_lifting
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent) (n : ℤ)
    (y : ((principalCechFunctor r f).obj F).X n) :
    ∃ (e : ℕ) (z : ((koszulCechHomDiagram A r f
      (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)).obj
        e).X n),
      (((koszulCechCocone A r f F).ι.app e ≫
        eqToHom (koszulCechCocone_exists A r f F).choose_spec.1).f n) z = y := by sorry

end AlgebraicGeometry
