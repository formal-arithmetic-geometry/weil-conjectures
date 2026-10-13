/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import Sheaf.AlgebraicGeometry.KoszulCechComparisonConstruction

/-! # Eventual vanishing in the kernel of the Koszul-to-Čech cocone

Source: Stacks, Tags 08D0 and 08D1.
(blueprint: lem-sc-koszul-cech-stage-kernel)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite-stage cochain with zero Čech image becomes zero at a later stage.
Source: Stacks, Tag 08D0, proof's localization equality criterion, and Tag 08D1,
finite total-degree diagonals (blueprint: lem-sc-koszul-cech-stage-kernel).

Proof: Transport z through koszulCechHomObjIso and evaluate on the ordered exterior
basis indexed by nonempty subsets J. Put g_J = product of f_j over J. Transport
the zero-image hypothesis through principalCechObjIso. The cocone's formula and
invertibility of its sign imply that every global-section coordinate m_J restricts
to zero on D(g_J). By affine quasi-coherence this restriction is localization at
g_J; the localization zero criterion gives a power g_J^k_J annihilating m_J.
Choose k at least every k_J, possible since there are finitely many nonempty J.
The specified transition from e to b = e+k multiplies the J-coordinate by g_J^k,
so every coordinate at b is zero. The ordered exterior bases detect equality of
the linear cochain components; the other tail terms are zero. Hence the cochain
at b is zero. The diagram's object identifications transport this equality to
its actual map. For r=0 there are no coordinates and z is already zero (b=e);
for r=1 this is the usual localization zero criterion; nilpotent generators and
F=0 require no exception. No assumption that z is a cycle is used. -/
theorem koszulCechCocone_stage_kernel
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent) (n : ℤ) (e : ℕ)
    (z : ((koszulCechHomDiagram A r f
      (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)).obj
        e).X n)
    (hz : (((koszulCechCocone A r f F).ι.app e ≫
      eqToHom (koszulCechCocone_exists A r f F).choose_spec.1).f n) z = 0) :
    ∃ (b : ℕ) (h : e ≤ b),
      (((koszulCechHomDiagram A r f
        (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)).map
          (homOfLE h)).f n) z = 0 := by sorry

end AlgebraicGeometry
