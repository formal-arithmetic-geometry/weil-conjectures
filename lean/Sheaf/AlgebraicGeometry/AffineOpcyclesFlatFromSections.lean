/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Flat affine module opcycles give flat sheaf opcycles

Source: Stacks Project, Tags 01IB and 01U4, and step 4 of
lem-pc-affine-universally-exact-opcycles-flat.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Transfer flatness of module opcycles to affine-local flatness of sheaf opcycles.
Source: Stacks Project, Tags 01IB (affine equivalence), 01HV (localization of
associated sheaves), and 01U4 (affine-local flatness).
(blueprint: lem-pc-affine-opcycles-flat-from-sections).

Proof: Let P be the global-sections complex and Q its degree-a opcycles.
The counit of the affine quasi-coherent equivalence identifies the two terms
of C defining this cokernel with the sheafifications of their global sections,
naturally in the differential. Sheafification is a left adjoint and preserves
cokernels, so C.opcycles a is the associated sheaf of Q. Localizing a flat
module gives flat stalks over the localized structure rings. On any affine
open U, the prime-local criterion implies that the sections of this associated
sheaf are flat over Gamma(U,O). For affine U contained in affine V, the open
immersion U to V gives a flat map Gamma(V,O) to Gamma(U,O). Transitivity of
module flatness gives flatness of Gamma(U,C.opcycles a) over Gamma(V,O), with
the scalar action obtained by restricting along the identity's appLE. This
proves every test in IsFlatOver(identity). Only the two displayed terms need
quasi-coherence, since opcycles are their cokernel; no other degree or homology
is involved. The empty scheme and zero cokernel are included. -/
theorem affine_opcycles_flat_from_sections (S : Scheme.{u}) (hS : IsAffine S)
    (C : CochainComplex S.Modules ℤ) (a : ℤ)
    (hprev : (C.X (a - 1)).IsQuasicoherent) (hcurr : (C.X a).IsQuasicoherent)
    (hflat : Module.Flat Γ(S, ⊤)
      ((((SheafOfModules.evaluation (R := S.ringCatSheaf) (.op ⊤) :
        S.Modules ⥤ ModuleCat.{u} Γ(S, ⊤)).mapHomologicalComplex
        (.up ℤ)).obj C).opcycles a)) :
    (C.opcycles a).IsFlatOver (𝟙 S) := by sorry

end AlgebraicGeometry.Scheme.Modules
