/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.AlgebraicGeometry.PrincipalOpenCechTotal

/-! # Sections of a quasi-coherent resolution on a basic open

Source: Stacks, Tags 08C2, 08D2 and 08BS
(blueprint: lem-sc-principal-open-sections-resolution-quasi-iso).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Taking sections on a basic open sends a resolution of a termwise quasi-coherent
complex to a quasi-isomorphism, even when the resolution is not termwise quasi-coherent.
Source: Stacks, Tags 08C2, 08D2 and 08BS
(blueprint: lem-sc-principal-open-sections-resolution-quasi-iso).

Proof:
1. Restrict the map to D(g). Restriction is exact and preserves K-injective complexes
   (Tag 08BS), so this is still a quasi-isomorphism into a K-injective complex.
2. On D(g), use the basis of all affine opens. Restriction preserves quasi-coherence;
   kernels, images and cokernels of maps of quasi-coherent modules are quasi-coherent.
   Thus on every member of this basis the terms of F, the differential cokernels and
   the cohomology sheaves have vanishing positive cohomology (01XB). This verifies all
   three acyclicity conditions of 08C2, not only vanishing on D(g) itself.
3. Apply 08C2 to the one-element cover of D(g) by itself. Its alternating total is
   exactly the section complex. The canonical map to derived sections is invertible.
   Computing derived sections using the given restricted resolution identifies this
   canonical map with the sections of i. The identification is first obtained for a
   K-injective resolution with injective terms, and then for any K-injective resolution
   by a homotopy equivalence between resolutions. Additive sections preserve that
   homotopy equivalence. Hence the displayed map is a quasi-isomorphism.
4. Forgetting from O(D(g))-modules to A-modules preserves and reflects homology
   isomorphisms. This gives exactly affineOpenSections. If D(g) is empty, both section
   complexes are zero, so the conclusion also holds. No truncation of F is assumed. -/
theorem principalOpenSections_resolution_quasiIso
    (A : Type u) [CommRing A] (g : A)
    (F J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent)
    [J.IsKInjective] (i : F ⟶ J) [QuasiIso i] :
    QuasiIso (((affineOpenSections A (PrimeSpectrum.basicOpen g)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map i) := by
  sorry

end AlgebraicGeometry
