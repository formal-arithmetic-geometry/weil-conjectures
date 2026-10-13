/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.KoszulOpenSystem
public import Sheaf.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore

/-! # Affine K-projective Hom-complex representatives

Source: Stacks Project, Tag 06Z0; Mathlib's K-projectivity and Hom-complex quotient.
(blueprint: lem-sc-affine-kprojective-hom-complex).
-/

@[expose] public section

universe u w v
open CategoryTheory
namespace AlgebraicGeometry

/-- For any module target complex, affine derived arrows out of a K-projective module
complex are its linear Hom-complex cohomology, with chain representatives and naturality.
Source: Stacks Project, Tag 06Z0; Mathlib HomComplexCohomology and KProjective.
(blueprint: lem-sc-affine-kprojective-hom-complex)

Proof: The core affine derived equivalence identifies the derived tilde Hom group
with the corresponding module derived Hom group, through its termwise tilde comparison.
For a K-projective source localization identifies this with homotopy classes of chain
maps. Degree-zero Hom cycles are chain maps and boundaries are null-homotopic maps,
so the quotient is degree-zero homology of the module-valued Hom complex. All three
identifications are additive. Precomposition by a chain map is precomposition on cycles,
and the stated formula for t gives exactly that map on the quotient. Every quotient
class has a cycle representative, which is a chain map g; this gives z and both displayed
identities. There is no boundedness hypothesis on the target M. The zero source, zero
ring and zero target give the same quotient and unique zero representative. -/
theorem affineKProjective_homComplex (A : Type u) [CommRing A]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} A)]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    let T := (koszulOpenTilde A).mapHomologicalComplex (.up ℤ)
    ∃ a : ∀ (L : CochainComplex (ModuleCat.{u} A) ℤ) (_hL : L.IsKProjective),
        (DerivedCategory.Q.obj (T.obj L) ⟶ DerivedCategory.Q.obj (T.obj M)) ≃+
          (CochainComplex.moduleHomComplex L M).homology 0,
      (∀ (L L' : CochainComplex (ModuleCat.{u} A) ℤ)
        (hL : L.IsKProjective) (hL' : L'.IsKProjective) (g : L' ⟶ L)
        (t : CochainComplex.moduleHomComplex L M ⟶ CochainComplex.moduleHomComplex L' M),
        (∀ (n : ℤ) (z : CochainComplex.HomComplex.Cochain L M n),
          (t.f n) z = (CochainComplex.HomComplex.Cochain.ofHom g).comp z (zero_add n)) →
        ∀ φ : DerivedCategory.Q.obj (T.obj L) ⟶ DerivedCategory.Q.obj (T.obj M),
          a L' hL' (DerivedCategory.Q.map (T.map g) ≫ φ) =
            HomologicalComplex.homologyMap t 0 (a L hL φ)) ∧
      ∀ (L : CochainComplex (ModuleCat.{u} A) ℤ) (hL : L.IsKProjective)
        (φ : DerivedCategory.Q.obj (T.obj L) ⟶ DerivedCategory.Q.obj (T.obj M)),
        ∃ (g : L ⟶ M) (z : (CochainComplex.moduleHomComplex L M).cycles 0),
          DerivedCategory.Q.map (T.map g) = φ ∧
          (CochainComplex.moduleHomComplex L M).iCycles 0 z =
            CochainComplex.HomComplex.Cochain.ofHom g ∧
          a L hL φ = (CochainComplex.moduleHomComplex L M).homologyπ 0 z := by
  sorry

end AlgebraicGeometry
