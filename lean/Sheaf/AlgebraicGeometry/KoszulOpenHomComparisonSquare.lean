/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.AlgebraicGeometry.KoszulCechComparisonConstruction
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.DerivedStructureSheafHomHypercohomology
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective

/-! # The degree-zero restriction square for the Koszul comparison
Source: Stacks Project, Tags 08DD and 08D1. -/

@[expose] public section

universe uMain wMain vMain
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The stage Hom and restricted structure-Hom identifications intertwine the canonical
Koszul comparison with restriction and augmentation.
Source: Stacks Project, Tag 08DD, proof of Proposition 36.9.5, and Tag 08D1.
(blueprint: lem-sc-koszul-open-hom-comparison-square)

Proof: The extended Koszul tail has finite free terms and vanishes in positive degrees,
so it is K-projective. Zeroth Hom-complex cohomology is therefore its derived Hom group.
The affine derived equivalence and the termwise tilde/global-section counit transport
this group to Hom(I_e,E). Compose the Hom-complex cohomology identification with the
specified koszulCechHomObjIso to obtain the stage equivalences a. On U, Hom from the
restricted structure object is H^0 of derived global sections by evaluation at 1.
Transport scalars along the structure ring map from A to sections on U; forgetting the
module structure gives the target equivalence b with the A-valued affineOpenSections.
For a chain representative of phi, the Koszul-to-Cech cocone evaluates on the ordered
exterior basis and divides by the product of the generators to exponent e+1. The
specified totalization sign is exactly the sign converting the Hom differential to
Cech totalization. The restricted augmentation admits a contracting inverse on each
principal open; composing phi with that inverse gives the same fractions. The Cech
resolution comparison then gives the displayed identity in H^0. The condition h says
that psi is this inverse-augmentation composite: the augmentation is an isomorphism
on U, since one generator is invertible locally. Both identifications and this equality
are invariant under chain homotopies and quasi-isomorphic representatives, so transporting
along i proves the square for all derived phi and psi. For r=0 all stage tails and
sections on the empty open are zero; the same construction is the unique zero square.
The argument also covers the zero ring and E=0. -/
theorem koszulOpenHom_comparison_square
    (A : Type uMain) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    [HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))]
    (E : schemeDerivedQCohCategory (Spec (.of A)))
    [HasDerivedCategory.{vMain} (ModuleCat.{uMain} A)]
    (F : CochainComplex
      (SheafOfModules.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent)
    (i : DerivedCategory.Q.obj F ≅ E.obj) :
    let R := ((SheafOfModules.overFunctor.{uMain}
      (moduleRings (Spec (.of A)).toRingedSpace) (koszulOpen A r f)) ⋙
      Equivalence.functor
        (C := SheafOfModules.{uMain}
          ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
        (D := SheafOfModules.{uMain}
          (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory
    let H := DerivedCategory.homologyFunctor (ModuleCat.{uMain} A) 0
    let D := koszulCechHomDiagram A r f
      (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
    let G := (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor
    let c := koszulCechDerivedComparison A r f F ≫ G.map i.hom
    ∃ (a : ∀ e : ℕ, (koszulOpenObject A r f e ⟶ E.obj) ≃
          H.obj (DerivedCategory.Q.obj (D.obj e)))
      (b : (R.obj (koszulOpenStructure A) ⟶ R.obj E.obj) ≃ H.obj (G.obj E.obj)),
      ∀ (e : ℕ) (φ : koszulOpenObject A r f e ⟶ E.obj)
        (ψ : R.obj (koszulOpenStructure A) ⟶ R.obj E.obj),
        R.map (koszulOpenUnit A r f e) ≫ ψ = R.map φ →
        b ψ = H.map c (H.map (DerivedCategory.Q.map (colimit.ι D e)) (a e φ)) := by
  sorry

end AlgebraicGeometry
