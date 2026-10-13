/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.KoszulCechComparisonConstruction
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore
import Sheaf.AlgebraicGeometry.DerivedStructureSheafHomHypercohomology
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective

/-! # The stagewise derived Hom identification for the Koszul comparison

Source: Stacks Project, Tags 06Z0, 08DC and 08DD.
(blueprint: lem-sc-koszul-open-hom-homology-comparison).
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Derived Hom from each Koszul tail is its Hom-complex cohomology, naturally in
power transitions. The canonical comparison sends a restriction-zero arrow to zero.
This statement does not assert exactness of a filtered colimit, injectivity of the
comparison on cohomology, or eventual vanishing.
Source: Stacks Project, Tag 06Z0 and Equation 36.9.4.1, Tag 08DC; Tag 08DD.
(blueprint: lem-sc-koszul-open-hom-homology-comparison)

Proof: On the affine scheme, termwise quasi-coherence identifies F with the tilde
of its global-sections complex M, naturally in the differentials. The affine
quasi-coherent derived equivalence identifies derived sheaf arrows from I_e into
Q(F) with derived module arrows from the extended module tail into M. The tail
has finite free terms and is bounded, so it is K-projective. Localization thus
identifies these arrows with homotopy classes of chain maps. The degree-zero
cycles of the linear Hom complex are exactly chain maps, and its boundaries are
null-homotopic maps. Take the inverse of this additive identification, and compose
with postcomposition by the inverse of the specified isomorphism to E. The object
identification koszulCechHomObjIso gives the displayed additive equivalences.
Precomposition of Hom cochains agrees with composition of chain maps; the power
transition formula for koszulCechHomDiagram therefore proves their naturality.
For the last clause, represent an arrow by such a module chain map. On the
principal intersection indexed by J, the Koszul-to-Cech comparison evaluates
that map on the ordered exterior generator and divides by the product of the
f_j to the stage exponent, with its specified totalization sign. This is exactly
the chain-level restriction followed by the inverse of the restricted augmentation:
the restricted Koszul complex contracts when one f_j is invertible. The Cech to
RΓ map and evaluation-at-one identification of Hom(O_U,E|_U) with H^0(RΓ(U,E))
identify its class with the given composite on derived homology. Restriction-zero
arrows therefore give the zero class. The argument uses no exactness of colimits
or invertibility of the comparison. For the empty cover, all tails and comparison
sources vanish; the zero ring and F=0 give zero groups by the same constructions. -/
theorem koszulOpenHom_homology_comparison
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} A)]
    (F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent)
    (E : schemeDerivedQCohCategory (Spec (.of A)))
    (eF : DerivedCategory.Q.obj F ≅ E.obj) :
    let R := ((SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) (koszulOpen A r f)) ⋙
      Equivalence.functor
        (C := SheafOfModules.{u}
          ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
        (D := SheafOfModules.{u}
          (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory
    let M := ((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F
    let D := koszulCechHomDiagram A r f M
    let C := koszulCechHomColimit A r f M
    let β := ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0).app C).inv ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        (koszulCechDerivedComparison A r f F ≫
          (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor.map eF.hom)
    ∃ α : ∀ e : ℕ, (koszulOpenObject A r f e ⟶ E.obj) ≃+ (D.obj e).homology 0,
      (∀ (a b : ℕ) (h : a ≤ b) (φ : koszulOpenObject A r f a ⟶ E.obj),
        α b (koszulOpenMap A r f a b h ≫ φ) =
          HomologicalComplex.homologyMap (D.map (homOfLE h)) 0 (α a φ)) ∧
      ∀ (e : ℕ) (φ : koszulOpenObject A r f e ⟶ E.obj), R.map φ = 0 →
        β (HomologicalComplex.homologyMap (colimit.ι D e) 0 (α e φ)) = 0 := by
  sorry

end AlgebraicGeometry
