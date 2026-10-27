module

public import Sheaf.AlgebraicGeometry.MPseudoCoherentComplex

/-! # Uniform approximation by perfect complexes with closed support

Source: Stacks Project, Derived Categories of Schemes, Tags 08EM and 08EN
(blueprint: def-sfb-supported-perfect-approximation-property).

The complement of each closed support is tested for retrocompactness on affine opens.
The approximation bound is chosen before the degree and the quasi-coherent derived object.
Support means vanishing of cohomology stalks, expressed by subsingleton underlying groups.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Approximation by perfect complexes holds on `Y` if, for every closed support with
retrocompact open complement, one integer `r` works for every degree `m` and every
quasi-coherent derived object that is `(m - r)`-pseudo-coherent and supported on that
closed subset in degrees at least `m - r`. The perfect approximation is supported there
in all degrees, is an isomorphism on cohomology above `m`, and is surjective at `m`.
The surjection is an epimorphism of module sheaves, not surjectivity on all open sections.
Source: Stacks Project, Derived Categories of Schemes, Tags 08EM and 08EN
(blueprint: def-sfb-supported-perfect-approximation-property). -/
def HasSupportedPerfectApproximation (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))] :
    Prop :=
  ∀ T : Set Y, IsClosed T →
    (∀ W : Y.Opens, IsAffineOpen W → IsCompact (Tᶜ ∩ (W : Set Y))) →
    ∃ r : ℤ, ∀ (m : ℤ) (F : schemeDerivedCategory Y),
      schemeDerivedQCohProperty Y F → IsMPseudoCoherent Y (m - r) F →
      (∀ i : ℤ, m - r ≤ i → ∀ y : Y, y ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj F).val.presheaf y))) →
      ∃ (P : schemeDerivedCategory Y) (v : P ⟶ F),
        IsPerfect Y P ∧
        (∀ (i : ℤ) (y : Y), y ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk
            ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj P).val.presheaf y))) ∧
        (∀ i : ℤ, m < i →
          IsIso ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).map v)) ∧
        Epi ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) m).map v)

end AlgebraicGeometry.Scheme
