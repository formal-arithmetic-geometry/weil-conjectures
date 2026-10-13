/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso
import Sheaf.Algebra.Homology.RhomGlobalSections

/-! # Shifted Hom as cohomology of restricted global derived Hom
Source: Stacks Project, Cohomology on Sites, Tag 08JA; Cohomology, Tag 0B6A.
(blueprint: lem-sc-restricted-global-hom-shifted-equiv).
-/

@[expose] public section

set_option autoImplicit false
universe u w wA
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The shifted-Hom/cohomology identification, including the action of a morphism
in the second entry. Exact scalar restriction changes the ring action, not the
underlying cohomology group.
Source: Stacks Project, Cohomology on Sites, Tag 08JA; Cohomology, Tag 0B6A.
(blueprint: lem-sc-restricted-global-hom-shifted-equiv).

Proof: Choose a K-flat representative of P and a K-injective representative of Q.
Their sheaf Hom complex represents internal RHom; its global sections compute global
RHom. Degree n-m cocycles modulo boundaries are derived morphisms P[m] to Q[n]: the
usual shift comparison carries the Hom-complex differential and its signs to the
chain-map equation. Localization into a K-injective target identifies homotopy
classes with derived morphisms. This is the shifted version of rhom_global_sections.
Evaluation at the unit identifies sheaf Hom global sections with the ordinary Hom
complex. Restriction of scalars is exact and leaves the underlying group unchanged,
so it commutes with cohomology. Transport these identifications through the right-
derived resolution isos, giving e. Postcomposition with q commutes with localization,
shift and each resolution comparison, giving the displayed naturality equation.
All integers are allowed; no boundedness or quasi-coherence hypothesis is needed. -/
theorem restrictedGlobalHom_shiftedHom_equiv
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]
    {X S : Scheme.{u}} (f : X ⟶ S) :
    ∃ e : ∀ (P Q : schemeDerivedCategory X) (m n : ℤ),
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((moduleRings S.toRingedSpace).obj.obj (op ⊤))) (n - m)).obj
          ((schemeGlobalScalarRestriction f).obj
            ((schemeGlobalDerivedHom X).obj (op P, Q)))) ≃+ (P⟦m⟧ ⟶ Q⟦n⟧),
      ∀ (P Q Q' : schemeDerivedCategory X) (m n : ℤ) (q : Q ⟶ Q')
        (x : ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((moduleRings S.toRingedSpace).obj.obj (op ⊤))) (n - m)).obj
            ((schemeGlobalScalarRestriction f).obj
              ((schemeGlobalDerivedHom X).obj (op P, Q))))),
        e P Q' m n
          (((DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((moduleRings S.toRingedSpace).obj.obj (op ⊤))) (n - m)).map
              ((schemeGlobalScalarRestriction f).map
                ((schemeGlobalDerivedHom X).map ((𝟙 P).op, q)))) x) =
          e P Q m n x ≫ q⟦n⟧' := by sorry

end AlgebraicGeometry
