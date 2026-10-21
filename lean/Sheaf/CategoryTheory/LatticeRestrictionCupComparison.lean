/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Sheaf.CategoryTheory.LatticeAlgebraDerivedCup
public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus

/-! # Pinned discrete-action and section-action derived cup comparison

Source: main-20261015 direct-images proof, paragraph (3), agent-expanded lattice
calculation, proof steps 9 and 13
(blueprint: def-sfb-lattice-restriction-cup-comparison).

The bridge retains both recorded action categories and both localization universes.
Its invariant comparison is pinned by inclusions and its derived comparison on every
complex by computation units. The regular-coefficient cup equation uses this comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace Profinite.DiscreteLattice
namespace RestrictionCup

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] (r : ℕ)

/-- Bundle precisely the given commutative ring for the sectionwise restriction calculus.
Source: paragraph (3) (blueprint: def-sfb-lattice-restriction-cup-comparison). -/
def ring : CategoryTheory.CondensedBar.Ring.{u} := ⟨R.X⟩

/-- The regular R-algebra with trivial lattice action is the diagonal tensor unit algebra.
Source: paragraph (3) (blueprint: def-sfb-lattice-restriction-cup-comparison). -/
def regularAlgebra : DerivedCup.Algebra R r := ⟨𝟙_ (Equivariant R r)⟩

/-- The existing K-injective localization supplies the restriction calculus's small Hom size.
Source: paragraph (3), universe convention and ordinary derived invariants
(blueprint: def-sfb-lattice-restriction-cup-comparison). -/
@[instance_reducible] def smallModulesDerived (R : Profinite.CondensedRing.{u})
    [IsCommMonObj R.X] : HasDerivedCategory.{u + 1} (Modules R) :=
  HasDerivedCategory.ofHasKInjectiveResolutions.{u + 1} (Modules R)

/-- The smaller coefficient localization retains its explicit canonical K-injective datum.
Source: paragraph (3) (blueprint: def-sfb-lattice-restriction-cup-comparison). -/
abbrev SmallDerived := @DerivedCategory.{u + 1} (Modules R) _ _ (smallModulesDerived R)

/-- The smaller localization functor, with its localization datum supplied explicitly.
Source: paragraph (3) (blueprint: def-sfb-lattice-restriction-cup-comparison). -/
def smallQ : CochainComplex (Modules R) ℤ ⥤ SmallDerived R :=
  @DerivedCategory.Q.{u + 1} (Modules R) _ _ (smallModulesDerived R)

/-- The identical exact coefficient functor changes only the derived localization universe.
Source: paragraph (3) (blueprint: def-sfb-lattice-restriction-cup-comparison). -/
def raise : SmallDerived R ⥤ DerivedCategory.{u + 2} (Modules R) :=
  @Functor.mapDerivedCategory.{u + 1, u + 2} (Modules R) _ _ (smallModulesDerived R)
    (Modules R) _ _ (modulesDerived R) (𝟭 (Modules R)) _ _ _

/-- The exact identity localization comparison, with both localization data explicit.
Source: paragraph (3) (blueprint: def-sfb-lattice-restriction-cup-comparison). -/
def raiseFactors : smallQ R ⋙ raise R ≅ DerivedCategory.Q.{u + 2} (C := Modules R) :=
  @Functor.mapDerivedCategoryFactors.{u + 1, u + 2}
    (Modules R) _ _ (smallModulesDerived R) (Modules R) _ _ (modulesDerived R)
    (𝟭 (Modules R)) _ _ _

/-- The existing sectionwise computation unit in its recorded smaller localization.
Source: paragraph (3) (blueprint: def-sfb-lattice-restriction-cup-comparison). -/
def sectionUnit (N : CochainComplex
    (CategoryTheory.CondensedBar.Equivariant (ring R) (ULift.{u} (Group r))) ℤ) :
    (smallQ R).obj (((CategoryTheory.CondensedDerivedRestriction.invariants
      (ring R) (ULift.{u} (Group r))).functor.mapHomologicalComplex (.up ℤ)).obj N) ⟶
    (CategoryTheory.CondensedDerivedRestriction.derived (ring R) (ULift.{u} (Group r))).obj
      (DerivedCategory.Q.{u + 1}.obj N) :=
  @Functor.rightDerivedFunctorUnitQ.{u + 2, u + 2, u + 1, u + 1, u + 1, u + 1}
    (CategoryTheory.CondensedBar.Equivariant (ring R) (ULift.{u} (Group r)))
    (Modules R) _ _ _ _ _ (smallModulesDerived R) _
    (CategoryTheory.CondensedDerivedRestriction.invariants
      (ring R) (ULift.{u} (Group r))).functor _ N

/-- The smaller localization has the existing K-flat lax tensor, with its datum explicit.
Source: paragraph (3), proof step 13
(blueprint: def-sfb-lattice-restriction-cup-comparison). -/
instance smallQLax : (smallQ R).LaxMonoidal :=
  @DerivedCategory.instLaxMonoidalCochainComplexIntQ_weilConjectures
    (Modules R) _ _ (smallModulesDerived R) _ _ _ _ _ _ _

/-- The identity functor's tensor comparison is pinned on flat K-flat representatives
and by the localized regular unit, the identity specialization of derivedTensorNormalization.
Source: paragraph (3), proof step 13
(blueprint: def-sfb-lattice-restriction-cup-comparison). -/
def BaseTensorNormalized (c : (raise R).CoreMonoidal) : Prop :=
  (∀ P Q : CochainComplex (Modules R) ℤ,
    (HomologicalComplex.quasiIso (Modules R) (.up ℤ)).kFlat P →
    (HomologicalComplex.quasiIso (Modules R) (.up ℤ)).kFlat Q →
    (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
    (∀ i : ℤ, ObjectProperty.flat (Q.X i)) →
    (raise R).map (Functor.LaxMonoidal.μ (smallQ R) P Q) ≫
      (raiseFactors R).hom.app (P ⊗ Q) =
    (c.μIso ((smallQ R).obj P) ((smallQ R).obj Q)).inv ≫
      ((raiseFactors R).hom.app P ⊗ₘ (raiseFactors R).hom.app Q) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q.{u + 2} P Q) ∧
  c.εIso.hom ≫
      (raise R).map (CategoryTheory.CondensedDerivedRestriction.baseUnitIso (ring R)).hom ≫
      (raiseFactors R).hom.app
        ((HomologicalComplex.single (Modules R) (.up ℤ) 0).obj (𝟙_ (Modules R))) =
    Functor.LaxMonoidal.ε (DerivedCategory.Qh.{u + 2} (C := Modules R))

/-- A comparison of the two discrete action presentations, fixed by its underlying-module
map and every constant section action. The inclusion equation determines the invariant
isomorphism; the computation-unit equation on every complex determines the derived one.
The base tensor comparison is fixed on flat K-flat representatives and the regular unit.
This is a specification of canonical data, with existence asserted by the consuming theorem.
Source: paragraph (3), proof steps 9 and 13
(blueprint: def-sfb-lattice-restriction-cup-comparison). -/
structure Bridge where
  equivalence : CategoryTheory.CondensedBar.Equivariant (ring R) (ULift.{u} (Group r)) ≌
    Equivariant R r
  underlying : equivalence.functor ⋙ Action.forget _ _ ≅
    CategoryTheory.CondensedBar.forgetAction
  constants : ∀ (N : CategoryTheory.CondensedBar.Equivariant (ring R) (ULift.{u} (Group r)))
    (S : Profinite.{u}) (g : Group r)
    (x : CategoryTheory.CondensedBar.sections (ring R) (equivalence.functor.obj N).V S),
    ((underlying.hom.app N).hom.hom.app (op S))
        ((((equivalence.functor.obj N).ρ g).hom.hom.app (op S)) x) =
      N.act S (ContinuousMap.const S (ULift.up g))
        (((underlying.hom.app N).hom.hom.app (op S)) x)
  [additive : equivalence.functor.Additive]
  [limits : PreservesFiniteLimits equivalence.functor]
  [colimits : PreservesFiniteColimits equivalence.functor]
  invariants : equivalence.functor ⋙ DiscreteLattice.invariants R r ≅
    (CategoryTheory.CondensedDerivedRestriction.invariants (ring R) (ULift.{u} (Group r))).functor
  inclusion : ∀ N, invariants.hom.app N ≫
      (CategoryTheory.CondensedDerivedRestriction.invariants
        (ring R) (ULift.{u} (Group r))).inclusion.app N =
    limit.π ((Action.functorCategoryEquivalence (Modules R) (Group r)).functor.obj
      (equivalence.functor.obj N)) PUnit.unit ≫ underlying.hom.app N
  derived : equivalence.functor.mapDerivedCategory.{u + 1, u + 2} ⋙
      derivedInvariants R r ≅
    CategoryTheory.CondensedDerivedRestriction.derived (ring R) (ULift.{u} (Group r)) ⋙ raise R
  normalization : ∀ N : CochainComplex
      (CategoryTheory.CondensedBar.Equivariant (ring R) (ULift.{u} (Group r))) ℤ,
    derivedUnit R r ((equivalence.functor.mapHomologicalComplex (.up ℤ)).obj N) ≫
      (derivedInvariants R r).map
        (equivalence.functor.mapDerivedCategoryFactors.{u + 1, u + 2}.inv.app N) ≫
      derived.hom.app (DerivedCategory.Q.{u + 1}.obj N) =
    DerivedCategory.Q.{u + 2}.map
        ((NatIso.mapHomologicalComplex invariants (.up ℤ)).hom.app N) ≫
      (raiseFactors R).inv.app
        (((CategoryTheory.CondensedDerivedRestriction.invariants
          (ring R) (ULift.{u} (Group r))).functor.mapHomologicalComplex (.up ℤ)).obj N) ≫
      (raise R).map (sectionUnit R r N)
  regular : equivalence.functor.obj
      ((Profinite.CondensedAction.trivial (R := R) (P := ULift.{u} (Group r))).obj
        (𝟙_ (Modules R))) ≅ (regularAlgebra R r).X
  regularUnderlying : regular.hom.hom = underlying.hom.app _
  baseTensor : (raise R).CoreMonoidal
  baseTensorNormalization : BaseTensorNormalized R baseTensor

attribute [instance] Bridge.additive Bridge.limits Bridge.colimits

/-- The regular-coefficient derived invariants comparison uses the same normalized bridge
and the localized underlying identity of the regular module.
Source: paragraph (3), proof step 13
(blueprint: def-sfb-lattice-restriction-cup-comparison). -/
def cohomologyIso (E : Bridge R r) :
    (raise R).obj (CategoryTheory.CondensedDerivedRestriction.cohomology
      (ring R) (ULift.{u} (Group r))) ≅
    (derivedInvariants R r).obj
      ((DerivedCategory.singleFunctor.{u + 2} (Equivariant R r) 0).obj
        (regularAlgebra R r).X) :=
  (E.derived.app (CategoryTheory.CondensedDerivedRestriction.coefficient
    (ring R) (ULift.{u} (Group r)))).symm ≪≫
  (derivedInvariants R r).mapIso
    ((E.equivalence.functor.mapDerivedCategorySingleFunctor.{u + 1, u + 2} 0).app _) ≪≫
  (derivedInvariants R r).mapIso
    ((DerivedCategory.singleFunctor.{u + 2} _ 0).mapIso E.regular)

/-- The missing regular-coefficient clause: under the pinned derived invariants and
universe comparisons, the binary cup and its unit are the restriction-calculus cup and
unit. Both equations retain the actual localized regular-unit identifications.
Source: paragraph (3), proof step 13
(blueprint: def-sfb-lattice-restriction-cup-comparison). -/
def Compatible (E : Bridge R r) : Prop :=
  (raise R).map (CategoryTheory.CondensedDerivedRestriction.cup
      (A := ring R) (G := ULift.{u} (Group r))) ≫ (cohomologyIso R r E).hom =
    (E.baseTensor.μIso _ _).inv ≫
      ((cohomologyIso R r E).hom ⊗ₘ (cohomologyIso R r E).hom) ≫
      DerivedCup.cup R r (regularAlgebra R r) ∧
  E.baseTensor.εIso.hom ≫
      (raise R).map (CategoryTheory.CondensedDerivedRestriction.cupUnit
        (A := ring R) (G := ULift.{u} (Group r))) ≫ (cohomologyIso R r E).hom =
    Functor.LaxMonoidal.ε (DerivedCategory.Qh.{u + 2} (C := Modules R)) ≫
      DerivedCup.cupUnit R r (regularAlgebra R r)

end RestrictionCup
end Profinite.DiscreteLattice
