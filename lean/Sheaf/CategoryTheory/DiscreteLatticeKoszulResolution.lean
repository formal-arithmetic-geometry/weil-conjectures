/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import Sheaf.CategoryTheory.CondensedActionModule
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.CategoryTheory.SheafTensor
import Sheaf.CategoryTheory.InternalActionSitePresentation
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.CategoryTheory.DoubleComplexTotal
import WeilConjectures.Algebra.Homology.FirstQuadrantTotalComparison
import Sheaf.CategoryTheory.DerivedInjectiveResolutionNaturality
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.ModelCategory.Injective

/-! # Discrete lattice invariants and finite Koszul coordinates

Source: main-20261015, direct-image stability proof, paragraph (3), algebraic lattice input;
Stacks Tags 0623 and 062F (blueprint: lem-sfb-discrete-lattice-koszul-resolution).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace Profinite.DiscreteLattice

/-- Internal modules in the recorded profinite-site convention.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-koszul-resolution). -/
abbrev Modules (R : Profinite.CondensedRing.{u}) :=
  Profinite.CondensedAction.Modules R

/-- The multiplicative presentation of the additive lattice with its ordered basis.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-koszul-resolution). -/
abbrev Group (r : ℕ) := Multiplicative (Fin r → ℤ)

/-- Discrete actions, equivalently commuting module automorphisms.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-koszul-resolution). -/
abbrev Equivariant (R : Profinite.CondensedRing.{u}) (r : ℕ) := Action (Modules R) (Group r)

/-- The ith generator is the ith integral basis vector.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-koszul-resolution). -/
def generator {r : ℕ} (i : Fin r) : Group r :=
  Multiplicative.ofAdd (Pi.single i 1)

/-- Invariants are the actual limit of the one-object action diagram.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-koszul-resolution). -/
def invariants (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] (r : ℕ) :
    Equivariant R r ⥤ Modules R :=
  (Action.functorCategoryEquivalence (Modules R) (Group r)).functor ⋙ lim

/-- Invariants preserve addition.
Source: paragraph (3), DAG step 1 (blueprint: lem-sfb-discrete-lattice-koszul-resolution).
Proof: the limit inclusion is monic, and its composites with the maps induced by f+g
and by the sum of the induced maps both equal (f+g) on the underlying module. -/
theorem invariants_additive (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] (r : ℕ) :
    (invariants R r).Additive := by
  sorry

attribute [instance] invariants_additive

/-- The equivariant category admits arbitrary quasi-isomorphisms to K-injectives.
Source: paragraph (3), DAG step 1 (blueprint: lem-sfb-discrete-lattice-koszul-resolution).
Proof: internal modules are Grothendieck by their section-module equivalence. Small
one-object diagrams are Grothendieck by smallModuleDiagrams_isGrothendieckAbelian;
transport along the action equivalence. Apply the K-injective resolution theorem for
Grothendieck abelian categories, and forget that the resolution map is monomorphic. -/
theorem resolutions (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] (r : ℕ)
    (K : CochainComplex (Equivariant R r) ℤ) :
    ∃ (I : CochainComplex (Equivariant R r) ℤ) (s : K ⟶ I),
      I.IsKInjective ∧ QuasiIso s := by
  sorry

/-- Use the standard localization universe without restricting the coefficient universe.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-koszul-resolution). -/
instance modulesDerived (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] :
    HasDerivedCategory.{u + 2} (Modules R) := HasDerivedCategory.standard _

/-- The equivariant derived category uses the same localization universe.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-koszul-resolution). -/
instance equivariantDerived (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] (r : ℕ) :
    HasDerivedCategory.{u + 2} (Equivariant R r) := HasDerivedCategory.standard _

/-- Ordinary total right derived invariants using the recorded universal derived functor.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-koszul-resolution). -/
def derivedInvariants (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] (r : ℕ) :=
  (invariants R r).rightDerivedFunctorOfQuasiIsoResolutions (resolutions R r)

/-- The finite subset labels in a specified integral degree, empty outside [0,r].
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-koszul-resolution). -/
abbrev Subsets (r : ℕ) (a : ℤ) := {I : Finset (Fin r) // (I.card : ℤ) = a}

/-- The signed Koszul matrix from one subset coordinate to another. The formula uses
all summands of the target subset and therefore fixes the precise sign convention.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-koszul-resolution). -/
def differentialEntry {R : Profinite.CondensedRing.{u}} [IsCommMonObj R.X] {r : ℕ}
    (P : Equivariant R r) (I J : Finset (Fin r)) : P.V ⟶ P.V :=
  ∑ i ∈ J, if J.erase i = I then
    ((-1 : ℤ) ^ (J.filter (fun j ↦ j < i)).card) • (@id (P.V ⟶ P.V) (P.ρ (generator i)) - 𝟙 P.V)
    else 0

/-- Finite biproduct coordinates are supplied globally by the internal-module API.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-koszul-resolution). -/
instance subsetFinite (r : ℕ) (a : ℤ) : Fintype (Subsets r a) := Fintype.ofFinite _

/-- Finite Koszul complexes with their exact ordered-subset differential and augmentation.
The coordinates characterize the functor, so the structure does not admit an arbitrary
replacement for the Koszul complex.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-koszul-resolution). -/
structure KoszulModel (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] (r : ℕ) where
  /-- The complex, functorial in equivariant coefficients. -/
  functor : Equivariant R r ⥤ CochainComplex (Modules R) ℤ
  /-- Each term is precisely the stated finite direct sum. -/
  coordinates : ∀ (P : Equivariant R r) (a : ℤ),
    (functor.obj P).X a ≅ ⨁ (fun _ : Subsets r a ↦ P.V)
  /-- The differential in these coordinates has the prescribed signs. -/
  differential : ∀ (P : Equivariant R r) (a : ℤ)
    (I : Subsets r a) (J : Subsets r (a + 1)),
    biproduct.ι _ I ≫ (coordinates P a).inv ≫ (functor.obj P).d a (a + 1) ≫
      (coordinates P (a + 1)).hom ≫ biproduct.π _ J = differentialEntry P I.val J.val
  /-- Maps act termwise on every subset coordinate. -/
  maps : ∀ {P Q : Equivariant R r} (f : P ⟶ Q) (a : ℤ)
    (I J : Subsets r a),
    biproduct.ι _ I ≫ (coordinates P a).inv ≫ (functor.map f).f a ≫
      (coordinates Q a).hom ≫ biproduct.π _ J = if I = J then f.hom else 0
  /-- The map from invariants, regarded as a complex concentrated in degree zero. -/
  augmentation : invariants R r ⋙ HomologicalComplex.single (Modules R) (.up ℤ) 0 ⟶
    functor
  /-- Its only possible nonzero component is the actual invariant inclusion. -/
  augmentation_zero : ∀ (P : Equivariant R r) (I : Subsets r 0),
    (augmentation.app P).f 0 ≫ (coordinates P 0).hom ≫ biproduct.π _ I =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 ((invariants R r).obj P)).hom ≫
        limit.π ((Action.functorCategoryEquivalence (Modules R) (Group r)).functor.obj P)
          PUnit.unit

/-- The recorded universal derived unit, expressed on actual cochain complexes.
Source: paragraph (3), normalized derived functor
(blueprint: lem-sfb-discrete-lattice-koszul-resolution). -/
def derivedUnit (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] (r : ℕ)
    (K : CochainComplex (Equivariant R r) ℤ) :
    DerivedCategory.Q.obj (((invariants R r).mapHomologicalComplex (.up ℤ)).obj K) ⟶
      (derivedInvariants R r).obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso (Modules R)).inv.app
      (((invariants R r).mapHomologicalComplex (.up ℤ)).obj K) ≫
    ((invariants R r).rightDerivedFunctorOfQuasiIsoResolutionsUnit
      (resolutions R r)).app ((HomotopyCategory.quotient _ _).obj K) ≫
    (derivedInvariants R r).map
      ((DerivedCategory.quotientCompQhIso (Equivariant R r)).hom.app K)

/-- The degree-zero invariant map into derived invariants, with its specified unit.
Source: paragraph (3), DAG steps 6 and 9
(blueprint: lem-sfb-discrete-lattice-koszul-resolution). -/
def invariantUnit (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] (r : ℕ)
    (P : Equivariant R r) :
    (DerivedCategory.singleFunctor (Modules R) 0).obj ((invariants R r).obj P) ⟶
      (derivedInvariants R r).obj ((DerivedCategory.singleFunctor _ 0).obj P) :=
  DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex (invariants R r) (.up ℤ) 0).inv.app
        P) ≫
    derivedUnit R r ((HomologicalComplex.single _ (.up ℤ) 0).obj P)

/-- Restriction is the existing internal-module comap, with the original monoid map.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-koszul-resolution). -/
abbrev restriction {R R' : Profinite.CondensedRing.{u}} (φ : R ⟶ R') :
    Modules R' ⥤ Modules R := Mod.comap φ.hom

/-- Apply scalar restriction to the action without changing its group.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-koszul-resolution). -/
def equivariantRestriction {R R' : Profinite.CondensedRing.{u}} (φ : R ⟶ R') (r : ℕ) :
    Equivariant R' r ⥤ Equivariant R r :=
  (restriction φ).mapAction (Group r)

/-- Restricting action maps preserves their original addition.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-koszul-resolution). -/
instance equivariantRestriction_additive {R R' : Profinite.CondensedRing.{u}}
    [IsCommMonObj R.X] [IsCommMonObj R'.X] (φ : R ⟶ R') (r : ℕ) :
    (equivariantRestriction φ r).Additive where
  map_add := by intros; rfl

/-- Limit-preserving restriction commutes with actual invariants. The map is the
canonical limit comparison, with no choice of a map or of fixed sections.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-koszul-resolution). -/
def restrictionInvariants {R R' : Profinite.CondensedRing.{u}}
    [IsCommMonObj R.X] [IsCommMonObj R'.X] (φ : R ⟶ R') (r : ℕ)
    (P : Equivariant R' r) :
    (restriction φ).obj ((invariants R' r).obj P) ≅
      (invariants R r).obj ((equivariantRestriction φ r).obj P) :=
  preservesLimitIso (restriction φ)
    ((Action.functorCategoryEquivalence (Modules R') (Group r)).functor.obj P)

/-- Naturality of the invariant limit comparison.
Source: paragraph (3), DAG step 8 (blueprint: lem-sfb-discrete-lattice-koszul-resolution).
Proof: compose with the invariant limit inclusion. Both composites are the original
linear map after coefficient restriction; limit uniqueness identifies them. -/
theorem restrictionInvariants_naturality {R R' : Profinite.CondensedRing.{u}}
    [IsCommMonObj R.X] [IsCommMonObj R'.X] (φ : R ⟶ R') (r : ℕ)
    {P Q : Equivariant R' r} (f : P ⟶ Q) :
    (restriction φ).map ((invariants R' r).map f) ≫
        (restrictionInvariants φ r Q).hom =
      (restrictionInvariants φ r P).hom ≫
        (invariants R r).map ((equivariantRestriction φ r).map f) := by
  sorry

/-- The ordinary invariant comparison on a complex is the degreewise limit comparison.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-koszul-resolution). -/
def restrictionInvariantComplex {R R' : Profinite.CondensedRing.{u}}
    [IsCommMonObj R.X] [IsCommMonObj R'.X] (φ : R ⟶ R') (r : ℕ)
    (K : CochainComplex (Equivariant R' r) ℤ) :
    ((restriction φ).mapHomologicalComplex (.up ℤ)).obj
        (((invariants R' r).mapHomologicalComplex (.up ℤ)).obj K) ≅
      ((invariants R r).mapHomologicalComplex (.up ℤ)).obj
        (((equivariantRestriction φ r).mapHomologicalComplex (.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents (fun a ↦ restrictionInvariants φ r (K.X a))
    (fun a b _ ↦ (restrictionInvariants_naturality φ r (K.d a b)).symm)

/-- The normalized comparison attached to any K-injective resolution of P[0].
Source: paragraph (3), DAG steps 6--9
(blueprint: lem-sfb-discrete-lattice-koszul-resolution). -/
def resolutionComparison {R : Profinite.CondensedRing.{u}} [IsCommMonObj R.X] (r : ℕ)
    (P : Equivariant R r) (I : CochainComplex (Equivariant R r) ℤ) [I.IsKInjective]
    (s : (HomologicalComplex.single _ (.up ℤ) 0).obj P ⟶ I) [QuasiIso s] :
    (derivedInvariants R r).obj ((DerivedCategory.singleFunctor _ 0).obj P) ≅
      DerivedCategory.Q.obj (((invariants R r).mapHomologicalComplex (.up ℤ)).obj I) :=
  (invariants R r).rightDerivedFunctorOfQuasiIsoResolutionsObjIso (resolutions R r) s

/-- The coefficient map is specified on every pair of K-injective resolutions. This
records the inverse of the ordinary derived-unit comparison on the restricted resolution;
restriction is not assumed to preserve injectives.
Source: paragraph (3), DAG steps 8--9
(blueprint: lem-sfb-discrete-lattice-koszul-resolution). -/
structure CoefficientComparison {R R' : Profinite.CondensedRing.{u}}
    [IsCommMonObj R.X] [IsCommMonObj R'.X] (φ : R ⟶ R') (r : ℕ) where
  /-- The canonical coefficient isomorphism on each equivariant module. -/
  iso : ∀ P : Equivariant R' r,
    (derivedInvariants R r).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((equivariantRestriction φ r).obj P)) ≅
      (restriction φ).mapDerivedCategory.obj
        ((derivedInvariants R' r).obj ((DerivedCategory.singleFunctor _ 0).obj P))
  /-- Resolution normalization determines the coefficient isomorphism. -/
  normalization : ∀ (P : Equivariant R' r)
    (I : CochainComplex (Equivariant R r) ℤ) (J : CochainComplex (Equivariant R' r) ℤ)
    [I.IsKInjective] [J.IsKInjective]
    (s : (HomologicalComplex.single _ (.up ℤ) 0).obj
      ((equivariantRestriction φ r).obj P) ⟶ I)
    (t : (HomologicalComplex.single _ (.up ℤ) 0).obj P ⟶ J)
    [QuasiIso s] [QuasiIso t]
    (β : ((equivariantRestriction φ r).mapHomologicalComplex (.up ℤ)).obj J ⟶ I),
    (HomologicalComplex.singleMapHomologicalComplex
        (equivariantRestriction φ r) (.up ℤ) 0).inv.app P ≫
      ((equivariantRestriction φ r).mapHomologicalComplex (.up ℤ)).map t ≫ β = s →
    (iso P).inv ≫ (resolutionComparison r _ I s).hom =
      (restriction φ).mapDerivedCategory.map (resolutionComparison r P J t).hom ≫
        (restriction φ).mapDerivedCategoryFactors.hom.app
          (((invariants R' r).mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map ((restrictionInvariantComplex φ r J).hom ≫
          ((invariants R r).mapHomologicalComplex (.up ℤ)).map β)

/-- A natural Koszul comparison with the actual invariant inclusion normalization.
Source: paragraph (3), DAG steps 5--7
(blueprint: lem-sfb-discrete-lattice-koszul-resolution). -/
structure Comparison (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] (r : ℕ)
    (K : KoszulModel R r) where
  /-- The comparison is an isomorphism in the ordinary derived category. -/
  iso : K.functor ⋙ DerivedCategory.Q ≅
    DerivedCategory.singleFunctor _ 0 ⋙ derivedInvariants R r
  /-- The invariant augmentation is carried to the ordinary derived unit. -/
  normalization : ∀ P : Equivariant R r,
    DerivedCategory.Q.map (K.augmentation.app P) ≫ iso.hom.app P = invariantUnit R r P

/-- Discrete lattice cohomology is the finite Koszul complex with its ordered signs,
invariant inclusion, naturality, canonical coefficient square and rank-zero identity.
Source: main-20261015 direct-image proof paragraph (3), algebraic lattice input;
Stacks Tags 0623 and 062F (blueprint: lem-sfb-discrete-lattice-koszul-resolution).

Proof, following the ten DAG steps:
1. Use the internal/section-module equivalence and small-module-diagram Grothendieck
property on the one-object lattice category; choose equivariant injective resolutions.
2. Internalize the integral lattice cubical contraction by replacing each integral
basis element with a copy of the coefficient module. Its finite columns define maps;
the augmented underlying complex is split exact, hence also exact equivariantly.
3. Tensor the cubical complex by the free test module R[S]. Its augmented complex is
exact without projectivity. Applying Hom into an equivariant injective is exact;
evaluation on every profinite S detects exactness of the internal Hom complex.
4. Evaluate equivariant maps on [0,I]. The boundary gives precisely the signed T_i-1
matrix, and the augmentation is the invariant inclusion. Opposite signs cancel in d².
5. Apply the finite-biproduct functors K^a to an injective resolution. Columnwise
quasi-isomorphisms give K(P) -> Tot K(I) by first-quadrant total comparison.
6. The acyclic-injective calculation gives Gamma(I) -> Tot K(I) by the row version of
total comparison. The transpose sign (-1)^(ab) identifies conventions and is one on
both axes. Invert this map and compose to obtain lambda; its augmentation is the unit.
7. Lift coefficient maps to resolutions. Two lifts are homotopic, and multiplying the
vertical homotopy in column a by (-1)^a yields a total homotopy. Thus lambda is natural.
8. For scalar restriction U, extend UP'[0] -> I along the monic quasi-isomorphism
UP'[0] -> UJ, obtaining beta:UJ -> I. Restriction is exact but need not preserve
injectives. Finite column comparison and the acyclic rows imply Gamma(beta) is a
quasi-isomorphism.
9. Invert Gamma(beta) using the normalized derived unit. Homotopy uniqueness of the
extension proves independence. Both total-comparison squares commute already on
complexes; inversion gives exactly the coefficient square stated here.
10. With no generators K is P[0] and Gamma is the identity. The two total maps reduce
to the resolution and its identity; lambda is the identity under those canonical
identifications. Zero modules and zero rings obey the same formulas. -/
theorem discrete_lattice_koszul_resolution :
    ∃ (K : ∀ (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] (r : ℕ), KoszulModel R r)
      (comparison : ∀ (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] (r : ℕ),
        Comparison R r (K R r)),
      (∀ (R R' : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] [IsCommMonObj R'.X]
        (φ : R ⟶ R') (r : ℕ),
        ∃ c : CoefficientComparison φ r,
        ∀ P' : Equivariant R' r,
        ∃ k : (K R r).functor.obj ((equivariantRestriction φ r).obj P') ≅
          ((restriction φ).mapHomologicalComplex (.up ℤ)).obj ((K R' r).functor.obj P'),
        (∀ (a : ℤ) (I J : Subsets r a),
          biproduct.ι _ I ≫ ((K R r).coordinates _ a).inv ≫ k.hom.f a ≫
            (restriction φ).map (((K R' r).coordinates P' a).hom ≫ biproduct.π _ J) =
              if I = J then 𝟙 _ else 0) ∧
        (∀ (P : Equivariant R r) (f : P ⟶ (equivariantRestriction φ r).obj P'),
          (comparison R r).iso.hom.app P ≫
              (derivedInvariants R r).map ((DerivedCategory.singleFunctor _ 0).map f) ≫
              (c.iso P').hom =
            DerivedCategory.Q.map ((K R r).functor.map f ≫ k.hom) ≫
              (restriction φ).mapDerivedCategoryFactors.inv.app
                ((K R' r).functor.obj P') ≫
              (restriction φ).mapDerivedCategory.map ((comparison R' r).iso.hom.app P'))) ∧
      (∀ (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] (P : Equivariant R 0),
        ∃ (e : P.V ≅ (invariants R 0).obj P)
          (k : (K R 0).functor.obj P ≅ (HomologicalComplex.single _ (.up ℤ) 0).obj P.V),
          e.hom ≫ limit.π
            ((Action.functorCategoryEquivalence (Modules R) (Group 0)).functor.obj P)
              PUnit.unit = 𝟙 P.V ∧
          k.hom.f 0 = ((K R 0).coordinates P 0).hom ≫
            biproduct.π _ ⟨∅, rfl⟩ ≫
              (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P.V).inv ∧
          (comparison R 0).iso.hom.app P = DerivedCategory.Q.map k.hom ≫
            (DerivedCategory.singleFunctor _ 0).map e.hom ≫ invariantUnit R 0 P) := by
  sorry

end Profinite.DiscreteLattice
