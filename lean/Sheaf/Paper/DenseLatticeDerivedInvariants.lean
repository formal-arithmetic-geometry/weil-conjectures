/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.CategoryTheory.CondensedActionModule
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import Sheaf.CategoryTheory.CondensedEquivariantBarData
public import Sheaf.RepresentationTheory.LAdic
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Sheaf.CategoryTheory.DerivedInjectiveResolutionNaturality
import Sheaf.RepresentationTheory.ContinuousCoefficientSubquotients
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Dense integer lattices and ordinary internal derived invariants

Source: main-20261015 blueprint, direct-image stability, paragraph (3), agent-expanded
analytic condensed tame-inertia input
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison).

All actions below are the recorded internal actions on the coherent profinite site.
Right-derived functors are specified by their localization universal property. The
restriction arrow is constructed by that universal property from the invariant inclusion.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace Profinite.DenseLattice

/-- Bundle exactly the recorded continuous coefficient ring object.
Source: blueprint paragraph (3), coefficients C(S,F)
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
def coefficientRing (F : Type u) [TopologicalSpace F] [CommRing F] [IsTopologicalRing F] :
    CategoryTheory.CondensedBar.Ring.{u} :=
  { X := continuousMapRingObjOfUniverse.{u, u} F
    mon := continuousMapRingObjOfUniverseMonObj.{u, u} F
    comm := isCommMonObj_continuousMapRingObjOfUniverse.{u, u} F }

variable (A : CategoryTheory.CondensedBar.Ring.{u})
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The canonical abelian properties of the fixed category of internal action modules.
Only proof data is supplied; the existing addition and composition remain fixed.
Source: blueprint paragraph (3), restriction calculus, first paragraph
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison).
Proof: present actions as modules over the internal group ring. Kernels and cokernels
are the underlying internal-module kernels and cokernels with the induced actions.
Finite products are underlying products, and every mono and epi is normal. These are
precisely the five proof fields of the existing ActionAbelian interface. -/
theorem actionAbelian_exists : Nonempty (CategoryTheory.CondensedBar.ActionAbelian A G) := by
  sorry

/-- The fixed action category's abelian proof properties; all fields are propositions.
Source: blueprint paragraph (3), restriction calculus
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
instance actionAbelian : CategoryTheory.CondensedBar.ActionAbelian A G :=
  Classical.choice (actionAbelian_exists A G)

/-- A normalized invariant subsheaf exists, with exactly the recorded fixed sections.
Source: blueprint paragraph (3), restriction calculus
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison).
Proof: the sections fixed after every profinite base change form submodules stable
under restrictions and gluing. Restrict equivariant maps to these submodules. Maps from
trivial actions have precisely fixed image; restricting the codomain and composing with
the inclusion are inverse adjunction transposes. This is the existing Invariants record,
which determines the object and every map up to its unique inclusion-preserving isomorphism. -/
theorem invariants_exists : Nonempty (CategoryTheory.CondensedBar.Invariants A G) := by
  sorry

/-- The invariant subsheaf, chosen solely by its fixed-section and adjunction properties.
Source: blueprint paragraph (3), restriction calculus
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
def invariants : CategoryTheory.CondensedBar.Invariants A G :=
  Classical.choice (invariants_exists A G)

variable [HasDerivedCategory.{u + 2} (CategoryTheory.CondensedBar.Equivariant A G)]
  [HasDerivedCategory.{u + 2} (CategoryTheory.CondensedBar.Modules A)]

/-- The ordinary complex-level invariant functor followed by localization.
Source: blueprint paragraph (3), ordinary total right derived invariants
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
def invariantComplex :
    CochainComplex (CategoryTheory.CondensedBar.Equivariant A G) ℤ ⥤
      DerivedCategory (CategoryTheory.CondensedBar.Modules A) :=
  (invariants A G).functor.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

/-- The ordinary total right derived functor exists in the internal-module category.
Source: blueprint paragraph (3), restriction calculus
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison).
Proof: the internal group-ring module category is Grothendieck abelian. Choose K-injective
resolutions. Localization of the invariant functor on those resolutions gives the left
Kan extension at quasi-isomorphisms, hence the ordinary total right derived functor. On
bounded-below objects an ordinary equivariant injective resolution computes it. -/
theorem invariantComplex_hasRightDerived :
    (invariantComplex A G).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (CategoryTheory.CondensedBar.Equivariant A G) (.up ℤ)) := by
  sorry

attribute [instance] invariantComplex_hasRightDerived

/-- Ordinary derived invariants, obtained by the localization universal property.
Source: blueprint paragraph (3), definition of RΓ
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
def derivedInvariants :
    DerivedCategory (CategoryTheory.CondensedBar.Equivariant A G) ⥤
      DerivedCategory (CategoryTheory.CondensedBar.Modules A) :=
  (invariantComplex A G).totalRightDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso (CategoryTheory.CondensedBar.Equivariant A G) (.up ℤ))

/-- The actual right-derived unit, retaining its normalization before localization.
Source: blueprint paragraph (3), canonical derived restriction
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
def derivedUnit : invariantComplex A G ⟶ DerivedCategory.Q ⋙ derivedInvariants A G :=
  (invariantComplex A G).totalRightDerivedUnit DerivedCategory.Q
    (HomologicalComplex.quasiIso (CategoryTheory.CondensedBar.Equivariant A G) (.up ℤ))

/-- Expose the universal property of the actual chosen total right derived functor.
Source: Mathlib right-derived localization universal property, blueprint paragraph (3)
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
instance derivedInvariants_isRightDerived :
    (derivedInvariants A G).IsRightDerivedFunctor (derivedUnit A G)
      (HomologicalComplex.quasiIso (CategoryTheory.CondensedBar.Equivariant A G) (.up ℤ)) := by
  dsimp only [derivedInvariants, derivedUnit]
  infer_instance

variable (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [HasDerivedCategory.{u + 2} (CategoryTheory.CondensedBar.Equivariant A H)]
  (ι : H →ₜ* G)

/-- Restriction acts on exactly the existing action modules.
Source: blueprint paragraph (3), restriction along ι
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
abbrev restriction := Profinite.CondensedAction.inflate (R := A.toMon) ι

/-- Restriction is additive and exact because it leaves underlying modules unchanged.
Source: blueprint paragraph (3), restriction calculus
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison).
Proof: precompose every section action with C(S,ι). The underlying maps, kernels and
cokernels are unchanged; addition and both finite-limit constructions are unchanged. -/
theorem restriction_exact :
    (restriction A G H ι).Additive ∧
    PreservesFiniteLimits (restriction A G H ι) ∧
    PreservesFiniteColimits (restriction A G H ι) := by
  sorry

/-- Additivity of restriction, with the original addition of internal maps.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
instance restriction_additive : (restriction A G H ι).Additive :=
  (restriction_exact A G H ι).1

/-- Restriction preserves finite limits on the fixed action category.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
instance restriction_limits : PreservesFiniteLimits (restriction A G H ι) :=
  (restriction_exact A G H ι).2.1

/-- Restriction preserves finite colimits on the fixed action category.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
instance restriction_colimits : PreservesFiniteColimits (restriction A G H ι) :=
  (restriction_exact A G H ι).2.2

/-- The invariant inclusion uniquely determines its restriction transformation.
Source: blueprint paragraph (3), specified underived restriction map
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison).
Proof: a section fixed by every generalized element of G is fixed after restricting to H.
The image characterization in Invariants gives a unique factorization through the
H-invariant subsheaf. Injectivity of its inclusion gives naturality and uniqueness. -/
theorem invariantRestriction_existsUnique :
    ∃! τ : (invariants A G).functor ⟶ restriction A G H ι ⋙ (invariants A H).functor,
      ∀ N, τ.app N ≫ (invariants A H).inclusion.app ((restriction A G H ι).obj N) =
        (invariants A G).inclusion.app N := by
  sorry

/-- Restriction of invariants is the uniquely inclusion-preserving factorization.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
def invariantRestriction :
    (invariants A G).functor ⟶ restriction A G H ι ⋙ (invariants A H).functor :=
  (invariantRestriction_existsUnique A G H ι).choose

/-- The ordinary comparison on complexes followed by the H-derived unit. All components
are specified before the derived universal property is applied.
Source: blueprint paragraph (3), canonical derived restriction
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
def restrictionUnitComponent (K : CochainComplex
    (CategoryTheory.CondensedBar.Equivariant A G) ℤ) :
    (invariantComplex A G).obj K ⟶
      ((restriction A G H ι).mapDerivedCategory ⋙ derivedInvariants A H).obj
        (DerivedCategory.Q.obj K) :=
    DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (invariantRestriction A G H ι) (.up ℤ)).app K) ≫
      (derivedUnit A H).app (((restriction A G H ι).mapHomologicalComplex (.up ℤ)).obj K) ≫
      (derivedInvariants A H).map
        ((restriction A G H ι).mapDerivedCategoryFactors.inv.app K)

/-- The explicit restriction-unit components are natural in complexes.
Source: blueprint paragraph (3), restriction calculus
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison).
Proof: apply naturality of the invariant inclusion, the derived unit and the exact
restriction factorization in succession. Functoriality identifies the two composites. -/
theorem restrictionUnit_naturality
    {K L : CochainComplex (CategoryTheory.CondensedBar.Equivariant A G) ℤ} (f : K ⟶ L) :
    (invariantComplex A G).map f ≫ restrictionUnitComponent A G H ι L =
      restrictionUnitComponent A G H ι K ≫
        ((restriction A G H ι).mapDerivedCategory ⋙ derivedInvariants A H).map
          (DerivedCategory.Q.map f) := by
  sorry

/-- The natural comparison before the derived universal property.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
def restrictionUnit : invariantComplex A G ⟶ DerivedCategory.Q ⋙
    (restriction A G H ι).mapDerivedCategory ⋙ derivedInvariants A H where
  app := restrictionUnitComponent A G H ι
  naturality _ _ f := restrictionUnit_naturality A G H ι f

/-- The specified derived restriction arrow, constructed by right Kan extension from the
invariant inclusion. It is not an isomorphism selected between the two derived objects.
Source: blueprint paragraph (3), b_F
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
def derivedRestriction : derivedInvariants A G ⟶
    (restriction A G H ι).mapDerivedCategory ⋙ derivedInvariants A H :=
  (derivedInvariants A G).rightDerivedDesc (derivedUnit A G)
    (HomologicalComplex.quasiIso (CategoryTheory.CondensedBar.Equivariant A G) (.up ℤ))
    _ (restrictionUnit A G H ι)

/-- The restriction arrow on a module in degree zero, with the canonical exact-functor
single-complex identification inserted on its target.
Source: blueprint paragraph (3), b_F on V_F[0]
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
def moduleRestriction (N : CategoryTheory.CondensedBar.Equivariant A G) :
    (derivedInvariants A G).obj ((DerivedCategory.singleFunctor _ 0).obj N) ⟶
      (derivedInvariants A H).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((restriction A G H ι).obj N)) :=
  (derivedRestriction A G H ι).app ((DerivedCategory.singleFunctor _ 0).obj N) ≫
    (derivedInvariants A H).map
      (((restriction A G H ι).mapDerivedCategorySingleFunctor 0).hom.app N)

/-- Naturality retains the specified restriction transformation for every equivariant map.
Source: blueprint paragraph (3), naturality clause
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison).
Proof: use naturality of the right-Kan-extension transformation and of the canonical
identification of exact restriction with the degree-zero single-complex functor. -/
theorem moduleRestriction_naturality {N N' : CategoryTheory.CondensedBar.Equivariant A G}
    (f : N ⟶ N') :
    (derivedInvariants A G).map ((DerivedCategory.singleFunctor _ 0).map f) ≫
      moduleRestriction A G H ι N' = moduleRestriction A G H ι N ≫
        (derivedInvariants A H).map
          ((DerivedCategory.singleFunctor _ 0).map ((restriction A G H ι).map f)) := by
  sorry

/-- The derived unit on a module in degree zero, with its single-complex normalization.
Source: blueprint paragraph (3), degree-zero normalization
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
def zeroUnit (N : CategoryTheory.CondensedBar.Equivariant A G) :
    (DerivedCategory.singleFunctor _ 0).obj ((invariants A G).functor.obj N) ⟶
      (derivedInvariants A G).obj ((DerivedCategory.singleFunctor _ 0).obj N) :=
  DerivedCategory.Q.map
    ((HomologicalComplex.singleMapHomologicalComplex (invariants A G).functor
      (.up ℤ) 0).inv.app N) ≫
    (derivedUnit A G).app ((HomologicalComplex.single _ (.up ℤ) 0).obj N)

/-- The canonical map from invariants to degree-zero derived invariants.
Source: blueprint paragraph (3), identity on invariants
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
def zeroSectionMap (N : CategoryTheory.CondensedBar.Equivariant A G) :
    (invariants A G).functor.obj N ⟶
      (DerivedCategory.homologyFunctor _ 0).obj
        ((derivedInvariants A G).obj ((DerivedCategory.singleFunctor _ 0).obj N)) :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app
    ((invariants A G).functor.obj N) ≫
      (DerivedCategory.homologyFunctor _ 0).map (zeroUnit A G N)

/-- Left exactness of invariants identifies it with degree-zero derived invariants.
Source: blueprint paragraph (3), restriction calculus, degree-zero assertion
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison).
Proof: invariants is a right adjoint, so it is left exact. In an equivariant injective
resolution, its degree-zero kernel is therefore the invariant submodule of N itself.
The augmentation gives exactly zeroSectionMap, not an independently chosen isomorphism. -/
theorem zeroSectionMap_isIso (N : CategoryTheory.CondensedBar.Equivariant A G) :
    IsIso (zeroSectionMap A G N) := by
  sorry

attribute [instance] zeroSectionMap_isIso

/-- The augmentation-normalized identification H⁰(RΓ N) = Γ N.
Source: blueprint paragraph (3), degree-zero clause
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
def zeroIso (N : CategoryTheory.CondensedBar.Equivariant A G) :
    (DerivedCategory.homologyFunctor _ 0).obj
      ((derivedInvariants A G).obj ((DerivedCategory.singleFunctor _ 0).obj N)) ≅
        (invariants A G).functor.obj N :=
  (asIso (zeroSectionMap A G N)).symm

/-- The actual degree-zero comparison is the ordinary invariant inclusion.
Source: blueprint paragraph (3), degree-zero clause
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison).
Proof: the defining right-derived factorization of b commutes with the two augmentation
units. Apply H⁰ and the augmentation-normalized identifications zeroIso. The resulting
map is exactly the invariant inclusion used to define the transformation. -/
theorem moduleRestriction_zero (N : CategoryTheory.CondensedBar.Equivariant A G) :
    (DerivedCategory.homologyFunctor _ 0).map (moduleRestriction A G H ι N) ≫
      (zeroIso A H ((restriction A G H ι).obj N)).hom =
        (zeroIso A G N).hom ≫ (invariantRestriction A G H ι).app N := by
  sorry

/-- Invariants for a trivial group are the original module, and their derived unit on
modules is invertible, with the actual inclusion and augmentation as the two maps.
Source: blueprint paragraph (3), rank-zero clause
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison).
Proof: every generalized element of a singleton group is its unit, so every section is
fixed after every base change. The invariant inclusion is therefore an isomorphism.
The invariant functor is exact; its ordinary unit computes its derived functor on
single complexes and is an isomorphism. -/
theorem trivialGroup_normalization [Subsingleton G]
    (N : CategoryTheory.CondensedBar.Equivariant A G) :
    IsIso ((invariants A G).inclusion.app N) ∧ IsIso (zeroUnit A G N) := by
  sorry

/-- The actual invariant inclusion for a trivial group is invertible.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
instance trivial_inclusion_isIso [Subsingleton G]
    (N : CategoryTheory.CondensedBar.Equivariant A G) :
    IsIso ((invariants A G).inclusion.app N) := (trivialGroup_normalization A G N).1

/-- The augmentation unit for a trivial group is invertible on modules.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
instance trivial_zeroUnit_isIso [Subsingleton G]
    (N : CategoryTheory.CondensedBar.Equivariant A G) :
    IsIso (zeroUnit A G N) := (trivialGroup_normalization A G N).2

/-- The unit-and-inclusion-normalized identification RΓ_{1}(N) = N[0].
Source: blueprint paragraph (3), rank-zero identity
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
def trivialIso [Subsingleton G] (N : CategoryTheory.CondensedBar.Equivariant A G) :
    (derivedInvariants A G).obj ((DerivedCategory.singleFunctor _ 0).obj N) ≅
      (DerivedCategory.singleFunctor _ 0).obj N.module :=
  (asIso (zeroUnit A G N)).symm ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (asIso ((invariants A G).inclusion.app N))

/-- Between trivial groups the specified comparison is identity after the canonical
unit-and-inclusion identifications with the original module in degree zero.
Source: blueprint paragraph (3), r = 0
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison).
Proof: the underived invariant comparison becomes identity under the two inclusions.
The right-derived unit equation defining derivedRestriction then makes the normalized
comparison identity on the original module in degree zero. -/
theorem moduleRestriction_trivial [Subsingleton G] [Subsingleton H]
    (N : CategoryTheory.CondensedBar.Equivariant A G) :
    moduleRestriction A G H ι N ≫ (trivialIso A H ((restriction A G H ι).obj N)).hom =
      (trivialIso A G N).hom := by
  sorry

section Lattice

/-- The additive ell-adic lattice, written multiplicatively for the existing action API.
The universe lift carries its original inverse-limit topology.
Source: blueprint paragraph (3), L = Z_ell^r
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
abbrev AdicLattice (l r : ℕ) [Fact l.Prime] :=
  ULift.{u} (Multiplicative (Fin r → PadicInt l))

/-- The integer lattice with its discrete topology, including the rank-zero lattice.
Source: blueprint paragraph (3), D = Z^r
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
abbrev IntegerLattice (r : ℕ) := ULift.{u} (Multiplicative (Fin r → ℤ))

variable (l r : ℕ) [Fact l.Prime]

/-- The actual coordinatewise integer inclusion.
Source: blueprint paragraph (3), the specified standard generators
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
def latticeFunction (n : IntegerLattice.{u} r) : AdicLattice.{u} l r :=
  ULift.up (Multiplicative.ofAdd (fun i ↦ (Multiplicative.toAdd n.down i : PadicInt l)))

/-- The coordinatewise inclusion preserves the group operations.
Source: blueprint paragraph (3), definition of ι
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison).
Proof: at each coordinate the two identities are integer-cast zero and integer-cast add
in Z_ell. The domain is discrete, so the resulting homomorphism is continuous. -/
theorem latticeFunction_laws :
    latticeFunction.{u} l r 1 = 1 ∧
    ∀ x y, latticeFunction.{u} l r (x * y) =
      latticeFunction l r x * latticeFunction l r y := by
  sorry

/-- The continuous homomorphism sending each integer generator to the corresponding
ell-adic coordinate generator. No completion or alternative dense subgroup is used.
Source: blueprint paragraph (3), ι
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
def latticeInclusion : IntegerLattice.{u} r →ₜ* AdicLattice.{u} l r where
  toFun := latticeFunction l r
  map_one' := (latticeFunction_laws l r).1
  map_mul' := (latticeFunction_laws l r).2
  continuous_toFun := continuous_of_discreteTopology

end Lattice

section Realization

variable (E F : Type u) [NormedField E] [NormedField F] [Algebra E F]
  (V : Type v) [AddCommGroup V] [Module E V]

/-- Scalar extension with the finite-dimensional module topology, which is exactly the
product norm topology in any basis. In particular F is not completed.
Source: blueprint paragraph (3), F tensor_E V
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
def ScalarSpace := F ⊗[E] V

/-- The canonical scalar-extension structure with the finite-product module topology.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
instance scalarSpaceAddCommGroup : AddCommGroup (ScalarSpace E F V) :=
  inferInstanceAs (AddCommGroup (F ⊗[E] V))

/-- The canonical scalar-extension structure with the finite-product module topology.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
instance scalarSpaceModule : Module F (ScalarSpace E F V) :=
  inferInstanceAs (Module F (F ⊗[E] V))

/-- The canonical scalar-extension structure with the finite-product module topology.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
instance scalarSpaceTopology : TopologicalSpace (ScalarSpace E F V) :=
  moduleTopology F (F ⊗[E] V)

/-- The canonical scalar-extension structure with the finite-product module topology.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
instance scalarSpaceModuleTopology : IsModuleTopology F (ScalarSpace E F V) := ⟨rfl⟩

/-- The canonical scalar-extension structure with the finite-product module topology.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
instance scalarSpaceTopologicalAddGroup : IsTopologicalAddGroup (ScalarSpace E F V) :=
  IsModuleTopology.topologicalAddGroup F (ScalarSpace E F V)

/-- The canonical scalar-extension structure with the finite-product module topology.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
instance scalarSpaceContinuousSMul : ContinuousSMul F (ScalarSpace E F V) :=
  inferInstanceAs (ContinuousSMul F (ScalarSpace E F V))

variable (P : Type u) [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  (ρ : P →* (V ≃ₗ[E] V))

/-- A presentation of the actual continuous-section action module. Both restriction and
scalar multiplication are prescribed, and the action is pointwise scalar extension of ρ.
Thus this record determines the presented object up to its unique section-preserving
isomorphism, and cannot present a different condensed module.
Source: blueprint paragraph (3), V_F(S) = C(S,F tensor_E V)
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
structure Realization where
  module : CategoryTheory.CondensedBar.Equivariant (coefficientRing F) P
  sections : ∀ S : Profinite.{u},
    Profinite.CondensedAction.sectionModule (coefficientRing F).toMon module.module S ≃+
      ULift.{max u v + 1} C(S, ScalarSpace E F V)
  naturality : ∀ (S T : Profinite.{u}) (f : T ⟶ S)
    (m : Profinite.CondensedAction.sectionModule (coefficientRing F).toMon module.module S),
    sections T ((module.module.X.obj.map f.op).hom m) =
      ULift.up ((sections S m).down.comp f.hom.hom)
  linearity : ∀ (S : Profinite.{u})
    (c : (CategoryTheory.InternalAbelianSheafModule.sectionRings
      (coherentTopology Profinite.{u}) (coefficientRing F).X).obj (op S))
    (m : Profinite.CondensedAction.sectionModule (coefficientRing F).toMon module.module S)
    (t : S),
    (sections S (c • m)).down t = c.down t • (sections S m).down t
  action : ∀ (S : Profinite.{u}) (g : C(S, P))
    (m : Profinite.CondensedAction.sectionModule (coefficientRing F).toMon module.module S)
    (t : S),
    (sections S (module.act S g m)).down t =
      Representation.coefficientScalarExtension E F P V ρ (g t) ((sections S m).down t)

/-- The continuous-section module with its specified action exists for every continuous
finite-dimensional representation and every norm-topological extension field F.
Source: blueprint paragraph (3), the construction of V_F
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison).
Proof: endow F tensor_E V with the finite-product topology in an E-basis of V. Matrices
over E induce continuous F-linear maps, so the scalar-extended action is jointly continuous.
Continuous maps form an additive sheaf on the coherent profinite site by quotient descent.
Pointwise scalar multiplication gives its internal C_F-module action using the existing
internal/sectionwise module equivalence. Pointwise ρ gives its condensed P-action. This
construction gives exactly the four presentation formulas, including on the empty set.
If the universe of V is larger than the coefficient universe, use the same finite basis
to take a small finite-product carrier; its section equivalence transports the original
continuous functions without any universe restriction on V. -/
theorem realization_exists (hEF : Continuous (algebraMap E F))
    [FiniteDimensional E V] [TopologicalSpace V] [IsModuleTopology E V]
    (hρ : Continuous (fun p : P × V ↦ ρ p.1 p.2)) :
    Nonempty (Realization E F V P ρ) := by
  sorry

variable (Q : Type u) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  (ι : Q →ₜ* P)

/-- Restricting the presented continuous representation changes only the group action.
The sections, scalar action and restriction maps are literally the original ones.
Source: blueprint paragraph (3), Res_ι V_F
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
def restrictionRealization (M : Realization E F V P ρ) :
    Realization E F V Q (ρ.comp ι.toMonoidHom) where
  module := (restriction (coefficientRing F) P Q ι).obj M.module
  sections := M.sections
  naturality := M.naturality
  linearity := M.linearity
  action S g m t := M.action S (ι.toContinuousMap.comp g) m t

end Realization

section Scalar

variable {A B : CategoryTheory.CondensedBar.Ring.{u}} (φ : A ⟶ B)
  (P : Type u) [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  [HasDerivedCategory.{u + 2} (CategoryTheory.CondensedBar.Modules A)]
  [HasDerivedCategory.{u + 2} (CategoryTheory.CondensedBar.Modules B)]
  [HasDerivedCategory.{u + 2} (CategoryTheory.CondensedBar.Equivariant A P)]
  [HasDerivedCategory.{u + 2} (CategoryTheory.CondensedBar.Equivariant B P)]

/-- The existing restriction of internal module scalars, with both categories explicit.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
abbrev moduleScalars : CategoryTheory.CondensedBar.Modules B ⥤
    CategoryTheory.CondensedBar.Modules A := Mod.comap φ.hom.hom

/-- Scalar restriction on the underlying internal modules is exact and additive.
Source: blueprint paragraph (3), coefficient maps
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison).
Proof: restriction of scalars retains the abelian sheaf and every underlying map. Its
kernels and cokernels are therefore unchanged; their induced scalar actions are the
restricted ones. Addition is the same addition of underlying sheaf morphisms. -/
theorem scalar_exact :
    (moduleScalars φ).Additive ∧
    PreservesFiniteLimits (moduleScalars φ) ∧
    PreservesFiniteColimits (moduleScalars φ) := by
  sorry

/-- The additive structure on the actual scalar restriction.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
instance scalar_additive : (moduleScalars φ).Additive := (scalar_exact φ).1

/-- Finite limits for actual scalar restriction.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
instance scalar_limits : PreservesFiniteLimits (moduleScalars φ) := (scalar_exact φ).2.1

/-- Finite colimits for actual scalar restriction.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
instance scalar_colimits : PreservesFiniteColimits (moduleScalars φ) := (scalar_exact φ).2.2

/-- An exact scalar restriction on action modules, normalized by its actual underlying
module map and every generalized group action. The inherited ScalarAction supplies the
underlying isomorphism and the action formula; no group action is chosen independently.
Source: blueprint paragraph (3), scalar restriction
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
structure ExactScalar where
  action : CategoryTheory.CondensedBar.ScalarAction φ P
  limits : PreservesFiniteLimits action.functor
  colimits : PreservesFiniteColimits action.functor

attribute [instance] ExactScalar.limits ExactScalar.colimits

/-- Scalar restriction and invariants commute with their invariant inclusions.
The derived isomorphism is normalized on EVERY complex by the actual derived units.
The inverse is the unique right-derived factorization from the scalar-restricted
invariant functor; this normalization excludes arbitrary natural isomorphisms.
Source: blueprint paragraph (3), coefficient map construction
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
structure ScalarCompatibility (S : ExactScalar φ P) where
  ordinary : S.action.functor ⋙ (invariants A P).functor ≅
    (invariants B P).functor ⋙ moduleScalars φ
  inclusion : ∀ N, (invariants A P).inclusion.app (S.action.functor.obj N) ≫
    S.action.underlying.hom.app N =
      ordinary.hom.app N ≫ (moduleScalars φ).map ((invariants B P).inclusion.app N)
  derived : S.action.functor.mapDerivedCategory ⋙ derivedInvariants A P ≅
    derivedInvariants B P ⋙ (moduleScalars φ).mapDerivedCategory
  normalization : ∀ K : CochainComplex (CategoryTheory.CondensedBar.Equivariant B P) ℤ,
    (derivedUnit A P).app ((S.action.functor.mapHomologicalComplex (.up ℤ)).obj K) ≫
      (derivedInvariants A P).map (S.action.functor.mapDerivedCategoryFactors.inv.app K) ≫
      derived.hom.app (DerivedCategory.Q.obj K) =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app K) ≫
      (moduleScalars φ).mapDerivedCategoryFactors.inv.app
        (((invariants B P).functor.mapHomologicalComplex (.up ℤ)).obj K) ≫
      (moduleScalars φ).mapDerivedCategory.map ((derivedUnit B P).app K)

/-- The scalar-restriction construction exists with its inclusion and derived-unit
normalizations; the data are determined up to the unique underlying-section comparison.
Source: blueprint paragraph (3), restriction calculus, coefficient paragraph
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison).
Proof: restrict scalars on each section and retain its group action. This is exact on
underlying modules. The invariant subsheaf is unchanged, giving the normalized ordinary
isomorphism. Compute derived invariants by equivariant injective resolutions. For an
injective resolution J over B, resolve its A-restriction and lift its augmentation. On
internal functions from a profinite parameter, the change-of-rings adjunction for the
flat free parameter module identifies the derived internal Homs. Totalizing the
first-quadrant comparison shows that the invariant comparison is a quasi-isomorphism.
Its inverse gives the displayed derived isomorphism. Naturality of resolutions makes it
independent of the lifts, and their augmentation square is exactly normalization. Scalar
restriction has both adjoints on internal modules; it preserves the right-derived Kan
extension. Consequently the inverse satisfying this unit equation is unique. No flatness
of φ is assumed. This is the formal scalar part of the node's cited restriction calculus. -/
theorem scalarCompatibility_exists :
    ∃ S : ExactScalar φ P, Nonempty (ScalarCompatibility φ P S) := by
  sorry

/-- Canonical exact scalar restriction, characterized on all section actions.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
def exactScalar : ExactScalar φ P := (scalarCompatibility_exists φ P).choose

/-- Canonical derived scalar comparison, with the inclusion and derived-unit
normalizations of ScalarCompatibility, which determine the comparison.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
def scalarCompatibility : ScalarCompatibility φ P (exactScalar φ P) :=
  Classical.choice (scalarCompatibility_exists φ P).choose_spec

/-- The canonical coefficient map induced by an equivariant module map. This uses the
actual derived map of f and the derived-unit-normalized scalar comparison.
Source: blueprint paragraph (3), c_J
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
def coefficientMap {N : CategoryTheory.CondensedBar.Equivariant A P}
    {N' : CategoryTheory.CondensedBar.Equivariant B P}
    (f : N ⟶ (exactScalar φ P).action.functor.obj N') :
    (derivedInvariants A P).obj ((DerivedCategory.singleFunctor _ 0).obj N) ⟶
      (moduleScalars φ).mapDerivedCategory.obj
        ((derivedInvariants B P).obj ((DerivedCategory.singleFunctor _ 0).obj N')) :=
  (derivedInvariants A P).map ((DerivedCategory.singleFunctor _ 0).map f) ≫
    (derivedInvariants A P).map
      (((exactScalar φ P).action.functor.mapDerivedCategorySingleFunctor 0).inv.app N') ≫
    (scalarCompatibility φ P).derived.hom.app ((DerivedCategory.singleFunctor _ 0).obj N')

attribute [irreducible] exactScalar scalarCompatibility

end Scalar

section RealizationMaps

variable (E F : Type u) [NormedField E] [NormedField F] [Algebra E F]
  (P : Type u) [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  {V : Type v} [AddCommGroup V] [Module E V]
  {W : Type w} [AddCommGroup W] [Module E W]
  {ρ : P →* (V ≃ₗ[E] V)} {σ : P →* (W ≃ₗ[E] W)}

/-- An equivariant linear map gives the unique morphism of its continuous-section
realizations with pointwise scalar-extended formula. This also states existence of the
maps used in the node's naturality clause.
Source: blueprint paragraph (3), naturality in continuous equivariant E-linear maps
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison).
Proof: scalar extension of the linear map is continuous between finite-product module
topologies. Postcompose each continuous section. These maps are linear, commute with
restrictions and the specified actions, hence give an internal equivariant morphism.
The section equivalences and faithfulness of the underlying sheaf determine it uniquely. -/
theorem realizationMap_existsUnique [FiniteDimensional E V] [FiniteDimensional E W]
    (M : Realization E F V P ρ) (N : Realization E F W P σ)
    (f : V →ₗ[E] W) (hf : Representation.IsEquivariant E P V W ρ σ f) :
    ∃! g : M.module ⟶ N.module,
      ∀ (S : Profinite.{u})
        (m : Profinite.CondensedAction.sectionModule (coefficientRing F).toMon M.module.module S)
        (t : S),
        (N.sections S (((g.val).hom.hom.app (op S)).hom m)).down t =
          f.baseChange F ((M.sections S m).down t) := by
  sorry

/-- The unique pointwise scalar-extended morphism. Applying moduleRestriction_naturality
to this map is the node's naturality for continuous equivariant E-linear maps.
Source: blueprint paragraph (3), naturality
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
def realizationMap [FiniteDimensional E V] [FiniteDimensional E W]
    (M : Realization E F V P ρ) (N : Realization E F W P σ)
    (f : V →ₗ[E] W) (hf : Representation.IsEquivariant E P V W ρ σ f) :
    M.module ⟶ N.module := (realizationMap_existsUnique E F P M N f hf).choose

end RealizationMaps

section CoefficientRealizations

variable (E F : Type u) [NormedField E] [NormedField F] [Algebra E F]
  (V : Type v) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  [TopologicalSpace V] [IsModuleTopology E V]
  (P : Type u) [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  (ρ : P →* (V ≃ₗ[E] V)) (hEF : Continuous (algebraMap E F))
  (hρ : Continuous (fun p : P × V ↦ ρ p.1 p.2))

/-- The actual continuous-section realization, determined up to the unique isomorphism
preserving its specified sections, restrictions, scalar action and group action.
Source: blueprint paragraph (3), V_F
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
def realization : Realization E F V P ρ :=
  Classical.choice (realization_exists E F V P ρ hEF hρ)

attribute [irreducible] realization

end CoefficientRealizations

section CoefficientRingMap

variable (E F : Type u) [NormedField E] [NormedField F] [Algebra E F]
  (hEF : Continuous (algebraMap E F))

set_option backward.isDefEq.respectTransparency false in
/-- The specified map C_E to C_F: the recorded postcomposition ring-object map.
Source: blueprint paragraph (3), coefficient compatibility
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
def coefficientRingMap : coefficientRing E ⟶ coefficientRing F := by
  letI := continuousMapRingObjOfUniverseMonObj.{u, u} E
  letI := continuousMapRingObjOfUniverseMonObj.{u, u} F
  letI : IsMonHom (continuousMapRingObjMapOfUniverse.{u, u} (algebraMap E F) hEF) :=
    isMonHom_continuousMapRingObjMapOfUniverse.{u, u} (algebraMap E F) hEF
  exact CommMon.homMk (Mon.ofHom
    (continuousMapRingObjMapOfUniverse.{u, u} (algebraMap E F) hEF))

end CoefficientRingMap

section RealizationCoefficientMaps

variable (E F : Type u) [NormedField E] [NormedField F] [Algebra E F]
  (hEF : Continuous (algebraMap E F))
  (V : Type v) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  (P : Type u) [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  (ρ : P →* (V ≃ₗ[E] V))
  [HasDerivedCategory.{u + 2} (CategoryTheory.CondensedBar.Modules (coefficientRing E))]
  [HasDerivedCategory.{u + 2} (CategoryTheory.CondensedBar.Modules (coefficientRing F))]
  [HasDerivedCategory.{u + 2}
    (CategoryTheory.CondensedBar.Equivariant (coefficientRing E) P)]
  [HasDerivedCategory.{u + 2}
    (CategoryTheory.CondensedBar.Equivariant (coefficientRing F) P)]

/-- The coefficient map on continuous sections exists and is uniquely determined by the
pointwise formula a tensor v maps to φ(a) tensor v. Under E tensor_E V = V this is
exactly v maps to 1 tensor v. Its codomain uses actual scalar restriction of actions.
Source: blueprint paragraph (3), coefficient compatibility
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison).
Proof: the scalar-extended identity has the displayed tensor formula and is continuous
in a finite basis, since E to F is continuous. Postcomposition on continuous sections is
E-linear, natural in test sets and equivariant for the same matrices over E. The
underlying-section normalization of exactScalar identifies its codomain. Faithfulness
of the underlying sheaf and the section equivalences give uniqueness. -/
theorem realizationCoefficientMap_existsUnique
    (M : Realization E E V P ρ) (N : Realization E F V P ρ) :
    ∃! f : M.module ⟶
      (exactScalar (coefficientRingMap E F hEF) P).action.functor.obj N.module,
    ∀ (S : Profinite.{u})
      (m : Profinite.CondensedAction.sectionModule (coefficientRing E).toMon M.module.module S)
      (t : S),
      (N.sections S
        (((f.val ≫ (exactScalar (coefficientRingMap E F hEF) P).action.underlying.hom.app
          N.module).hom.hom.app (op S)).hom m)).down t =
        TensorProduct.map (Algebra.linearMap E F) (LinearMap.id : V →ₗ[E] V)
          ((M.sections S m).down t) := by
  sorry

/-- The canonical equivariant coefficient map, chosen by its unique section formula.
Source: blueprint paragraph (3), v maps to 1 tensor v
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison). -/
def realizationCoefficientMap
    (M : Realization E E V P ρ) (N : Realization E F V P ρ) :
    M.module ⟶ (exactScalar (coefficientRingMap E F hEF) P).action.functor.obj N.module :=
  (realizationCoefficientMap_existsUnique E F hEF V P ρ M N).choose

end RealizationCoefficientMaps

section FixedSections

variable (l r : ℕ) [Fact l.Prime] (E F : Type u)
  [NormedField E] [NormedField F] [Algebra E F]
  (V : Type v) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  (ρ : AdicLattice.{u} l r →* (V ≃ₗ[E] V))

/-- The two invariant objects identify with exactly the SAME submodule of continuous
sections, after every profinite base change. Together with moduleRestriction_zero this
is the assertion that the degree-zero map is identity under the invariant identification.
Source: blueprint paragraph (3), degree-zero clause
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison).
Proof: finite congruence conditions in each coordinate have integer representatives,
so the integer lattice is dense. For a D-fixed section and each point of its test set,
its value is fixed by every constant integer. The map x maps to x acting on that value
minus that value is continuous: apply the action to the constant section on the profinite
L-test object and use the presentation's action formula. Its zero set is closed because
the finite-dimensional product norm space is Hausdorff, hence density makes it all of L.
After every base change, evaluate a generalized L-element pointwise to get L-fixedness.
The reverse implication follows by restricting the generalized elements along ι. -/
theorem realization_fixedSections (M : Realization E F V (AdicLattice.{u} l r) ρ) :
    ∀ (S : Profinite.{u})
      (m : Profinite.CondensedAction.sectionModule (coefficientRing F).toMon M.module.module S),
      Profinite.CondensedAction.FixedAll M.module S m ↔
        Profinite.CondensedAction.FixedAll
          ((restriction (coefficientRing F) (AdicLattice.{u} l r) (IntegerLattice.{u} r)
            (latticeInclusion l r)).obj M.module) S m := by
  sorry

end FixedSections

section Main

variable (l r : ℕ) [Fact l.Prime] (Ω : Type u) [NormedField Ω]
  [NormedAlgebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (E : IntermediateField ℚ_[l] Ω) [FiniteDimensional ℚ_[l] E]
  (V : Type v) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  [TopologicalSpace V] [IsModuleTopology E V]
  (ρ : AdicLattice.{u} l r →* (V ≃ₗ[E] V))
  (hρ : Continuous (fun p : AdicLattice.{u} l r × V ↦ ρ p.1 p.2))
  [HasDerivedCategory.{u + 2} (CategoryTheory.CondensedBar.Modules (coefficientRing E))]
  [HasDerivedCategory.{u + 2} (CategoryTheory.CondensedBar.Modules (coefficientRing Ω))]
  [HasDerivedCategory.{u + 2}
    (CategoryTheory.CondensedBar.Equivariant (coefficientRing E) (AdicLattice.{u} l r))]
  [HasDerivedCategory.{u + 2}
    (CategoryTheory.CondensedBar.Equivariant (coefficientRing E) (IntegerLattice.{u} r))]
  [HasDerivedCategory.{u + 2}
    (CategoryTheory.CondensedBar.Equivariant (coefficientRing Ω) (AdicLattice.{u} l r))]
  [HasDerivedCategory.{u + 2}
    (CategoryTheory.CondensedBar.Equivariant (coefficientRing Ω) (IntegerLattice.{u} r))]

/-- The canonical dense-lattice comparison for BOTH coefficient fields is an isomorphism
in the ordinary derived category of internal condensed modules.
Source: main-20261015 blueprint, direct-image stability paragraph (3), dense-lattice input
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison).

Proof:
1. Use lem-sfb-condensed-derived-restriction-calculus to obtain precisely the canonical
   restriction transformation from invariant inclusion; moduleRestriction is its
   localization-universal-property construction.
2. Z^r is dense in Z_ell^r by integer representatives of finite congruence conditions.
   Fixed sections agree: at each test-set point, the zero set of x acting on v minus v
   is closed in the Hausdorff finite-dimensional coefficient space and contains Z^r.
3. For the trivial rank-one representation, lem-sfb-trivial-ladic-derived-exterior and
   lem-sfb-discrete-lattice-cup-exterior have the same exterior-complex source. Each
   coordinate character restricts to its integer coordinate. Restriction preserves the
   unit and ordered cups, so its composite with the first exterior map is the second.
   Hence it is invertible. Finite direct sums give every trivial representation, including
   dimension zero; no completeness of Ω is used.
4. A central element acts as the identity after derived invariants: on an equivariant
   injective resolution it acts termwise, and on invariants each such action is identity.
   Use lem-sp-derived-injective-resolution-naturality. If T_i minus 1 is invertible, its
   derived image is zero and invertible, so both derived invariant objects vanish.
5. For an invariant subspace U, lem-sfb-continuous-representation-subquotients gives the
   continuous subquotient representations. An E-linear splitting is continuous by
   lem-sfb-finite-dimensional-linear-map-continuous, applied only over complete E.
   Its finite matrices remain continuous over Ω. Thus the coefficient-section sequence
   is split exact on underlying modules, and exact in the action categories.
6. Induct strongly on dimension. The invertible case was handled in step 4; if every
   T_i minus 1 is zero, density reduces to step 3. Otherwise a nonzero singular T_i minus
   1 has nonzero proper invariant kernel. Apply induction to that kernel and the quotient
   and lem-sf-triangle-two-out-of-three to the two derived-invariant triangles. Shift
   compatibility comes from the restriction calculus, including the connecting arrow.
7. Naturality, degree-zero normalization, coefficient compatibility and rank-zero identity
   are the accompanying declarations, with the same canonical arrow in every clause.
-/
theorem denseLatticeDerivedInvariantsComparison :
    IsIso (moduleRestriction (coefficientRing E) (AdicLattice.{u} l r)
      (IntegerLattice.{u} r) (latticeInclusion l r)
        (realization E E V (AdicLattice.{u} l r) ρ continuous_id hρ).module) ∧
    IsIso (moduleRestriction (coefficientRing Ω) (AdicLattice.{u} l r)
      (IntegerLattice.{u} r) (latticeInclusion l r)
        (realization E Ω V (AdicLattice.{u} l r) ρ continuous_subtype_val hρ).module) := by
  sorry

/-- The coefficient square commutes for the actual maps induced by v maps to 1 tensor v.
Both vertical arrows use the normalized equality of invariants with scalar restriction;
the two horizontal arrows are precisely the same derived restriction used in the main
isomorphism assertion. This is equality in D(Mod_{C_E}), not only equality on cohomology.
Source: blueprint paragraph (3), coefficient compatibility square
(blueprint: lem-sfb-dense-lattice-derived-invariants-comparison).
Proof: let φ be postcomposition by E into Ω, and let f be the unique equivariant map of
continuous sections a tensor v maps to φ(a) tensor v. Restricting this map along ι gives
the unique map with the same formula between the restricted realizations. Apply the
coefficient-pasting equality of lem-sfb-condensed-derived-restriction-calculus. Its scalar
comparison is the inclusion-and-derived-unit-normalized comparison in ScalarCompatibility,
and its restriction transformation is the right-derived factorization defining
moduleRestriction. The uniqueness of the underlying pointwise maps and derived
factorizations therefore identifies its equality with exactly the displayed square. -/
theorem denseLatticeDerivedInvariantsComparison_coefficients :
    moduleRestriction (coefficientRing E) (AdicLattice.{u} l r) (IntegerLattice.{u} r)
      (latticeInclusion l r)
        (realization E E V (AdicLattice.{u} l r) ρ continuous_id hρ).module ≫
      coefficientMap (coefficientRingMap E Ω continuous_subtype_val) (IntegerLattice.{u} r)
        (realizationCoefficientMap E Ω continuous_subtype_val V (IntegerLattice.{u} r)
          (ρ.comp (latticeInclusion l r).toMonoidHom)
          (restrictionRealization E E V (AdicLattice.{u} l r) ρ (IntegerLattice.{u} r)
            (latticeInclusion l r)
            (realization E E V (AdicLattice.{u} l r) ρ continuous_id hρ))
          (restrictionRealization E Ω V (AdicLattice.{u} l r) ρ (IntegerLattice.{u} r)
            (latticeInclusion l r)
            (realization E Ω V (AdicLattice.{u} l r) ρ continuous_subtype_val hρ))) =
    coefficientMap (coefficientRingMap E Ω continuous_subtype_val) (AdicLattice.{u} l r)
        (realizationCoefficientMap E Ω continuous_subtype_val V (AdicLattice.{u} l r) ρ
          (realization E E V (AdicLattice.{u} l r) ρ continuous_id hρ)
          (realization E Ω V (AdicLattice.{u} l r) ρ continuous_subtype_val hρ)) ≫
      (moduleScalars (coefficientRingMap E Ω continuous_subtype_val)).mapDerivedCategory.map
        (moduleRestriction (coefficientRing Ω) (AdicLattice.{u} l r) (IntegerLattice.{u} r)
          (latticeInclusion l r)
          (realization E Ω V (AdicLattice.{u} l r) ρ continuous_subtype_val hρ).module) := by
  sorry

end Main

end Profinite.DenseLattice
