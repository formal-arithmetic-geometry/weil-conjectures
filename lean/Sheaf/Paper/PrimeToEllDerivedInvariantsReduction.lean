/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.Paper.ContinuousRepresentationCondensation
public import Sheaf.CategoryTheory.CondensedDerivedInflationArrows
public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import Sheaf.CategoryTheory.CondensedProductBarComparison
public import Sheaf.CategoryTheory.CondensedEquivariantBarData
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Sheaf.CategoryTheory.CondensedProductActionInflation
import Sheaf.CategoryTheory.CondensedDerivedInvariantBar
import Sheaf.CategoryTheory.InternalActionSitePresentation
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions

/-! # Removing a pro-prime-to-ell factor from derived invariants

Source: blueprint main-20261015, direct-image stability proof, paragraph (3),
tame-boundary analytic condensed input
(blueprint: lem-sfb-prime-to-ell-derived-invariants-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace Profinite.CondensedAction.PrimeToEll
open ContinuousRepresentation AlgebraicGeometry.ProEtale

section RealizationMaps
variable {E : Type u} [Field E] (F : Type u) [NormedField F] [Algebra E F]
  (P : Type u) [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  {U U' : Type (u + 1)} [AddCommGroup U] [Module E U] [FiniteDimensional E U]
  [AddCommGroup U'] [Module E U'] [FiniteDimensional E U']
  (τ : Representation E P U) (τ' : Representation E P U')
  (f : U →ₗ[E] U') (heq : ∀ (p : P) (v : U), f (τ p v) = τ' p (f v))

/-- Scalar extension preserves equivariance of the specified linear map.
Source: paragraph (3) (blueprint: lem-sfb-prime-to-ell-derived-invariants-reduction).
Proof: tensor induction reduces the equation to a pure tensor a tensor v. Both sides
are a tensor f(tau(p)v), using the assumed equivariance on v. -/
theorem extendedMap_equivariant
    (_heq : ∀ (p : P) (v : U), f (τ p v) = τ' p (f v)) :
    ∀ (p : P) (v : Extended E F U),
      f.baseChange F (extendedRepresentation E F U P τ p v) =
        extendedRepresentation E F U' P τ' p (f.baseChange F v) := by
  sorry

/-- The actual section realization of the scalar-extended equivariant linear map.
Source: paragraph (3) (blueprint: lem-sfb-prime-to-ell-derived-invariants-reduction). -/
def realizationMap
    (M : Realization F P (Extended E F U) (extendedRepresentation E F U P τ))
    (M' : Realization F P (Extended E F U') (extendedRepresentation E F U' P τ')) :
    M.object ⟶ M'.object :=
  ContinuousRepresentation.map M M' (f.baseChange F)
    (IsModuleTopology.continuous_of_linearMap _) (extendedMap_equivariant F P τ τ' f heq)

end RealizationMaps

section TrivialFactor
variable (R : CondensedRing.{u}) [IsCommMonObj R.X]
  (B L : ProfiniteGrp.{u})

/-- Removing the one-element factor identifies invariant equalizers by their inclusions.
The displayed normalization uniquely determines the isomorphism on all sections.
Source: paragraph (3) (blueprint: lem-sfb-prime-to-ell-derived-invariants-reduction).
Proof: every generalized B-element is the identity, so a section is B times L-fixed
exactly when it is L-fixed. The two injective invariant inclusions have identical
images. Their unique sectionwise factorization gives inverse module maps, natural
in the action module. Injectivity proves both inverse laws and uniqueness. -/
theorem trivialFactorInvariantIso_unique [Subsingleton B] (dBL : Invariants R (B × L))
    (dL : Invariants R L) :
    ∃! e : inflate (R := R) (ContinuousMonoidHom.snd B L) ⋙ dBL.functor ≅ dL.functor,
      ∀ N : ActionModule R L,
        e.hom.app N ≫ dL.inclusion.app N =
          dBL.inclusion.app ((inflate (R := R) (ContinuousMonoidHom.snd B L)).obj N) := by
  sorry

/-- The canonical equality of fixed sections under the identification B times L = L.
Source: paragraph (3) (blueprint: lem-sfb-prime-to-ell-derived-invariants-reduction). -/
def trivialFactorInvariantIso [Subsingleton B] (dBL : Invariants R (B × L)) (dL : Invariants R L) :
    inflate (R := R) (ContinuousMonoidHom.snd B L) ⋙ dBL.functor ≅ dL.functor :=
  Classical.choose (trivialFactorInvariantIso_unique R B L dBL dL).exists

/-- Restriction along B times L = L preserves K-injectives.
Source: paragraph (3) (blueprint: lem-sfb-prime-to-ell-derived-invariants-reduction).
Proof: the inverse restriction is induced by l mapping to (1,l). The two composites
are naturally the identity on underlying modules, since B has a single element.
These inverse exact equivalences preserve acyclic complexes and the Hom-complex
criterion for K-injectivity, proving the assertion for unbounded complexes. -/
theorem trivialFactorPreservesKInjectives [Subsingleton B] :
    (inflate (R := R) (ContinuousMonoidHom.snd B L)).PreservesKInjectiveComplexes := by
  sorry

/-- Derive the inclusion-normalized equality of invariants under B times L = L.
This comparison uses the fixed-section identification and the derived universal
property; it is defined independently of reductionMap.
Source: paragraph (3) (blueprint: lem-sfb-prime-to-ell-derived-invariants-reduction). -/
def trivialFactorDerivedIso [Subsingleton B] (dBL : Invariants R (B × L)) (dL : Invariants R L) :
    dL.functor.rightDerivedFunctor ≅
      (inflate (R := R) (ContinuousMonoidHom.snd B L)).mapDerivedCategory ⋙
        dBL.functor.rightDerivedFunctor :=
  letI := trivialFactorPreservesKInjectives R B L
  Functor.rightDerivedFunctorIsoMapDerivedCategoryComp
    (trivialFactorInvariantIso R B L dBL dL)

end TrivialFactor


section FormalReduction
variable (E F : Type u) [Field E] [NormedField F] [Algebra E F]
  (B L : ProfiniteGrp.{u}) (V : Type (u + 1)) [AddCommGroup V] [Module E V]
  [FiniteDimensional E V]
  (ρ : Representation E (B × L) V)

/-- Condensation of the scalar-extended fixed-space inclusion, before deriving.
Its morphism is chosen from a unique sectionwise formula, never an arbitrary map.
Source: paragraph (3) (blueprint: lem-sfb-prime-to-ell-derived-invariants-reduction). -/
def inclusion
    (M : Realization F (B × L)
      (Extended E F V)
      (extendedRepresentation E F V (B × L) ρ))
    (W : Realization F L
      (Extended E F (fixedSpace B L ρ))
      (extendedRepresentation E F (fixedSpace B L ρ) L
        (fixedRepresentation B L ρ))) :
    (inflate (R := normContinuousRing F)
      (ContinuousMonoidHom.snd B L)).obj W.object ⟶ M.object :=
  ContinuousRepresentation.map
    (W.inflate (P := B × L) (ContinuousMonoidHom.snd B L)) M
    (fixedInclusion F B L ρ)
    (IsModuleTopology.continuous_of_linearMap _)
    (fixedInclusion_equivariant F B L ρ)

/-- The canonical morphism a_F from the node, formed with the derived inflation adjunction.
Source: paragraph (3) (blueprint: lem-sfb-prime-to-ell-derived-invariants-reduction). -/
def reductionMap
    (M : Realization F (B × L)
      (Extended E F V)
      (extendedRepresentation E F V (B × L) ρ))
    (W : Realization F L
      (Extended E F (fixedSpace B L ρ))
      (extendedRepresentation E F (fixedSpace B L ρ) L
        (fixedRepresentation B L ρ)))
    (dBL : Invariants (normContinuousRing F) (B × L))
    (dL : Invariants (normContinuousRing F) L) :
    dL.functor.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj W.object) ⟶
      dBL.functor.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj M.object) :=
  inflationZero _ (B × L) L (ContinuousMonoidHom.snd B L) dBL dL
    (inclusion E F B L V ρ M W)

/-- The exact realization-existence proposition for the two objects in the reduction.
Source: paragraph (3) (blueprint: lem-sfb-prime-to-ell-derived-invariants-reduction). -/
def HasReductionRealizations : Prop :=
  Nonempty (Realization F (B × L) (Extended E F V)
    (extendedRepresentation E F V (B × L) ρ)) ∧
  Nonempty (Realization F L (Extended E F (fixedSpace B L ρ))
    (extendedRepresentation E F (fixedSpace B L ρ) L (fixedRepresentation B L ρ)))

/-- The isomorphism assertion, for every presentation of the specified two objects
and every normalized invariants equalizer. This merely abbreviates the full assertion.
Source: paragraph (3) (blueprint: lem-sfb-prime-to-ell-derived-invariants-reduction). -/
def ReductionIsIso : Prop :=
  ∀ (M : Realization F (B × L) (Extended E F V)
      (extendedRepresentation E F V (B × L) ρ))
    (W : Realization F L (Extended E F (fixedSpace B L ρ))
      (extendedRepresentation E F (fixedSpace B L ρ) L (fixedRepresentation B L ρ)))
    (dBL : Invariants (normContinuousRing F) (B × L))
    (dL : Invariants (normContinuousRing F) L),
      IsIso (reductionMap E F B L V ρ M W dBL dL)

section Clauses
variable
  (M : Realization F (B × L)
    (Extended E F V)
    (extendedRepresentation E F V (B × L) ρ))
  (W : Realization F L
    (Extended E F (fixedSpace B L ρ))
    (extendedRepresentation E F (fixedSpace B L ρ) L
      (fixedRepresentation B L ρ)))
  (dBL : Invariants (normContinuousRing F) (B × L))
  (dL : Invariants (normContinuousRing F) L)

/-- On H^0 the actual reductionMap is the fixed-section inclusion. The unit isomorphisms
identify derived H^0 with ordinary invariants. The displayed unit square
identifies its map with the ordinary transpose j, whose inclusion formula follows.
Thus this is the identity after identifying the
source and target with the same invariant sections, including the zero space.
Source: paragraph (3) (blueprint: lem-sfb-prime-to-ell-derived-invariants-reduction).
Proof: apply homology in degree zero to inflationZero_unit for the actual inclusion.
The unit maps are isomorphisms by left exactness of invariants. Cancel the target
unit on H^0 in the displayed unit square. Finally the ordinary
transpose inclusion formula identifies the resulting map with inclusion on sections.
Scalar extension of the fixed subspace has precisely the B-fixed vectors: the
fixed subspace is the solution space of linear equations, preserved by field extension.
The L-fixed vectors on both sides are consequently identical. -/
theorem reductionMap_h0 :
    let R := normContinuousRing F
    let H := DerivedCategory.homologyFunctor (Modules R) 0
    let j := invariantMap R (B × L) L (ContinuousMonoidHom.snd B L) dBL dL
      (inclusion E F B L V ρ M W)
    IsIso (H.map (unitZero R L dL W.object)) ∧
      IsIso (H.map (unitZero R (B × L) dBL M.object)) ∧
      unitZero R L dL W.object ≫ reductionMap E F B L V ρ M W dBL dL =
        (DerivedCategory.singleFunctor _ 0).map j ≫ unitZero R (B × L) dBL M.object ∧
      j ≫ dBL.inclusion.app M.object =
        dL.inclusion.app W.object ≫ (inclusion E F B L V ρ M W).val := by
  sorry

/-- For B trivial the fixed-space inclusion identifies the actual representations.
Source: paragraph (3) (blueprint: lem-sfb-prime-to-ell-derived-invariants-reduction).
Proof: every b is 1, so every vector satisfies the B-fixed equations and V^B is V.
Its inclusion is a linear homeomorphism with inverse v mapping to v with this proof.
Tensoring the inverse with F gives the inverse on extended spaces. Condense both
continuous maps; their section formulas make both composites identities. -/
theorem inclusion_trivial_isIso [Subsingleton B] :
    IsIso (inclusion E F B L V ρ M W) := by
  sorry

/-- For every trivial B, reductionMap is the identity after the canonical identifications
B times L = L and V^B = V. The inverse inclusion implements V^B = V; the derived
fixed-section comparison implements B times L = L and is independent of reductionMap.
Source: paragraph (3) (blueprint: lem-sfb-prime-to-ell-derived-invariants-reduction).
Proof: projection has inverse l mapping to (1,l). On invariant equalizers this is the
unique inclusion-normalized trivialFactorInvariantIso. Exact restriction preserves
K-injectives, so its derived comparison is trivialFactorDerivedIso. The derived
adjunction transpose defining reductionMap agrees with this comparison followed by
the derived inclusion: both are obtained from the same counit and invariant inclusion.
Compose with the inverse of that inclusion and the inverse derived comparison; the
two isomorphism cancellation laws give the displayed identity. -/
theorem reductionMap_trivial_identity [Subsingleton B] :
    let R := normContinuousRing F
    letI := inclusion_trivial_isIso E F B L V ρ M W
    reductionMap E F B L V ρ M W dBL dL ≫
      dBL.functor.rightDerivedFunctor.map
        ((DerivedCategory.singleFunctor _ 0).map
          (inv (inclusion E F B L V ρ M W))) ≫
      dBL.functor.rightDerivedFunctor.map
        (((inflate (R := R) (ContinuousMonoidHom.snd B L)).mapDerivedCategorySingleFunctor
          0).inv.app W.object) ≫
      (trivialFactorDerivedIso R B L dBL dL).inv.app
        ((DerivedCategory.singleFunctor _ 0).obj W.object) = 𝟙 _ := by
  sorry

section Naturality
variable [TopologicalSpace V] {V' : Type (u + 1)} [AddCommGroup V'] [Module E V']
  [FiniteDimensional E V'] [TopologicalSpace V']
  (ρ' : Representation E (B × L) V') (f : V →ₗ[E] V')
  (heq : ∀ (p : B × L) (v : V), f (ρ p v) = ρ' p (f v))

/-- An equivariant map restricts to an equivariant map of residual L-representations.
Source: paragraph (3) (blueprint: lem-sfb-prime-to-ell-derived-invariants-reduction).
Proof: apply equivariance to (1,l). The fixedMap definition is f with codomain
restricted to the B-fixed subspace; equality of subtype elements follows from the
same equality in V'. -/
theorem fixedMap_equivariant :
    ∀ (l : L) (v : fixedSpace B L ρ),
      fixedMap B L ρ ρ' f heq (fixedRepresentation B L ρ l v) =
        fixedRepresentation B L ρ' l (fixedMap B L ρ ρ' f heq v) := by
  sorry

variable
  (M' : Realization F (B × L)
    (Extended E F V')
    (extendedRepresentation E F V' (B × L) ρ'))
  (W' : Realization F L
    (Extended E F (fixedSpace B L ρ'))
    (extendedRepresentation E F (fixedSpace B L ρ') L
      (fixedRepresentation B L ρ')))

/-- The condensed naturality square uses the uniquely specified realization maps of f
and its restriction to fixed vectors; its commutativity is a conclusion.
Source: paragraph (3) (blueprint: lem-sfb-prime-to-ell-derived-invariants-reduction).
Proof: evaluate on every profinite test set and continuous section. Both composites
send a tensor v to a tensor f(v), by tensor functoriality and the realization formulas.
Faithfulness of the section presentation gives the equality of equivariant maps. -/
theorem reduction_inclusion_natural (_hf : Continuous f) :
    (inflate (R := normContinuousRing F)
        (ContinuousMonoidHom.snd B L)).map
      (realizationMap F L
        (fixedRepresentation B L ρ) (fixedRepresentation B L ρ')
        (fixedMap B L ρ ρ' f heq) (fixedMap_equivariant E B L V ρ ρ' f heq) W W') ≫
      inclusion E F B L V' ρ' M' W' =
    inclusion E F B L V ρ M W ≫
      realizationMap F (B × L) ρ ρ' f heq M M' := by
  sorry

/-- The actual reductionMap is natural for every continuous equivariant E-linear f,
using its scalar-extended realization map and the realization of its fixed restriction.
No invertibility or nonzero hypothesis on f is imposed.
Source: paragraph (3) (blueprint: lem-sfb-prime-to-ell-derived-invariants-reduction).
Proof: use reduction_inclusion_natural for f. Apply the single-object functor and
its natural exact-restriction comparison to obtain the derived inclusion square.
Naturality of the derived counit and of the adjunction transpose then gives exactly
the equality below, which is derivedInflation_natural for these specified maps. -/
theorem reductionMap_natural (_hf : Continuous f) :
    dL.functor.rightDerivedFunctor.map ((DerivedCategory.singleFunctor _ 0).map
      (realizationMap F L
        (fixedRepresentation B L ρ) (fixedRepresentation B L ρ')
        (fixedMap B L ρ ρ' f heq) (fixedMap_equivariant E B L V ρ ρ' f heq) W W')) ≫
      reductionMap E F B L V' ρ' M' W' dBL dL =
    reductionMap E F B L V ρ M W dBL dL ≫
      dBL.functor.rightDerivedFunctor.map ((DerivedCategory.singleFunctor _ 0).map
        (realizationMap F (B × L) ρ ρ' f heq M M')) := by
  sorry

end Naturality
end Clauses

end FormalReduction

section CoefficientArrows
variable (E F : Type u) [NormedField E] [NormedField F] [Algebra E F]
  (hφ : Continuous (algebraMap E F))

/-- The actual vector coefficient insertion is continuous and equivariant, including
on the fixed subspace. This supplies the maps used in the coefficient square.
Source: paragraph (3) (blueprint: lem-sfb-prime-to-ell-derived-invariants-reduction).
Proof: in a finite E-basis, insertion is coordinatewise the continuous algebra map E
to F. Finite products preserve continuity. Scalar linearity follows on pure tensors
from the algebra-map multiplication law, and equivariance is tensor functoriality.
The fixed subspace is finite dimensional, so the same calculation applies to it. -/
theorem coefficientInsertion_properties
    (_hφ : Continuous (algebraMap E F))
    (U : Type (u + 1)) [AddCommGroup U] [Module E U] [FiniteDimensional E U] :
    Continuous (scalarInsertion (E := E) F U) ∧
      ∀ (a : E) (v : Extended E E U),
        scalarInsertion (E := E) F U (a • v) =
          algebraMap E F a • scalarInsertion (E := E) F U v := by
  sorry

/-- Condensation of v mapping to 1 tensor v, with its unique section formula.
Source: paragraph (3) (blueprint: lem-sfb-prime-to-ell-derived-invariants-reduction). -/
def realizationCoefficientMap (P : ProfiniteGrp.{u})
    (U : Type (u + 1)) [AddCommGroup U] [Module E U] [FiniteDimensional E U]
    (τ : Representation E P U)
    (ME : Realization E P (Extended E E U) (extendedRepresentation E E U P τ))
    (MO : Realization F P (Extended E F U) (extendedRepresentation E F U P τ))
    (s : CategoryTheory.CondensedBar.ScalarAction
      (coefficientRingMap E (algebraMap E F) hφ) P) :
    ME.object ⟶ s.functor.obj MO.object :=
  scalarMap (algebraMap E F) hφ ME MO s
    (scalarInsertion (E := E) F U).toAddMonoidHom (coefficientInsertion_properties E F hφ U).1
    (coefficientInsertion_properties E F hφ U).2
    (scalarInsertion_equivariant F P τ)

end CoefficientArrows

section CoefficientClause
variable (E F : Type u) [NormedField E] [NormedField F] [Algebra E F]
  (hφ : Continuous (algebraMap E F))
  (B L : ProfiniteGrp.{u}) (V : Type (u + 1)) [AddCommGroup V] [Module E V]
  [FiniteDimensional E V] [TopologicalSpace V] [IsModuleTopology E V]
  (ρ : Representation E (B × L) V)
open CategoryTheory.CondensedBar
variable
  (ME : Realization E (B × L) (Extended E E V)
    (extendedRepresentation E E V (B × L) ρ))
  (WE : Realization E L (Extended E E (fixedSpace B L ρ))
    (extendedRepresentation E E (fixedSpace B L ρ) L (fixedRepresentation B L ρ)))
  (MO : Realization F (B × L) (Extended E F V)
    (extendedRepresentation E F V (B × L) ρ))
  (WO : Realization F L (Extended E F (fixedSpace B L ρ))
    (extendedRepresentation E F (fixedSpace B L ρ) L (fixedRepresentation B L ρ)))
  (MP : Model (coefficientRing E) (B × L)) (MP' : Model (coefficientRing F) (B × L))
  (ML : Model (coefficientRing E) L) (ML' : Model (coefficientRing F) L)
  (sP : ScalarModel
    (coefficientRingMap E (algebraMap E F) hφ) MP MP')
  (sL : ScalarModel
    (coefficientRingMap E (algebraMap E F) hφ) ML ML')
  (cP : ScalarComputation (coefficientRingMap E (algebraMap E F) hφ) sP)
  (cL : ScalarComputation (coefficientRingMap E (algebraMap E F) hφ) sL)

/-- The coefficient square for reductionMap itself, with the actual realizations of
v mapping to 1 tensor v. Coefficient maps derive the normalized equality of invariants
with restriction of scalars; the square holds for every compatible resolution and lift.
For the source inclusion E to Omega, take hφ to be coefficientContinuity.
Source: paragraph (3) (blueprint: lem-sfb-prime-to-ell-derived-invariants-reduction).
Proof: on each continuous section the ordinary square sends a tensor v to the
same tensor v with its coefficient mapped into F, so that square commutes.
The normalized scalarInflationIso is identity on underlying modules. Apply
inflationZero_coefficients with this ordinary square and the four resolutions below.
The canonical reduction maps unfold to its two inflationZero arrows, and the vertical
maps are coefficientMap with realizationCoefficientMap, giving the stated equality.
The normalized resolution comparison makes the result independent of all lifts. -/
theorem reductionMap_coefficients
    (IP : InjectiveResolution (sP.restriction.functor.obj MO.object))
    (JP : InjectiveResolution MO.object)
    (βP : (sP.restriction.functor.mapHomologicalComplex (.up ℕ)).obj JP.cocomplex ⟶
      IP.cocomplex)
    (hβP : sP.restriction.functor.map (JP.ι.f 0) ≫ βP.f 0 = IP.ι.f 0)
    (IL : InjectiveResolution (sL.restriction.functor.obj WO.object))
    (JL : InjectiveResolution WO.object)
    (βL : (sL.restriction.functor.mapHomologicalComplex (.up ℕ)).obj JL.cocomplex ⟶
      IL.cocomplex)
    (hβL : sL.restriction.functor.map (JL.ι.f 0) ≫ βL.f 0 = IL.ι.f 0) :
    reductionMap E E B L V ρ ME WE MP.invariants ML.invariants ≫
      coefficientMap (coefficientRingMap E (algebraMap E F) hφ) MP MP' sP cP
        (realizationCoefficientMap E F hφ (ProfiniteGrp.of (B × L)) V ρ
          ME MO sP.restriction) IP JP βP hβP =
    coefficientMap (coefficientRingMap E (algebraMap E F) hφ) ML ML' sL cL
        (realizationCoefficientMap E F hφ L (fixedSpace B L ρ)
          (fixedRepresentation B L ρ) WE WO sL.restriction) IL JL βL hβL ≫
      (Mod.comap (coefficientRingMap E (algebraMap E F)
        hφ).hom.hom).mapDerivedCategory.map
        (reductionMap E F B L V ρ MO WO MP'.invariants ML'.invariants) := by
  sorry

end CoefficientClause

section Reduction
variable (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[ℓ] Ω]
  [IsAlgClosure ℚ_[ℓ] Ω]
  (E : IntermediateField ℚ_[ℓ] Ω) [FiniteDimensional ℚ_[ℓ] E]
  (B L : ProfiniteGrp.{u}) (V : Type (u + 1)) [AddCommGroup V] [Module E V]
  [FiniteDimensional E V] [TopologicalSpace V] [IsModuleTopology E V]
  (ρ : Representation E (B × L) V)

/-- The two representations used in the node always have the specified realizations;
these presentation parameters impose no extra mathematical assumption.
Source: paragraph (3) (blueprint: lem-sfb-prime-to-ell-derived-invariants-reduction).
Proof: in a finite basis, joint continuity is continuity of finitely many matrix
entries, obtained by evaluating the action on the basis vectors. Scalar extension
postcomposes those entries by the continuous inclusion E to F and matrix evaluation
is a finite sum of continuous products. Restricting the original action to the closed
finite-dimensional fixed subspace is continuous. Its subspace topology is the module
topology, by the finite-dimensional subspace theorem over the complete field E.
Apply exists_realization to these two joint continuous actions. This argument uses
only finite products for F=Omega and never requires its completeness. -/
theorem reduction_realizations_exist
    (_hρ : Continuous (fun x : (B × L) × V ↦ ρ x.1 x.2)) :
    HasReductionRealizations E E B L V ρ ∧ HasReductionRealizations E Ω B L V ρ := by
  sorry

/-- The norm-preserving intermediate-field inclusion is continuous.
Source: paragraph (3) (blueprint: lem-sfb-prime-to-ell-derived-invariants-reduction).
Proof: the intermediate field carries the subtype norm and its inclusion is the
subtype inclusion. The inverse image of an open set is open in the subtype topology. -/
theorem coefficientContinuity : Continuous (algebraMap E Ω) := by
  sorry



/-- Removing the pro-prime-to-ell factor gives an isomorphism for each of the two
all-continuous coefficient fields. The realization and normalized invariants data merely
present the objects and functors fixed by the statement, and the result holds for every
such presentation. Source: paragraph (3), analytic tame-inertia input
(blueprint: lem-sfb-prime-to-ell-derived-invariants-reduction).

Proof:
1. The finite B-image Q has open normal kernel K, since its finite Hausdorff matrix
image is discrete. Taking the normal core of any open subgroup of K shows that all
finite quotients of K have order prime to ell. A basis of V identifies V_F with
finitely many copies of C_F with trivial K-action, including the empty sum.
2. Apply lem-sfb-prime-to-ell-condensed-acyclicity to K. Finite sums of K-injectives
are K-injective, since maps and their null homotopies are finite tuples. Invariants
preserve these sums, so the canonical augmentation for V_F is invertible.
3. Apply lem-sfb-derived-invariants-normal-subgroup-comparison to K normal in B.
The action-site presentation detects vanishing cohomology after forgetting actions,
so its unit is invertible in the residual Q times L action category. The normalized
comparison equation identifies its image with the inflation from Q times L.
4. Average the Q-action by |Q| inverse times the finite sum. It is an internal
L-equivariant idempotent with image the full condensed fixed sections: Q-valued
continuous sections are locally constant on finite clopen partitions. Averaging local
lifts makes Q-invariants exact, using the generated action topology's base cokernels.
5. Apply the same normal-subgroup comparison to Q normal in Q. Exact Q-invariants
identify their derived functor with the ordinary fixed submodule. The averaging
splitting and a basis of image and kernel identify (V^B)_F with (V_F)^Q, with exactly
the finite-dimensional product topology and residual L-action.
6. Composition normalization identifies the two successive inflations with the actual
adjunction transpose `reductionMap`. Both factors are isomorphisms, proving the claim.
7. Equivariant maps preserve fixed vectors and commute with the finite average. The
comparison is natural; coefficient insertion commutes term by term with this average.
8. For B trivial the augmentations and comparisons are identities. For V=0 the
finite sum is empty. No completeness of Omega or locally constant replacement is used. -/
theorem primeToEll_derived_invariants_reduction
    (_hB : ∀ N : OpenNormalSubgroup B,
      Nat.Coprime (Nat.card (B ⧸ N.toSubgroup)) ℓ)
    (_hρ : Continuous (fun x : (B × L) × V ↦ ρ x.1 x.2))
    (_hfinite : Finite (Set.range (fun b : B ↦ ρ (b, 1))))
    (_horder : Nat.Coprime (Nat.card (Set.range (fun b : B ↦ ρ (b, 1)))) ℓ) :
    ReductionIsIso E E B L V ρ ∧ ReductionIsIso E Ω B L V ρ := by
  sorry

end Reduction

end Profinite.CondensedAction.PrimeToEll
