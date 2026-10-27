/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.Paper.IntegralQuotientResolutionNormalization
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.Additive
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.CategoryTheory.ConstantFiniteFreePresentationExtension
import Sheaf.Targets.SliceRestrictionStrictDerivedLimit
import Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Derived and ordinary quotient limits of finite scalar local models

Source: blueprint, det-sf-comp-coherence-refinement proof, paragraph (2), via the
Refinement isomorphisms paragraph of det-sf-comp-coherence-cocycle; Stacks 0941.
(blueprint: lem-sfb-finite-scalar-model-ordinary-quotient-comparison).

All complexes are in the ordinary abelian category of strict module towers. Its
cokernel is computed levelwise, so the quotient transitions below are the actual
quotient maps. The index n denotes exponent n+1. No completion category is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w ua va
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteScalarOrdinaryComparison

variable {A : Type ua} [Category.{va} A] [Abelian A]
variable (s : 𝟭 A ⟶ 𝟭 A)

/-- The constant target tower M with identity transitions.
Source: blueprint refinement (2), strict reductions
(blueprint: lem-sfb-finite-scalar-model-ordinary-quotient-comparison). -/
abbrev constant (M : A) : ℕᵒᵖ ⥤ A :=
  (Functor.const ℕᵒᵖ).obj M

/-- The source tower M with uniformizer transitions.
Source: blueprint refinement (2), strict reductions
(blueprint: lem-sfb-finite-scalar-model-ordinary-quotient-comparison). -/
def source (M : A) : ℕᵒᵖ ⥤ A :=
  Functor.ofOpSequence (X := fun _ ↦ M) (fun _ ↦ s.app M)

/-- Uniformizer powers as one strict tower morphism, from source to constant.
Source: blueprint refinement (2), strict reductions
(blueprint: lem-sfb-finite-scalar-model-ordinary-quotient-comparison). -/
def powers (M : A) : source s M ⟶ constant M :=
  NatTrans.ofOpSequence (fun n ↦ End.asHom ((End.of (s.app M)) ^ (n + 1))) (by
    intro n
    simp only [source, Functor.ofOpSequence_map_homOfLE_succ, constant,
      Functor.const_obj_map]
    change s.app M ≫ End.asHom ((End.of (s.app M)) ^ (n + 1)) =
      End.asHom ((End.of (s.app M)) ^ (n + 1 + 1)) ≫ 𝟙 M
    exact ((@pow_succ (End M) inferInstance (End.of (s.app M)) (n + 1)).symm).trans
      (@Category.comp_id A inferInstance M M
        (End.asHom ((End.of (s.app M)) ^ (n + 1 + 1)))).symm)

/-- M[0] as a complex of constant strict towers.
Source: blueprint refinement (2), augmentation
(blueprint: lem-sfb-finite-scalar-model-ordinary-quotient-comparison). -/
abbrev constantComplex (M : A) :=
  (CochainComplex.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj (constant M)

/-- The strict two-term tower [M --pi^(n+1)--> M] in degrees -1,0.
Source: blueprint refinement (2), derived reductions
(blueprint: lem-sfb-finite-scalar-model-ordinary-quotient-comparison). -/
abbrev derivedTower (M : A) :=
  CochainComplex.mappingCone
    ((CochainComplex.singleFunctor (ℕᵒᵖ ⥤ A) 0).map (powers s M))

/-- The ordinary sheaf cokernel tower, in degree zero, with actual quotient transitions.
Source: blueprint refinement (2), ordinary finite quotients
(blueprint: lem-sfb-finite-scalar-model-ordinary-quotient-comparison). -/
abbrev quotientTower (M : A) :=
  (CochainComplex.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj
    (cokernel (powers s M))

/-- The degree-zero quotient augmentation.
Source: blueprint refinement (2), actual quotient augmentation
(blueprint: lem-sfb-finite-scalar-model-ordinary-quotient-comparison). -/
def quotientUnit (M : A) : constantComplex M ⟶ quotientTower s M :=
  (CochainComplex.singleFunctor (ℕᵒᵖ ⥤ A) 0).map
    (cokernel.π (powers s M))

/-- The degree-zero identity augmentation into the cone tower.
Source: blueprint refinement (2), derived reduction augmentation
(blueprint: lem-sfb-finite-scalar-model-ordinary-quotient-comparison). -/
def derivedUnit (M : A) : constantComplex M ⟶ derivedTower s M :=
  CochainComplex.mappingCone.inr
    ((CochainComplex.singleFunctor (ℕᵒᵖ ⥤ A) 0).map (powers s M))

/-- The canonical strict comparison, zero in degree -1 and quotient in degree zero.
Source: blueprint refinement (2), comparison of integral finite quotients
(blueprint: lem-sfb-finite-scalar-model-ordinary-quotient-comparison). -/
def comparison (M : A) : derivedTower s M ⟶ quotientTower s M :=
  CochainComplex.mappingCone.descShortComplex
    (ShortComplex.mk
      ((CochainComplex.singleFunctor (ℕᵒᵖ ⥤ A) 0).map (powers s M))
      (quotientUnit s M) (by
        change _ ≫ (CochainComplex.singleFunctor _ 0).map _ = 0
        rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]))

/-- An actual module map on the source towers, retaining all scalar transitions.
Source: blueprint refinement (2), naturality
(blueprint: lem-sfb-finite-scalar-model-ordinary-quotient-comparison). -/
def sourceMap {M N : A} (f : M ⟶ N) : source s M ⟶ source s N :=
  NatTrans.ofOpSequence (fun _ ↦ f) (by
    intro n
    simpa only [source, Functor.ofOpSequence_map_homOfLE_succ, Functor.id_map] using
      (s.naturality f).symm)

/-- An actual module map on the constant target towers.
Source: blueprint refinement (2), naturality
(blueprint: lem-sfb-finite-scalar-model-ordinary-quotient-comparison). -/
abbrev constantMap {M N : A} (f : M ⟶ N) :
    constant M ⟶ constant N := (Functor.const ℕᵒᵖ).map f

/-- The natural square of powers for an actual module map.
Source: blueprint refinement (2), naturality
(blueprint: lem-sfb-finite-scalar-model-ordinary-quotient-comparison).
Proof: scalar naturality gives pi f = f pi; induction gives the same equality
for every positive power, hence for the corresponding strict tower morphisms. -/
theorem powers_naturality {M N : A} (f : M ⟶ N) :
    powers s M ≫ constantMap f = sourceMap s f ≫ powers s N := by
  sorry

/-- The cone map (f,f), on the actual strict derived-reduction towers.
Source: blueprint refinement (2), naturality
(blueprint: lem-sfb-finite-scalar-model-ordinary-quotient-comparison). -/
def derivedMap {M N : A} (f : M ⟶ N) :
    derivedTower s M ⟶ derivedTower s N :=
  CochainComplex.mappingCone.map _ _
    ((CochainComplex.singleFunctor _ 0).map (sourceMap s f))
    ((CochainComplex.singleFunctor _ 0).map (constantMap f)) (by
      simpa only [← Functor.map_comp] using
        congrArg ((CochainComplex.singleFunctor (ℕᵒᵖ ⥤ A) 0).map)
          (powers_naturality s f))

/-- The map on the ordinary cokernels induced by f.
Source: blueprint refinement (2), naturality
(blueprint: lem-sfb-finite-scalar-model-ordinary-quotient-comparison). -/
def quotientMap {M N : A} (f : M ⟶ N) :
    quotientTower s M ⟶ quotientTower s N :=
  (CochainComplex.singleFunctor _ 0).map
    (cokernel.map _ _ (sourceMap s f) (constantMap f)
      (powers_naturality s f))

variable [HasLimitsOfShape ℕᵒᵖ A]
variable [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]

/-- The ordinary termwise limit on complexes of strict towers.
Source: Stacks 0941, the strict-tower right-derived limit
(blueprint: lem-sfb-finite-scalar-model-ordinary-quotient-comparison). -/
abbrev limitComplex :=
  (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)

/-- The canonical diagonal into the ordinary limit of the constant tower complex.
Source: Stacks 0941, diagonal/limit adjunction
(blueprint: lem-sfb-finite-scalar-model-ordinary-quotient-comparison). -/
def diagonal (M : A) :
    (CochainComplex.singleFunctor (A) 0).obj M ⟶
      (limitComplex (A := A)).obj (constantComplex M) :=
  (CochainComplex.singleFunctor _ 0).map
      ((constLimAdj (J := ℕᵒᵖ) (C := A)).unit.app M) ≫
    (HomologicalComplex.singleMapHomologicalComplex
      (lim : (ℕᵒᵖ ⥤ A) ⥤ A) (.up ℤ) 0).inv.app
        (constant M)

/-- The canonical augmentation into any strict tower, using the right-derived unit.
Source: Stacks 0941 and the blueprint integral comparison augmentation
(blueprint: lem-sfb-finite-scalar-model-ordinary-quotient-comparison). -/
def limitUnit
    (L : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} (A))
    (η : limitComplex (A := A) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ L)
    (M : A) {T : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (a : constantComplex M ⟶ T) :
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor (A) 0).obj M) ⟶
      L.obj (DerivedCategory.Q.obj T) :=
  DerivedCategory.Q.map (diagonal (A := A) M) ≫ η.app (constantComplex M) ≫
    L.map (DerivedCategory.Q.map a)


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (V : Scheme.{u})

/-- Ordinary modules over the pullback of the continuous condensed valuation ring.
Source: blueprint refinement (2), integral finite models
(blueprint: lem-sfb-finite-scalar-model-ordinary-quotient-comparison). -/
abbrev Modules := Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
  (condensedRingObj (IntegralQuotient.integral l E) V)

/-- Multiplication by the chosen uniformizer on every module, via the existing scalar action.
Source: blueprint refinement (2), integral finite models
(blueprint: lem-sfb-finite-scalar-model-ordinary-quotient-comparison). -/
def scalar : 𝟭 (Modules l E V) ⟶ 𝟭 (Modules l E V) :=
  (leftUnitorNatIso (Modules l E V)).inv ≫
    (tensoringLeft (Modules l E V)).map (IntegralQuotient.multiplication l E V 0) ≫
      (leftUnitorNatIso (Modules l E V)).hom

variable [HasDerivedCategory.{w} (Modules l E V)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ Modules l E V)]

/-- The canonical comparison of derived and ordinary quotient limits, natural for actual
module maps and identifying the two prescribed augmentations.

Source: blueprint det-sf-comp-coherence-refinement proof (2), via the Refinement
isomorphisms paragraph of det-sf-comp-coherence-cocycle; Stacks 0941, 093J, 093M, 00PD.
(blueprint: lem-sfb-finite-scalar-model-ordinary-quotient-comparison).

Proof plan:
1. On each member of the finite-scalar-model cover, choose a finite presentation
A^r -> P (def-sc-finitely-presented-module). Apply lem-weil-l-adic-extension-integers-dvr,
lem-sc-dvr-saturation-line-smith-normal-form and
lem-weil-pbc-dvr-unit-times-uniformizer-power to get P = A^(r-s) plus
finitely many A/pi^b summands. Zero summands and ranks are allowed.
2. Constant sheafification and the normalized flat scalar extension carry this
presentation to the same diagonal matrix over B, using
lem-sfb-integral-quotient-resolution-normalization and
lem-sfb-constant-finite-free-presentation-extension. Thus all kernels of pi^n on
this local model lie in its quotient summands, since pi is injective on B.
Take c = max({1} union {b_j}); it kills every such kernel on this cover member.
3. The cone of the actual map [M --pi^n--> M] -> (M/pi^n)[0] is quasi-isomorphic
to ker(pi^n)[2]: it is [M --(-pi^n)--> M --q_n--> M/pi^n] in degrees -2,-1,0.
Its degree -2 cohomology is ker(pi^n), while exactness of the cokernel sequence
kills cohomology in degrees -1 and 0. Kernel inclusion gives a quasi-isomorphism
commuting with transitions pi,1 and quotient, also after exact slice restriction.
4. On this slice, c successive transitions on that kernel tower vanish.
Apply lem-weil-pbc-ringed-strict-tower-homotopy-limit to make Rlim(comparison) invertible.
5. Use lem-sp-slice-restriction-strict-derived-limit and
lem-zl-condensed-cover-restriction-conservative: exact slice restriction commutes with
strict derived limit, and cover restriction detects isomorphisms. No common
bound on c, quasi-compactness, Noetherianity or invertibility of l is used.
6. For every actual f the cone map (f,f) and induced quotient map commute with
the comparison. Apply Rlim. The identity-in-degree-zero augmentation followed
by the comparison is exactly the quotient augmentation. Apply Rlim and
precompose with the diagonal and right-derived unit to obtain the last equality.
No assertion that M is complete or that levelwise comparisons are invertible is made.
-/
theorem finiteScalarOrdinaryQuotientComparison
    (L : DerivedCategory.{w} (ℕᵒᵖ ⥤ Modules l E V) ⥤ DerivedCategory.{w} (Modules l E V))
    (η : limitComplex (A := Modules l E V) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ L)
    [L.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ Modules l E V) (.up ℤ))] :
    (∀ (M : Modules l E V), HasFiniteConstantLocalModel (IntegralQuotient.integral l E) V M →
      IsIso (L.map (DerivedCategory.Q.map (comparison (scalar l E V) M)))) ∧
    (∀ (M N : Modules l E V),
      HasFiniteConstantLocalModel (IntegralQuotient.integral l E) V M →
      HasFiniteConstantLocalModel (IntegralQuotient.integral l E) V N →
      ∀ f : M ⟶ N,
        L.map (DerivedCategory.Q.map (derivedMap (scalar l E V) f)) ≫
            L.map (DerivedCategory.Q.map (comparison (scalar l E V) N)) =
          L.map (DerivedCategory.Q.map (comparison (scalar l E V) M)) ≫
            L.map (DerivedCategory.Q.map (quotientMap (scalar l E V) f))) ∧
    (∀ (M : Modules l E V), HasFiniteConstantLocalModel (IntegralQuotient.integral l E) V M →
      limitUnit L η M (derivedUnit (scalar l E V) M) ≫
          L.map (DerivedCategory.Q.map (comparison (scalar l E V) M)) =
        limitUnit L η M (quotientUnit (scalar l E V) M)) := by
  sorry

end AlgebraicGeometry.ProEtale.FiniteScalarOrdinaryComparison
