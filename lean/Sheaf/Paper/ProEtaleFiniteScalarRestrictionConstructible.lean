/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-!
# Finite scalar restriction preserves pro-etale constructibility

Source: current Weil blueprint, sec-proetale-coefficients,
`sk-prop-integral-criterion-reductions.proof.md`, second paragraph, last sentence;
Stacks Tags 03DA, 03D2, 093I, 093Q, 09AJ, 010N and 015F
(blueprint: lem-pe-finite-scalar-restriction-constructible).

The coefficient map is arbitrary; no surjectivity or flatness is imposed.
The intrinsic constant-ring module category and its existing exact restriction functor
are used throughout. The witness statements retain each original local trivialization cover.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Finite scalar restriction is exact, preserves constructible sheaves and bounded
constructibility, commutes naturally with every cohomology functor, and preserves and
reflects cohomology vanishing in every degree.
Source: current Weil blueprint, integral-criterion reductions, second proof paragraph,
last sentence; Stacks Tags 03DA, 03D2, 093I, 093Q, 09AJ, 010N and 015F
(blueprint: lem-pe-finite-scalar-restriction-constructible).
Proof:
1. Restriction leaves the underlying abelian sheaf and maps unchanged. The kernel and
sheafified cokernel constructions of lem-weil-pbc-module-sheaves-colimits-forgetful
therefore commute with it. It is additive, exact and reflects zero objects.
2. On every stratum, the canonical inverse-image identifications of the two constant
rings commute with the coefficient map, since both composites agree on constant sections
(prop-weil-pbc-proetale-constant-ring-map). Inverse image of the restricted action is
thus the restricted inverse-image action. Extension along the coefficient identifications
only transports this action. Restriction to a covering object also commutes sectionwise.
3. The constant module presheaf has the same underlying abelian presheaf after scalar
restriction. Its abelian sheafification is unchanged (lem-cbc-sieve-module-sheafification),
and the restricted scalar actions agree on constant sections. Thus the same strata and
covers trivialize the restricted sheaf, with the scalar-restricted constant modules.
4. Geometric stalks retain their underlying sets. A finitely generated module over finite
B is a quotient of a finite power of B, hence finite. Its restriction is generated over A
by the finite list of all its elements. This proves constructibility without surjectivity.
5. Exact descent (lem-weil-pbc-exact-functor-derived-factorization) gives the existing
termwise mapDerivedCategory on unbounded complexes. The exact-functor homology comparison
(lem-weil-pbc-exact-functor-complex-cohomology) descends naturally through localization,
giving the displayed natural isomorphisms in every degree, without a resolution bound.
6. Combine that comparison with reflection of zero objects. Each vanishing degree is
preserved and reflected; thus the same lower and upper bounds work. Constructibility of
all cohomology sheaves follows from steps 2--4. This proves bounded constructibility. -/
theorem proEtaleFiniteScalarRestriction_constructible
    (X : Scheme.{u}) [IsNoetherian X]
    (A B : Type u) [CommRing A] [CommRing B] [Finite A] [Finite B] (a : A →+* B) :
    PreservesFiniteLimits (proEtaleRingRestrictScalars
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))) ∧
    PreservesFiniteColimits (proEtaleRingRestrictScalars
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))) ∧
    (∀ F : proEtaleRingModules X (proEtaleConstantRing X B),
      IsConstructibleProEtaleModuleSheaf X B F →
      IsConstructibleProEtaleModuleSheaf X A
        ((proEtaleRingRestrictScalars
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))).obj F)) ∧
    (∀ q : ℤ, Nonempty
      ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          (proEtaleRingRestrictScalars
            ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
              (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))) _
          (proEtaleRingRestrictScalars_preservesFiniteLimits _)
          (proEtaleRingRestrictScalars_preservesFiniteColimits _)) ⋙
          DerivedCategory.homologyFunctor (proEtaleRingModules X (proEtaleConstantRing X A)) q ≅
        DerivedCategory.homologyFunctor (proEtaleRingModules X (proEtaleConstantRing X B)) q ⋙
          proEtaleRingRestrictScalars
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom a.ulift.{u + 1, u + 1})))) ∧
    (∀ (L : DerivedCategory (proEtaleRingModules X (proEtaleConstantRing X B))) (q : ℤ),
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) q).obj
          ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          (proEtaleRingRestrictScalars
            ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
              (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))) _
          (proEtaleRingRestrictScalars_preservesFiniteLimits _)
          (proEtaleRingRestrictScalars_preservesFiniteColimits _)).obj L)) ↔
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X B)) q).obj L)) ∧
    (∀ L : DerivedCategory (proEtaleRingModules X (proEtaleConstantRing X B)),
      DerivedCategory.TStructure.t.bounded L →
      (∀ q : ℤ, IsConstructibleProEtaleModuleSheaf X B
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules X (proEtaleConstantRing X B)) q).obj L)) →
      DerivedCategory.TStructure.t.bounded
        ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          (proEtaleRingRestrictScalars
            ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
              (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))) _
          (proEtaleRingRestrictScalars_preservesFiniteLimits _)
          (proEtaleRingRestrictScalars_preservesFiniteColimits _)).obj L) ∧
      ∀ q : ℤ, IsConstructibleProEtaleModuleSheaf X A
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules X (proEtaleConstantRing X A)) q).obj
            ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          (proEtaleRingRestrictScalars
            ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
              (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))) _
          (proEtaleRingRestrictScalars_preservesFiniteLimits _)
          (proEtaleRingRestrictScalars_preservesFiniteColimits _)).obj L))) := by
  sorry

/-- Every chosen stratum cover and its constant module models still trivialize the
scalar-restricted sheaf. This records the unchanged witnesses in constructibility.
Source: current Weil blueprint, integral-criterion reductions, second proof paragraph;
Stacks Tags 03D2, 093I and 093Q
(blueprint: lem-pe-finite-scalar-restriction-constructible).
Proof: use the commuting coefficient square of step 2 of the node's proof to identify
pullback after restriction with restriction after pullback. Localizing over each U j
commutes with restriction sectionwise. Restrict the given trivialization, then identify
restriction of the constant module sheaf with the constant sheaf of the restricted
module: their abelian sheafifications coincide and their scalar actions on constant
sections are both (b,m) ↦ a(b)m (step 3, lem-cbc-sieve-module-sheafification).
The displayed covers and indices are literally the input covers and indices. -/
theorem proEtaleFiniteScalarRestriction_sameTrivializations
    (X : Scheme.{u}) [IsNoetherian X]
    (A B : Type u) [CommRing A] [CommRing B] [Finite A] [Finite B] (a : A →+* B)
    (F : proEtaleRingModules X (proEtaleConstantRing X B))
    (S : Stratification X) (i : Fin S.n)
    (I : Type (u + 1)) (U : I → (S.domain i).ProEt)
    (f : ∀ j : I, U j ⟶ ProEt.mk (𝟙 (S.domain i)))
    (_hc : Presieve.ofArrows U f ∈ (ProEt.precoverage (S.domain i)).coverings _)
    (M : I → ModuleCat.{u + 1} (ULift.{u + 1, u} B))
    (_ht : ∀ j : I, Nonempty
      ((proEtaleConstantModulePullback (S.immersion i) B F).over (U j) ≅
        proEtaleConstantModuleSheafOver (S.domain i) B (U j) (M j))) :
    ∀ j : I, Nonempty
      ((proEtaleConstantModulePullback (S.immersion i) A
        ((proEtaleRingRestrictScalars
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))).obj F)).over (U j) ≅
        proEtaleConstantModuleSheafOver (S.domain i) A (U j)
          ((ModuleCat.restrictScalars.{u + 1} a.ulift.{u + 1, u + 1}).obj (M j))) := by
  sorry

/-- The locally constant and finite-stalk conditions hold on the very same strata.
Source: current Weil blueprint, integral-criterion reductions, second proof paragraph;
Stacks Tag 09AJ (blueprint: lem-pe-finite-scalar-restriction-constructible).
Proof: apply the unchanged-cover comparison of steps 2--3 to each stratum's chosen
local constancy witness. The geometric-stalk neighbourhood diagrams and equivalence
relations are unchanged by restriction of scalars, so the stalk sets are unchanged.
A finite B-module stalk is finite as a set and hence is generated over A by all of its
elements (step 4). This gives both clauses for each original stratum, with no refinement. -/
theorem proEtaleFiniteScalarRestriction_sameStratification
    (X : Scheme.{u}) [IsNoetherian X]
    (A B : Type u) [CommRing A] [CommRing B] [Finite A] [Finite B] (a : A →+* B)
    (F : proEtaleRingModules X (proEtaleConstantRing X B)) (S : Stratification X)
    (_hS : ∀ i : Fin S.n,
      IsLocallyConstantProEtaleModuleSheaf (S.domain i) B
        (proEtaleConstantModulePullback (S.immersion i) B F) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (y : Spec (.of Ω) ⟶ S.domain i),
        Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing (S.domain i) B)
          (proEtaleConstantModulePullback (S.immersion i) B F))) :
    ∀ i : Fin S.n,
      IsLocallyConstantProEtaleModuleSheaf (S.domain i) A
        (proEtaleConstantModulePullback (S.immersion i) A
          ((proEtaleRingRestrictScalars
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))).obj F)) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (y : Spec (.of Ω) ⟶ S.domain i),
        Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing (S.domain i) A)
          (proEtaleConstantModulePullback (S.immersion i) A
            ((proEtaleRingRestrictScalars
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))).obj F))) := by
  sorry

end AlgebraicGeometry.Scheme
