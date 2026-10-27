/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

-- Definition owner: def-sfb-continuous-algcl-scalar-data.
public import Sheaf.Paper.ContinuousAlgclScalarConstructibility
-- Definition owner: def-sfb-support-scalar-data.
public import Sheaf.Paper.ContinuousAlgClFiniteStageDevissage
public import Sheaf.Paper.ConstantModelTorAmplitude
public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CondensedOpenClosedRecollement
import Sheaf.Algebra.Homology.LocallyFreeDerivedScalars
import Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula
import Sheaf.Paper.KFlatScalarComparisonNormalization
import Sheaf.Paper.ContinuousQbarConstructibleGenerators
import Sheaf.Paper.CoefficientHeartGeneration
import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings

/-!
# Constructibility under all-continuous algebraic-closure scalar extension

Source: blueprint, sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3),
extracted supported-lattice step 2 and its reviewed four-step finite-cone argument
(blueprint: lem-sfb-continuous-algcl-scalar-extension-constructible).

The coefficient rings contain all continuous functions with their norm topologies.
The supported comparison is the total derived counit followed by the existing
unit-normalized balanced support mate. All its arrows are in the target module category.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The canonical scalar/support comparison on a degree-zero supported module.
It is the universal total-left-derived counit, the single-complex comparison,
and the ordinary scalar/support mate, in that order. The last map is the existing
closed pushforward mate followed by the open scalar isomorphism. Its balancing
and unit normalization are those of the scalar-extension adjunctions.
Source: blueprint direct-images proof (3), extracted supported-lattice step 2
(blueprint: lem-sfb-continuous-algcl-scalar-extension-constructible). -/
def lisseSupportDerivedScalarMap
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (ρ : Λ ⟶ Λ') [IsMonHom ρ] {S C Z : Scheme.{u}}
    (j : S ⟶ C) (hj : IsOpenImmersion j) (i : C ⟶ Z)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :
    (Mod.extendScalars (coefficientMap ρ Z)).leftDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((finiteStageSupportExtension Λ j hj i).obj L)) ⟶
      (DerivedCategory.singleFunctor _ 0).obj
        ((finiteStageSupportExtension Λ' j hj i).obj
          ((Mod.extendScalars (coefficientMap ρ S)).obj L)) :=
  let F := Mod.extendScalars (coefficientMap ρ Z)
  let M := (finiteStageSupportExtension Λ j hj i).obj L
  F.leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj ((CochainComplex.singleFunctor _ 0).obj M)) ≫
    DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app M) ≫
      (DerivedCategory.singleFunctor _ 0).map (finiteStageSupportScalarMap ρ j hj i L)

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.ContinuousAlgclScalar

/-- All-continuous algebraic-closure scalar extension preserves bounded constant-model
constructibility and gives finite Tor amplitude. On supported lisse modules it preserves
local ranks and the specified derived support comparison is invertible.

Source: blueprint sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3),
extracted supported-lattice step 2; the reviewed four-step proof of the DAG node
(blueprint: lem-sfb-continuous-algcl-scalar-extension-constructible).

Proof plan:
1. Apply lem-sfb-locally-free-derived-scalars to L on S. Local finite freeness gives
flatness and a K-flat single complex. Scalar extension has the same ranks: on a rank-r
chart the balanced map sends b tensor (a_k) to (b a_k), with inverse (b_k) mapping to
the sum of b_k tensor e_k. These formulas include r = 0, with no flatness of A to B.
2. Factor c as j followed by i. Apply lem-sfb-condensed-support-projection-formula
first to the closed support and then inversely to the open support, with tensor
argument B_Z[0]. The complementary opens are quasi-compact because Z is Noetherian.
Use lem-sfb-alpha-iso for both coefficient rings, including the all-continuous B,
and lem-sfb-kflat-scalar-comparison-normalization to identify the pullback/tensor
map with its unit-preserving balancing map. Apply step 1. The exact support functors
act termwise. The resulting map is precisely lisseSupportDerivedScalarMap:
the derived counit followed by the closed mate and open scalar isomorphism.
All maps are B-linear since multiplication on the B factor commutes with balancing.
3. By lem-sfb-continuous-qbar-constructible-generators, each supported target lisse
module is bounded constructible. Against every B_Z-module N in degree zero, the
same two support projections express its tensor as the support extension of
L_B tensor c^*N. Local freeness of L_B and exactness of pullback and support put
this in degree zero, giving Tor amplitude [0,0], also for nonconstructible N.
4. Apply det-cor-coefficient-heart-ii-generation only to the finite-E source.
Every bounded constructible K is a finite construction by shifts and cones of the
supported lisse generators. Derived change of rings is exact triangulated by
lem-pur-derived-change-of-rings. The target generator theorem makes bounded
constructibility replete and triangulated; det-def-sfb-constructible-tor-amplitude
makes finite Tor amplitude thick. Thus their intersection contains the image.
A shift n changes [a,b] to [a-n,b-n]; a cone of intervals [a,b] and [c,d] has
interval [min(c,a-1),max(d,b-1)]. Finitely many operations give finite bounds.
The zero complex, empty scheme and rank-zero modules use the zero generator. -/
theorem scalar_extension_constructible
    (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [NormedField Ω]
    [NormedAlgebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]
    (E : IntermediateField ℚ_[ℓ] Ω) [FiniteDimensional ℚ_[ℓ] E]
    (Z : Scheme.{u}) [IsLocallyNoetherian Z] [CompactSpace Z] :
    (∀ K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousCoefficientRingObj E) Z)),
      constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj E) Z K →
      constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj Ω) Z
          ((scalarExtension ℓ Ω E Z).obj K) ∧
        DerivedCategory.finiteTorAmplitude _ ((scalarExtension ℓ Ω E Z).obj K)) ∧
    (∀ (S C : Scheme.{u}) (j : S ⟶ C) (hj : IsOpenImmersion j)
      (i : C ⟶ Z) (_hi : IsClosedImmersion i),
      Topology.IsConstructible (Set.range (j ≫ i)) →
      Set.range i = closure (Set.range (j ≫ i)) →
      ∀ L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousCoefficientRingObj E) S),
      IsLisseCoefficientModule (Profinite.continuousCoefficientRingObj E) L →
      IsLisseCoefficientModule (Profinite.continuousCoefficientRingObj Ω)
          ((Mod.extendScalars (coefficientInclusion ℓ Ω E S)).obj L) ∧
        (∀ (V : Scheme.{u}) (f : V ⟶ S) (r : ℕ),
          Nonempty ((CondensedRing.upperStar (Profinite.continuousCoefficientRingObj E) f).obj L ≅
            Mod.finiteFree (condensedRingObj (Profinite.continuousCoefficientRingObj E) V) r) →
          Nonempty
            ((CondensedRing.upperStar (Profinite.continuousCoefficientRingObj Ω) f).obj
                ((Mod.extendScalars (coefficientInclusion ℓ Ω E S)).obj L) ≅
              Mod.finiteFree (condensedRingObj (Profinite.continuousCoefficientRingObj Ω) V) r)) ∧
        IsIso (@CondensedRing.lisseSupportDerivedScalarMap _ _ _ _ _ _
          (inclusion ℓ Ω E).hom (inclusion ℓ Ω E).isMonHom_hom _ _ _ j hj i L)) := by
  sorry

end AlgebraicGeometry.ProEtale.ContinuousAlgclScalar
