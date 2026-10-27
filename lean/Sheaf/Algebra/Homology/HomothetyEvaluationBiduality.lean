/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Algebra.Homology.DerivedEvaluationFiniteInjective
import Sheaf.Algebra.Homology.DerivedEvaluationCanonicalMap

/-! # Homothety, evaluation and coherent biduality

Source: Stacks Project, dualizing.tex, Tag 0A7C, lemma-dualizing, proof;
more-algebra.tex, Tags 0A67, 0A69 and 066E
(blueprint: lem-trf-homothety-evaluation-biduality).

All objects belong to the ordinary module derived category. Tensor and internal Hom
are the existing K-flat derived tensor and K-injective derived closed structure.
The braiding is the existing descended Koszul braiding, supplied explicitly.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace DerivedCategory

variable (R : Type u) [CommRing R]

/-- The canonical evaluation comparison in ordinary D(R), transposed from the composite
which sends B tensor (T tensor K) to T tensor (K tensor B), evaluates K tensor B,
and then evaluates L tensor T, where B = RHom(K,L) and T = RHom(L,L).
The two interchanges are the descended graded symmetry, not chosen maps.
Source: Stacks Project, Tag 0A67, lemma-internal-hom-evaluate
(blueprint: lem-trf-homothety-evaluation-biduality). -/
def homothetyEvaluationComparison (K L : DerivedCategory (ModuleCat.{u} R)) :
    (ordinaryModuleDerivedInternalHom R).obj (op L, L) ⊗ K ⟶
      (ordinaryModuleDerivedInternalHom R).obj
        (op ((ordinaryModuleDerivedInternalHom R).obj (op K, L)), L) :=
  MonoidalClosed.curry
    (((DerivedMonoidal.braidedCategory' Qh
        (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))).braiding
        ((ihom K).obj L) ((ihom L).obj L ⊗ K)).hom ≫
      (α_ ((ihom L).obj L) K ((ihom K).obj L)).hom ≫
      ((ihom L).obj L) ◁ (ihom.ev K).app L ≫
      ((DerivedMonoidal.braidedCategory' Qh
        (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))).braiding
        ((ihom L).obj L) L).hom ≫
      (ihom.ev L).app L)

/-- Canonical biduality in ordinary D(R): transpose of evaluation, with the graded
symmetry placing the internal-Hom factor on the right for Mathlib's left tensor adjunction.
It is the existing general double-dual map `MonoidalClosed.toIhomIhom L K`, that is
`curry ((β_ _ K).hom ≫ (ihom.ev K).app L)`, for the descended Koszul braiding.
Source: Stacks Project, Tag 0A7C, lemma-dualizing, proof, and Tag 0A67
(blueprint: lem-trf-homothety-evaluation-biduality). -/
abbrev homothetyCanonicalBidual (K L : DerivedCategory (ModuleCat.{u} R)) :
    K ⟶ (ordinaryModuleDerivedInternalHom R).obj
      (op ((ordinaryModuleDerivedInternalHom R).obj (op K, L)), L) :=
  @MonoidalClosed.toIhomIhom (DerivedCategory (ModuleCat.{u} R)) _ _
    (DerivedMonoidal.braidedCategory' Qh
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))) _ L K

/-- Homothety and finite injective dimension give canonical biduality for every complex
with degreewise finite cohomology, without any cohomological bound on K or finiteness
condition on the cohomology of L. The homothety is the transpose of the unit action,
with R[0] identified with the tensor unit by singleFunctorObjUnitIso.
Source: Stacks Project, Tag 0A7C, lemma-dualizing, proof; Tags 0A67, 0A69 and 066E
(blueprint: lem-trf-homothety-evaluation-biduality).

Proof:
1. For each n the good truncation truncLE n K is bounded above and has the same finite
cohomology as K in degrees at most n. The Noetherian pseudo-coherence criterion
(lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion, Tag 066E) makes it
pseudo-coherent. No uniform upper bound on K is imposed.
2. The closed symmetric monoidal structure on the one-object ringed site
(lem-sf-ringed-derived-closed-symmetric-monoidal) identifies its unit with R[0].
The homothety isomorphism identifies RHom(L,L) with this unit. Tensoring with any
module in degree zero therefore has cohomology only in degree zero: its Tor amplitude
is [0,0]. The given bounded injective representative supplies finite injective dimension.
3. Apply lem-trf-derived-evaluation-finite-injective (Tag 0A69) with M=L, using the
pseudo-coherent truncations from step 1 and both dimension conditions from step 2.
The specified evaluation comparison is an isomorphism.
4. Uncurry the displayed composite using lem-trf-derived-evaluation-canonical-map
(Tag 0A67). Evaluation of homothety acts as the identity of L. Naturality of the unitors
reduces the transpose to evaluation RHom(K,L) tensor K to L. Injectivity of the
adjunction bijection identifies the composite with homothetyCanonicalBidual.
5. Every factor of the composite is invertible, hence so is canonical biduality.
Naturality of evaluation, tensoring homothety, and the unitor gives the last equation,
where the internal-Hom map is contravariantly applied twice. No finite cohomology
assumption on L is used in any step. -/
theorem homothety_evaluation_biduality
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (L : DerivedCategory (ModuleCat.{u} R))
    (hL : ∃ J : CochainComplex (ModuleCat.{u} R) ℤ,
      (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (J.X i)) ∧
      (∀ i : ℤ, Injective (J.X i)) ∧ Nonempty (Q.obj J ≅ L))
    (hh : IsIso ((singleFunctorObjUnitIso (ModuleCat.{u} R)).hom ≫
      MonoidalClosed.id L)) :
    (∀ K : DerivedCategory (ModuleCat.{u} R),
      (∀ i : ℤ, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj K)) →
      IsIso (homothetyEvaluationComparison R K L) ∧
      (λ_ K).inv ≫ (singleFunctorObjUnitIso (ModuleCat.{u} R)).inv ▷ K ≫
          (((singleFunctorObjUnitIso (ModuleCat.{u} R)).hom ≫
            MonoidalClosed.id L) ▷ K) ≫ homothetyEvaluationComparison R K L =
        homothetyCanonicalBidual R K L ∧
      IsIso (homothetyCanonicalBidual R K L)) ∧
    (∀ (K K' : DerivedCategory (ModuleCat.{u} R)) (f : K ⟶ K'),
      (∀ i : ℤ, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj K)) →
      (∀ i : ℤ, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj K')) →
      f ≫ homothetyCanonicalBidual R K' L =
        homothetyCanonicalBidual R K L ≫
          (ordinaryModuleDerivedInternalHom R).map
            (((ordinaryModuleDerivedInternalHom R).map (f.op, 𝟙 L)).op, 𝟙 L)) := by
  sorry

end DerivedCategory
