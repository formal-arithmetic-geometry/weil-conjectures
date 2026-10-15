/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
import Sheaf.Paper.ReducedSourceFactors
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.FiniteOverProjective

/-!
# Normalizations of the components of a projective scheme

Source: Stacks Project, Varieties, Tags 0BXR and 0GK4; Properties, Tag 033M;
Algebra, Tags 00OK and 00OY
(blueprint: lem-weil-pbc-normalization-projective-components).

The family `Z` presents the reduced irreducible components: integral closed subschemes
whose images enumerate the irreducible components bijectively. The cocone `ι` presents
`N` as the coproduct of their existing integral-scheme normalizations. Thus this statement
applies to any choice of the coproduct, including the empty one.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Componentwise normalization of a projective scheme over a field is finite and surjective,
projective and proper, with finitely many nonempty normal integral clopen summands.
Source: Stacks Project, Varieties, Tags 0BXR and 0GK4; Properties, Tag 033M;
dimension via Algebra, Tags 00OK and 00OY.
(blueprint: lem-weil-pbc-normalization-projective-components)

The structure data `Z`, `a`, `hcomponents`, and `hindex` mean precisely the reduced
irreducible components, not an extra restriction on `C`: an integral closed subscheme
is reduced, and the reduced induced structure on each closed subset is unique.
The data `N`, `ι`, `hN`, `ν`, and `hν` express the componentwise normalization in the node.
The final factorization uses the same component normalizations over the reduction.

Proof:
1. Projective implies proper (lem-pc-projective-proper), hence finite type and
   quasi-compact. Over the Noetherian field, C is Noetherian (pqf-lem-locnoeth-lft,
   pqf-def-locnoeth, def-weil-pbc-quasi-compact-scheme). Its components are finite
   (lem-sc-noetherian-closed-subset-finite-components).
2. Each reduced component is integral, and its closed immersion into C is finite
   (lem-weil-pbc-reduced-induced-closed-subscheme, def-pc-integral-scheme,
   lem-weil-pbc-closed-immersion-finite). Apply lem-fin-finite-over-projective over
   the affine Noetherian base Spec k; it is projective, proper and finite type.
3. Its normalization is finite, surjective and of the same dimension
   (lem-sc-normalization-exists). Composing with its inclusion into C is finite
   (lem-weil-pbc-finite-composition).
4. Affine normalization charts are integral closures in the function field
   (def-fin-normalization-extension, lem-sc-integral-function-field-affine-fraction,
   lem-sc-scheme-sober). They are normal domains
   (lem-weil-pbc-integral-closure-finite-extension-normal). Their stalks are normal
   domains by lem-weil-pbc-spec-domain-stalks-function-field and
   lem-weil-pbc-localization-normal-domain. Their common generic point gives integrality.
5. The coprojections are clopen, disjoint and cover N
   (lem-weil-pbc-scheme-coproduct-family). The induced map is finite by finite
   coproducts (lem-weil-pbc-finite-coproduct), including the empty spectrum of the zero
   ring (def-weil-finite-integral-morphism). Componentwise surjectivity gives surjectivity.
6. Apply lem-fin-finite-over-projective over the affine Noetherian base Spec k to N
   and each summand, and then lem-pc-projective-proper.
7. The component maps factor through the reduction
   (lem-weil-pbc-reduced-source-factors-through-closed-subscheme). The reduced induced
   components of C and its reduction agree; taking the same normalized coproduct gives
   the normalization of the reduction and its factorization (def-weil-pbc-scheme-reduction,
   lem-weil-pbc-reduced-induced-closed-subscheme, lem-weil-pbc-scheme-coproduct-family).
8. A closed component has dimension at most that of C
   (def-kun-topological-krull-dimension). Normalization preserves its dimension
   (lem-sc-normalization-exists), giving the bound by one.
9. Components cover C and are nonempty (def-weil-irreducible-components), so the
   indexing set is empty exactly when C is empty; then the summand assertions are vacuous.
-/
theorem normalization_projective_components
    {k : Type u} [Field k] {C : Scheme.{u}}
    (p : C ⟶ Spec (.of k)) [IsHProjective p]
    {I : Type u} (Z : I → Scheme.{u}) [∀ i : I, IsIntegral (Z i)]
    (a : ∀ i : I, Z i ⟶ C) [∀ i : I, IsClosedImmersion (a i)]
    (hcomponents : ∀ i : I, Set.range (a i) ∈ irreducibleComponents C)
    (hindex : Function.Bijective
      (fun i : I ↦ (⟨Set.range (a i), hcomponents i⟩ : irreducibleComponents C)))
    (N : Scheme.{u}) (ι : ∀ i : I, (Z i).normalization ⟶ N)
    (hN : IsColimit (Cofan.mk N ι)) (ν : N ⟶ C)
    (hν : ∀ i : I, ι i ≫ ν = (Z i).fromNormalization ≫ a i) :
    Finite I ∧ IsFinite ν ∧ Surjective ν ∧
      IsHProjective (ν ≫ p) ∧ IsProper (ν ≫ p) ∧
      (∀ i : I, Nonempty (Z i).normalization ∧
        (∀ x : (Z i).normalization,
          IsDomain ((Z i).normalization.presheaf.stalk x) ∧
            IsIntegrallyClosed ((Z i).normalization.presheaf.stalk x)) ∧
        IsIntegral (Z i).normalization ∧ IsOpenImmersion (ι i) ∧
        IsClosed (Set.range (ι i)) ∧
        IsHProjective ((Z i).fromNormalization ≫ a i ≫ p) ∧
        IsProper ((Z i).fromNormalization ≫ a i ≫ p)) ∧
      (topologicalKrullDim C ≤ 1 →
        ∀ i : I, topologicalKrullDim (Z i).normalization ≤ 1) ∧
      (∃ (b : ∀ i : I, Z i ⟶ C.nilradical.subscheme)
          (νred : N ⟶ C.nilradical.subscheme),
        (∀ i : I, b i ≫ C.nilradical.subschemeι = a i) ∧
          νred ≫ C.nilradical.subschemeι = ν ∧
          ∀ i : I, ι i ≫ νred = (Z i).fromNormalization ≫ b i) ∧
      (IsEmpty I ↔ IsEmpty C) := by
  sorry

end AlgebraicGeometry
