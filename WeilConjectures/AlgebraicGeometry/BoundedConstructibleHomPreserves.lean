/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleHomSingle
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleHomPreservation

/-! # Derived internal Hom preserves bounded constructibility

Source: latest blueprint, `sec-six-functors-basics/sk-prop-open-coefficients/`,
`lem-sfb-dc-hom-preserves.md`,
node `lem-sfb-dc-hom-preserves`, order 2721 (blueprint: lem-sfb-dc-hom-preserves).

The statement says that for the three specified condensed coefficient families on a separated
finite-type scheme over a field of positive characteristic different from `ℓ`, the native relative
derived internal Hom of two bounded constructible complexes is bounded constructible. The proof
uses the definitional identification of the determinant and sketch predicates, the Noetherian
finite-type lemma, the constructibility-predicate comparison, degree-zero internal-Hom finiteness,
and the two-variable finite-truncation dévissage theorem.
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped CategoryTheory.Obj

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The derived internal Hom of bounded constructible complexes is bounded constructible for
`ℓ`-adic condensed coefficients.

Source: Bhatt--Scholze, Proposition 6.8.11(3), Proposition 6.8.14 and Remark 6.8.15;
Stacks Project, Tag 01T6. The proof uses the existing degree-zero finiteness
and truncation lemmas, rather than the obsolete SGA citation in the source metadata.
(blueprint: lem-sfb-dc-hom-preserves)

Proof plan: (1) the determinant and sketch definitions of bounded constructibility and the native
relative derived internal Hom identify the objects in this statement
(`det-def-sfb-bounded-constructible`, `sk-def-sfb-bounded-constructible`,
`det-def-sfb-derived-tensor-hom`, `sk-def-sfb-derived-tensor-hom`). The two pairs of condensed-ring
definitions and the pulled-back coefficient definitions likewise give identical coefficients.
(2) A field is Noetherian,
so the finite-type structure morphism makes `X.left` Noetherian; the characteristic and separated
finite-type hypotheses give the required geometric assumptions
(`lem-weil-pbc-finite-type-over-noetherian`, `det-def-sfb-dc-setting`).
(3) On this Noetherian scheme,
`lem-sfb-adic-constructibility-predicate-comparison` converts the general locally-finitely-presented
predicate to the finite constant-local-model predicate. The degree-zero internal-Hom finiteness
statement `lem-sfb-dc-hom-single` applies to all three families, including integral torsion modules.
(4) The
finite-truncation theorem `lem-sfb-dc-hom-devissage` closes bounded constructibility under Hom for
arbitrary bounded constructible inputs. -/
theorem boundedConstructible_hom_preserves
    (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ (E : Type) (_ : Field E) (_ : Algebra E (PadicAlgCl ℓ))
          (_ : Algebra ℚ_[ℓ] E) (_ : IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ))
          (_ : FiniteDimensional ℚ_[ℓ] E),
        Mon.mk Λ = Mon.mk (Profinite.padicIntegersRingObj ℓ E)) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Mon.mk Λ = Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Mon.mk Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    (K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left)
      Ab.{u + 1}) (condensedRingObj Λ X.left)))
    (hK : boundedConstructible (condensedRingObj Λ X.left) K)
    (hL : boundedConstructible (condensedRingObj Λ X.left) L) :
    boundedConstructible (condensedRingObj Λ X.left)
      (((derivedHom Λ X.left).obj (op K)).obj L) := by
  let P : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) → Prop :=
    fun R ↦ ∀ [IsCommMonObj R.X],
      (boundedConstructible (condensedRingObj R.X X.left)).IsMonoidalClosed
  have hclosed : P (Mon.mk Λ) := by
    rcases hΛ with ⟨E, hE, hAlg, hPadic, hTower, hFin, h⟩ | ⟨E, h⟩ | h
    · rw [h]
      intro
      exact PadicIntegersRingObj.boundedConstructible_hom_closure X ℓ E
        (PadicIntegersRingObj.boundedConstructible_hom_single ℓ E X)
    · rw [h]
      intro
      exact ContinuousMapRingObj.boundedConstructible_hom_closure X ℓ E
        (ContinuousMapRingObj.boundedConstructible_hom_single ℓ E X)
    · rw [h]
      intro
      exact boundedConstructible_hom_closure X ℓ
        (boundedConstructible_hom_single ℓ X)
  have : (boundedConstructible (condensedRingObj Λ X.left)).IsMonoidalClosed := hclosed
  exact (boundedConstructible _).prop_ihom hK hL

end AlgebraicGeometry.ProEtale.CondensedRing
