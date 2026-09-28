/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!
# Torsors and étale `H^1`

Let `Y` be a scheme and `M` a finite abelian group. An `M`-torsor on the small étale site of
`Y` is the same thing as a finite étale surjective `Y`-scheme `P` carrying a simply
transitive action of `M` over `Y`; that is the form in which the notion is recorded here, as
`AlgebraicGeometry.Scheme.EtaleTorsor`. Simple transitivity is the statement that the
canonical morphism `∐_{m ∈ M} P ⟶ P ×_Y P` sending the `m`-th summand by `(m +ᵥ -, id)` is an
isomorphism, which is available because `M` is finite, hence `Small.{u}`.

Isomorphism of torsors is an equivalence relation
(`AlgebraicGeometry.Scheme.EtaleTorsor.setoid`), and the proposition of the blueprint
subsection `sk-prop-input-torsors` is that the quotient by it is in canonical bijection with
`H^1(Y_ét, M)`, the first sheaf cohomology of the constant sheaf with value `M`. The
statement below records that bijection together with the one further property of it that the
smooth base change proof uses: a torsor has class `0` exactly when its structure morphism
admits a section.

## Implementation notes

Two refinements of Stacks `02NE` recorded in the sketch are not part of the statement.

The first is the naturality of the bijection in the pair `(Y, M)`. The proof of the vanishing
theorem `sk-thm-vanishing` uses naturality in `Y`: it pulls a torsor back along a morphism
`Y' ⟶ Y` and concludes that its class dies. Stating it needs a pullback map
`H^1(Y_ét, M) ⟶ H^1(Y'_ét, M)` on sheaf cohomology along a morphism of schemes, which neither
Mathlib nor this repository has; recording that map is what a file completing this subsection
needs first.

The second is the criterion, for `Y` connected and `M = ℤ/dℤ`, that the torsor attached to a
class be connected — a Galois cover with group `ℤ/dℤ`, which is the input of
`sk-prop-input-spreading` — exactly when the corresponding homomorphism out of the étale
fundamental group is surjective. Mathlib has no étale fundamental group, so this is left to
the prose.

## Main definitions

- `AlgebraicGeometry.Scheme.EtaleTorsor`: an `M`-torsor over a scheme `Y`.
- `AlgebraicGeometry.Scheme.EtaleTorsor.IsIsomorphic` and
  `AlgebraicGeometry.Scheme.EtaleTorsor.setoid`: the isomorphism relation on torsors, and
  the fact that it is an equivalence relation.

## Main statements

- `AlgebraicGeometry.Scheme.EtaleTorsor.exists_quotientEquivSheafH`: the bijection between
  isomorphism classes of `M`-torsors on `Y` and `H^1(Y_ét, M)`, under which the class of a
  torsor vanishes exactly when the torsor has a section.

## References

- Stacks Project, Tag `02NE`, <https://stacks.math.columbia.edu/tag/02NE>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (M : Type (u + 1)) [AddCommGroup M] [Finite M]

/-- An `M`-torsor over a scheme `Y`: a finite étale surjective `Y`-scheme with a simply
transitive action of the finite abelian group `M`.

Simple transitivity is expressed by the isomorphism `M × P ≅ P ×_Y P`, in the form that the
morphism `∐_{m ∈ M} P ⟶ P ×_Y P` whose `m`-th component is `(m +ᵥ -, id)` is an isomorphism:

```
∐_{m ∈ M} P --≅--> P ×_Y P --pr₁--> P
                                    |
                                    π
                                    v
                                    Y
```

The coproduct exists because `M` is finite, hence small. -/
structure Scheme.EtaleTorsor (Y : Scheme.{u}) where
  /-- the total space of the torsor -/
  P : Scheme.{u}
  /-- the structure morphism to the base -/
  π : P ⟶ Y
  [isFinite : IsFinite π]
  [etale : Etale π]
  [surjective : Surjective π]
  /-- the action of `M` on `P` over `Y` -/
  vadd : M → (P ⟶ P)
  /-- the action is by morphisms over `Y` -/
  vadd_π (m : M) : vadd m ≫ π = π
  /-- the zero of `M` acts as the identity -/
  zero_vadd : vadd 0 = 𝟙 P
  /-- the action is additive in the acting variable -/
  add_vadd (m n : M) : vadd (m + n) = vadd m ≫ vadd n
  /-- the action is simply transitive: `∐_{m ∈ M} P ≅ P ×_Y P` -/
  isIso_sigmaDesc : IsIso (Sigma.desc
    fun m : M ↦ pullback.lift (f := π) (g := π) (vadd m) (𝟙 P) (by simp [vadd_π]))

namespace Scheme.EtaleTorsor

variable {M} {Y : Scheme.{u}}

/-- Two `M`-torsors over `Y` are isomorphic when their total spaces are isomorphic over `Y`
by an isomorphism commuting with the `M`-actions. -/
def IsIsomorphic (t₁ t₂ : EtaleTorsor M Y) : Prop :=
  ∃ φ : t₁.P ≅ t₂.P, φ.hom ≫ t₂.π = t₁.π ∧
    ∀ m : M, t₁.vadd m ≫ φ.hom = φ.hom ≫ t₂.vadd m

lemma isIsomorphic_refl (t : EtaleTorsor M Y) : t.IsIsomorphic t :=
  ⟨Iso.refl _, by simp, by simp⟩

lemma IsIsomorphic.symm {t₁ t₂ : EtaleTorsor M Y} (h : t₁.IsIsomorphic t₂) :
    t₂.IsIsomorphic t₁ := by
  obtain ⟨φ, hπ, hv⟩ := h
  refine ⟨φ.symm, ?_, fun m ↦ ?_⟩
  · rw [Iso.symm_hom, ← hπ, Iso.inv_hom_id_assoc]
  · rw [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, hv, Iso.inv_hom_id_assoc]

lemma IsIsomorphic.trans {t₁ t₂ t₃ : EtaleTorsor M Y} (h₁ : t₁.IsIsomorphic t₂)
    (h₂ : t₂.IsIsomorphic t₃) : t₁.IsIsomorphic t₃ := by
  obtain ⟨φ, hπ, hv⟩ := h₁
  obtain ⟨ψ, hπ', hv'⟩ := h₂
  refine ⟨φ ≪≫ ψ, ?_, fun m ↦ ?_⟩
  · rw [Iso.trans_hom, Category.assoc, hπ', hπ]
  · simp only [Iso.trans_hom, ← Category.assoc, hv]
    simp only [Category.assoc, hv']

lemma isIsomorphic_equivalence : Equivalence (IsIsomorphic (M := M) (Y := Y)) :=
  ⟨isIsomorphic_refl, IsIsomorphic.symm, IsIsomorphic.trans⟩

variable (M Y) in
/-- Isomorphism of `M`-torsors over `Y` as a setoid, so that the isomorphism classes are
the quotient `Quotient (EtaleTorsor.setoid M Y)`. -/
instance setoid : Setoid (EtaleTorsor M Y) := ⟨IsIsomorphic, isIsomorphic_equivalence⟩

variable (M Y) in
/-- Blueprint `sk-prop-input-torsors`: Torsors and étale H^1

For a scheme `Y` and a finite abelian group `M` the isomorphism classes of `M`-torsors on
the small étale site of `Y` are in canonical bijection with the first sheaf cohomology
group `H^1(Y_ét, M)` of the constant sheaf with value `M`, under which the class of a
torsor vanishes exactly when its structure morphism admits a section, that is, exactly
when the torsor is trivial.

An `M`-torsor is, by `AlgebraicGeometry.Scheme.EtaleTorsor`, the same thing as a finite
étale surjective `Y`-scheme with a simply transitive `M`-action; the naturality of the
bijection in `(Y, M)` and the connectedness criterion of the sketch are not part of this
statement, see the implementation notes of this file. -/
@[stacks 02NE]
theorem exists_quotientEquivSheafH :
    ∃ c : Quotient (EtaleTorsor.setoid M Y) ≃ Sheaf.H
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of M)) 1,
      ∀ t : EtaleTorsor M Y, c ⟦t⟧ = 0 ↔ ∃ s : Y ⟶ t.P, s ≫ t.π = 𝟙 Y :=
  sorry

end Scheme.EtaleTorsor

end AlgebraicGeometry
