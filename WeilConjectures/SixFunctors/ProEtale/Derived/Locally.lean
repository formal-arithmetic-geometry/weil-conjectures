/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.DualizableLocalRetract
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar

/-!
# Properties holding locally on the pro-étale site

Let `P` be a property of objects of the derived categories `D(Y_proét)` of pro-étale sheaves,
for all schemes `Y`. An object `K ∈ D(X_proét)` satisfies `P` *locally* if there is a pro-étale
covering family `g i : W i ⟶ X` such that every derived pullback `Lg_i^* K` satisfies `P`
(`AlgebraicGeometry.ProEtale.IsLocally`).

## Main results

- `AlgebraicGeometry.ProEtale.IsLocally.of_prop`: a property which holds holds locally.
- `AlgebraicGeometry.ProEtale.IsLocally.trans`: a property which holds locally locally holds
  locally, as pro-étale covering families are stable under composition.
- `AlgebraicGeometry.ProEtale.IsLocally.of_mem_topology`: a property holding at the pullbacks to
  the members of a covering sieve of the terminal object of `X_proét` holds locally.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open _root_.AlgebraicGeometry.Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- A property `P` of objects of the derived categories of pro-étale sheaves holds *locally* at
`K ∈ D(X_proét)` if there is a pro-étale covering family `g i : W i ⟶ X`, indexed by a
`Type u`, such that every derived pullback `Lg_i^* K` satisfies `P`. -/
def IsLocally (P : ∀ Y : Scheme.{u}, DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) → Prop)
    {X : Scheme.{u}} (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) : Prop :=
  ∃ (ι : Type u) (W : ι → Scheme.{u}) (g : ∀ i, W i ⟶ X) (_ : ∀ i, WeaklyEtale (g i)),
    Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X ∧
      ∀ i, P (W i) (L((g i)^*[A]).obj K)

variable {A} {P P' : ∀ Y : Scheme.{u}, DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) → Prop}

/-- A property is *closed under isomorphisms* if it is transported along isomorphisms. -/
def IsClosedUnderIsoms (P : ∀ Y : Scheme.{u}, DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) →
    Prop) : Prop :=
  ∀ ⦃Y : Scheme.{u}⦄ ⦃K K' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)⦄,
    (K ≅ K') → P Y K → P Y K'

lemma IsLocally.mono {X : Scheme.{u}} {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (h : IsLocally A P K) (hPP' : ∀ Y K, P Y K → P' Y K) : IsLocally A P' K := by
  obtain ⟨ι, W, g, hg, hcov, hP⟩ := h
  exact ⟨ι, W, g, hg, hcov, fun i ↦ hPP' _ _ (hP i)⟩

/-- A property which holds holds locally, for the covering by the identity. -/
lemma IsLocally.of_prop (hP : IsClosedUnderIsoms P) {X : Scheme.{u}}
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (h : P X K) : IsLocally A P K := by
  refine ⟨PUnit, fun _ ↦ X, fun _ ↦ 𝟙 X, fun _ ↦ inferInstance, ?_,
    fun _ ↦ hP ((leftDerivedUpperStarId A X).app K).symm h⟩
  rw [Presieve.ofArrows_pUnit]
  exact Precoverage.mem_coverings_of_isIso _

/-- A property which holds locally locally holds locally: pro-étale covering families are
stable under composition, and derived pullbacks compose. -/
lemma IsLocally.trans (hP : IsClosedUnderIsoms P) {X : Scheme.{u}}
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (h : IsLocally A (fun _ K ↦ IsLocally A P K) K) : IsLocally A P K := by
  obtain ⟨ι, W, g, hg, hcov, h⟩ := h
  choose σ V f hf hcov' h' using h
  refine ⟨Σ i, σ i, fun p ↦ V p.1 p.2, fun p ↦ f p.1 p.2 ≫ g p.1, fun p ↦ inferInstance,
    Precoverage.comp_mem_coverings _ hcov _ hcov',
    fun p ↦ hP ((leftDerivedUpperStarComp A (f p.1 p.2) (g p.1)).app K).symm (h' p.1 p.2)⟩

/-- A property which holds at the pullbacks of `K` to the members `V` of a covering sieve of the
terminal object of `X_proét` holds locally at `K`. -/
lemma IsLocally.of_mem_topology {X : Scheme.{u}}
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    {S : Sieve (terminalProEt X)} (hS : S ∈ Scheme.ProEt.topology X (terminalProEt X))
    (h : ∀ ⦃V : X.ProEt⦄ (f : V ⟶ terminalProEt X), S f → P V.left (L((V.hom)^*[A]).obj K)) :
    IsLocally A P K := by
  obtain ⟨ι, W, g, hcov, hS⟩ := exists_proetalePrecoverage_of_mem_topology_terminalProEt hS
  exact ⟨ι, fun i ↦ (W i).left, fun i ↦ (W i).hom, fun i ↦ (W i).prop, hcov,
    fun i ↦ h (g i) (hS i)⟩

/-- Every property holds locally on the empty scheme, for the empty covering family. -/
lemma IsLocally.of_isEmpty {X : Scheme.{u}} [IsEmpty X]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) : IsLocally A P K := by
  refine ⟨PEmpty, PEmpty.elim, fun i ↦ i.elim, fun i ↦ i.elim, ?_, fun i ↦ i.elim⟩
  have : Presieve.ofArrows (PEmpty.elim : PEmpty.{u + 1} → Scheme.{u}) (fun i ↦ i.elim) = ⊥ := by
    ext Z f
    simp only [Presieve.bot_apply, iff_false]
    rintro ⟨i⟩
    exact i.elim
  rw [this]
  exact bot_mem_propQCPrecoverage X

/-- A property which holds at the pullbacks of `K` to the nonempty members `V` of a covering
sieve of the terminal object of `X_proét` holds locally at `K`. -/
lemma IsLocally.of_mem_topology_of_nonempty (hP : IsClosedUnderIsoms P) {X : Scheme.{u}}
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    {S : Sieve (terminalProEt X)} (hS : S ∈ Scheme.ProEt.topology X (terminalProEt X))
    (h : ∀ ⦃V : X.ProEt⦄ (f : V ⟶ terminalProEt X), S f → Nonempty V.left →
      P V.left (L((V.hom)^*[A]).obj K)) :
    IsLocally A P K := by
  refine IsLocally.trans hP (IsLocally.of_mem_topology hS fun V f hf ↦ ?_)
  rcases isEmpty_or_nonempty V.left with hV | hV
  · exact IsLocally.of_isEmpty _
  · exact IsLocally.of_prop hP (h f hf hV)

end AlgebraicGeometry.ProEtale
