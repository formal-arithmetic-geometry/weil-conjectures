/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.LocallyConstant.Basic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCover
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# Pro-étale locally constant sheaves of sets, in cocycle form

Let `f : V ⟶ Y` be a single-morphism pro-étale cover (weakly étale, surjective and
quasi-compact) and `S` a set. A *descent cocycle* (`AlgebraicGeometry.IsDescentCocycle`) is a
function `c : V ×_Y V → (S → S)` on the underlying points such that `z ↦ c z s` is locally
constant for every `s`, every `c z` is bijective, `c` is the identity on the diagonal and
`c (p₁₃ w) = c (p₁₂ w) ∘ c (p₂₃ w)` on the points of `V ×_Y V ×_Y V`. It is a descent datum on
the constant sheaf `S_V`, whose sections are the locally constant functions to `S`, and so it
defines a sheaf of sets `F_c` on `Y_proét` which is pro-étale locally constant. For a scheme
`π : T ⟶ Y`, the sections of `π^* F_c` are the locally constant functions
`σ : V ×_Y T → S` compatible with `c` on `(V ×_Y T) ×_T (V ×_Y T)`
(`AlgebraicGeometry.IsTwistedSection`).

The input from the theory of the pro-étale fundamental group is
`AlgebraicGeometry.exists_isTwistedSection_universalCover`: on a connected regular Noetherian
scheme, every pro-étale locally constant sheaf of sets becomes constant on the universal
profinite étale cover `Ỹ_y`, i.e. it has a section over `Ỹ_y` through every point. This is
Bhatt–Scholze, *The pro-étale topology for schemes*, Lemma 7.4.10 (on a geometrically unibranch
scheme every locally constant sheaf of sets on `Y_proét` is a disjoint union of finite étale
`Y`-schemes) combined with the splitting of finite étale `Y`-schemes over `Ỹ_y`.

We also record the connectedness principle
(`AlgebraicGeometry.IsTwistedSection.apply_eq_of_preconnectedSpace`): over a connected `T`, a
locally constant function on `V ×_Y T` which is invariant under the equivalence relation
`V ×_Y T ×_T V ×_Y T` is constant, open subsets descending along pro-étale covers.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {Y V : Scheme.{u}} (f : V ⟶ Y)

/-- The triple fibre product `V ×_Y V ×_Y V`, as `(V ×_Y V) ×_V (V ×_Y V)`. -/
noncomputable abbrev tripleProduct : Scheme.{u} :=
  pullback (pullback.snd f f) (pullback.fst f f)

/-- The projection `p₁₃ : V ×_Y V ×_Y V ⟶ V ×_Y V` to the outer factors. -/
noncomputable abbrev tripleProj₁₃ : tripleProduct f ⟶ pullback f f :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst f f) (pullback.snd _ _ ≫ pullback.snd f f)
    (by simp only [Category.assoc, pullback.condition, pullback.condition_assoc])

/-- For a scheme `π : T ⟶ Y`, the map `(V ×_Y T) ×_T (V ×_Y T) ⟶ V ×_Y V`. -/
noncomputable abbrev twistedPairMap {T : Scheme.{u}} (π : T ⟶ Y) :
    pullback (pullback.snd f π) (pullback.snd f π) ⟶ pullback f f :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst f π) (pullback.snd _ _ ≫ pullback.fst f π)
    (by simp only [Category.assoc, pullback.condition, pullback.condition_assoc])

/-- A *descent cocycle* on the constant sheaf `S_V` along `f : V ⟶ Y`, on underlying points:
`z ↦ c z s` is locally constant for every `s`, every `c z` is bijective, `c` is the identity
on the diagonal, and `c (p₁₃ w) = c (p₁₂ w) ∘ c (p₂₃ w)` on `V ×_Y V ×_Y V`. -/
structure IsDescentCocycle {S : Type*} (c : ↥(pullback f f) → S → S) : Prop where
  isLocallyConstant (s : S) : IsLocallyConstant fun z ↦ c z s
  bijective (z : ↥(pullback f f)) : Function.Bijective (c z)
  diagonal (v : V) : c ((pullback.diagonal f).base v) = id
  cocycle (w : ↥(tripleProduct f)) :
    c ((tripleProj₁₃ f).base w) = c ((pullback.fst (pullback.snd f f) (pullback.fst f f)).base w) ∘
      c ((pullback.snd (pullback.snd f f) (pullback.fst f f)).base w)

/-- A *section over `π : T ⟶ Y`* of the sheaf of sets defined by a descent cocycle `c`: a
locally constant function `σ : V ×_Y T → S` such that `σ x = c z (σ x')` whenever `(x, x')` is
a point of `(V ×_Y T) ×_T (V ×_Y T)` lying over `z ∈ V ×_Y V`. -/
def IsTwistedSection {S : Type*} (c : ↥(pullback f f) → S → S) {T : Scheme.{u}} (π : T ⟶ Y)
    (σ : ↥(pullback f π) → S) : Prop :=
  IsLocallyConstant σ ∧ ∀ w : ↥(pullback (pullback.snd f π) (pullback.snd f π)),
    σ ((pullback.fst (pullback.snd f π) (pullback.snd f π)).base w) =
      c ((twistedPairMap f π).base w)
        (σ ((pullback.snd (pullback.snd f π) (pullback.snd f π)).base w))

variable {f}

/-- **The connectedness principle.** Let `f : V ⟶ Y` be weakly étale, surjective and
quasi-compact and `π : T ⟶ Y` with `T` preconnected. A locally constant function `τ` on
`V ×_Y T` which takes the same value at the two components of every point of
`(V ×_Y T) ×_T (V ×_Y T)` is constant: its level sets are the preimages of open subsets of `T`,
open subsets descending along the pro-étale cover `V ×_Y T ⟶ T`. -/
lemma IsTwistedSection.apply_eq_of_preconnectedSpace [WeaklyEtale f] [Surjective f]
    [QuasiCompact f] {T : Scheme.{u}} (π : T ⟶ Y) [PreconnectedSpace T] {A : Type*}
    (τ : ↥(pullback f π) → A) (hτ : IsLocallyConstant τ)
    (hinv : ∀ w : ↥(pullback (pullback.snd f π) (pullback.snd f π)),
      τ ((pullback.fst (pullback.snd f π) (pullback.snd f π)).base w) =
        τ ((pullback.snd (pullback.snd f π) (pullback.snd f π)).base w)) (x x' : ↥(pullback f π)) :
    τ x = τ x' := by
  classical
  set q := pullback.snd f π
  -- the level sets of `τ` are saturated
  have hsat (a : A) : q.base ⁻¹' (q.base '' (τ ⁻¹' {a})) = τ ⁻¹' {a} := by
    refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
    rintro x₁ ⟨x₂, hx₂, hq⟩
    obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := q) x₁ x₂
      hq.symm
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx₂ ⊢
    rw [← hw₁, hinv w, hw₂, hx₂]
  have hcov : Presieve.ofArrows (fun _ : Unit ↦ pullback f π) (fun _ ↦ q) ∈
      Scheme.proetalePrecoverage T := by
    rw [Presieve.ofArrows_pUnit]
    exact Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) inferInstance
  have hopen (a : A) : IsOpen (q.base '' (τ ⁻¹' {a})) :=
    Scheme.isOpen_of_isOpen_preimage_of_mem_proetalePrecoverage _ hcov _ fun _ ↦ by
      rw [hsat]
      exact hτ.isOpen_fiber a
  have hclopen : IsClopen (q.base '' (τ ⁻¹' {τ x})) := by
    refine ⟨?_, hopen _⟩
    have : (q.base '' (τ ⁻¹' {τ x}))ᶜ = ⋃ a ∈ ({τ x}ᶜ : Set A), q.base '' (τ ⁻¹' {a}) := by
      ext t
      obtain ⟨x₁, rfl⟩ := q.surjective t
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
      constructor
      · intro h
        refine ⟨τ x₁, fun h' ↦ h ⟨x₁, h', rfl⟩, x₁, rfl, rfl⟩
      · rintro ⟨a, ha, x₂, hx₂, hq⟩ ⟨x₃, hx₃, hq'⟩
        have h₂ : x₁ ∈ τ ⁻¹' {a} := by rw [← hsat]; exact ⟨x₂, hx₂, hq⟩
        have h₃ : x₁ ∈ τ ⁻¹' {τ x} := by rw [← hsat]; exact ⟨x₃, hx₃, hq'⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at h₂ h₃
        exact ha (h₂.symm.trans h₃)
    rw [← isOpen_compl_iff, this]
    exact isOpen_biUnion fun a _ ↦ hopen a
  have hx' : x' ∈ τ ⁻¹' {τ x} := by
    rw [← hsat, hclopen.eq_univ ⟨q.base x, x, rfl, rfl⟩]
    trivial
  exact hx'.symm

/-- **Pro-étale locally constant sheaves of sets are constant on the universal cover.** Let `Y`
be a connected regular Noetherian scheme, `Ỹ_y = U.cover y` its universal profinite étale cover
at a geometric point `y`, `f : V ⟶ Y` a single-morphism pro-étale cover and `c` a descent
cocycle on the constant sheaf `S_V`. Then the sheaf of sets defined by `c` has a section over
`Ỹ_y` through every point of `V ×_Y Ỹ_y` and every value in `S`.

Indeed `c` defines a sheaf of sets `F_c` on `Y_proét` which is pro-étale locally constant. Since
`Y` is normal, hence geometrically unibranch, `F_c` is a disjoint union of sheaves represented by
finite étale `Y`-schemes (Bhatt–Scholze, *The pro-étale topology for schemes*, Lemma 7.4.10,
with Lemma 7.3.9 for the dictionary between locally constant sheaves and geometric covers). Each
of them splits over `Ỹ_y` (`AlgebraicGeometry.Scheme.UniversalCovers.bijective_fiber`, `Ỹ_y`
being connected), so the pullback of `F_c` to `Ỹ_y` is constant, and the global sections of a
constant sheaf on the connected `Ỹ_y` take every value at every point. -/
theorem exists_isTwistedSection_universalCover {Ω : Type u} [Field Ω] [IsLocallyNoetherian Y]
    [CompactSpace Y] [IsRegular Y] [ConnectedSpace Y] (U : Scheme.UniversalCovers Y Ω)
    (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (f : V ⟶ Y) [WeaklyEtale f] [Surjective f]
    [QuasiCompact f] {S : Type*} {c : ↥(pullback f f) → S → S} (hc : IsDescentCocycle f c)
    (x : ↥(pullback f (U.proj y))) (s : S) :
    ∃ σ, IsTwistedSection f c (U.proj y) σ ∧ σ x = s := by
  sorry

end AlgebraicGeometry
