/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.LocallyConstant.Basic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCover
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.GaloisCategory
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

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

On a connected regular Noetherian scheme every pro-étale locally constant sheaf of sets becomes
constant on the universal profinite étale cover `Ỹ_y`, i.e. it has a section over `Ỹ_y` through
every point (`AlgebraicGeometry.exists_isTwistedSection_universalCover`). The input from the
theory of the pro-étale fundamental group is Bhatt–Scholze, *The pro-étale topology for
schemes*, Lemma 7.4.10: on a geometrically unibranch scheme every locally constant sheaf of sets
on `Y_proét` is a disjoint union of finite étale `Y`-schemes
(`AlgebraicGeometry.exists_isTwistedSection_finiteEtale`, the only unproved input). It is
combined with the splitting of finite étale `Y`-schemes over `Ỹ_y` at all geometric points
(`AlgebraicGeometry.Scheme.UniversalCovers.exists_comp_eq_of_finiteEtale`), deduced from
`AlgebraicGeometry.Scheme.UniversalCovers.bijective_fiber` in the Galois category of finite
étale `Ỹ_y`-schemes.

We also record the connectedness principle
(`AlgebraicGeometry.IsTwistedSection.apply_eq_of_preconnectedSpace`): over a connected `T`, a
locally constant function on `V ×_Y T` which is invariant under the equivalence relation
`V ×_Y T ×_T V ×_Y T` is constant, open subsets descending along pro-étale covers.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme.FiniteEtale

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

/-- **Pullback of twisted sections.** A section of the sheaf of sets defined by `c` over
`π : T ⟶ Y` pulls back along a morphism `t : T' ⟶ T` over `Y` to a section over `T'`. -/
lemma IsTwistedSection.comp {S : Type*} {c : ↥(pullback f f) → S → S} {T T' : Scheme.{u}}
    {π : T ⟶ Y} {π' : T' ⟶ Y} (t : T' ⟶ T) (ht : t ≫ π = π') {σ : ↥(pullback f π) → S}
    (hσ : IsTwistedSection f c π σ) :
    IsTwistedSection f c π' (σ ∘ (pullback.map f π' f π (𝟙 V) t (𝟙 Y) (by simp)
      (by simp [ht])).base) := by
  set m := pullback.map f π' f π (𝟙 V) t (𝟙 Y) (by simp) (by simp [ht])
  have hm : m ≫ pullback.snd f π = pullback.snd f π' ≫ t := pullback.lift_snd _ _ _
  set M := pullback.map (pullback.snd f π') (pullback.snd f π') (pullback.snd f π)
    (pullback.snd f π) m m t hm.symm hm.symm
  have hM₁ : M ≫ pullback.fst _ _ = pullback.fst _ _ ≫ m := pullback.lift_fst _ _ _
  have hM₂ : M ≫ pullback.snd _ _ = pullback.snd _ _ ≫ m := pullback.lift_snd _ _ _
  have hMp : M ≫ twistedPairMap f π = twistedPairMap f π' := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      rw [reassoc_of% hM₁]
      simp [m]
    · simp only [Category.assoc, pullback.lift_snd]
      rw [reassoc_of% hM₂]
      simp [m]
  refine ⟨hσ.1.comp_continuous m.base.hom.continuous, fun w ↦ ?_⟩
  have h := hσ.2 (M.base w)
  simp only [Function.comp_apply]
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← hM₁, ← hM₂, ← hMp]
  exact h

/-- **Locally constant sheaves of sets on a geometrically unibranch scheme are unions of finite
étale ones** (Bhatt–Scholze, *The pro-étale topology for schemes*, Lemma 7.4.10, with Lemma
7.3.9), in cocycle form. Let `Y` be a connected regular (hence normal, hence geometrically
unibranch) Noetherian scheme, `f : V ⟶ Y` a single-morphism pro-étale cover and `c` a descent
cocycle on the constant sheaf `S_V`, defining a pro-étale locally constant sheaf of sets `F_c` on
`Y`. Then `F_c` is a disjoint union of sheaves represented by finite étale `Y`-schemes: through
every point `s` of the stalk of `F_c` at a geometric point `v̄ ≫ f` (identified with `S` through
`v̄ : Spec K ⟶ V`) passes a section of `F_c` over a finite étale `p : P ⟶ Y`, at a geometric
point `p̄` of `P` over `v̄ ≫ f`. Namely, `P` represents the summand of `F_c` containing `s`, and
the section is its tautological one. -/
theorem exists_isTwistedSection_finiteEtale [IsLocallyNoetherian Y] [CompactSpace Y]
    [IsRegular Y] [ConnectedSpace Y] (f : V ⟶ Y) [WeaklyEtale f] [Surjective f]
    [QuasiCompact f] {S : Type*} {c : ↥(pullback f f) → S → S} (hc : IsDescentCocycle f c)
    {K : Type u} [Field K] [IsAlgClosed K] (v : Spec (.of K) ⟶ V) (s : S) :
    ∃ (P : Scheme.{u}) (p : P ⟶ Y) (_ : IsFinite p) (_ : Etale p) (σ : ↥(pullback f p) → S)
      (p' : Spec (.of K) ⟶ P) (h : v ≫ f = p' ≫ p),
      IsTwistedSection f c p σ ∧
        σ ((pullback.lift v p' h).base (IsLocalRing.closedPoint K)) = s := by
  sorry

/-- The points of the fibre of a finite coproduct of finite étale schemes come from the
summands. -/
lemma Scheme.FiniteEtale.exists_fiber_map_sigmaι {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) {N : ℕ} (Z : Fin N → X.FiniteEtale)
    (d : (fiber s).obj (∐ Z)) :
    ∃ i, ∃ x : (fiber s).obj (Z i), (fiber s).map (Sigma.ι Z i) x = d := by
  obtain ⟨⟨i⟩, x, hx⟩ := Types.jointly_surjective _
    (isColimitOfPreserves (fiber s ⋙ FintypeCat.incl) (colimit.isColimit (Discrete.functor Z))) d
  exact ⟨i, x, hx⟩

/-- **Finite étale schemes split over the universal cover at every geometric point.** For a
finite étale `p : P ⟶ Y`, every geometric point of `P` over a geometric point `t` of the
universal cover `Ỹ_y` is the image of `t` under a `Y`-morphism `Ỹ_y ⟶ P`. Indeed the
`Y`-morphisms `a : Ỹ_y ⟶ P` give sections of the finite étale `P ×_Y Ỹ_y ⟶ Ỹ_y`, hence a
morphism `∐_a Ỹ_y ⟶ P ×_Y Ỹ_y` of finite étale `Ỹ_y`-schemes. It is bijective on the geometric
fibres at the base point (`AlgebraicGeometry.Scheme.UniversalCovers.bijective_fiber`), hence an
isomorphism, `Ỹ_y` being connected
(`AlgebraicGeometry.Scheme.FiniteEtale.isIso_of_isIso_fiber_map`), hence bijective on the geometric
fibres at `t`. -/
theorem Scheme.UniversalCovers.exists_comp_eq_of_finiteEtale {Ω : Type u} [Field Ω]
    (U : Scheme.UniversalCovers Y Ω) (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)
    {P : Scheme.{u}} (p : P ⟶ Y) [IsFinite p] [Etale p] {K : Type u} [Field K] [IsAlgClosed K]
    (t : Spec (.of K) ⟶ U.cover y) (p' : Spec (.of K) ⟶ P) (h : t ≫ U.proj y = p' ≫ p) :
    ∃ a : U.cover y ⟶ P, a ≫ p = U.proj y ∧ t ≫ a = p' := by
  have := U.connectedSpace y
  set π := U.proj y
  let PF : Y.FiniteEtale := ⟨Scheme.Etale.mk p, inferInstanceAs (IsFinite p)⟩
  let Q : (U.cover y).FiniteEtale :=
    ⟨Scheme.Etale.mk (pullback.snd p π), inferInstanceAs (IsFinite (pullback.snd p π))⟩
  let top : (U.cover y).FiniteEtale :=
    ⟨Scheme.Etale.mk (𝟙 (U.cover y)), inferInstanceAs (IsFinite (𝟙 (U.cover y)))⟩
  let A := {g : U.cover y ⟶ P // g ≫ p = π}
  have hbij := U.bijective_fiber y PF
  have : Finite A := Finite.of_injective _ hbij.1
  let e := Finite.equivFin A
  let N := Nat.card A
  -- the sections of `Q` given by the `Y`-morphisms `Ỹ_y ⟶ P`
  let σ (a : A) : top ⟶ Q := ObjectProperty.homMk (MorphismProperty.Over.homMk
    (pullback.lift a.1 (𝟙 _) (by simp [a.2])) (by simp [Q, top]; rfl) trivial)
  let φ : ∐ (fun _ : Fin N ↦ top) ⟶ Q := Sigma.desc fun i ↦ σ (e.symm i)
  have hσleft (a : A) : (σ a).hom.left = pullback.lift a.1 (𝟙 _) (by simp [a.2]) := rfl
  -- the unique point of the fibre of `top`
  let star {L : Type u} [Field L] [IsSepClosed L] (s : Spec (.of L) ⟶ U.cover y) :
      (fiber s).obj top := fiberMk s top s (Category.comp_id s)
  have hstar {L : Type u} [Field L] [IsSepClosed L] (s : Spec (.of L) ⟶ U.cover y)
      (x : (fiber s).obj top) : x = star s :=
    fiber_ext s ((Category.comp_id _).symm.trans (fiber_left_comp s x))
  have hφσ {L : Type u} [Field L] [IsSepClosed L] (s : Spec (.of L) ⟶ U.cover y) (i : Fin N) :
      ((fiber s).map φ ((fiber s).map (Sigma.ι _ i) (star s))).left =
        pullback.lift (s ≫ (e.symm i).1) s (by simp [(e.symm i).2, π]) := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Sigma.ι_desc, fiber_map_left]
    apply pullback.hom_ext
    · simp [hσleft, star]
    · simp only [Category.assoc, pullback.lift_snd, fiberMk_left, star, hσleft]
      exact Category.comp_id _
  -- the comparison map is an isomorphism, as it is bijective on the fibre at the base point
  have hiso : IsIso φ := by
    have hs : U.pt y ≫ π = y := U.pt_proj y
    have : IsIso ((fiber (U.pt y)).map φ) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      refine ⟨fun d₁ d₂ hd ↦ ?_, fun q ↦ ?_⟩
      · obtain ⟨i, x, rfl⟩ := exists_fiber_map_sigmaι (U.pt y) _ d₁
        obtain ⟨j, x', rfl⟩ := exists_fiber_map_sigmaι (U.pt y) _ d₂
        rw [hstar _ x, hstar _ x'] at hd ⊢
        have h₁ := congrArg (fun z ↦ z.left ≫ pullback.fst p π) hd
        simp only [hφσ, pullback.lift_fst] at h₁
        have hij : e.symm i = e.symm j := hbij.1 (fiber_ext y h₁)
        rw [e.symm.injective hij]
      · have hq : q.left ≫ pullback.snd p π = U.pt y := fiber_left_comp (U.pt y) q
        let x := fiberMk y PF (q.left ≫ pullback.fst p π) (by
          rw [Category.assoc, show pullback.fst p π ≫ PF.obj.hom = pullback.snd p π ≫ π from
            pullback.condition, ← Category.assoc, hq]
          exact hs)
        obtain ⟨a, ha⟩ := hbij.2 x
        refine ⟨(fiber (U.pt y)).map (Sigma.ι _ (e a)) (star _), fiber_ext _ ?_⟩
        rw [hφσ]
        apply pullback.hom_ext
        · simpa [x] using congrArg (fun z ↦ z.left) ha
        · simpa using hq.symm
    exact isIso_of_isIso_fiber_map (U.pt y) φ
  -- hence also bijective on the fibre at `t`
  have hbt : Function.Bijective ((fiber t).map φ) := ConcreteCategory.bijective_of_isIso _
  obtain ⟨d, hd⟩ := hbt.2 (fiberMk t Q (pullback.lift p' t h.symm) (pullback.lift_snd _ _ _))
  obtain ⟨i, x, rfl⟩ := exists_fiber_map_sigmaι t _ d
  rw [hstar _ x] at hd
  have h₁ := congrArg (fun z ↦ z.left ≫ pullback.fst p π) hd
  simp only [hφσ, pullback.lift_fst, fiberMk_left] at h₁
  exact ⟨(e.symm i).1, (e.symm i).2, h₁⟩


/-- **Pro-étale locally constant sheaves of sets are constant on the universal cover.** Let `Y`
be a connected regular Noetherian scheme, `Ỹ_y = U.cover y` its universal profinite étale cover
at a geometric point `y`, `f : V ⟶ Y` a single-morphism pro-étale cover and `c` a descent
cocycle on the constant sheaf `S_V`. Then the sheaf of sets defined by `c` has a section over
`Ỹ_y` through every point of `V ×_Y Ỹ_y` and every value in `S`: the sheaf is a union of finite
étale ones (`AlgebraicGeometry.exists_isTwistedSection_finiteEtale`), which split over `Ỹ_y`
(`AlgebraicGeometry.Scheme.UniversalCovers.exists_comp_eq_of_finiteEtale`). -/
theorem exists_isTwistedSection_universalCover {Ω : Type u} [Field Ω] [IsLocallyNoetherian Y]
    [CompactSpace Y] [IsRegular Y] [ConnectedSpace Y] (U : Scheme.UniversalCovers Y Ω)
    (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (f : V ⟶ Y) [WeaklyEtale f] [Surjective f]
    [QuasiCompact f] {S : Type*} {c : ↥(pullback f f) → S → S} (hc : IsDescentCocycle f c)
    (x : ↥(pullback f (U.proj y))) (s : S) :
    ∃ σ, IsTwistedSection f c (U.proj y) σ ∧ σ x = s := by
  -- a geometric point over `x`
  set x' := (pullback f (U.proj y)).fromSpecAlgebraicClosureResidueField x
  have hx' : x'.base (IsLocalRing.closedPoint _) = x := by
    simp only [x', Scheme.fromSpecAlgebraicClosureResidueField, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply (X := pullback f (U.proj y)) x _
  obtain ⟨P, p, _, _, σ, p', h, hσ, hσs⟩ :=
    exists_isTwistedSection_finiteEtale f hc (x' ≫ pullback.fst _ _) s
  obtain ⟨a, ha, hap⟩ := U.exists_comp_eq_of_finiteEtale y p (x' ≫ pullback.snd _ _) p' (by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, h])
  have hm : x' ≫ pullback.map f (U.proj y) f p (𝟙 V) a (𝟙 Y) (by simp) (by simp [ha]) =
      pullback.lift (x' ≫ pullback.fst _ _) p' h :=
    pullback.hom_ext (by simp) (by simpa using hap)
  refine ⟨_, hσ.comp a ha, ?_⟩
  simp only [Function.comp_apply]
  rw [← hx', ← Scheme.Hom.comp_apply, hm]
  exact hσs

end AlgebraicGeometry
