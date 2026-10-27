/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q135
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.SheafPullbackCone
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.Limits

/-!
# Sheaf pullbacks and scheme equality loci

Source: Stacks Project, Spaces, Tags 04T9 and 02X2; Sites, Tag 00VM
(blueprint: lem-trf-sheaf-pullback-diagonal).

The explicit type-valued pullback cones are combined into a presheaf. This retains
literal pairs of compatible sections and the componentwise restriction maps.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite ConcreteCategory

namespace AlgebraicGeometry.AlgebraicSpace

private def compatiblePairLimit {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u}
    (f : F ⟶ H) (g : G ⟶ H) : IsLimit (sheafPullbackCone f g) := by
  apply evaluationJointlyReflectsLimits
  intro T
  refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_
    (Types.pullbackLimitCone (f.app T) (g.app T)).isLimit
  · exact cospanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · refine Cone.ext (Iso.refl _) ?_
    rintro (_ | _ | _)
    all_goals rfl

private theorem diagonalIntersection {C : Type*} [Category* C]
    {P F G H T A B W : C} [HasBinaryProduct P P]
    [HasBinaryProduct F F] [HasBinaryProduct G G]
    {p : P ⟶ F} {q : P ⟶ G} {f : F ⟶ H} {g : G ⟶ H}
    (hP : IsPullback p q f g) (a₁ a₂ : T ⟶ P)
    {pA : A ⟶ T} {pB : B ⟶ T} {qA : A ⟶ F} {qB : B ⟶ G}
    (hA : IsPullback qA pA (prod.lift (𝟙 F) (𝟙 F))
      (prod.lift (a₁ ≫ p) (a₂ ≫ p)))
    (hB : IsPullback qB pB (prod.lift (𝟙 G) (𝟙 G))
      (prod.lift (a₁ ≫ q) (a₂ ≫ q)))
    {rA : W ⟶ A} {rB : W ⟶ B} (hW : IsPullback rA rB pA pB) :
    IsPullback ((rA ≫ pA) ≫ a₁) (rA ≫ pA)
      (prod.lift (𝟙 P) (𝟙 P)) (prod.lift a₁ a₂) := by
  have hA₁ : qA = pA ≫ a₁ ≫ p := by
    simpa using congrArg (fun k ↦ k ≫ prod.fst) hA.w
  have hA₂ : qA = pA ≫ a₂ ≫ p := by
    simpa using congrArg (fun k ↦ k ≫ prod.snd) hA.w
  have hB₁ : qB = pB ≫ a₁ ≫ q := by
    simpa using congrArg (fun k ↦ k ≫ prod.fst) hB.w
  have hB₂ : qB = pB ≫ a₂ ≫ q := by
    simpa using congrArg (fun k ↦ k ≫ prod.snd) hB.w
  have he : (rA ≫ pA) ≫ a₁ = (rA ≫ pA) ≫ a₂ := by
    apply hP.hom_ext
    · simp only [Category.assoc, ← hA₁, ← hA₂]
    · rw [hW.w]
      simp only [Category.assoc, ← hB₁, ← hB₂]
  have : Mono pA := hA.mono_snd_of_mono
  have : Mono pB := hB.mono_snd_of_mono
  have : Mono rA := hW.mono_fst_of_mono
  apply IsPullback.mk'
  · apply prod.hom_ext <;> simp [he]
  · intro Z m n _ hn
    exact (cancel_mono (rA ≫ pA)).mp hn
  · intro Z a b hab
    have ha : a = b ≫ a₁ := by
      simpa using congrArg (fun k ↦ k ≫ prod.fst) hab
    have hb : a = b ≫ a₂ := by
      simpa using congrArg (fun k ↦ k ≫ prod.snd) hab
    have hFa : (a ≫ p) ≫ prod.lift (𝟙 F) (𝟙 F) =
        b ≫ prod.lift (a₁ ≫ p) (a₂ ≫ p) := by
      apply prod.hom_ext
      · simpa using congrArg (fun k ↦ k ≫ p) ha
      · simpa using congrArg (fun k ↦ k ≫ p) hb
    have hGa : (a ≫ q) ≫ prod.lift (𝟙 G) (𝟙 G) =
        b ≫ prod.lift (a₁ ≫ q) (a₂ ≫ q) := by
      apply prod.hom_ext
      · simpa using congrArg (fun k ↦ k ≫ q) ha
      · simpa using congrArg (fun k ↦ k ≫ q) hb
    let lA := hA.lift (a ≫ p) b hFa
    let lB := hB.lift (a ≫ q) b hGa
    have hl : lA ≫ pA = lB ≫ pB := by simp [lA, lB]
    refine ⟨hW.lift lA lB hl, ?_, ?_⟩
    · simp [Category.assoc, ← ha, lA]
    · simp [lA]

/-- The pointwise fibre product of fppf sheaves is a sheaf, its diagonal is
representable, its equality loci are the fibre products of the two scheme equality
loci over the test scheme, and its Hom bijection has the componentwise inverse.
The maps `a₁,a₂` are the two sections over `T`, in Yoneda form.
Source: Stacks, Spaces, Tag 04T9, first two conditions of the proof; Tag 02X2,
universal property; Sites, Tag 00VM (blueprint: lem-trf-sheaf-pullback-diagonal).

Proof: (1) Restrict compatible pairs componentwise; naturality preserves their equality.
Glue a matching family in `F` and `G`. The two images in `H` agree on the cover and
hence agree by uniqueness of gluing in `H`, including for the empty covering. This
proves the sheaf condition [def-weil-pbc-sites-and-cohomology].
(2) Projection gives a compatible pair of maps out of every sheaf `Q`. Conversely
send `q` to `(a(q),b(q))`; naturality is componentwise, and the constructions are
inverse since equality of subtype pairs is componentwise.
(3) A map into `A` over a map `U → T` is exactly equality of the restricted first
components, by its given representing square [def-trf-algebraic-space]. Similarly
`B` records equality of the second components. The scheme pullback universal
property [def-pc-fibre-product] identifies maps into `A ×_T B` with these two
equalities over the same map to `T`.
(4) These are exactly equality of the two restricted compatible pairs. Send such a
map to the first restricted pair; conversely the two representing squares give
the unique maps to `A,B`, hence their pullback lift. Both operations commute with
restriction and preserve the map to `T`, giving the displayed representing square.
Every map from `h_T` to the product comes from two sections by Yoneda, so this
also proves representability of the diagonal. -/
theorem sheafPullback_diagonal {S : Scheme.{u}}
    (F G H : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (f : F.obj ⟶ H.obj) (g : G.obj ⟶ H.obj)
    (hF : IsRepresentable (prod.lift (𝟙 F.obj) (𝟙 F.obj)))
    (hG : IsRepresentable (prod.lift (𝟙 G.obj) (𝟙 G.obj))) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (sheafPullbackCone f g).pt ∧
    IsRepresentable
      (prod.lift (𝟙 (sheafPullbackCone f g).pt) (𝟙 (sheafPullbackCone f g).pt)) ∧
    (∀ (T : Over S) (a₁ a₂ : yoneda.obj T ⟶ (sheafPullbackCone f g).pt)
      (A B : Over S) (pA : A ⟶ T) (pB : B ⟶ T)
      (qA : yoneda.obj A ⟶ F.obj) (qB : yoneda.obj B ⟶ G.obj),
      IsPullback qA (yoneda.map pA) (prod.lift (𝟙 F.obj) (𝟙 F.obj))
        (prod.lift (a₁ ≫ (sheafPullbackCone f g).fst)
          (a₂ ≫ (sheafPullbackCone f g).fst)) →
      IsPullback qB (yoneda.map pB) (prod.lift (𝟙 G.obj) (𝟙 G.obj))
        (prod.lift (a₁ ≫ (sheafPullbackCone f g).snd)
          (a₂ ≫ (sheafPullbackCone f g).snd)) →
      ∃ q : yoneda.obj (Limits.pullback pA pB) ⟶ (sheafPullbackCone f g).pt,
        IsPullback q (yoneda.map (Limits.pullback.fst pA pB ≫ pA))
          (prod.lift (𝟙 (sheafPullbackCone f g).pt) (𝟙 (sheafPullbackCone f g).pt))
          (prod.lift a₁ a₂)) ∧
    ∀ Q : Sheaf (Scheme.fppfTopology.over S) (Type u),
      ∃ e : (Q.obj ⟶ (sheafPullbackCone f g).pt) ≃
          {ab : (Q.obj ⟶ F.obj) × (Q.obj ⟶ G.obj) // ab.1 ≫ f = ab.2 ≫ g},
        (∀ c : Q.obj ⟶ (sheafPullbackCone f g).pt,
          (e c).val = (c ≫ (sheafPullbackCone f g).fst,
            c ≫ (sheafPullbackCone f g).snd)) ∧
        ∀ (ab : {ab : (Q.obj ⟶ F.obj) × (Q.obj ⟶ G.obj) // ab.1 ≫ f = ab.2 ≫ g})
          (T : (Over S)ᵒᵖ) (q : Q.obj.obj T),
          ((e.symm ab).app T q).val = (ab.val.1.app T q, ab.val.2.app T q) := by
  classical
  let c := sheafPullbackCone f g
  have hc : IsLimit c := compatiblePairLimit f g
  have hp : IsPullback c.fst c.snd f g := IsPullback.of_isLimit hc
  have loci (T : Over S) (a₁ a₂ : yoneda.obj T ⟶ c.pt)
      (A B : Over S) (pA : A ⟶ T) (pB : B ⟶ T)
      (qA : yoneda.obj A ⟶ F.obj) (qB : yoneda.obj B ⟶ G.obj)
      (hA : IsPullback qA (yoneda.map pA) (prod.lift (𝟙 F.obj) (𝟙 F.obj))
        (prod.lift (a₁ ≫ c.fst) (a₂ ≫ c.fst)))
      (hB : IsPullback qB (yoneda.map pB) (prod.lift (𝟙 G.obj) (𝟙 G.obj))
        (prod.lift (a₁ ≫ c.snd) (a₂ ≫ c.snd))) :
      ∃ q : yoneda.obj (Limits.pullback pA pB) ⟶ c.pt,
        IsPullback q (yoneda.map (Limits.pullback.fst pA pB ≫ pA))
          (prod.lift (𝟙 c.pt) (𝟙 c.pt)) (prod.lift a₁ a₂) := by
    refine ⟨yoneda.map (Limits.pullback.fst pA pB ≫ pA) ≫ a₁, ?_⟩
    simpa only [Functor.map_comp] using
      diagonalIntersection hp a₁ a₂ hA hB ((IsPullback.of_hasPullback pA pB).map yoneda)
  refine ⟨?_, ?_, loci, ?_⟩
  · apply ObjectProperty.prop_of_isLimit
      (P := fun X ↦ Presheaf.IsSheaf (Scheme.fppfTopology.over S) X) hc
    intro j
    cases j with
    | none => exact H.property
    | some j =>
      cases j with
      | left => exact F.property
      | right => exact G.property
  · intro T a
    let a₁ := a ≫ prod.fst
    let a₂ := a ≫ prod.snd
    obtain ⟨A, pA, qA, hA, _⟩ := hF T (prod.lift (a₁ ≫ c.fst) (a₂ ≫ c.fst))
    obtain ⟨B, pB, qB, hB, _⟩ := hG T (prod.lift (a₁ ≫ c.snd) (a₂ ≫ c.snd))
    obtain ⟨q, hq⟩ := loci T a₁ a₂ A B pA pB qA qB hA hB
    refine ⟨Limits.pullback pA pB, Limits.pullback.fst pA pB ≫ pA, q, ?_, trivial⟩
    have ha : prod.lift a₁ a₂ = a := by
      apply prod.hom_ext
      · simp only [prod.lift_fst]
        rfl
      · simp only [prod.lift_snd]
        rfl
    rw [ha] at hq
    exact hq
  · intro Q
    let e : (Q.obj ⟶ c.pt) ≃
        {ab : (Q.obj ⟶ F.obj) × (Q.obj ⟶ G.obj) // ab.1 ≫ f = ab.2 ≫ g} :=
      { toFun := fun k ↦ ⟨(k ≫ c.fst, k ≫ c.snd), by
          simp only [Category.assoc, c.condition]⟩
        invFun := fun ab ↦ hp.lift ab.val.1 ab.val.2 ab.property
        left_inv := fun k ↦ hp.hom_ext (by simp) (by simp)
        right_inv := fun ab ↦ Subtype.ext (Prod.ext (by simp) (by simp)) }
    refine ⟨e, fun _ ↦ rfl, ?_⟩
    intro ab T q
    apply Prod.ext
    · exact congr_hom (congr_app (hp.lift_fst ab.val.1 ab.val.2 ab.property) T) q
    · exact congr_hom (congr_app (hp.lift_snd ab.val.1 ab.val.2 ab.property) T) q

end AlgebraicGeometry.AlgebraicSpace
