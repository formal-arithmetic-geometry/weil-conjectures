/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField

/-!
# Rigidity

The rigidity lemma says that a morphism `g : X ×_K Y ⟶ Z` of `K`-schemes, with `X` proper,
geometrically connected and geometrically reduced over `K`, `Y` connected and `Z` separated over
`K`, which contracts a single fibre `X ×_K {y₀}` to a point, necessarily factors through the
second projection. This file also records two propositions on the fibres of the morphism
`(g, pr₂) : X ×_K Y ⟶ Z ×_K Y` over `Y`: the locus of `y` whose geometric fibre is contracted to
a point is closed, and the locus of `y` whose fibre has finite image is open. The second one is
independent of the rigidity lemma.

All three statements are set in the commutative square

```
  pullback fX fY ───── pullback.snd ─────▶ Y
        │        ╲                         │
        │         ╲  g                     │ fY
 pullback.fst      ╲                       │
        │           ╲                      │
        ▼            ▼                     ▼
        X ─── fX ──▶ Spec K ◀─── fZ ────── Z
```

in which `hg : g ≫ fZ = pullback.fst fX fY ≫ fX` says that `g` is a morphism of `K`-schemes.
The fibres of `(g, pr₂) = pullback.lift g (pullback.snd fX fY) _` over `Y` are spelled with
`AlgebraicGeometry.Scheme.Hom.fiberMap`.

The blueprint uses the rigidity lemma to prove that abelian varieties are commutative. That
corollary is proved instead in `WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic` from
Mathlib's `AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`, so the results
below are recorded for their own sake and have no consumer in this repository yet.

## Main statements

- `AlgebraicGeometry.isClosed_setOf_subsingleton_range_fiberMap`: for a morphism `F : A ⟶ B` over
  `Y` with `A` universally open and locally of finite type and `B` separated over `Y`, the locus
  of `y : Y` whose geometric fibre `F_ȳ` has subsingleton image is closed in `Y`.
- `AlgebraicGeometry.isClosed_setOf_subsingleton_image`: the locus of `y : Y` whose geometric
  fibre is contracted to a single point is closed in `Y`.
- `AlgebraicGeometry.eventually_finite_image`: if the fibre over `y₀` has finite image, then so
  does the fibre over every `y` near `y₀`.
- `AlgebraicGeometry.exists_eq_snd_comp`: the rigidity lemma, `g` factors through the second
  projection.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- The general form of blueprint `lem-sc-constant-locus-closed`. Let `F : A ⟶ B` be a morphism
of schemes over `Y`, with `a : A ⟶ Y` universally open and locally of finite type and with
`b : B ⟶ Y` separated. Then the locus of `y : Y` such that the base change
`F_ȳ : A_{κ(y)‾} ⟶ B_{κ(y)‾}` of `F` along the geometric point `ȳ` over `y` has subsingleton
image is closed.

Following the blueprint, write `Φ : A ×_Y A ⟶ B ×_Y B` for the product of `F` with itself and
`π : A ×_Y A ⟶ Y` for the projection. The locus is the complement of the image under `π` of the
open set `U` of points that `Φ` sends off the diagonal of `b`, and `π` is an open map. To see
that `y` lies outside `π(U)` exactly when the image of `F_ȳ` is a subsingleton, base change
along `ȳ`: the diagonal of `B_{κ(y)‾}` is the preimage of the diagonal of `b`
(`Scheme.Pullback.map_fst_mem_range_diagonal_iff`), and if the image of `F_ȳ` is a single point
then that point is a `κ(y)‾`-point, since `A_{κ(y)‾}` has a closed, hence rational, point. -/
theorem isClosed_setOf_subsingleton_range_fiberMap {A B Y : Scheme.{u}} (a : A ⟶ Y)
    (b : B ⟶ Y) [UniversallyOpen a] [LocallyOfFiniteType a] [IsSeparated b] (F : A ⟶ B)
    (hF : F ≫ b = a) :
    IsClosed {y : Y | (Set.range (Scheme.Hom.fiberMap F hF
      (Y.fromSpecAlgebraicClosureResidueField y)).base).Subsingleton} := by
  let Φ := pullback.map a a b b F F (𝟙 Y) (by simp [hF]) (by simp [hF])
  let π := pullback.fst a a ≫ a
  let U : Set ↑(pullback a a) := Φ ⁻¹' (Set.range (pullback.diagonal b))ᶜ
  have hU : IsOpen U :=
    (pullback.diagonal b).isClosedEmbedding.isClosed_range.isOpen_compl.preimage Φ.continuous
  suffices key : ∀ y, (Set.range
      (Scheme.Hom.fiberMap F hF (Y.fromSpecAlgebraicClosureResidueField y)).base).Subsingleton ↔
      y ∉ π '' U by
    convert (π.isOpenMap U hU).isClosed_compl using 1
    ext y
    exact key y
  intro y
  set p := Y.fromSpecAlgebraicClosureResidueField y
  have hp (q) : p q = y := by
    simp only [p, Scheme.fromSpecAlgebraicClosureResidueField, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  let FΩ := Scheme.Hom.fiberMap F hF p
  have hFΩ : FΩ ≫ pullback.snd b p = pullback.snd a p := by simp [FΩ, Scheme.Hom.fiberMap]
  let hA := pullback.map _ _ a a (pullback.fst a p) (pullback.fst a p) p
    pullback.condition.symm pullback.condition.symm
  let hB := pullback.map _ _ b b (pullback.fst b p) (pullback.fst b p) p
    pullback.condition.symm pullback.condition.symm
  let ΦΩ := pullback.map (pullback.snd a p) (pullback.snd a p) (pullback.snd b p)
    (pullback.snd b p) FΩ FΩ (𝟙 _) (by simp [hFΩ]) (by simp [hFΩ])
  have hcomm : hA ≫ Φ = ΦΩ ≫ hB := by
    ext <;> simp [hA, hB, Φ, ΦΩ, FΩ, Scheme.Hom.fiberMap]
  have hΦΩ₁ (v) : pullback.fst (pullback.snd b p) (pullback.snd b p) (ΦΩ v) =
      FΩ (pullback.fst (pullback.snd a p) (pullback.snd a p) v) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
    simp [ΦΩ]
  have hΦΩ₂ (v) : pullback.snd (pullback.snd b p) (pullback.snd b p) (ΦΩ v) =
      FΩ (pullback.snd (pullback.snd a p) (pullback.snd a p) v) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
    simp [ΦΩ]
  constructor
  · rintro hsub ⟨w, hw, hπw⟩
    apply hw
    obtain ⟨c, rfl⟩ : w ∈ Set.range (pullback.fst π p) := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨IsLocalRing.closedPoint _, by rw [hp, hπw]⟩
    let ψ : pullback π p ⟶ pullback (pullback.snd a p) (pullback.snd a p) :=
      pullback.lift (pullback.lift (pullback.fst π p ≫ pullback.fst a a) (pullback.snd π p)
          (by rw [Category.assoc]; exact pullback.condition))
        (pullback.lift (pullback.fst π p ≫ pullback.snd a a) (pullback.snd π p)
          (by rw [Category.assoc, ← pullback.condition]; exact pullback.condition))
        (by simp)
    have hψ : ψ ≫ hA = pullback.fst π p := by ext <;> simp [ψ, hA]
    rw [← hψ, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply,
      Scheme.Pullback.map_fst_mem_range_diagonal_iff]
    have : JacobsonSpace ↑(pullback a p) := LocallyOfFiniteType.jacobsonSpace (pullback.snd a p)
    obtain ⟨e, -, he⟩ := nonempty_inter_closedPoints
      ⟨pullback.fst (pullback.snd a p) (pullback.snd a p) (ψ c), Set.mem_univ _⟩
      isClosed_univ.isLocallyClosed
    let σ := pointOfClosedPoint (pullback.snd a p) e he
    have hσ : (σ ≫ FΩ) (IsLocalRing.closedPoint _) = FΩ e := by simp [σ]
    exact Scheme.Pullback.mem_range_diagonal_of_mem_range (σ ≫ FΩ) (by simp [σ, hFΩ]) _
      ⟨_, hσ.trans ((hsub ⟨_, rfl⟩ ⟨_, rfl⟩).trans (hΦΩ₁ _).symm)⟩
      ⟨_, hσ.trans ((hsub ⟨_, rfl⟩ ⟨_, rfl⟩).trans (hΦΩ₂ _).symm)⟩
  · intro hy
    rintro _ ⟨x₁, rfl⟩ _ ⟨x₂, rfl⟩
    by_contra hne
    obtain ⟨v, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd a p)
      (g := pullback.snd a p) x₁ x₂ (Subsingleton.elim _ _)
    refine hy ⟨hA v, fun h ↦ hne ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply,
        Scheme.Pullback.map_fst_mem_range_diagonal_iff] at h
      obtain ⟨β, hβ⟩ := h
      rw [← hΦΩ₁, ← hΦΩ₂, ← hβ, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
        pullback.diagonal_fst, pullback.diagonal_snd]
    · have : hA ≫ π = (pullback.fst _ _ ≫ pullback.snd a p) ≫ p := by
        simp [hA, π, pullback.condition]
      rw [← Scheme.Hom.comp_apply, this, Scheme.Hom.comp_apply, hp]

/-- Blueprint `sk-prop-av-const-locus`: The locus of constant fibres is closed

Let `X` be a `K`-scheme proper over `K`, let `Z` be separated over `K`, let `Y` be any
`K`-scheme and let `g : X ×_K Y ⟶ Z` be a morphism of `K`-schemes. For `y : Y` let
`g_ȳ : X_{κ(y)‾} ⟶ Z_{κ(y)‾}` be the base change of `(g, pr₂) : X ×_K Y ⟶ Z ×_K Y` along the
geometric point `ȳ` over `y`. Then the locus `L = {y ∈ Y | g_ȳ(X_{κ(y)‾}) is a subsingleton}` is
closed in `Y`. For nonempty `X` the image of `g_ȳ` is a subsingleton exactly when it is a single
point.

Constancy must be tested on the geometric fibre, not on the set-theoretic image of
`X ×_K {y}` in `Z`: for `K` algebraically closed of characteristic `≠ 2`,
`X = Spec K ⊔ Spec K`, `Y = Z = 𝔸¹_K` and `g = (t ↦ t, t ↦ -t)`, that image is one point
exactly for `y` the generic point or `y = 0`, which is not a closed set. -/
theorem isClosed_setOf_subsingleton_image {X Y Z : Scheme.{u}}
    (fX : X ⟶ Spec (.of K)) (fY : Y ⟶ Spec (.of K)) (fZ : Z ⟶ Spec (.of K)) [IsProper fX]
    [IsSeparated fZ] (g : pullback fX fY ⟶ Z) (hg : g ≫ fZ = pullback.fst fX fY ≫ fX) :
    IsClosed {y : Y | (Set.range (Scheme.Hom.fiberMap
      (pullback.lift (f := fZ) (g := fY) g (pullback.snd fX fY)
        (by rw [hg, pullback.condition]))
      (pullback.lift_snd _ _ _) (Y.fromSpecAlgebraicClosureResidueField y)).base).Subsingleton} :=
  isClosed_setOf_subsingleton_range_fiberMap _ _ _ _

/-- Blueprint `sk-prop-av-image-open`: Finiteness of the image is open in the parameter

Let `X` be proper over `K`, let `Z` be separated and locally of finite type over `K`, let
`g : X ×_K Y ⟶ Z` be a morphism of `K`-schemes and let `y₀ ∈ Y`. For `y : Y` let
`g_y : X_{κ(y)} ⟶ Z_{κ(y)}` be the fibre of `(g, pr₂) : X ×_K Y ⟶ Z ×_K Y` over `y`. If the
image of `g_{y₀}` is finite, then the image of `g_y` is finite for every `y` in some open
neighbourhood of `y₀`.

The rigidity lemma `AlgebraicGeometry.exists_eq_snd_comp` does not depend on this result. -/
theorem eventually_finite_image {X Y Z : Scheme.{u}} (fX : X ⟶ Spec (.of K))
    (fY : Y ⟶ Spec (.of K)) (fZ : Z ⟶ Spec (.of K)) [IsProper fX] [IsSeparated fZ]
    [LocallyOfFiniteType fZ] (g : pullback fX fY ⟶ Z)
    (hg : g ≫ fZ = pullback.fst fX fY ≫ fX) (y₀ : Y)
    (hy₀ : (Set.range (Scheme.Hom.fiberMap
      (pullback.lift (f := fZ) (g := fY) g (pullback.snd fX fY)
        (by rw [hg, pullback.condition]))
      (pullback.lift_snd _ _ _) (Y.fromSpecResidueField y₀)).base).Finite) :
    ∀ᶠ y in 𝓝 y₀, (Set.range (Scheme.Hom.fiberMap
      (pullback.lift (f := fZ) (g := fY) g (pullback.snd fX fY)
        (by rw [hg, pullback.condition]))
      (pullback.lift_snd _ _ _) (Y.fromSpecResidueField y)).base).Finite :=
  sorry

/-- Blueprint `sk-prop-av-rigidity`: The rigidity lemma

Let `X`, `Y`, `Z` be `K`-schemes with `X` proper, geometrically connected and geometrically
reduced over `K`, with `Y` connected and with `Z` separated over `K`, and let
`g : X ×_K Y ⟶ Z` be a morphism of `K`-schemes. If `g (X ×_K {y₀})` is a single point for some
point `y₀ ∈ Y`, then `g` factors through the second projection: `g = pr₂ ≫ h` for some
`h : Y ⟶ Z`, that is, the triangle

```
  pullback fX fY ─── pullback.snd ──▶ Y
             ╲                        │
              ╲  g                    │ h
               ╲                      ▼
                ╲──────────────────▶ Z
```

commutes. The set `g (X ×_K {y₀})` is spelled as the range of the restriction of `g` to the
scheme-theoretic fibre of `pr₂` over `y₀`; the point `y₀` need not be `K`-rational.

Neither geometric hypothesis on `X` can be dropped on its own. For `K = ℝ`, `X = Spec ℂ`,
`Y = 𝔸¹_ℝ`, `Z = 𝔸¹_ℂ` and `g` the identity of `X ×_K Y = 𝔸¹_ℂ`, `X` is connected and
geometrically reduced but not geometrically connected, and `g` does not factor. For `K`
imperfect of characteristic `p`, `a ∈ K ∖ K^p`, `K' = K(a^{1/p})`, `X = Spec K'`, `Y = 𝔸¹_K`,
`Z = 𝔸¹_{K'}` and `g` the identity of `X ×_K Y = 𝔸¹_{K'}`, `X` is geometrically connected and
reduced but not geometrically reduced, and `g` does not factor since `pr₂ : 𝔸¹_{K'} ⟶ 𝔸¹_K` is
not a monomorphism. In both examples `Γ(X, 𝒪_X) ≠ K`. -/
theorem exists_eq_snd_comp {X Y Z : Scheme.{u}} (fX : X ⟶ Spec (.of K))
    (fY : Y ⟶ Spec (.of K)) (fZ : Z ⟶ Spec (.of K)) [IsProper fX] [GeometricallyConnected fX]
    [GeometricallyReduced fX] [ConnectedSpace Y] [IsSeparated fZ]
    (g : pullback fX fY ⟶ Z) (hg : g ≫ fZ = pullback.fst fX fY ≫ fX) (y₀ : Y)
    (hy₀ : (Set.range ((pullback.snd fX fY).fiberι y₀ ≫ g).base).Subsingleton) :
    ∃ h : Y ⟶ Z, g = pullback.snd fX fY ≫ h :=
  -- Proof sketch (Mumford, Abelian Varieties §4). Let `L'` be the set of `y` with
  -- `g (X ×_K {y})` a single point. For `y ∈ L'` and an affine open `V` around that point,
  -- `Y ∖ pr₂ (g⁻¹ (Z ∖ V))` is an open neighbourhood of `y` since `pr₂` is closed. On an
  -- affine open `U` inside it, `Γ(X ×_K U, 𝒪) = 𝒪(U)` (flat base change and `Γ(X, 𝒪_X) = K`)
  -- gives `g = pr₂ ≫ h_U` on `X ×_K U`. So `L'` is open and equals the geometric locus of
  -- `isClosed_setOf_subsingleton_image`, which is closed; as `Y` is connected, `L' = Y`, and
  -- the `h_U` glue since `pr₂` is an epimorphism.
  sorry

end AlgebraicGeometry
