/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.Sheaves.CommRingCat
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.RingTheory.Flat.Equalizer

/-!
# Fibre products of schemes: slice inclusions, and flat base change of global sections

## Slice inclusions

A section `y₀ : S ⟶ Y` of `πY : Y ⟶ S` cuts out a *slice* `X × {y₀} ⊆ X ×_S Y`: the morphism
`AlgebraicGeometry.sliceInclusionFst` induced by `𝟙 X` and `πX ≫ y₀`. It is a section of the
first projection, hence a closed immersion as soon as `πY` is separated, and it is a morphism of
`S`-schemes for the structure morphism `AlgebraicGeometry.Scheme.canonicallyOverPullback` puts
on `X ×_S Y`. Base changing it along a third `S`-scheme `Z` gives the slice
`X ×_S Z ⟶ (X ×_S Y) ×_S Z` of a triple product
(`AlgebraicGeometry.pullbackMapSliceInclusionFst`).

When `X`, `Y` and `Z` are presented as objects of the cartesian monoidal category `Over S` and
the base points as sections `𝟙_ (Over S) ⟶ _`, the three slices of the triple product
`(X ⊗ Y) ⊗ Z` are the evident cartesian lifts; that is
`AlgebraicGeometry.sliceInclusionFst_eq_lift` and its two companions, which is what lets a
statement about slices of a triple product be applied to a group object in `Over S`.

## Flat base change of global sections

Let `X` be a separated scheme over `Spec R`, let `φ : R ⟶ R'` be a flat ring map and let
`p : X ×_{Spec R} Spec R' ⟶ X` be the first projection. For a quasi-compact open `U ⊆ X`, the
ring `Γ(X ×_{Spec R} Spec R', p⁻¹ U)` is the base change of `Γ(X, U)` along `φ`, that is
`Γ(X, U) ⊗[R] R'`. This is the degree-zero case of Stacks tag `02KH`.

As in `WeilConjectures.Mathlib.Algebra.Category.Ring.Constructions`, "is the base change along
`φ`" is phrased as a `CategoryTheory.IsPushout` square in `CommRingCat`, which needs no `Algebra`
instances on the rings of sections.

The proof is the usual one: the statement holds over an affine open because a base change of
affine schemes is the `Spec` of a tensor product, and it propagates from `U`, `V` and `U ⊓ V` to
`U ⊔ V` because `Γ(X, U ⊔ V)` is the equaliser of the two restriction maps
`Γ(X, U) × Γ(X, V) ⇉ Γ(X, U ⊓ V)` and flat base change preserves that equaliser. Every
quasi-compact open is a finite union of affine opens, and on a separated scheme an intersection
of two affine opens is affine, so an induction on the number of members of the cover finishes it.

## Main results

- `AlgebraicGeometry.sliceInclusionFst`, `AlgebraicGeometry.sliceInclusionSnd` and their
  `IsClosedImmersion` and `IsOver` instances
- `AlgebraicGeometry.isPushout_app_of_isAffineOpen`
- `AlgebraicGeometry.isPushout_app_of_isCompact`

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

variable {X : Scheme.{u}} {R R' : CommRingCat.{u}}

section

variable (φ : R ⟶ R') (f : X ⟶ Spec R)

/-- (Implementation.) `IsPushoutApp φ f U` says that the sections of the base change
`X ×_{Spec R} Spec R'` over the preimage of `U` form the base change along `φ` of the sections
of `X` over `U`. -/
private def IsPushoutApp (U : X.Opens) : Prop :=
  IsPushout ((Scheme.ΓSpecIso R).inv ≫ f.appLE ⊤ U le_top) φ
    ((pullback.fst f (Spec.map φ)).app U)
    ((Scheme.ΓSpecIso R').inv ≫
      (pullback.snd f (Spec.map φ)).appLE ⊤ (pullback.fst f (Spec.map φ) ⁻¹ᵁ U) le_top)

end

/-- Over an affine open `U`, the sections of the base change `X ×_{Spec R} Spec R'` over the
preimage of `U` are the base change of the sections of `X` over `U`. -/
theorem isPushout_app_of_isAffineOpen (φ : R ⟶ R') (f : X ⟶ Spec R) {U : X.Opens}
    (hU : IsAffineOpen U) :
    IsPushout ((Scheme.ΓSpecIso R).inv ≫ f.appLE ⊤ U le_top) φ
      ((pullback.fst f (Spec.map φ)).app U)
      ((Scheme.ΓSpecIso R').inv ≫
        (pullback.snd f (Spec.map φ)).appLE ⊤ (pullback.fst f (Spec.map φ) ⁻¹ᵁ U) le_top) := by
  have hp : IsPullback (pullback.fst f (Spec.map φ)) (pullback.snd f (Spec.map φ)) f (Spec.map φ) :=
    IsPullback.of_hasPullback _ _
  have key := Scheme.Hom.isPullback_resLE hp (US := ⊤) (UT := ⊤) (UX := U) le_top le_top
    (UY := pullback.fst f (Spec.map φ) ⁻¹ᵁ U) (by simp)
  have : IsAffine U.toScheme := hU
  have : IsAffine (⊤ : (Spec R).Opens).toScheme := isAffineOpen_top _
  have : IsAffine (⊤ : (Spec R').Opens).toScheme := isAffineOpen_top _
  have key2 := isPushout_appTop_of_isPullback key
  simp only [Scheme.Hom.resLE_app_top] at key2
  refine key2.of_iso' (((⊤ : (Spec R).Opens).topIso ≪≫ Scheme.ΓSpecIso R).symm) U.topIso.symm
    (((⊤ : (Spec R').Opens).topIso ≪≫ Scheme.ΓSpecIso R').symm)
    (pullback.fst f (Spec.map φ) ⁻¹ᵁ U).topIso.symm ?_ ?_ ?_ ?_
  · simp
  · simp [← Scheme.Hom.appLE_eq_app]
  · simp [Scheme.Hom.app_eq_appLE]
  · simp

/-- (Implementation.) The base-change square of sections over an open `U` commutes. -/
private lemma commSq_app (φ : R ⟶ R') (f : X ⟶ Spec R) (W : X.Opens) :
    ((Scheme.ΓSpecIso R).inv ≫ f.appLE ⊤ W le_top) ≫ (pullback.fst f (Spec.map φ)).app W =
      φ ≫ ((Scheme.ΓSpecIso R').inv ≫ (pullback.snd f (Spec.map φ)).appLE ⊤
        (pullback.fst f (Spec.map φ) ⁻¹ᵁ W) le_top) := by
  rw [Category.assoc, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, pullback.condition,
    ← Scheme.Hom.appLE_comp_appLE (V := ⊤) (e₁ := le_top) (e₂ := le_top), ← Category.assoc,
    ← Category.assoc]
  congr 1
  simp [← Scheme.Hom.appLE_eq_app]

/-- (Implementation.) The first projection of a product of two rings. -/
private def pr₁ (A B : CommRingCat.{u}) : CommRingCat.of (↥A × ↥B) ⟶ A :=
  CommRingCat.ofHom (RingHom.fst ↥A ↥B)

/-- (Implementation.) The second projection of a product of two rings. -/
private def pr₂ (A B : CommRingCat.{u}) : CommRingCat.of (↥A × ↥B) ⟶ B :=
  CommRingCat.ofHom (RingHom.snd ↥A ↥B)

/-- (Implementation.) The map into a product of two rings given by a pair of maps. -/
private def prodLift {A B C : CommRingCat.{u}} (u : A ⟶ B) (v : A ⟶ C) :
    A ⟶ CommRingCat.of (↥B × ↥C) :=
  CommRingCat.ofHom (u.hom.prod v.hom)

@[simp]
private lemma comp_prodLift {A' A B C : CommRingCat.{u}} (g : A' ⟶ A) (u : A ⟶ B) (v : A ⟶ C) :
    g ≫ prodLift u v = prodLift (g ≫ u) (g ≫ v) := rfl

@[reassoc (attr := simp)]
private lemma prodLift_comp_pr₁ {A B C : CommRingCat.{u}} (u : A ⟶ B) (v : A ⟶ C) :
    prodLift u v ≫ pr₁ B C = u := rfl

@[reassoc (attr := simp)]
private lemma prodLift_comp_pr₂ {A B C : CommRingCat.{u}} (u : A ⟶ B) (v : A ⟶ C) :
    prodLift u v ≫ pr₂ B C = v := rfl

/-- (Implementation.) The pair of restriction maps `Γ(X, U ⊔ V) ⟶ Γ(X, U) × Γ(X, V)`. -/
private def resProd (U V : X.Opens) : Γ(X, U ⊔ V) ⟶ CommRingCat.of (↥Γ(X, U) × ↥Γ(X, V)) :=
  prodLift (X.presheaf.map (homOfLE (le_sup_left : U ≤ U ⊔ V)).op)
    (X.presheaf.map (homOfLE (le_sup_right : V ≤ U ⊔ V)).op)

/-- (Implementation.) Restriction of the first factor of `Γ(X, U) × Γ(X, V)` to `U ⊓ V`. -/
private def resFst (U V : X.Opens) : CommRingCat.of (↥Γ(X, U) × ↥Γ(X, V)) ⟶ Γ(X, U ⊓ V) :=
  pr₁ _ _ ≫ X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op

/-- (Implementation.) Restriction of the second factor of `Γ(X, U) × Γ(X, V)` to `U ⊓ V`. -/
private def resSnd (U V : X.Opens) : CommRingCat.of (↥Γ(X, U) × ↥Γ(X, V)) ⟶ Γ(X, U ⊓ V) :=
  pr₂ _ _ ≫ X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op

private lemma resProd_injective (U V : X.Opens) : Function.Injective (resProd U V) :=
  fun s t h => X.sheaf.eq_of_locally_eq₂ (homOfLE le_sup_left) (homOfLE le_sup_right) le_rfl s t
    (congrArg Prod.fst h) (congrArg Prod.snd h)

private lemma exists_resProd_eq (U V : X.Opens) (x : ↥Γ(X, U) × ↥Γ(X, V))
    (hx : resFst U V x = resSnd U V x) : ∃ y : Γ(X, U ⊔ V), resProd U V y = x := by
  refine ⟨(TopCat.Sheaf.objSupIsoProdEqLocus X.sheaf U V).inv ⟨x, hx⟩, Prod.ext ?_ ?_⟩
  · exact TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst X.sheaf U V ⟨x, hx⟩
  · exact TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd X.sheaf U V ⟨x, hx⟩

private lemma resProd_comp_resFst (U V : X.Opens) :
    resProd U V ≫ resFst U V = resProd U V ≫ resSnd U V := by
  simp only [resProd, resFst, resSnd, prodLift_comp_pr₁_assoc, prodLift_comp_pr₂_assoc,
    ← Functor.map_comp, ← op_comp]
  rfl

private lemma map_comp_app {Y : Scheme.{u}} (p : Y ⟶ X) {U W : X.Opens} (h : U ≤ W) :
    X.presheaf.map (homOfLE h).op ≫ p.app U =
      p.app W ≫ Y.presheaf.map (homOfLE (Scheme.Hom.preimage_mono p h)).op := by
  simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

/-- (Implementation.) The Mayer-Vietoris step: if the base-change square is a pushout over `U`,
over `V` and over `U ⊓ V`, then it is a pushout over `U ⊔ V`. -/
private lemma isPushoutApp_sup (φ : R ⟶ R') (f : X ⟶ Spec R) [Flat (Spec.map φ)] {U V : X.Opens}
    (hU : IsPushoutApp φ f U) (hV : IsPushoutApp φ f V) (hUV : IsPushoutApp φ f (U ⊓ V)) :
    IsPushoutApp φ f (U ⊔ V) := by
  have hφ : φ.hom.Flat := Flat.SpecMap_iff.mp ‹_›
  unfold IsPushoutApp at hU hV hUV ⊢
  set Y := pullback f (Spec.map φ)
  set p : Y ⟶ X := pullback.fst f (Spec.map φ)
  set q : Y ⟶ Spec R' := pullback.snd f (Spec.map φ)
  have hB : IsPushout
      (prodLift ((Scheme.ΓSpecIso R).inv ≫ f.appLE ⊤ U le_top)
        ((Scheme.ΓSpecIso R).inv ≫ f.appLE ⊤ V le_top)) φ
      (prodLift (pr₁ _ _ ≫ p.app U) (pr₂ _ _ ≫ p.app V))
      (prodLift ((Scheme.ΓSpecIso R').inv ≫ q.appLE ⊤ (p ⁻¹ᵁ U) le_top)
        ((Scheme.ΓSpecIso R').inv ≫ q.appLE ⊤ (p ⁻¹ᵁ V) le_top)) :=
    CommRingCat.isPushout_prod hU hV
  have e₁ : ((Scheme.ΓSpecIso R).inv ≫ f.appLE ⊤ (U ⊔ V) le_top) ≫ resProd U V =
      prodLift ((Scheme.ΓSpecIso R).inv ≫ f.appLE ⊤ U le_top)
        ((Scheme.ΓSpecIso R).inv ≫ f.appLE ⊤ V le_top) := by
    simp only [resProd, comp_prodLift, Category.assoc, Scheme.Hom.appLE_map]
  have e₂ : prodLift ((Scheme.ΓSpecIso R).inv ≫ f.appLE ⊤ U le_top)
        ((Scheme.ΓSpecIso R).inv ≫ f.appLE ⊤ V le_top) ≫ resFst U V =
      (Scheme.ΓSpecIso R).inv ≫ f.appLE ⊤ (U ⊓ V) le_top := by
    simp only [resFst, prodLift_comp_pr₁_assoc, Category.assoc, Scheme.Hom.appLE_map]
  have e₃ : prodLift ((Scheme.ΓSpecIso R).inv ≫ f.appLE ⊤ U le_top)
        ((Scheme.ΓSpecIso R).inv ≫ f.appLE ⊤ V le_top) ≫ resSnd U V =
      (Scheme.ΓSpecIso R).inv ≫ f.appLE ⊤ (U ⊓ V) le_top := by
    simp only [resSnd, prodLift_comp_pr₂_assoc, Category.assoc, Scheme.Hom.appLE_map]
  have e₁' : ((Scheme.ΓSpecIso R').inv ≫ q.appLE ⊤ (p ⁻¹ᵁ (U ⊔ V)) le_top) ≫
        resProd (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) =
      prodLift ((Scheme.ΓSpecIso R').inv ≫ q.appLE ⊤ (p ⁻¹ᵁ U) le_top)
        ((Scheme.ΓSpecIso R').inv ≫ q.appLE ⊤ (p ⁻¹ᵁ V) le_top) := by
    simp only [resProd, comp_prodLift, Category.assoc, Scheme.Hom.appLE_map]
  have e₂' : prodLift ((Scheme.ΓSpecIso R').inv ≫ q.appLE ⊤ (p ⁻¹ᵁ U) le_top)
        ((Scheme.ΓSpecIso R').inv ≫ q.appLE ⊤ (p ⁻¹ᵁ V) le_top) ≫
        resFst (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) =
      (Scheme.ΓSpecIso R').inv ≫ q.appLE ⊤ (p ⁻¹ᵁ (U ⊓ V)) le_top := by
    simp only [resFst, prodLift_comp_pr₁_assoc, Category.assoc, Scheme.Hom.appLE_map]
    rfl
  have e₃' : prodLift ((Scheme.ΓSpecIso R').inv ≫ q.appLE ⊤ (p ⁻¹ᵁ U) le_top)
        ((Scheme.ΓSpecIso R').inv ≫ q.appLE ⊤ (p ⁻¹ᵁ V) le_top) ≫
        resSnd (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) =
      (Scheme.ΓSpecIso R').inv ≫ q.appLE ⊤ (p ⁻¹ᵁ (U ⊓ V)) le_top := by
    simp only [resSnd, prodLift_comp_pr₂_assoc, Category.assoc, Scheme.Hom.appLE_map]
    rfl
  have hα : resProd U V ≫ prodLift (pr₁ _ _ ≫ p.app U) (pr₂ _ _ ≫ p.app V) =
      p.app (U ⊔ V) ≫ resProd (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) := by
    simp only [resProd, comp_prodLift, prodLift_comp_pr₁_assoc, prodLift_comp_pr₂_assoc,
      map_comp_app p le_sup_left, map_comp_app p le_sup_right]
  have hβ₁ : resFst U V ≫ p.app (U ⊓ V) =
      prodLift (pr₁ _ _ ≫ p.app U) (pr₂ _ _ ≫ p.app V) ≫ resFst (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) := by
    simp only [resFst, Category.assoc, prodLift_comp_pr₁_assoc, map_comp_app p inf_le_left]
  have hβ₂ : resSnd U V ≫ p.app (U ⊓ V) =
      prodLift (pr₁ _ _ ≫ p.app U) (pr₂ _ _ ≫ p.app V) ≫ resSnd (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) := by
    simp only [resSnd, Category.assoc, prodLift_comp_pr₂_assoc, map_comp_app p inf_le_right]
  exact CommRingCat.isPushout_of_isEqualizer hφ e₁ e₂ e₃ e₁' e₂' e₃'
    (resProd_comp_resFst U V) (resProd_injective U V) (exists_resProd_eq U V)
    (resProd_comp_resFst (p ⁻¹ᵁ U) (p ⁻¹ᵁ V)) (resProd_injective (p ⁻¹ᵁ U) (p ⁻¹ᵁ V))
    hα hβ₁ hβ₂ hB hUV (commSq_app φ f (U ⊔ V))

private lemma isPushoutApp_bot (φ : R ⟶ R') (f : X ⟶ Spec R) : IsPushoutApp φ f ⊥ :=
  isPushout_app_of_isAffineOpen φ f (isAffineOpen_bot X)

private lemma isPushoutApp_finsetSup (φ : R ⟶ R') (f : X ⟶ Spec R) [IsSeparated f]
    [Flat (Spec.map φ)] :
    ∀ (n : ℕ) (s : Finset X.Opens), s.card ≤ n → (∀ a ∈ s, IsAffineOpen a) →
      IsPushoutApp φ f (s.sup id) := by
  classical
  have hsep : IsSeparated (terminal.from X) := by
    rw [show terminal.from X = f ≫ terminal.from (Spec R) from Subsingleton.elim _ _]
    infer_instance
  intro n
  induction n with
  | zero =>
    intro s hs _
    rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hs), Finset.sup_empty]
    exact isPushoutApp_bot φ f
  | succ n ih =>
    intro s hs haff
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · rw [Finset.sup_empty]
      exact isPushoutApp_bot φ f
    · obtain ⟨t, hat, rfl⟩ : ∃ t : Finset X.Opens, a ∉ t ∧ s = insert a t :=
        ⟨s.erase a, Finset.notMem_erase _ _, (Finset.insert_erase ha).symm⟩
      have hcard : t.card ≤ n := by
        have := Finset.card_insert_of_notMem hat
        omega
      have haffa : IsAffineOpen a := haff a (Finset.mem_insert_self _ _)
      have hafft : ∀ b ∈ t, IsAffineOpen b := fun b hb => haff b (Finset.mem_insert_of_mem hb)
      rw [Finset.sup_insert]
      refine isPushoutApp_sup φ f (isPushout_app_of_isAffineOpen φ f haffa) (ih t hcard hafft) ?_
      have himg : id a ⊓ t.sup id = (t.image (fun b => a ⊓ b)).sup id := by
        rw [Finset.sup_inf_distrib_left, Finset.sup_image]
        rfl
      rw [himg]
      refine ih _ (le_trans Finset.card_image_le hcard) fun b hb => ?_
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
      exact haffa.inf (hafft c hc)

/-- **Global sections and flat base change of the ground ring**, over a quasi-compact open.

For a separated `R`-scheme `X`, a quasi-compact open `U ⊆ X` and a flat ring map `φ : R ⟶ R'`,
the sections of `X ×_{Spec R} Spec R'` over the preimage of `U` are the base change along `φ` of
the sections of `X` over `U`. -/
@[stacks 02KH]
theorem isPushout_app_of_isCompact (φ : R ⟶ R') (f : X ⟶ Spec R) [IsSeparated f]
    [Flat (Spec.map φ)] {U : X.Opens} (hU : IsCompact (U : Set X)) :
    IsPushout ((Scheme.ΓSpecIso R).inv ≫ f.appLE ⊤ U le_top) φ
      ((pullback.fst f (Spec.map φ)).app U)
      ((Scheme.ΓSpecIso R').inv ≫ (pullback.snd f (Spec.map φ)).appLE ⊤
        (pullback.fst f (Spec.map φ) ⁻¹ᵁ U) le_top) := by
  classical
  obtain ⟨s, hs, rfl⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hU
  have hsup : (⨆ i ∈ s, (i : X.Opens)) =
      (hs.toFinset.image (fun i : X.affineOpens => (i : X.Opens))).sup id := by
    rw [Finset.sup_id_eq_sSup, Finset.coe_image, Set.Finite.coe_toFinset, sSup_image]
  rw [hsup]
  refine isPushoutApp_finsetSup φ f _ _ le_rfl fun a ha => ?_
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
  exact i.2

section SliceInclusion

variable {Y S : Scheme.{u}} (πX : X ⟶ S) (πY : Y ⟶ S)

/-- The slice inclusion `j_{y₀} : X ⟶ X ×_S Y` determined by a section `y₀` of `πY`. -/
noncomputable def sliceInclusionFst (y₀ : S ⟶ Y) (hy₀ : y₀ ≫ πY = 𝟙 _) : X ⟶ pullback πX πY :=
  pullback.lift (𝟙 X) (πX ≫ y₀) (by simp [hy₀])

@[reassoc (attr := simp)]
lemma sliceInclusionFst_fst (y₀ : S ⟶ Y) (hy₀ : y₀ ≫ πY = 𝟙 _) :
    sliceInclusionFst πX πY y₀ hy₀ ≫ pullback.fst πX πY = 𝟙 X := by
  simp [sliceInclusionFst]

@[reassoc (attr := simp)]
lemma sliceInclusionFst_snd (y₀ : S ⟶ Y) (hy₀ : y₀ ≫ πY = 𝟙 _) :
    sliceInclusionFst πX πY y₀ hy₀ ≫ pullback.snd πX πY = πX ≫ y₀ := by
  simp [sliceInclusionFst]

/-- The slice inclusion `j_{x₀} : Y ⟶ X ×_S Y` determined by a section `x₀` of `πX`. -/
noncomputable def sliceInclusionSnd (x₀ : S ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 _) : Y ⟶ pullback πX πY :=
  pullback.lift (πY ≫ x₀) (𝟙 Y) (by simp [hx₀])

@[reassoc (attr := simp)]
lemma sliceInclusionSnd_fst (x₀ : S ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 _) :
    sliceInclusionSnd πX πY x₀ hx₀ ≫ pullback.fst πX πY = πY ≫ x₀ := by
  simp [sliceInclusionSnd]

@[reassoc (attr := simp)]
lemma sliceInclusionSnd_snd (x₀ : S ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 _) :
    sliceInclusionSnd πX πY x₀ hx₀ ≫ pullback.snd πX πY = 𝟙 Y := by
  simp [sliceInclusionSnd]

/-- **A slice inclusion is a closed immersion**, being a section of the projection
`pr₁ : X ×_S Y ⟶ X`, which is separated because `πY` is. -/
instance [IsSeparated πY] (y₀ : S ⟶ Y) (hy₀ : y₀ ≫ πY = 𝟙 _) :
    IsClosedImmersion (sliceInclusionFst πX πY y₀ hy₀) :=
  IsClosedImmersion.of_comp_eq_id (f := pullback.fst πX πY) (by simp)

/-- **A slice inclusion is a closed immersion**, being a section of the projection
`pr₂ : X ×_S Y ⟶ Y`, which is separated because `πX` is. -/
instance [IsSeparated πX] (x₀ : S ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 _) :
    IsClosedImmersion (sliceInclusionSnd πX πY x₀ hx₀) :=
  IsClosedImmersion.of_comp_eq_id (f := pullback.snd πX πY) (by simp)

/-! ### Base change of a slice inclusion -/

variable {Z : Scheme.{u}} (πZ : Z ⟶ S)

/-- **A slice inclusion base changed along `πZ : Z ⟶ S`**: the morphism
`j_{y₀} ×_S 𝟙_Z : X ×_S Z ⟶ (X ×_S Y) ×_S Z`, where `X ×_S Y` is regarded as an `S`-scheme
through its first projection.

```
                 pullbackMapSliceInclusionFst
        X ×_S Z ───────────────────────▶ (X ×_S Y) ×_S Z
          │   ╲                            ╱   │
      pr₁ │     ╲ pr₂                pr₂ ╱     │ pr₁
          ▼       ▼                    ▼       ▼
          X ────▶ Z ══════════════════ Z ◀──── X ×_S Y
             j_{y₀} ▶
```
-/
noncomputable def pullbackMapSliceInclusionFst (y₀ : S ⟶ Y) (hy₀ : y₀ ≫ πY = 𝟙 _) :
    pullback πX πZ ⟶ pullback (pullback.fst πX πY ≫ πX) πZ :=
  pullback.map πX πZ (pullback.fst πX πY ≫ πX) πZ (sliceInclusionFst πX πY y₀ hy₀) (𝟙 Z) (𝟙 S)
    (by simp) (by simp)

@[reassoc (attr := simp)]
lemma pullbackMapSliceInclusionFst_fst (y₀ : S ⟶ Y) (hy₀ : y₀ ≫ πY = 𝟙 _) :
    pullbackMapSliceInclusionFst πX πY πZ y₀ hy₀ ≫
        pullback.fst (pullback.fst πX πY ≫ πX) πZ =
      pullback.fst πX πZ ≫ sliceInclusionFst πX πY y₀ hy₀ := by
  simp [pullbackMapSliceInclusionFst]

@[reassoc (attr := simp)]
lemma pullbackMapSliceInclusionFst_snd (y₀ : S ⟶ Y) (hy₀ : y₀ ≫ πY = 𝟙 _) :
    pullbackMapSliceInclusionFst πX πY πZ y₀ hy₀ ≫
        pullback.snd (pullback.fst πX πY ≫ πX) πZ =
      pullback.snd πX πZ := by
  simp [pullbackMapSliceInclusionFst]

/-- **A slice inclusion base changed along `πZ : Z ⟶ S`**: the morphism
`j_{x₀} ×_S 𝟙_Z : Y ×_S Z ⟶ (X ×_S Y) ×_S Z`, where `X ×_S Y` is regarded as an `S`-scheme
through its first projection.

```
                 pullbackMapSliceInclusionSnd
        Y ×_S Z ───────────────────────▶ (X ×_S Y) ×_S Z
          │   ╲                            ╱   │
      pr₁ │     ╲ pr₂                pr₂ ╱     │ pr₁
          ▼       ▼                    ▼       ▼
          Y ────▶ Z ══════════════════ Z ◀──── X ×_S Y
             j_{x₀} ▶
```
-/
noncomputable def pullbackMapSliceInclusionSnd (x₀ : S ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 _) :
    pullback πY πZ ⟶ pullback (pullback.fst πX πY ≫ πX) πZ :=
  pullback.map πY πZ (pullback.fst πX πY ≫ πX) πZ (sliceInclusionSnd πX πY x₀ hx₀) (𝟙 Z) (𝟙 S)
    (by simp [hx₀]) (by simp)

@[reassoc (attr := simp)]
lemma pullbackMapSliceInclusionSnd_fst (x₀ : S ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 _) :
    pullbackMapSliceInclusionSnd πX πY πZ x₀ hx₀ ≫
        pullback.fst (pullback.fst πX πY ≫ πX) πZ =
      pullback.fst πY πZ ≫ sliceInclusionSnd πX πY x₀ hx₀ := by
  simp [pullbackMapSliceInclusionSnd]

@[reassoc (attr := simp)]
lemma pullbackMapSliceInclusionSnd_snd (x₀ : S ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 _) :
    pullbackMapSliceInclusionSnd πX πY πZ x₀ hx₀ ≫
        pullback.snd (pullback.fst πX πY ≫ πX) πZ =
      pullback.snd πY πZ := by
  simp [pullbackMapSliceInclusionSnd]

end SliceInclusion

section Over

variable {Y S : Scheme.{u}} [X.Over S] [Y.Over S]

/-- The first projection of a fibre product of two `S`-schemes is a morphism of `S`-schemes.
The structure morphism of `X ×_S Y` is the *second* projection followed by `Y ↘ S`
(`AlgebraicGeometry.Scheme.canonicallyOverPullback`), so this is `pullback.condition`. -/
instance : (pullback.fst (X ↘ S) (Y ↘ S)).IsOver S := ⟨pullback.condition⟩

/-- The second projection of a fibre product of two `S`-schemes is a morphism of `S`-schemes. -/
instance : (pullback.snd (X ↘ S) (Y ↘ S)).IsOver S := ⟨rfl⟩

/-- **The slice inclusion `j_{y₀} : X ⟶ X ×_S Y` is a morphism of `S`-schemes**:

```
  X ─────j_{y₀}─────▶ X ×_S Y
    ╲                ╱
      ╲            ╱  pr₂ ≫ (Y ↘ S)
  X ↘ S ╲        ╱      (the structure morphism of `X ×_S Y`)
          ▼    ▼
            S
```

The triangle commutes because `pr₂ ∘ j_{y₀} = (X ↘ S) ≫ y₀` and `y₀` is a section of `Y ↘ S`. -/
instance isOver_sliceInclusionFst (y₀ : S ⟶ Y) (hy₀ : y₀ ≫ Y ↘ S = 𝟙 _) :
    (sliceInclusionFst (X ↘ S) (Y ↘ S) y₀ hy₀).IsOver S :=
  ⟨by
    change sliceInclusionFst (X ↘ S) (Y ↘ S) y₀ hy₀ ≫ pullback.snd _ _ ≫ Y ↘ S = X ↘ S
    rw [← Category.assoc, sliceInclusionFst_snd, Category.assoc, hy₀, Category.comp_id]⟩

/-- **The slice inclusion `j_{x₀} : Y ⟶ X ×_S Y` is a morphism of `S`-schemes**:

```
  Y ─────j_{x₀}─────▶ X ×_S Y
    ╲                ╱
      ╲            ╱  pr₂ ≫ (Y ↘ S)
  Y ↘ S ╲        ╱      (the structure morphism of `X ×_S Y`)
          ▼    ▼
            S
```

The triangle commutes because `pr₂ ∘ j_{x₀} = 𝟙 Y`. -/
instance isOver_sliceInclusionSnd (x₀ : S ⟶ X) (hx₀ : x₀ ≫ X ↘ S = 𝟙 _) :
    (sliceInclusionSnd (X ↘ S) (Y ↘ S) x₀ hx₀).IsOver S :=
  ⟨by
    change sliceInclusionSnd (X ↘ S) (Y ↘ S) x₀ hx₀ ≫ pullback.snd _ _ ≫ Y ↘ S = Y ↘ S
    rw [← Category.assoc, sliceInclusionSnd_snd, Category.id_comp]⟩

end Over

section OverCartesian

open MonoidalCategory CartesianMonoidalCategory

variable {S : Scheme.{u}} (A B C : Over S)

/-- **The slice `A × B × {z₀}` of a triple product is a cartesian lift.** For three objects
`A`, `B`, `C` of `Over S` and a section `z₀ : 𝟙_ (Over S) ⟶ C`, the slice inclusion of the
triple product `(A ×_S B) ×_S C` through `z₀` is, on underlying schemes, the morphism
`⟨𝟙, z₀⟩ : A ⊗ B ⟶ (A ⊗ B) ⊗ C` of `Over S`. Both sides are determined by their two
projections:

```
            j = ⟨𝟙, z₀⟩                                j = ⟨𝟙, z₀⟩
 A ⊗ B ──────────────────▶ (A⊗B) ⊗ C       A ⊗ B ──────────────────▶ (A⊗B) ⊗ C
    ╲                          │              ╲                          │
  𝟙  ╲                         │ pr₁           ╲ toUnit ≫ z₀             │ pr₂
      ◥                        ▼                 ◥                       ▼
       ──────────────────▶ A ⊗ B                  ──────────────────────▶ C
```
-/
theorem sliceInclusionFst_eq_lift (z₀ : 𝟙_ (Over S) ⟶ C) :
    sliceInclusionFst (pullback.fst A.hom B.hom ≫ A.hom) C.hom z₀.left (Over.w z₀) =
      (lift (𝟙 (A ⊗ B)) (toUnit (A ⊗ B) ≫ z₀) : A ⊗ B ⟶ (A ⊗ B) ⊗ C).left := by
  refine pullback.hom_ext ?_ ?_ <;>
    simp [sliceInclusionFst, Over.lift_left, Over.comp_left, Over.toUnit_left]

/-- **The slice `A × {y₀} × C` of a triple product is a cartesian lift.** For three objects
`A`, `B`, `C` of `Over S` and a section `y₀ : 𝟙_ (Over S) ⟶ B`, the base change along `C` of
the slice inclusion of `A ×_S B` through `y₀` is, on underlying schemes, the morphism
`⟨⟨pr₁, y₀⟩, pr₂⟩ : A ⊗ C ⟶ (A ⊗ B) ⊗ C` of `Over S`. Both sides are determined by their three
projections:

```
                 j                              j                            j
  A ⊗ C ──────────────▶ (A⊗B) ⊗ C   A ⊗ C ─────────▶ (A⊗B) ⊗ C   A ⊗ C ─────────▶ (A⊗B) ⊗ C
     ╲                      │          ╲                 │          ╲                 │
  pr₁ ╲              pr₁ ≫ pr₁          ╲ toUnit ≫ y₀    │ pr₁≫pr₂    ╲ pr₂           │ pr₂
       ◥                    ▼             ◥              ▼             ◥               ▼
        ─────────────────▶ A               ──────────▶ B                ──────────────▶ C
```
-/
theorem pullbackMapSliceInclusionFst_eq_lift (y₀ : 𝟙_ (Over S) ⟶ B) :
    pullbackMapSliceInclusionFst A.hom B.hom C.hom y₀.left (Over.w y₀) =
      (lift (lift (fst A C) (toUnit (A ⊗ C) ≫ y₀)) (snd A C) :
        A ⊗ C ⟶ (A ⊗ B) ⊗ C).left := by
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_ <;>
    simp [pullbackMapSliceInclusionFst, sliceInclusionFst, Over.lift_left, Over.comp_left,
      Over.toUnit_left]

/-- **The slice `{x₀} × B × C` of a triple product is a cartesian lift.** For three objects
`A`, `B`, `C` of `Over S` and a section `x₀ : 𝟙_ (Over S) ⟶ A`, the base change along `C` of
the slice inclusion of `A ×_S B` through `x₀` is, on underlying schemes, the morphism
`⟨⟨x₀, pr₁⟩, pr₂⟩ : B ⊗ C ⟶ (A ⊗ B) ⊗ C` of `Over S`. Both sides are determined by their three
projections:

```
                 j                              j                            j
  B ⊗ C ──────────────▶ (A⊗B) ⊗ C   B ⊗ C ─────────▶ (A⊗B) ⊗ C   B ⊗ C ─────────▶ (A⊗B) ⊗ C
     ╲                      │          ╲                 │          ╲                 │
      ╲ toUnit ≫ x₀  pr₁ ≫ pr₁          ╲ pr₁            │ pr₁≫pr₂    ╲ pr₂           │ pr₂
       ◥                    ▼             ◥              ▼             ◥               ▼
        ─────────────────▶ A               ──────────▶ B                ──────────────▶ C
```
-/
theorem pullbackMapSliceInclusionSnd_eq_lift (x₀ : 𝟙_ (Over S) ⟶ A) :
    pullbackMapSliceInclusionSnd A.hom B.hom C.hom x₀.left (Over.w x₀) =
      (lift (lift (toUnit (B ⊗ C) ≫ x₀) (fst B C)) (snd B C) :
        B ⊗ C ⟶ (A ⊗ B) ⊗ C).left := by
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_ <;>
    simp [pullbackMapSliceInclusionSnd, sliceInclusionSnd, Over.lift_left, Over.comp_left,
      Over.toUnit_left]

end OverCartesian

end AlgebraicGeometry
