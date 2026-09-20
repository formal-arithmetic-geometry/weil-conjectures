/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FibrewiseCriteria
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import WeilConjectures.AlgebraicGeometry.Modules.TrivialLineBundle
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# The triviality criterion for a line bundle over a field

Let `K` be a field, let `X` be a proper geometrically integral `K`-scheme and let `L` be a line
bundle on `X`, with tensor inverse `N`. This file proves that `L` is trivial — isomorphic to the
structure sheaf — **if and only if** both `Γ(X, L)` and `Γ(X, N)` are non-zero. The field `K` is
not assumed algebraically closed, which is what makes the criterion applicable at *every* point
of a base scheme and not only at the rational ones.

The invertibility of `L` and of `N` is not a separate hypothesis: the criterion takes an
isomorphism `e : L ⊗ N ≅ 𝟙_ X.Modules`, from which `SheafOfModules.Invertible.left` and
`SheafOfModules.Invertible.right` recover `L.Invertible` and `N.Invertible`.

The file also collects the **product of two sections** that the criterion runs on. For
`e : L ⊗ N ≅ 𝒪ₓ`, a global section `s` of `L` and a global section `u` of `N` have a product
`s ⊗ u`, taken here as the endomorphism `AlgebraicGeometry.Scheme.Modules.pairingHom` of the
structure sheaf rather than as a section of `L ⊗ N ≅ 𝒪ₓ`. It is non-zero on a fibre exactly when
both factors are, and it is the composite whose invertibility on a fibre is the key step of the
criterion. Finally the criterion is read on the fibres of a morphism `f : W ⟶ T`, over the residue
field of a point of the base.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.pairingHom`: the product of a global section of `L` and a
  global section of `N`, and `AlgebraicGeometry.Scheme.Modules.pairingHomOfNhds`, its version for
  two sections of `f _* L` and `f _* N` over an open subset of the base.

## Main results

- `AlgebraicGeometry.Scheme.Pic.map_mk_eq_one_iff`: the class of `f ^* L` is trivial in the
  Picard group exactly when `f ^* L` is isomorphic to the structure sheaf.
- `AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_iff_of_isField`: **the triviality
  criterion**, under the hypotheses that `X` is integral and that its ring of global functions is
  a field.
- `AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_iff_of_universallyClosed` and
  `AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_iff_of_geometricallyIntegral`: the
  same criterion for `X` integral and universally closed over a field `K`, and for `X` proper and
  geometrically integral over `K`, where those two hypotheses are automatic.
- `AlgebraicGeometry.Scheme.Modules.nonempty_restrictToFiber_iso_structureModules_iff_nontrivial`:
  the same criterion on the fibre of a morphism `f : W ⟶ T` over a point `t` of the base.
- `AlgebraicGeometry.Scheme.Modules.fiberMap_pairingHom_ne_zero`,
  `AlgebraicGeometry.Scheme.Modules.fiberMap_pairingHom_eq_zero_of_left` and
  `AlgebraicGeometry.Scheme.Modules.fiberMap_pairingHom_eq_zero_of_right`: the product of two
  sections is non-zero on a fibre exactly when both factors are.

The key step of the proof is
`AlgebraicGeometry.Scheme.Modules.isIso_fiberMap_pairing_of_ne_zero`.

## Implementation notes

* The product `s ⊗ u` is taken as a morphism `𝒪ₓ ⟶ 𝒪ₓ` and not as the section
  `AlgebraicGeometry.Scheme.Modules.tensorPairing` of the structure sheaf that it corresponds to,
  because a morphism of sheaves of modules pulls back functorially — by
  `AlgebraicGeometry.Scheme.Modules.map_homOfSectionTop` multiplication by a section pulls back to
  multiplication by the pulled back section — whereas a section does not without the monoidal
  structure of the pullback of sections, which is not available. This is what lets the
  non-vanishing of `s ⊗ u` be read on a fibre.

## Blueprint

`lem:cube-triviality-criterion` of
`blueprint/src/version/detailed/curve_estimates/27_theorem_of_the_cube.tex`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SheafOfModules

namespace AlgebraicGeometry.Scheme

/-- **The class of a pullback is trivial in the Picard group exactly when the pullback is
isomorphic to the structure sheaf.** This is the bridge between the `Pic`-theoretic spelling of
"`L` is trivial" and the sheaf-theoretic one: it is
`AlgebraicGeometry.Scheme.Pic.mk_eq_one_iff` composed with
`AlgebraicGeometry.Scheme.Modules.nonempty_iso_structureModules_iff`. -/
theorem Pic.map_mk_eq_one_iff {X Y : Scheme.{u}} (f : X ⟶ Y) {L : Y.Modules} (hL : L.Invertible) :
    Pic.map f (Pic.mk L hL) = 1 ↔
      Nonempty ((Modules.pullback f).obj L ≅ X.structureModules) := by
  rw [Pic.map_mk, Pic.mk_eq_one_iff, Modules.nonempty_iso_structureModules_iff]

namespace Modules

variable {X : Scheme.{u}} {L N : X.Modules}

/-- **The key step of the triviality criterion.** Let `e : L ⊗ N ≅ 𝒪ₓ` and let `g : 𝒪ₓ ⟶ L` and
`h : 𝒪ₓ ⟶ N` be two morphisms which are both non-zero on the fibre at `x`. Then their product
`CategoryTheory.MonoidalCategory.pairing e g h` is an isomorphism on the fibre at `x`, because it
is the lower edge of the commuting square

```
              g ⊗ h
   𝟙 ⊗ 𝟙 ──────────────→ L ⊗ N
     ↑                      │
  λ⁻¹│                      │ e
     │                      ↓
     𝟙 ────────────────────→ 𝟙
```

whose three other edges have invertible fibres at `x`. -/
theorem isIso_fiberMap_pairing_of_ne_zero (hL : L.Invertible) (hN : N.Invertible)
    (e : L ⊗ N ≅ 𝟙_ X.Modules) (g : 𝟙_ X.Modules ⟶ L) (h : 𝟙_ X.Modules ⟶ N) {x : X}
    (hg : fiberMap g x ≠ 0) (hh : fiberMap h x ≠ 0) :
    IsIso (fiberMap (pairing e g h) x) := by
  have hone : (𝟙_ X.Modules).Invertible := invertible_tensorUnit X.sheaf
  have hgiso : IsIso (fiberMap g x) := isIso_fiberMap_of_ne_zero hone hL g hg
  have hhiso : IsIso (fiberMap h x) := isIso_fiberMap_of_ne_zero hone hN h hh
  have htensor : IsIso (fiberMap (g ⊗ₘ h) x) := by
    have hcomp : IsIso (fiberMap (g ⊗ₘ h) x ≫ (fiberTensorIso L N x).hom) := by
      rw [← fiberTensorIso_hom_naturality g h x]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (fiberTensorIso L N x).hom
  rw [pairing_eq]
  simp only [fiberMap_comp]
  infer_instance

/-- **The triviality criterion for a line bundle.** Let `X` be an integral scheme whose ring of
global functions is a field, and let `L` and `N` be `𝒪ₓ`-modules with `L ⊗ N ≅ 𝒪ₓ`. Then `L` is
isomorphic to the structure sheaf if and only if both `Γ(X, L)` and `Γ(X, N)` are non-zero.

This is `lem:cube-triviality-criterion` of the blueprint, stated under the two hypotheses on `X`
that the proof actually uses; see
`AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_iff_of_geometricallyIntegral` for the
form the blueprint gives it. -/
theorem nonempty_iso_tensorUnit_iff_of_isField [IsIntegral X] (hfield : IsField Γ(X, ⊤))
    (e : L ⊗ N ≅ 𝟙_ X.Modules) :
    Nonempty (L ≅ 𝟙_ X.Modules) ↔ Nontrivial Γ(L, ⊤) ∧ Nontrivial Γ(N, ⊤) := by
  have hL : L.Invertible := Invertible.left (R := X.sheaf) e
  have hN : N.Invertible := Invertible.right (R := X.sheaf) e
  have hone : (𝟙_ X.Modules).Invertible := invertible_tensorUnit X.sheaf
  have : Nontrivial Γ(X, ⊤) := ⟨hfield.exists_pair_ne⟩
  constructor
  · rintro ⟨f⟩
    exact ⟨nontrivial_sections_of_iso_unit (f ≪≫ tensorUnitIso X.sheaf),
      nontrivial_sections_of_iso_unit (isoTensorUnitOfTensorIso e f ≪≫ tensorUnitIso X.sheaf)⟩
  · rintro ⟨hLnt, hNnt⟩
    -- a non-zero global section of a line bundle gives a morphism from `𝒪ₓ` which is non-zero
    -- on some fibre
    have key {M : X.Modules} (hM : M.Invertible) {m : Γ(M, ⊤)} (hm : m ≠ 0) :
        ∃ (u : 𝟙_ X.Modules ⟶ M) (x : X), fiberMap u x ≠ 0 := by
      obtain ⟨x, hx⟩ := exists_fiberMap_homOfSectionTop_ne_zero hM hm
      refine ⟨(tensorUnitIso X.sheaf).hom ≫ homOfSectionTop M m, x, ?_⟩
      rw [fiberMap_comp, Ne, Preadditive.IsIso.comp_left_eq_zero]
      exact hx
    obtain ⟨s, hs⟩ := exists_ne (0 : Γ(L, ⊤))
    obtain ⟨v, hv⟩ := exists_ne (0 : Γ(N, ⊤))
    obtain ⟨g, x₁, hx₁⟩ := key hL hs
    obtain ⟨h, x₂, hx₂⟩ := key hN hv
    -- the two non-degeneracy loci are non-empty opens, and `X` is irreducible, so they meet
    obtain ⟨x₀, hx₀₁, hx₀₂⟩ := nonempty_preirreducible_inter
      (isClosed_setOf_fiberMap_eq_zero hone hL g).isOpen_compl
      (isClosed_setOf_fiberMap_eq_zero hone hN h).isOpen_compl
      ⟨x₁, by simpa using hx₁⟩ ⟨x₂, by simpa using hx₂⟩
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hx₀₁ hx₀₂
    -- the composite `𝒪ₓ ⟶ L ⟶ 𝒪ₓ` is multiplication by a global function which does not vanish
    -- at `x₀`, hence is a unit because `Γ(X, 𝒪ₓ)` is a field
    obtain ⟨ψ, hψ⟩ : ∃ ψ : L ⟶ 𝟙_ X.Modules, ψ = (ρ_ L).inv ≫ (L ◁ h) ≫ e.hom := ⟨_, rfl⟩
    have hfib : IsIso (fiberMap (g ≫ ψ) x₀) := by
      rw [hψ]
      exact isIso_fiberMap_pairing_of_ne_zero hL hN e g h hx₀₁ hx₀₂
    obtain ⟨χ, hχ⟩ : ∃ χ : X.structureModules ⟶ X.structureModules,
        χ = (tensorUnitIso X.sheaf).inv ≫ (g ≫ ψ) ≫ (tensorUnitIso X.sheaf).hom := ⟨_, rfl⟩
    have hχfib : IsIso (fiberMap χ x₀) := by
      rw [hχ, fiberMap_comp, fiberMap_comp]
      infer_instance
    have hc : endSection χ ≠ 0 := fun hz ↦
      fiberMap_ne_zero_of_isIso_fiberMap χ x₀ hχfib
        ((fiberMap_eq_zero_iff_evaluation_endSection χ x₀).2 (by simp only [hz, map_zero]))
    have hχIso : IsIso χ :=
      (isIso_iff_isUnit_endSection χ).2 (isUnit_iff_exists_inv.mpr (hfield.mul_inv_cancel hc))
    rw [hχ] at hχIso
    have hright : IsIso ((g ≫ ψ) ≫ (tensorUnitIso X.sheaf).hom) :=
      IsIso.of_isIso_comp_left (tensorUnitIso X.sheaf).inv _
    have : IsIso (g ≫ ψ) := IsIso.of_isIso_comp_right _ (tensorUnitIso X.sheaf).hom
    -- so `g` is non-zero on every fibre, and the fibrewise criterion makes it an isomorphism
    have hall (x : X) : fiberMap g x ≠ 0 := by
      intro hz
      have := nontrivial_fiber hone x
      exact fiberMap_ne_zero_of_isIso (g ≫ ψ) x (by rw [fiberMap_comp, hz, Limits.zero_comp])
    have : IsIso g := isIso_of_forall_fiberMap_ne_zero hone hL g hall
    exact ⟨(asIso g).symm⟩

/-- **The triviality criterion for a line bundle on an integral scheme, universally closed over a
field.** Let `K` be a field, let `π : X ⟶ Spec K` be universally closed with `X` integral and let
`L` and `N` be `𝒪ₓ`-modules with `L ⊗ N ≅ 𝒪ₓ`. Then `L` is trivial if and only if both
`Γ(X, L)` and `Γ(X, N)` are non-zero. -/
theorem nonempty_iso_tensorUnit_iff_of_universallyClosed {K : Type u} [Field K]
    (π : X ⟶ Spec (.of K)) [IsIntegral X] [UniversallyClosed π] (e : L ⊗ N ≅ 𝟙_ X.Modules) :
    Nonempty (L ≅ 𝟙_ X.Modules) ↔ Nontrivial Γ(L, ⊤) ∧ Nontrivial Γ(N, ⊤) :=
  nonempty_iso_tensorUnit_iff_of_isField (isField_of_universallyClosed K π) e

/-- **The triviality criterion for a line bundle on a proper geometrically integral scheme over a
field.** Let `K` be a field, let `X` be proper and geometrically integral over `K` and let `L`
and `N` be `𝒪ₓ`-modules with `L ⊗ N ≅ 𝒪ₓ`. Then `L` is trivial if and only if both `Γ(X, L)` and
`Γ(X, N)` are non-zero. The field `K` need not be algebraically closed.

This is `lem:cube-triviality-criterion` of the blueprint. -/
theorem nonempty_iso_tensorUnit_iff_of_geometricallyIntegral (K : Type u) [Field K]
    [X.Over (Spec (.of K))] [IsProper (X ↘ Spec (.of K))]
    [GeometricallyIntegral (X ↘ Spec (.of K))] (e : L ⊗ N ≅ 𝟙_ X.Modules) :
    Nonempty (L ≅ 𝟙_ X.Modules) ↔ Nontrivial Γ(L, ⊤) ∧ Nontrivial Γ(N, ⊤) :=
  have : IsIntegral X := GeometricallyIntegral.isIntegral (X ↘ Spec (.of K))
  nonempty_iso_tensorUnit_iff_of_universallyClosed (X ↘ Spec (.of K)) e

/-! ### The product of two sections -/

section Pairing

/-- **The product `s ⊗ u` of a global section `s` of `L` and a global section `u` of `N`**, for a
tensor inverse pair `e : L ⊗ N ≅ 𝒪ₓ`: the composite

```
     homOfSectionTop L s        (ρ_ L).inv         L ◁ (· u)          e
𝒪ₓ ─────────────────────→ L ─────────────→ L ⊗ 𝒪ₓ ───────────→ L ⊗ N ───→ 𝒪ₓ
```

that is, the product `CategoryTheory.MonoidalCategory.pairing` of the two multiplication
morphisms `AlgebraicGeometry.Scheme.Modules.homOfSectionTop`. -/
noncomputable def pairingHom (e : L ⊗ N ≅ 𝟙_ X.Modules) (s : Γ(L, ⊤)) (u : Γ(N, ⊤)) :
    𝟙_ X.Modules ⟶ 𝟙_ X.Modules :=
  pairing e ((tensorUnitIsoUnit X).hom ≫ homOfSectionTop L s)
    ((tensorUnitIsoUnit X).hom ≫ homOfSectionTop N u)

/-- The product of two morphisms out of the tensor unit vanishes on the fibre at `x` as soon as
its first factor does. -/
lemma fiberMap_pairing_eq_zero_of_left (e : L ⊗ N ≅ 𝟙_ X.Modules) (g : 𝟙_ X.Modules ⟶ L)
    (h : 𝟙_ X.Modules ⟶ N) {x : X} (hg : fiberMap g x = 0) :
    fiberMap (pairing e g h) x = 0 := by
  rw [pairing]
  exact fiberMap_comp_eq_zero_of_left _ _ x hg

/-- The product of two morphisms out of the tensor unit vanishes on the fibre at `x` as soon as
its second factor does. -/
lemma fiberMap_pairing_eq_zero_of_right (e : L ⊗ N ≅ 𝟙_ X.Modules) (g : 𝟙_ X.Modules ⟶ L)
    (h : 𝟙_ X.Modules ⟶ N) {x : X} (hh : fiberMap h x = 0) :
    fiberMap (pairing e g h) x = 0 := by
  rw [pairing_eq]
  exact fiberMap_comp_eq_zero_of_right _ _ x
    (fiberMap_comp_eq_zero_of_left _ _ x (fiberMap_tensorHom_eq_zero_of_right g h hh))

/-- The product of two sections vanishes on the fibre at `x` if the first one does. -/
lemma fiberMap_pairingHom_eq_zero_of_left (e : L ⊗ N ≅ 𝟙_ X.Modules) {s : Γ(L, ⊤)} {u : Γ(N, ⊤)}
    {x : X} (hs : fiberMap (homOfSectionTop L s) x = 0) : fiberMap (pairingHom e s u) x = 0 :=
  fiberMap_pairing_eq_zero_of_left e _ _ (fiberMap_comp_eq_zero_of_right _ _ x hs)

/-- The product of two sections vanishes on the fibre at `x` if the second one does. -/
lemma fiberMap_pairingHom_eq_zero_of_right (e : L ⊗ N ≅ 𝟙_ X.Modules) {s : Γ(L, ⊤)} {u : Γ(N, ⊤)}
    {x : X} (hu : fiberMap (homOfSectionTop N u) x = 0) : fiberMap (pairingHom e s u) x = 0 :=
  fiberMap_pairing_eq_zero_of_right e _ _ (fiberMap_comp_eq_zero_of_right _ _ x hu)

/-- **The product of two sections which vanish nowhere on the fibre at `x` vanishes nowhere on it
either**: at `x` both factors are isomorphisms of one-dimensional `κ(x)`-vector spaces, hence so
is their product. -/
lemma fiberMap_pairingHom_ne_zero (e : L ⊗ N ≅ 𝟙_ X.Modules) {s : Γ(L, ⊤)} {u : Γ(N, ⊤)} {x : X}
    (hs : fiberMap (homOfSectionTop L s) x ≠ 0) (hu : fiberMap (homOfSectionTop N u) x ≠ 0) :
    fiberMap (pairingHom e s u) x ≠ 0 :=
  have : Nontrivial ((𝟙_ X.Modules).fiber x) :=
    nontrivial_fiber (invertible_tensorUnit X.sheaf) x
  fiberMap_ne_zero_of_isIso_fiberMap _ x
    (isIso_fiberMap_pairing_of_ne_zero (Invertible.left (R := X.sheaf) e)
      (Invertible.right (R := X.sheaf) e) e _ _
      (fun h ↦ hs ((fiberMap_isoComp_left_eq_zero_iff _ _ x).1 h))
      (fun h ↦ hu ((fiberMap_isoComp_left_eq_zero_iff _ _ x).1 h)))

end Pairing

/-! ### The product of two sections near a point of the base -/

section PairingOfNhds

variable {W T : Scheme.{u}} (f : W ⟶ T) {V : T.Opens} {L N : W.Modules}
  (e : L ⊗ N ≅ 𝟙_ W.Modules) (s : Γ((pushforward f).obj L, V)) (u : Γ((pushforward f).obj N, V))

/-- **The product `s ⊗ u`** of a section of `f _* L` and a section of `f _* N` over an open `V`
of the base, as an endomorphism of the structure sheaf of the open subscheme `f ⁻¹ᵁ V`: the two
sections are global sections of the restrictions of `L` and of `N` to `f ⁻¹ᵁ V`, by
`AlgebraicGeometry.Scheme.Modules.sectionsOfNhds`. -/
noncomputable def pairingHomOfNhds :
    𝟙_ (f ⁻¹ᵁ V).toScheme.Modules ⟶ 𝟙_ (f ⁻¹ᵁ V).toScheme.Modules :=
  pairingHom (Functor.Monoidal.mapIsoTensorUnit (pullback (f ⁻¹ᵁ V).ι) e)
    (sectionsOfNhds f L V s) (sectionsOfNhds f N V u)

/-- The product of two sections vanishes at a point of the fibre over `t` if the restriction of
the first one to that fibre vanishes. -/
lemma fiberMap_pairingHomOfNhds_eq_zero_of_left {t : T} (ht : t ∈ V) (x : f.fiber t)
    (h : fiberSectionsOfNhds f L t V ht s = 0) :
    fiberMap (pairingHomOfNhds f e s u) (f.fiberLift ht x) = 0 := by
  refine fiberMap_pairingHom_eq_zero_of_left _ ?_
  refine (fiberMap_homOfSectionTop_eq_zero_iff_over (f.fiberLift ht) (f.fiberLift_ι ht) L
    (sectionsOfNhds f L V s) x).2 ?_
  rw [sectionsPullbackOver_fiberLift_sectionsOfNhds f L ht s, h,
    (homOfSectionTop_eq_zero_iff _ _).2 rfl]
  exact fiberMap_zero _ _ x

/-- The product of two sections vanishes at a point of the fibre over `t` if the restriction of
the second one to that fibre vanishes. -/
lemma fiberMap_pairingHomOfNhds_eq_zero_of_right {t : T} (ht : t ∈ V) (x : f.fiber t)
    (h : fiberSectionsOfNhds f N t V ht u = 0) :
    fiberMap (pairingHomOfNhds f e s u) (f.fiberLift ht x) = 0 := by
  refine fiberMap_pairingHom_eq_zero_of_right _ ?_
  refine (fiberMap_homOfSectionTop_eq_zero_iff_over (f.fiberLift ht) (f.fiberLift_ι ht) N
    (sectionsOfNhds f N V u) x).2 ?_
  rw [sectionsPullbackOver_fiberLift_sectionsOfNhds f N ht u, h,
    (homOfSectionTop_eq_zero_iff _ _).2 rfl]
  exact fiberMap_zero _ _ x

/-- **The product of two sections does not vanish at a point of a fibre at which neither of their
restrictions to that fibre does.** -/
lemma fiberMap_pairingHomOfNhds_ne_zero {t : T} (ht : t ∈ V) (x : f.fiber t)
    (hsx : fiberMk ((restrictToFiber f t).obj L) x (fiberSectionsOfNhds f L t V ht s) ≠ 0)
    (hux : fiberMk ((restrictToFiber f t).obj N) x (fiberSectionsOfNhds f N t V ht u) ≠ 0) :
    fiberMap (pairingHomOfNhds f e s u) (f.fiberLift ht x) ≠ 0 := by
  refine fiberMap_pairingHom_ne_zero _ ?_ ?_
  · intro hz
    rw [fiberMap_homOfSectionTop_eq_zero_iff_over (f.fiberLift ht) (f.fiberLift_ι ht) L
      (sectionsOfNhds f L V s) x, sectionsPullbackOver_fiberLift_sectionsOfNhds f L ht s] at hz
    refine fiberMap_ne_zero_of_fiberMk_ne_zero _ x (oneSection (f.fiber t) ⊤) ?_ hz
    rwa [app_homOfSectionTop_oneSection]
  · intro hz
    rw [fiberMap_homOfSectionTop_eq_zero_iff_over (f.fiberLift ht) (f.fiberLift_ι ht) N
      (sectionsOfNhds f N V u) x, sectionsPullbackOver_fiberLift_sectionsOfNhds f N ht u] at hz
    refine fiberMap_ne_zero_of_fiberMk_ne_zero _ x (oneSection (f.fiber t) ⊤) ?_ hz
    rwa [app_homOfSectionTop_oneSection]

end PairingOfNhds

/-! ### The criterion on the fibres of a morphism -/

section Fibre

variable {W T : Scheme.{u}}

/-- **Triviality of `L` on the fibre over `t` is the non-vanishing of the two fibrewise spaces of
sections** `Γ(W_t, L_t)` and `Γ(W_t, N_t)`, where `N` is a tensor inverse of `L`.

This is `AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_iff_of_universallyClosed` read
on the fibre `W_t`, which is integral and universally closed over the residue field `κ(t)` — a
field which is not assumed algebraically closed. -/
theorem nonempty_restrictToFiber_iso_structureModules_iff_nontrivial (f : W ⟶ T)
    [UniversallyClosed f] {L N : W.Modules} (e : L ⊗ N ≅ 𝟙_ W.Modules) (t : T)
    [GeometricallyIntegral (f.fiberToSpecResidueField t)] :
    Nonempty ((restrictToFiber f t).obj L ≅ (f.fiber t).structureModules) ↔
      Nontrivial Γ((restrictToFiber f t).obj L, ⊤) ∧
        Nontrivial Γ((restrictToFiber f t).obj N, ⊤) :=
  have : IsIntegral (f.fiber t) := GeometricallyIntegral.isIntegral (f.fiberToSpecResidueField t)
  nonempty_iso_structureModules_iff.trans
    (nonempty_iso_tensorUnit_iff_of_universallyClosed (f.fiberToSpecResidueField t)
      (Functor.Monoidal.mapIsoTensorUnit (restrictToFiber f t) e))

end Fibre

end Modules

end AlgebraicGeometry.Scheme
