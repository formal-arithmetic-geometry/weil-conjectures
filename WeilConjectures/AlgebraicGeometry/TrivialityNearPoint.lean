/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FormalTriviality
public import WeilConjectures.AlgebraicGeometry.Modules.TrivialityCriterion
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Formal triviality is triviality near the point

Let `X` be a proper geometrically integral variety over a field `K`, let `T` be a locally
Noetherian `K`-scheme, let `t₀` be a point of `T` and let `L` be a line bundle on `X × T` whose
pullback to `X × Tₙ` is trivial for every `n`, where `Tₙ = Spec (𝒪_{T, t₀} ⧸ 𝔪 ^ (n + 1))`. This
file proves that `L` is then trivial on the fibre `X_t` for every `t` in some open neighbourhood
of `t₀`.

The input is `AlgebraicGeometry.Scheme.Modules.exists_fiberSectionsOfNhds_pullbackSnd_ne_zero`:
formal triviality produces a section `s` of `L` over `p_T ⁻¹ᵁ V₁` whose restriction to the fibre
`X_{t₀}` is non-zero, and likewise a section `u` of a tensor inverse `N` of `L` over
`p_T ⁻¹ᵁ V₂`. What this file adds is the argument that runs on those two sections: their
**product** `s ⊗ u` is a global function on `p_T ⁻¹ᵁ (V₁ ⊓ V₂)` which does not vanish anywhere on
the fibre `X_{t₀}`, because `L_{t₀}` is trivial and a non-zero section of a trivial line bundle
on a proper integral scheme vanishes nowhere
(`AlgebraicGeometry.Scheme.Modules.fiberMk_ne_zero_of_universallyClosed`); since `p_T` is a closed
map, the non-vanishing locus of `s ⊗ u` therefore contains the whole preimage of an open
neighbourhood `V` of `t₀`; and at a point `t` of `V` the non-vanishing of `s ⊗ u` on `X_t` forces
both `s` and `u` to be non-zero there, so that the triviality criterion over the residue field
`κ(t)` (`AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_iff_of_universallyClosed`)
makes `L_t` trivial.

## The product of two sections

The product `s ⊗ u` is not taken as a *section* of `L ⊗ N` but as the **endomorphism**
`AlgebraicGeometry.Scheme.Modules.pairingHom` of the structure sheaf obtained by composing
multiplication by `s`, whiskering by multiplication by `u` and the isomorphism `L ⊗ N ≅ 𝒪`. That
is the same thing, and it is the form in which it transports to a fibre: a morphism of sheaves of
modules pulls back functorially, whereas a section does not without the monoidal structure of the
pullback of sections, which is not available. Multiplication by a section does pull back to
multiplication by the pulled back section, by
`AlgebraicGeometry.Scheme.Modules.map_homOfSectionTop`, and that is what makes the argument run.

## Main statements

All three are in the namespace `AlgebraicGeometry.Scheme.Modules`.

- `pairingHom`: the product of a global section of `L` and a global section of `N`, for
  `e : L ⊗ N ≅ 𝒪`, as an endomorphism of the structure sheaf, together with
  `fiberMap_pairingHom_ne_zero` and the two statements `fiberMap_pairingHom_eq_zero_left` and
  `fiberMap_pairingHom_eq_zero_right` which say that it is non-zero on a fibre exactly when both
  factors are.
- `exists_mem_forall_nonempty_restrictToFiber_iso_structureModules`: **the open neighbourhood**,
  for an arbitrary proper morphism `f : W ⟶ T` with geometrically integral fibres, two sections
  of `f _* L` and `f _* N` over an open neighbourhood `V` of `t₀` which are non-zero on the fibre
  over `t₀`, and `L` trivial on that fibre.
- `exists_mem_forall_nonempty_restrictToFiber_pullbackSnd_iso_structureModules`: **formal
  triviality is triviality near the point**, the statement of the blueprint.

## Implementation notes

* Only the last statement is `sorry`-tainted, and only through
  `AlgebraicGeometry.Scheme.Modules.exists_fiberSectionsOfNhds_pullbackSnd_ne_zero`, which is
  applied once. Everything else, including the open-neighbourhood theorem, is `sorry`-free: the
  triviality criterion is used in the form
  `AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_iff_of_universallyClosed` rather than
  through `AlgebraicGeometry.Scheme.Modules.nonempty_restrictToFiber_iso_structureModules_iff`,
  which passes through the fibrewise dimension and hence through the coherence of a direct image.
* The blueprint shrinks `V` to an affine open and identifies `Γ(X × V, 𝒪)` with `Γ(V, 𝒪_V)` by
  base change, then takes the non-vanishing locus of `s ⊗ u` downstairs. Neither the shrinking
  nor the base change is needed: the non-vanishing locus of `s ⊗ u` is an open subset of
  `p_T ⁻¹ᵁ V` containing the fibre over `t₀`, and the complement of the image of its complement
  is the required neighbourhood because a proper morphism is a closed map. The `s ⊗ u` argument
  itself, Steps 4 and 5 of the blueprint proof, is unchanged.

## Blueprint

`prop:cube-formal-triviality` of
`blueprint/src/version/detailed/curve_estimates/27_theorem_of_the_cube.tex`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Opposite SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-!
### The product of two sections
-/

section Pairing

variable {X : Scheme.{u}} {L N : X.Modules}

/-- If a morphism out of the tensor unit is zero on the fibre at `x`, then so is its tensor
product with any other morphism. -/
lemma fiberMap_tensorHom_eq_zero_right (g : 𝟙_ X.Modules ⟶ L) (h : 𝟙_ X.Modules ⟶ N) {x : X}
    (hh : fiberMap h x = 0) : fiberMap (g ⊗ₘ h) x = 0 := by
  have hnat := fiberTensorIso_hom_naturality g h x
  rw [hh, MonoidalPreadditive.tensor_zero, Limits.comp_zero] at hnat
  exact (Preadditive.IsIso.comp_right_eq_zero _ (fiberTensorIso L N x).hom).1 hnat.symm

/-- The composite of the triviality criterion vanishes on the fibre at `x` as soon as its second
factor does. -/
lemma fiberMap_pairing_eq_zero_of_right (e : L ⊗ N ≅ 𝟙_ X.Modules) (g : 𝟙_ X.Modules ⟶ L)
    (h : 𝟙_ X.Modules ⟶ N) {x : X} (hh : fiberMap h x = 0) :
    fiberMap (g ≫ (ρ_ L).inv ≫ (L ◁ h) ≫ e.hom) x = 0 := by
  have hfac : g ≫ (ρ_ L).inv ≫ (L ◁ h) ≫ e.hom
      = (λ_ (𝟙_ X.Modules)).inv ≫ (g ⊗ₘ h) ≫ e.hom := by
    rw [rightUnitor_inv_naturality_assoc, tensorHom_def, unitors_inv_equal]
    simp
  rw [hfac, fiberMap_comp, fiberMap_comp, fiberMap_tensorHom_eq_zero_right g h hh,
    Limits.zero_comp, Limits.comp_zero]

/-- **The product `s ⊗ u` of a global section `m` of `L` and a global section `n` of `N`**, for a
tensor inverse pair `e : L ⊗ N ≅ 𝒪ₓ`: the endomorphism of the structure sheaf obtained by
composing multiplication by `m`, whiskering by multiplication by `n`, and `e`. -/
def pairingHom (e : L ⊗ N ≅ 𝟙_ X.Modules) (m : Γ(L, ⊤)) (n : Γ(N, ⊤)) :
    𝟙_ X.Modules ⟶ 𝟙_ X.Modules :=
  ((tensorUnitIsoUnit X).hom ≫ homOfSectionTop L m) ≫ (ρ_ L).inv ≫
    (L ◁ ((tensorUnitIsoUnit X).hom ≫ homOfSectionTop N n)) ≫ e.hom

/-- **The product of two sections which vanish nowhere on the fibre at `x` vanishes nowhere on
it either**: at `x` both factors are isomorphisms of one-dimensional `κ(x)`-vector spaces, hence
so is their product. -/
lemma fiberMap_pairingHom_ne_zero (hL : L.Invertible) (hN : N.Invertible)
    (e : L ⊗ N ≅ 𝟙_ X.Modules) {m : Γ(L, ⊤)} {n : Γ(N, ⊤)} {x : X}
    (hm : fiberMap (homOfSectionTop L m) x ≠ 0) (hn : fiberMap (homOfSectionTop N n) x ≠ 0) :
    fiberMap (pairingHom e m n) x ≠ 0 :=
  have : Nontrivial ((𝟙_ X.Modules).fiber x) :=
    nontrivial_fiber (SheafOfModules.invertible_tensorUnit X.sheaf) x
  fiberMap_ne_zero_of_isIso_fiberMap _ x
    (isIso_fiberMap_comp_of_ne_zero hL hN e _ _
      (fun h ↦ hm ((fiberMap_isoComp_left_eq_zero_iff _ _ x).1 h))
      (fun h ↦ hn ((fiberMap_isoComp_left_eq_zero_iff _ _ x).1 h)))

/-- **The product of two sections vanishes on the fibre at `x` if the first one does.** -/
lemma fiberMap_pairingHom_eq_zero_left (e : L ⊗ N ≅ 𝟙_ X.Modules) {m : Γ(L, ⊤)} {n : Γ(N, ⊤)}
    {x : X} (hm : fiberMap (homOfSectionTop L m) x = 0) : fiberMap (pairingHom e m n) x = 0 :=
  fiberMap_comp_eq_zero_of_left _ _ x (fiberMap_comp_eq_zero_of_right _ _ x hm)

/-- **The product of two sections vanishes on the fibre at `x` if the second one does.** -/
lemma fiberMap_pairingHom_eq_zero_right (e : L ⊗ N ≅ 𝟙_ X.Modules) {m : Γ(L, ⊤)} {n : Γ(N, ⊤)}
    {x : X} (hn : fiberMap (homOfSectionTop N n) x = 0) : fiberMap (pairingHom e m n) x = 0 :=
  fiberMap_pairing_eq_zero_of_right e _ _ (fiberMap_comp_eq_zero_of_right _ _ x hn)

end Pairing

/-!
### The product of two sections near a point of the base
-/

section PairingOfNhds

variable {W T : Scheme.{u}} (f : W ⟶ T) {V : T.Opens} {L N : W.Modules}
  (e : L ⊗ N ≅ 𝟙_ W.Modules) (s : Γ((pushforward f).obj L, V)) (v : Γ((pushforward f).obj N, V))

/-- **The product `s ⊗ u`** of a section of `f _* L` and a section of `f _* N` over an open `V`
of the base, as an endomorphism of the structure sheaf of the open subscheme `f ⁻¹ᵁ V`. -/
def pairingHomOfNhds : 𝟙_ (f ⁻¹ᵁ V).toScheme.Modules ⟶ 𝟙_ (f ⁻¹ᵁ V).toScheme.Modules :=
  pairingHom (Functor.Monoidal.mapIsoTensorUnit (pullback (f ⁻¹ᵁ V).ι) e)
    (sectionOfNhds f L s) (sectionOfNhds f N v)

lemma fiberMap_pairingHomOfNhds_eq_zero_of_left {t : T} (ht : t ∈ V) (x : f.fiber t)
    (h : fiberSectionsOfNhds f L t V ht s = 0) :
    fiberMap (pairingHomOfNhds f e s v) (f.fiberLift ht x) = 0 := by
  refine fiberMap_pairingHom_eq_zero_left _ ?_
  refine (fiberMap_homOfSectionTop_eq_zero_iff_over (f.fiberLift ht) (f.fiberLift_ι ht) L
    (sectionOfNhds f L s) x).2 ?_
  rw [sectionsPullbackOver_fiberLift_sectionOfNhds f L ht s, h,
    (homOfSectionTop_eq_zero_iff _ _).2 rfl]
  exact fiberMap_zero _ _ x

lemma fiberMap_pairingHomOfNhds_eq_zero_of_right {t : T} (ht : t ∈ V) (x : f.fiber t)
    (h : fiberSectionsOfNhds f N t V ht v = 0) :
    fiberMap (pairingHomOfNhds f e s v) (f.fiberLift ht x) = 0 := by
  refine fiberMap_pairingHom_eq_zero_right _ ?_
  refine (fiberMap_homOfSectionTop_eq_zero_iff_over (f.fiberLift ht) (f.fiberLift_ι ht) N
    (sectionOfNhds f N v) x).2 ?_
  rw [sectionsPullbackOver_fiberLift_sectionOfNhds f N ht v, h,
    (homOfSectionTop_eq_zero_iff _ _).2 rfl]
  exact fiberMap_zero _ _ x

/-- **The product of two sections does not vanish at a point of a fibre at which neither of their
restrictions to that fibre does.** -/
lemma fiberMap_pairingHomOfNhds_ne_zero (hL : L.Invertible) (hN : N.Invertible)
    {t : T} (ht : t ∈ V) (x : f.fiber t)
    (hsx : fiberMk ((restrictToFiber f t).obj L) x (fiberSectionsOfNhds f L t V ht s) ≠ 0)
    (hvx : fiberMk ((restrictToFiber f t).obj N) x (fiberSectionsOfNhds f N t V ht v) ≠ 0) :
    fiberMap (pairingHomOfNhds f e s v) (f.fiberLift ht x) ≠ 0 := by
  refine fiberMap_pairingHom_ne_zero (SheafOfModules.Invertible.pullback (f ⁻¹ᵁ V).ι hL)
    (SheafOfModules.Invertible.pullback (f ⁻¹ᵁ V).ι hN) _ ?_ ?_
  · refine fun hz ↦ ?_
    rw [fiberMap_homOfSectionTop_eq_zero_iff_over (f.fiberLift ht) (f.fiberLift_ι ht) L
      (sectionOfNhds f L s) x, sectionsPullbackOver_fiberLift_sectionOfNhds f L ht s] at hz
    refine fiberMap_ne_zero_of_fiberMk_ne_zero _ x (oneSection (f.fiber t) ⊤) ?_ hz
    rwa [app_homOfSectionTop_oneSection]
  · refine fun hz ↦ ?_
    rw [fiberMap_homOfSectionTop_eq_zero_iff_over (f.fiberLift ht) (f.fiberLift_ι ht) N
      (sectionOfNhds f N v) x, sectionsPullbackOver_fiberLift_sectionOfNhds f N ht v] at hz
    refine fiberMap_ne_zero_of_fiberMk_ne_zero _ x (oneSection (f.fiber t) ⊤) ?_ hz
    rwa [app_homOfSectionTop_oneSection]

end PairingOfNhds

/-!
### Two consequences of an isomorphism of sheaves of modules
-/

section Transport

/-- **Pulling back along an isomorphism of schemes reflects isomorphisms** of sheaves of
modules. -/
lemma nonempty_iso_of_pullbackIso {Y Z : Scheme.{u}} (h : Z ⟶ Y) [IsIso h] {M M' : Y.Modules}
    (i : (pullback h).obj M ≅ (pullback h).obj M') : Nonempty (M ≅ M') :=
  letI c : pullback h ⋙ pullback (inv h) ≅ 𝟭 Y.Modules :=
    pullbackComp (inv h) h ≪≫ pullbackCongr (IsIso.inv_hom_id h) ≪≫ pullbackId Y
  ⟨(c.app M).symm ≪≫ (pullback (inv h)).mapIso i ≪≫ c.app M'⟩

/-- **A tensor inverse of a trivial sheaf of modules is trivial.** -/
lemma nonempty_iso_structureModules_of_tensorUnit {Y : Scheme.{u}} {M M' : Y.Modules}
    (e : M ⊗ M' ≅ 𝟙_ Y.Modules) (i : M ≅ Y.structureModules) :
    Nonempty (M' ≅ Y.structureModules) :=
  ⟨(λ_ M').symm ≪≫ ((i ≪≫ (tensorUnitIsoUnit Y).symm).symm ⊗ᵢ Iso.refl M') ≪≫ e ≪≫
    tensorUnitIsoUnit Y⟩

end Transport

/-!
### The open neighbourhood
-/

section NearPoint

variable {W T : Scheme.{u}}

/-- **A line bundle trivial on one fibre and carrying sections which are non-zero there is
trivial on every fibre over an open neighbourhood.**

Let `f : W ⟶ T` be a proper morphism all of whose fibres are geometrically integral, let `L` and
`N` be sheaves of modules on `W` with `e : L ⊗ N ≅ 𝒪_W`, and let `t₀` be a point of `T` at which
`L` restricts to a trivial sheaf on the fibre `W_{t₀}`. If `L` and `N` have sections over
`f ⁻¹ᵁ V`, for an open neighbourhood `V` of `t₀`, whose restrictions to `W_{t₀}` are non-zero,
then `L` is trivial on the fibre `W_t` for every `t` in some open neighbourhood of `t₀`.

This is Steps 4 and 5 of the proof of `prop:cube-formal-triviality` of the blueprint. -/
theorem exists_mem_forall_nonempty_restrictToFiber_iso_structureModules
    (f : W ⟶ T) [IsProper f] {L N : W.Modules} (e : L ⊗ N ≅ 𝟙_ W.Modules)
    (hgeom : ∀ t : T, GeometricallyIntegral (f.fiberToSpecResidueField t))
    {t₀ : T} {V : T.Opens} (hV : t₀ ∈ V)
    (hL₀ : Nonempty ((restrictToFiber f t₀).obj L ≅ (f.fiber t₀).structureModules))
    (s : Γ((pushforward f).obj L, V)) (hs : fiberSectionsOfNhds f L t₀ V hV s ≠ 0)
    (v : Γ((pushforward f).obj N, V)) (hv : fiberSectionsOfNhds f N t₀ V hV v ≠ 0) :
    ∃ V' : T.Opens, t₀ ∈ V' ∧ ∀ t ∈ V',
      Nonempty ((restrictToFiber f t).obj L ≅ (f.fiber t).structureModules) := by
  have hL : L.Invertible := SheafOfModules.Invertible.left (R := W.sheaf) e
  have hN : N.Invertible := SheafOfModules.Invertible.right (R := W.sheaf) e
  -- the locus, inside `f ⁻¹ᵁ V`, on which the product of `s` and `v` does not vanish
  set Ω : Set W := (f ⁻¹ᵁ V).ι.base ''
    {y : (f ⁻¹ᵁ V).toScheme | fiberMap (pairingHomOfNhds f e s v) y ≠ 0} with hΩ
  have hΩopen : IsOpen Ω :=
    (f ⁻¹ᵁ V).ι.isOpenEmbedding.isOpenMap _
      (isClosed_setOf_fiberMap_eq_zero
        (SheafOfModules.invertible_tensorUnit (f ⁻¹ᵁ V).toScheme.sheaf)
        (SheafOfModules.invertible_tensorUnit (f ⁻¹ᵁ V).toScheme.sheaf)
        (pairingHomOfNhds f e s v)).isOpen_compl
  have hclosed : IsClosed (f.base '' Ωᶜ) := f.isClosedMap _ hΩopen.isClosed_compl
  -- a point of the fibre over `t` lies in `Ω` exactly when the product does not vanish there
  have hmem : ∀ (t : T) (ht : t ∈ V) (x : f.fiber t),
      f.fiberι t x ∈ Ω ↔ fiberMap (pairingHomOfNhds f e s v) (f.fiberLift ht x) ≠ 0 := by
    refine fun t ht x ↦ ⟨fun ⟨y, hy, hxy⟩ ↦ ?_, fun hx ↦ ⟨f.fiberLift ht x, hx, ?_⟩⟩
    · have hyx : y = f.fiberLift ht x :=
        (f ⁻¹ᵁ V).ι.isEmbedding.injective (hxy.trans (f.fiberLift_apply ht x).symm)
      rwa [hyx] at hy
    · exact f.fiberLift_apply ht x
  refine ⟨⟨(V : Set T) \ f.base '' Ωᶜ, V.2.sdiff hclosed⟩, ⟨hV, ?_⟩, ?_⟩
  · -- the product does not vanish anywhere on the fibre over `t₀`, because `L` is trivial there
    have hg₀ : GeometricallyIntegral (f.fiberToSpecResidueField t₀) := hgeom t₀
    have : IsIntegral (f.fiber t₀) :=
      GeometricallyIntegral.isIntegral (K := ↥(T.residueField t₀))
        (f.fiberToSpecResidueField t₀)
    have hLunit : (restrictToFiber f t₀).obj L ≅ (f.fiber t₀).structureModules := hL₀.some
    have hNunit : (restrictToFiber f t₀).obj N ≅ (f.fiber t₀).structureModules :=
      (nonempty_iso_structureModules_of_tensorUnit
        (Functor.Monoidal.mapIsoTensorUnit (restrictToFiber f t₀) e) hLunit).some
    rintro ⟨w, hw, hwt⟩
    obtain ⟨x, rfl⟩ : ∃ x : f.fiber t₀, f.fiberι t₀ x = w := (f.range_fiberι t₀).ge hwt
    exact hw ((hmem _ hV x).2 (fiberMap_pairingHomOfNhds_ne_zero f e s v hL hN hV x
      (fiberMk_ne_zero_of_universallyClosed (K := ↥(T.residueField t₀))
        (f.fiberToSpecResidueField t₀) hLunit hs x)
      (fiberMk_ne_zero_of_universallyClosed (K := ↥(T.residueField t₀))
        (f.fiberToSpecResidueField t₀) hNunit hv x)))
  · rintro t ⟨htV, htn⟩
    have hgt : GeometricallyIntegral (f.fiberToSpecResidueField t) := hgeom t
    have : IsIntegral (f.fiber t) :=
      GeometricallyIntegral.isIntegral (K := ↥(T.residueField t)) (f.fiberToSpecResidueField t)
    obtain ⟨x⟩ : Nonempty (f.fiber t) := IsIntegral.nonempty
    have hne : fiberMap (pairingHomOfNhds f e s v) (f.fiberLift htV x) ≠ 0 := by
      refine fun hz ↦ htn ⟨f.fiberι t x, fun hcon ↦ ?_, f.apply_fiberι t x⟩
      exact ((hmem t htV x).1 hcon) hz
    rw [nonempty_iso_structureModules_iff,
      nonempty_iso_tensorUnit_iff_of_universallyClosed (K := ↥(T.residueField t))
        (f.fiberToSpecResidueField t) (Functor.Monoidal.mapIsoTensorUnit (restrictToFiber f t) e)]
    exact ⟨nontrivial_of_ne _ 0 fun h ↦
        hne (fiberMap_pairingHomOfNhds_eq_zero_of_left f e s v htV x h),
      nontrivial_of_ne _ 0 fun h ↦
        hne (fiberMap_pairingHomOfNhds_eq_zero_of_right f e s v htV x h)⟩

end NearPoint

/-!
### The projection of a proper variety
-/

section Projection

variable {X T : Scheme.{u}} {K : Type u} [Field K]

/-- **Formal triviality is triviality near the point.**

Let `X` be a proper geometrically integral variety over a field `K`, let `T` be a locally
Noetherian `K`-scheme, let `t₀` be a point of `T` and let `L` be a line bundle on `X × T` whose
pullback to `(X × T) ×_T Tₙ` is trivial for every `n`, where `Tₙ` is the `n`-th infinitesimal
neighbourhood of `t₀`. Then there is an open neighbourhood `V` of `t₀` such that the restriction
of `L` to the fibre `X_t` is trivial for every `t` in `V`.

This is `prop:cube-formal-triviality` of the blueprint. It rests on
`AlgebraicGeometry.Scheme.Modules.exists_fiberSectionsOfNhds_pullbackSnd_ne_zero`, which is
`sorry`-tainted by design, and is applied here once for `L` and once for its tensor inverse. -/
theorem exists_mem_forall_nonempty_restrictToFiber_pullbackSnd_iso_structureModules
    (πX : X ⟶ Spec (.of K)) [IsProper πX] [GeometricallyIntegral πX]
    (πT : T ⟶ Spec (.of K)) [IsLocallyNoetherian T] (t₀ : T)
    {L : (Limits.pullback πX πT).Modules} (hL : L.Invertible)
    (hF : ∀ n : ℕ, Nonempty
      ((pullback (infinitesimalBaseChangeFst (Limits.pullback.snd πX πT) t₀ n)).obj L ≅
        (infinitesimalBaseChange (Limits.pullback.snd πX πT) t₀ n).structureModules)) :
    ∃ V : T.Opens, t₀ ∈ V ∧ ∀ t ∈ V,
      Nonempty ((restrictToFiber (Limits.pullback.snd πX πT) t).obj L ≅
        ((Limits.pullback.snd πX πT).fiber t).structureModules) := by
  set f := Limits.pullback.snd πX πT with hf
  set N : (Limits.pullback πX πT).Modules := hL.tensorInv with hNdef
  have hN : N.Invertible := hNdef ▸ SheafOfModules.invertible_tensorInv hL
  have hLc : L.IsCoherent := hL.isCoherent
  have hNc : N.IsCoherent := hN.isCoherent
  -- `N` is trivial on every infinitesimal neighbourhood, because `L` is
  have hFN : ∀ n : ℕ, Nonempty
      ((pullback (infinitesimalBaseChangeFst f t₀ n)).obj N ≅
        (infinitesimalBaseChange f t₀ n).structureModules) := fun n ↦
    nonempty_iso_structureModules_of_tensorUnit
      (Functor.Monoidal.mapIsoTensorUnit (pullback (infinitesimalBaseChangeFst f t₀ n))
        hL.tensorInvIso) (hF n).some
  -- the restriction of `L` to the fibre over `t₀` is trivial, being its pullback to `T₀`
  have hL₀ : Nonempty ((restrictToFiber f t₀).obj L ≅ (f.fiber t₀).structureModules) :=
    nonempty_iso_of_pullbackIso (infinitesimalBaseChangeZeroIsoFiber f t₀).hom
      ((pullbackComp (infinitesimalBaseChangeZeroIsoFiber f t₀).hom (f.fiberι t₀)).app L ≪≫
        (pullbackCongr (infinitesimalBaseChangeZeroIsoFiber_hom_fiberι f t₀)).app L ≪≫
        (hF 0).some ≪≫
        (pullbackUnitIso (infinitesimalBaseChangeZeroIsoFiber f t₀).hom).symm)
  obtain ⟨V₁, hV₁, s, hs⟩ := exists_fiberSectionsOfNhds_pullbackSnd_ne_zero πX πT t₀ L hF
  obtain ⟨V₂, hV₂, v, hv⟩ := exists_fiberSectionsOfNhds_pullbackSnd_ne_zero πX πT t₀ N hFN
  refine exists_mem_forall_nonempty_restrictToFiber_iso_structureModules f hL.tensorInvIso
    (fun t ↦ inferInstance) (V := V₁ ⊓ V₂) ⟨hV₁, hV₂⟩ hL₀
    (((pushforward f).obj L).presheaf.map (homOfLE inf_le_left).op s) ?_
    (((pushforward f).obj N).presheaf.map (homOfLE inf_le_right).op v) ?_
  · exact fun hz ↦ hs
      ((ConcreteCategory.congr_hom (fiberSectionsOfNhds_map f L hV₁ inf_le_left
        ⟨hV₁, hV₂⟩) s).symm.trans ((ConcreteCategory.comp_apply _ _ s).trans hz))
  · exact fun hz ↦ hv
      ((ConcreteCategory.congr_hom (fiberSectionsOfNhds_map f N hV₂ inf_le_right
        ⟨hV₁, hV₂⟩) v).symm.trans ((ConcreteCategory.comp_apply _ _ v).trans hz))

end Projection

end

end AlgebraicGeometry.Scheme.Modules
