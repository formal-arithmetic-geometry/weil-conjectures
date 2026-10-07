/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmooth
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# The étale-local normal form of a smooth morphism

A smooth morphism of relative dimension `d` is, étale-locally on the source, the
projection of an affine space: if `g : X ⟶ Y` is smooth of relative dimension `d` and
`x : X`, then there are affine open neighbourhoods `V` of `x` and `U` of `g.base x` with
`V ≤ g ⁻¹ᵁ U` such that the restricted morphism `g.resLE U V` factors as an étale morphism
`V ⟶ 𝔸(d; U)` followed by the structure morphism `𝔸(d; U) ↘ U`.

The index type of the affine space is `ULift.{u} (Fin d)`, since
`AlgebraicGeometry.AffineSpace` takes an index type in the same universe as the scheme.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.exists_etale_to_affineSpace_of_isStandardSmoothOfRelativeDimension`:
  the normal form over a pair of affine opens on which the morphism is standard smooth.
- `AlgebraicGeometry.Smooth.exists_etale_to_affineSpace`: the étale-local normal form of a
  smooth morphism of relative dimension `d`.
- `AlgebraicGeometry.Scheme.Hom.exists_etale_to_affineSpace_of_mem_smoothLocus`: the étale-local
  normal form of a morphism near a point at which it is smooth.
- `AlgebraicGeometry.Smooth.exists_mem_etale_residueFieldMap`: in every fibre of a smooth
  morphism, the points with finite separable residue field extension are dense.
- `AlgebraicGeometry.Smooth.exists_etale_comp_of_etale_residueFieldMap`: through a point with
  finite separable residue field extension passes an étale slice.
- `AlgebraicGeometry.Smooth.exists_geometricallyIrreducible_of_section`: the relative connected
  component of a section of a smooth morphism is open, with geometrically irreducible fibres.
- `AlgebraicGeometry.smoothOfRelativeDimension_iff_topologicalKrullDim_eq`: an irreducible
  scheme smooth over a field is smooth of relative dimension `n` if and only if it has
  dimension `n`.
- `AlgebraicGeometry.topologicalKrullDim_le_of_smoothOfRelativeDimension`: a scheme smooth of
  relative dimension `n` over a field has dimension at most `n`.
- `AlgebraicGeometry.topologicalKrullDimAt_eq_of_smoothOfRelativeDimension`: a scheme smooth of
  relative dimension `n` over a field has local dimension `n` at every point.
- `AlgebraicGeometry.Smooth.isLocallyConstant_topologicalKrullDimAt_asFiber`: for a smooth
  morphism `f : X ⟶ Y`, the function `x ↦ dim_x (X_{f(x)})` is locally constant.
- `AlgebraicGeometry.AffineSpace.smoothOfRelativeDimension_over`: the affine space `𝔸(n; S)` in
  finitely many variables is smooth of relative dimension `#n` over `S`.
- `AlgebraicGeometry.AffineSpace.smoothOfRelativeDimension_reindex_succ`: forgetting the first
  coordinate `𝔸^{d+1}_S ⟶ 𝔸^d_S` is smooth of relative dimension one.
- `AlgebraicGeometry.Smooth.exists_smoothOfRelativeDimension_resLE`: a smooth morphism is
  locally smooth of some relative dimension.
- `AlgebraicGeometry.smoothOfRelativeDimension_pullback_fst`,
  `AlgebraicGeometry.smoothOfRelativeDimension_pullback_snd`: smoothness of relative dimension `n`
  is inherited by the projections of a fibre product.

## References

- Stacks Project, Tag `054L`, <https://stacks.math.columbia.edu/tag/054L>
- Stacks Project, Tags `056U`, `057G`, `055R`, <https://stacks.math.columbia.edu/tag/057G>
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Limits in
instance smoothOfRelativeDimension_pullback_fst {X Y Z : Scheme.{u}} (n : ℕ) (f : X ⟶ Z)
    (g : Y ⟶ Z) [SmoothOfRelativeDimension n g] :
    SmoothOfRelativeDimension n (pullback.fst f g) :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := n)
  MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension n) _ _ inferInstance

open Limits in
instance smoothOfRelativeDimension_pullback_snd {X Y Z : Scheme.{u}} (n : ℕ) (f : X ⟶ Z)
    (g : Y ⟶ Z) [SmoothOfRelativeDimension n f] :
    SmoothOfRelativeDimension n (pullback.snd f g) :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := n)
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension n) _ _ inferInstance

open MvPolynomial in
/-- Let `g : X ⟶ Y`, and let `U ⊆ Y`, `V ⊆ X` be affine opens with `V ≤ g ⁻¹ᵁ U` such that
`Γ(Y, U) ⟶ Γ(X, V)` is standard smooth of relative dimension `d`. Then `g.resLE U V hVU`
factors as an étale morphism `e : V ⟶ 𝔸(d; U)` followed by the projection `𝔸(d; U) ↘ U`:

```
V --e--> 𝔸(d; U)
 \          |
  \         ↓
g.resLE     U
```

On rings, this is `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`:
reading the last `d` variables of a submersive presentation as coordinates of the base turns
it into a square Jacobian presentation over `Γ(Y, U)[x₁, …, x_d]`. -/
theorem Scheme.Hom.exists_etale_to_affineSpace_of_isStandardSmoothOfRelativeDimension
    {X Y : Scheme.{u}} (g : X ⟶ Y) {d : ℕ} {U : Y.Opens} {V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hVU : V ≤ g ⁻¹ᵁ U)
    (H : (g.appLE U V hVU).hom.IsStandardSmoothOfRelativeDimension d) :
    ∃ e : V.toScheme ⟶ 𝔸(ULift.{u} (Fin d); U.toScheme),
      Etale e ∧ e ≫ (𝔸(ULift.{u} (Fin d); U.toScheme) ↘ U.toScheme) = g.resLE U V hVU := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  obtain ⟨φ, hφC, hφ⟩ := H.exists_etale_mvPolynomial
  let ε : MvPolynomial (ULift.{u} (Fin d)) Γ(U.toScheme, ⊤) ≃+* MvPolynomial (Fin d) Γ(Y, U) :=
    (mapEquiv _ U.topIso.commRingCatIsoToRingEquiv).trans
      (renameEquiv Γ(Y, U) Equiv.ulift).toRingEquiv
  let ψ : MvPolynomial (ULift.{u} (Fin d)) Γ(U.toScheme, ⊤) →+* Γ(V.toScheme, ⊤) :=
    (V.topIso.symm.commRingCatIsoToRingEquiv.toRingHom.comp φ).comp ε.toRingHom
  have hψ : ψ.Etale :=
    RingHom.Etale.respectsIso.2 _ _ (RingHom.Etale.respectsIso.1 _ _ hφ)
  have hψC : CommRingCat.ofHom (ψ.comp C) = (g.resLE U V hVU).appTop := by
    ext r
    change ψ (C r) = (g.resLE U V hVU).app ⊤ r
    have := RingHom.congr_fun hφC (U.topIso.hom r)
    rw [RingHom.comp_apply] at this
    have hε : ε (C r) = C (U.topIso.hom r) := by simp [ε]
    rw [Scheme.Hom.resLE_app_top]
    simp only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hε,
      this]
    rfl
  have : Etale (Spec.map (CommRingCat.ofHom ψ)) := HasRingHomProperty.Spec_iff.mpr hψ
  refine ⟨V.toScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ) ≫
    (AffineSpace.isoOfIsAffine _ U.toScheme).inv, inferInstance, ?_⟩
  rw [Category.assoc, Category.assoc, AffineSpace.isoOfIsAffine_inv_over, ← Spec.map_comp_assoc,
    ← CommRingCat.ofHom_comp, hψC, Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- The étale-local normal form (blueprint `sk-prop-normal-form`).
Let `g : X ⟶ Y` be smooth of relative dimension `d` and let `x : X`. After replacing
`X` and `Y` by affine open neighbourhoods `V ∋ x` and `U ∋ g.base x` with `V ≤ g ⁻¹ᵁ U`,
the morphism `g` factors as an étale morphism `e : V ⟶ 𝔸(d; U)` followed by the projection
`𝔸(d; U) ↘ U`:

```
V --e--> 𝔸(d; U)
 \          |
  \         ↓
g.resLE     U
```
-/
@[stacks 054L]
theorem Smooth.exists_etale_to_affineSpace {X Y : Scheme.{u}} (g : X ⟶ Y) (d : ℕ)
    [SmoothOfRelativeDimension d g] (x : X) :
    ∃ (U : Y.Opens) (V : X.Opens) (_ : IsAffineOpen U) (_ : IsAffineOpen V)
      (_ : g.base x ∈ U) (_ : x ∈ V) (hVU : V ≤ g ⁻¹ᵁ U)
      (e : V.toScheme ⟶ 𝔸(ULift.{u} (Fin d); U.toScheme)),
      Etale e ∧ e ≫ (𝔸(ULift.{u} (Fin d); U.toScheme) ↘ U.toScheme) = g.resLE U V hVU := by
  obtain ⟨U, hU, V, hV, hx, hVU, H⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := d) (f := g) x
  obtain ⟨e, he, hge⟩ :=
    g.exists_etale_to_affineSpace_of_isStandardSmoothOfRelativeDimension hU hV hVU H
  exact ⟨U, V, hU, hV, hVU hx, hx, hVU, e, he, hge⟩

/-- The étale-local normal form of a morphism smooth at a point (blueprint
`sbc-thm-etale-local-normal-form`). Let `g : X ⟶ Y` be locally of finite presentation and
smooth at `x : X`. Then there are `d : ℕ` and affine open neighbourhoods `V ∋ x` and
`U ∋ g.base x` with `V ≤ g ⁻¹ᵁ U` such that `g.resLE U V hVU` factors as an étale morphism
`e : V ⟶ 𝔸(d; U)` followed by the projection `𝔸(d; U) ↘ U`:

```
V --e--> 𝔸(d; U)
 \          |
  \         ↓
g.resLE     U
```

Near `x` the ring map `Γ(Y, U) ⟶ Γ(X, V)` is standard smooth, and
`Scheme.Hom.exists_etale_to_affineSpace_of_isStandardSmoothOfRelativeDimension` applies. -/
@[stacks 054L]
theorem Scheme.Hom.exists_etale_to_affineSpace_of_mem_smoothLocus {X Y : Scheme.{u}} (g : X ⟶ Y)
    [LocallyOfFinitePresentation g] {x : X} (hx : x ∈ g.smoothLocus) :
    ∃ (d : ℕ) (U : Y.Opens) (V : X.Opens) (_ : IsAffineOpen U) (_ : IsAffineOpen V)
      (_ : g.base x ∈ U) (_ : x ∈ V) (hVU : V ≤ g ⁻¹ᵁ U)
      (e : V.toScheme ⟶ 𝔸(ULift.{u} (Fin d); U.toScheme)),
      Etale e ∧ e ≫ (𝔸(ULift.{u} (Fin d); U.toScheme) ↘ U.toScheme) = g.resLE U V hVU := by
  obtain ⟨U, hU, V, hV, hVU, hxV, H⟩ := exists_smooth_of_formallySmooth_stalk g x hx
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : Smooth (g.resLE U V hVU) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @Smooth)]
    exact (RingHom.Smooth.propertyIsLocal.respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso g U V hVU)).mpr H
  obtain ⟨U', hU', V', hV', hxV', hVU', H'⟩ :=
    Smooth.exists_isStandardSmooth (g.resLE U V hVU) ⟨x, hxV⟩
  let := ((g.resLE U V hVU).appLE U' V' hVU').hom.toAlgebra
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := H'
  obtain ⟨n, H''⟩ : ∃ n,
      ((g.resLE U V hVU).appLE U' V' hVU').hom.IsStandardSmoothOfRelativeDimension n :=
    ⟨_, _, _, _, ‹_›, P, rfl⟩
  rw [Scheme.Hom.resLE_appLE] at H''
  have hU'' := hU'.image_of_isOpenImmersion U.ι
  have hV'' := hV'.image_of_isOpenImmersion V.ι
  obtain ⟨e, he, hge⟩ :=
    g.exists_etale_to_affineSpace_of_isStandardSmoothOfRelativeDimension hU'' hV'' _ H''
  have hxV'' : x ∈ V.ι ''ᵁ V' := ⟨⟨x, hxV⟩, hxV', rfl⟩
  exact ⟨_, _, _, hU'', hV'', (le_resLE_preimage_iff g hVU U' V').mp hVU' hxV'', hxV'', _, e,
    he, hge⟩

/-- **Density of separable points** (Stacks `056U`). Let `f : X ⟶ S` be smooth. Every open
`U` of `X` meeting the fibre through `x` contains a point `x'` of that fibre whose residue field
is finite separable over `κ(f x)`, that is, `κ(f x) ⟶ κ(x')` is étale. These are closed points of
the fibre. By the normal form `AlgebraicGeometry.Smooth.exists_etale_to_affineSpace`, an open of
the fibre is étale over an open of `𝔸ᵈ_{κ(s)}`, in which the closed points with separable
residue field are dense. -/
@[stacks 056U]
theorem Smooth.exists_mem_etale_residueFieldMap {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    (U : X.Opens) {x : X} (hx : x ∈ U) :
    ∃ x' ∈ U, f x' = f x ∧ (f.residueFieldMap x').hom.Etale :=
  sorry

/-- **Étale slices** (Stacks `057G`). Let `f : X ⟶ S` be smooth and let `x : X` have finite
separable residue field over `κ(f x)`, so that `x` is a closed point of its fibre. Then there is
an affine scheme `Z`, a point `z : Z` and an immersion `ι : Z ⟶ X` through `x` such that
`ι ≫ f` is étale: one cuts `X` near `x` by `d` functions vanishing at `x` whose differentials are
a basis of `Ω_{X/S} ⊗ κ(x)`. -/
@[stacks 057G]
theorem Smooth.exists_etale_comp_of_etale_residueFieldMap {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] {x : X} (hx : (f.residueFieldMap x).hom.Etale) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ X) (z : Z), IsAffine Z ∧ IsImmersion ι ∧ Etale (ι ≫ f) ∧
      ι z = x :=
  sorry

/-- **The relative connected component of a section** (Stacks `055R`, `055P`). Let `g : P ⟶ T`
be smooth with a section `σ`. The points `p` lying in the connected component of `σ (g p)` in
their fibre form an open `P⁰` of `P`, here an open `U` containing them. Its fibres over `T` are
the connected components through the rational points `σ t` of the smooth fibres, hence
geometrically connected and, being smooth, geometrically irreducible. -/
@[stacks 055R]
theorem Smooth.exists_geometricallyIrreducible_of_section {P T : Scheme.{u}} (g : P ⟶ T)
    [Smooth g] (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) :
    ∃ U : P.Opens, Set.range σ ⊆ U ∧ GeometricallyIrreducible (U.ι ≫ g) ∧
      ∀ p : P, p ∈ connectedComponentIn (g ⁻¹' {g p}) (σ (g p)) → p ∈ U :=
  sorry

/-- An irreducible scheme `X` smooth over a field `K` is smooth of relative dimension `n` over
`K` if and only if `X` has dimension `n`: the relative dimension of a smooth morphism at a point
is the dimension of the fibre at that point, and an irreducible scheme locally of finite type
over a field has the same dimension at all of its points. -/
theorem smoothOfRelativeDimension_iff_topologicalKrullDim_eq {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [Smooth f] [IrreducibleSpace X] (n : ℕ) :
    SmoothOfRelativeDimension n f ↔ topologicalKrullDim X = n :=
  sorry

/-- A scheme smooth of relative dimension `n` over a field has dimension at most `n`. It is
normal and locally noetherian, so its connected components are open and irreducible; each of
them is smooth of relative dimension `n`, hence of dimension `n` by
`AlgebraicGeometry.smoothOfRelativeDimension_iff_topologicalKrullDim_eq`. -/
theorem topologicalKrullDim_le_of_smoothOfRelativeDimension {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (n : ℕ) [SmoothOfRelativeDimension n f] :
    topologicalKrullDim X ≤ n :=
  sorry

/-- A nonempty scheme smooth of relative dimension `n` over a field has dimension exactly `n`:
each of its connected components is irreducible and smooth of relative dimension `n`, hence of
dimension `n` by `AlgebraicGeometry.smoothOfRelativeDimension_iff_topologicalKrullDim_eq`. -/
theorem topologicalKrullDim_eq_of_smoothOfRelativeDimension {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    [Nonempty X] : topologicalKrullDim X = n :=
  sorry

open Limits in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Affine space is smooth** (blueprint `sbc-lem-affine-space-smooth`). The affine space
`𝔸(n; S)` over `S` in finitely many variables is smooth of relative dimension `#n` over `S`. -/
instance AffineSpace.smoothOfRelativeDimension_over (n : Type u) [Finite n] (S : Scheme.{u}) :
    SmoothOfRelativeDimension (Nat.card n) (𝔸(n; S) ↘ S) :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := Nat.card n)
  MorphismProperty.pullback_fst _ _ <| by
  have := isIso_of_isTerminal specULiftZIsTerminal.{u} terminalIsTerminal (terminal.from _)
  rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom MvPolynomial.C)),
    MorphismProperty.cancel_right_of_respectsIso (P := @SmoothOfRelativeDimension (Nat.card n)),
    HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension (Nat.card n))]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (R := ULift.{u} ℤ)
    (S := MvPolynomial n (ULift.{u} ℤ)) (n := Nat.card n)).2
      (MvPolynomial.isStandardSmoothOfRelativeDimension _ _)

set_option backward.isDefEq.respectTransparency.types false in
/-- The map `𝔸^{d+1}_S ⟶ 𝔸^d_S` forgetting the first coordinate is smooth of relative
dimension one: it is isomorphic, over `𝔸^d_S`, to the affine line `𝔸^1` over `𝔸^d_S`. Writing
`𝔸^d_S ⟶ S` as the composite of `d` such maps reduces statements about smooth morphisms to
relative dimension one. -/
instance AffineSpace.smoothOfRelativeDimension_reindex_succ (d : ℕ) (S : Scheme.{u}) :
    SmoothOfRelativeDimension 1
      (reindex (fun i : ULift.{u} (Fin d) ↦ (⟨i.down.succ⟩ : ULift.{u} (Fin (d + 1)))) S) := by
  set r := reindex (fun i : ULift.{u} (Fin d) ↦ (⟨i.down.succ⟩ : ULift.{u} (Fin (d + 1)))) S
  let B := 𝔸(ULift.{u} (Fin d); S)
  let φ : 𝔸(ULift.{u} (Fin (d + 1)); S) ⟶ 𝔸(PUnit.{u + 1}; B) :=
    homOfVector r (fun _ ↦ coord S ⟨0⟩)
  let ψ : 𝔸(PUnit.{u + 1}; B) ⟶ 𝔸(ULift.{u} (Fin (d + 1)); S) :=
    homOfVector ((𝔸(PUnit.{u + 1}; B) ↘ B) ≫ (B ↘ S))
      (fun j ↦ Fin.cases (coord B PUnit.unit)
        (fun i ↦ (𝔸(PUnit.{u + 1}; B) ↘ B).appTop (coord S ⟨i⟩)) j.down)
  have h₁ : φ ≫ ψ = 𝟙 _ := by
    apply hom_ext
    · simp only [φ, ψ, Category.assoc, homOfVector_over, homOfVector_over_assoc, r,
        Category.id_comp]
      exact reindex_over _ _
    · rintro ⟨i⟩
      induction i using Fin.cases with
      | zero => simp [φ, ψ]
      | succ i =>
        simp only [φ, ψ, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, homOfVector_appTop_coord,
          Fin.cases_succ, Scheme.Hom.id_appTop, CommRingCat.id_apply]
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
        simp only [homOfVector_over, r]
        exact reindex_appTop_coord _ _ _
  have h₂ : ψ ≫ φ = 𝟙 _ := by
    apply hom_ext
    · apply hom_ext
      · simp [φ, ψ, r]
      · rintro ⟨i⟩
        simp only [φ, ψ, r, Category.assoc, homOfVector_over, Scheme.Hom.comp_appTop,
          CommRingCat.comp_apply, reindex_appTop_coord, homOfVector_appTop_coord,
          Fin.cases_succ, Category.id_comp]
        rfl
    · rintro ⟨⟩
      simp [φ, ψ]
  have : IsIso φ := ⟨ψ, h₁, h₂⟩
  have hr : r = φ ≫ (𝔸(PUnit.{u + 1}; B) ↘ B) := by simp [φ]
  have : SmoothOfRelativeDimension (0 + Nat.card PUnit.{u + 1}) (φ ≫ (𝔸(PUnit.{u + 1}; B) ↘ B)) :=
    inferInstance
  simpa [hr] using this

/-- A smooth morphism is, locally on the source and on the target, smooth of some relative
dimension: every point `x` has affine open neighbourhoods `V ∋ x` and `U ∋ f.base x` with
`V ≤ f ⁻¹ᵁ U` such that `f.resLE U V` is smooth of relative dimension `d` for some `d`.
This is the input needed to apply `AlgebraicGeometry.Smooth.exists_etale_to_affineSpace` to
a smooth morphism whose relative dimension varies. -/
theorem Smooth.exists_smoothOfRelativeDimension_resLE {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (x : X) :
    ∃ (U : Y.Opens) (V : X.Opens) (_ : IsAffineOpen U) (_ : IsAffineOpen V) (_ : x ∈ V)
      (e : V ≤ f ⁻¹ᵁ U) (d : ℕ), SmoothOfRelativeDimension d (f.resLE U V e) := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := (Smooth.iff_forall_exists_isStandardSmooth f).mp ‹_› x
  let := (f.appLE U V e).hom.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hf.out
  have hd : (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension P.dimension :=
    P.isStandardSmoothOfRelativeDimension rfl
  refine ⟨U, V, hU, hV, hx, e, P.dimension, ?_⟩
  have : IsAffine U := hU
  have : IsAffine V := hV
  rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension P.dimension)]
  have : (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension P.dimension))).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp <|
      (HasRingHomProperty.isLocal_ringHomProperty
        (@SmoothOfRelativeDimension P.dimension)).respectsIso
  exact (MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension P.dimension)))
      (arrowResLEAppIso f U V e)).mpr
    (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hd)

/-- A scheme `X` smooth of relative dimension `n` over a field has local dimension `n` at every
point: every open neighbourhood of a point is a nonempty scheme smooth of relative dimension `n`
over the field, hence of dimension `n` by
`AlgebraicGeometry.topologicalKrullDim_eq_of_smoothOfRelativeDimension`. -/
theorem topologicalKrullDimAt_eq_of_smoothOfRelativeDimension {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (n : ℕ) [SmoothOfRelativeDimension n f] (x : X) :
    topologicalKrullDimAt x = n := by
  refine topologicalKrullDimAt_eq_of_forall fun (U : X.Opens) hU ↦ ?_
  have : Nonempty U.toScheme := ⟨⟨x, hU⟩⟩
  have : SmoothOfRelativeDimension n (U.ι ≫ f) := by
    have : SmoothOfRelativeDimension (0 + n) (U.ι ≫ f) := inferInstance
    simpa using this
  exact topologicalKrullDim_eq_of_smoothOfRelativeDimension (U.ι ≫ f) n

open Limits in
/-- **Local constancy of the relative dimension** (blueprint
`sbc-lem-smooth-relative-dimension-locally-constant`). For a smooth morphism `f : X ⟶ Y`, the
function `x ↦ dim_x (X_{f(x)})`, the local dimension at `x` of the fibre of `f` through `x`, is
locally constant on `X`.

Near `x`, the morphism `f` restricts to a morphism `V ⟶ U` of open subschemes which is smooth
of some relative dimension `d`; for `x' ∈ V` the open subscheme `V ∩ X_{f(x')}` of the fibre
is its base change to `κ(f(x'))`, smooth of relative dimension `d` over that field, so that
`dim_{x'} (X_{f(x')}) = d` by
`AlgebraicGeometry.topologicalKrullDimAt_eq_of_smoothOfRelativeDimension`. -/
@[stacks 02G1]
theorem Smooth.isLocallyConstant_topologicalKrullDimAt_asFiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f] : IsLocallyConstant fun x : X ↦ topologicalKrullDimAt (f.asFiber x) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  obtain ⟨U, V, -, -, hx, e, d, hd⟩ := Smooth.exists_smoothOfRelativeDimension_resLE f x
  suffices ∀ x' ∈ V, topologicalKrullDimAt (f.asFiber x') = d by
    filter_upwards [V.isOpen.mem_nhds hx] with x' hx' using (this x' hx').trans (this x hx).symm
  intro x' hx'
  let W := (f.fiberι (f x')) ⁻¹ᵁ V
  have hW : f.asFiber x' ∈ W := by
    change f.fiberι _ (f.asFiber x') ∈ V
    rwa [Scheme.Hom.fiberι_asFiber]
  have : SmoothOfRelativeDimension d (V.ι ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f e]
    have : SmoothOfRelativeDimension (d + 0) (f.resLE U V e ≫ U.ι) := inferInstance
    simpa using this
  have hpb : IsPullback (f.fiberι (f x') ∣_ V) (W.ι ≫ f.fiberToSpecResidueField (f x'))
      (V.ι ≫ f) (Y.fromSpecResidueField (f x')) :=
    (isPullback_morphismRestrict (f.fiberι (f x')) V).paste_vert (IsPullback.of_hasPullback _ _)
  have : SmoothOfRelativeDimension d (W.ι ≫ f.fiberToSpecResidueField (f x')) := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
    exact MorphismProperty.of_isPullback hpb inferInstance
  rw [← IsOpen.topologicalKrullDimAt_eq W.isOpen hW]
  exact @topologicalKrullDimAt_eq_of_smoothOfRelativeDimension _ _ _
    (W.ι ≫ f.fiberToSpecResidueField (f x')) d this ⟨_, hW⟩

end AlgebraicGeometry
