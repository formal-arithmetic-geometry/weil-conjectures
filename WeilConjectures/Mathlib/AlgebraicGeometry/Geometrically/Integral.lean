/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Varieties over a field, and their global sections

A *variety over `S`* is a scheme `X` together with a morphism `f : X ⟶ S` which is separated, of
finite type and geometrically integral. This file introduces the abbreviation
`AlgebraicGeometry.IsVariety` over the three Mathlib predicates, records the standing stability
facts for products and projections, and proves the global-sections lemmas of the theorem of the
cube.

Following the project convention, products of `K`-schemes are formed as `Limits.pullback πX πY`
of the two structure morphisms rather than as `X ⊗ Y` in `Over (Spec (.of K))`: every Mathlib
lemma used below is stated for bare schemes.

Beware that Lean's composition `f ≫ g` is the classical `g ∘ f`, the opposite order to the
blueprint.

## Main definitions

- `AlgebraicGeometry.IsVariety` (blueprint: definition 10 of `sec:cube-cost`) — the abbreviation
  for "separated, of finite type and geometrically integral". Its four components are recovered
  by typeclass inference, and conversely a morphism with all four is a variety, so `[IsVariety f]`
  and the components are interchangeable in both directions.

## Main statements

- `AlgebraicGeometry.GeometricallyIntegral.comp` — geometric integrality is stable under
  composition, for a flat first morphism and a second one locally of finite type. This is what a
  product of varieties needs, and Mathlib has it for `GeometricallyIrreducible` but not for
  `GeometricallyReduced`.
- `AlgebraicGeometry.IsVariety.isIntegral` and its consequences
  `AlgebraicGeometry.IsVariety.irreducibleSpace`, `.connectedSpace`, `.isReduced`,
  `.nonempty` — a variety over a field is integral, hence irreducible, connected, reduced and
  non-empty.
- `AlgebraicGeometry.IsVariety.comp_fst` (blueprint `lem:cube-product-variety`) — a product of
  two varieties over a field is a variety; together with the properness of the projections this
  makes a product of *proper* varieties a proper variety.
- `AlgebraicGeometry.sliceInclusionFst`, `AlgebraicGeometry.sliceInclusionSnd` and their
  `IsClosedImmersion` instances (blueprint `lem:cube-product-variety`) — the slice inclusions
  `X ⟶ X × Y` and `Y ⟶ X × Y` through a rational point are closed immersions.
- `lem:cube-projection-proper-flat`(1)–(3) are entirely available to typeclass inference; the
  `example`s in the `Projection` section below spell them out. Part (1) uses the two instances of
  `WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian`.
- `lem:cube-global-sections`, the global sections of a proper integral scheme over an
  algebraically closed field, is `AlgebraicGeometry.isIso_ΓSpecIso_inv_comp_appTop`, which sits
  in `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper` next to the Mathlib lemmas it
  is proved from.
- `AlgebraicGeometry.isPushout_appTop_of_flat` (blueprint
  `prop:cube-global-sections-flat-base-change`, Stacks tag `02KH` in degree zero) — for a
  quasi-compact separated `R`-scheme `X` and a flat `R ⟶ R'`, the square of global sections is a
  pushout of commutative rings, that is `Γ(X ×_{Spec R} Spec R', 𝒪) = Γ(X, 𝒪_X) ⊗[R] R'`.
- `AlgebraicGeometry.isIso_ΓSpecIso_inv_comp_appTop_of_geometricallyIntegral` (blueprint
  `lem:cube-global-sections-general`, Stacks tag `0BUG` part (8)) — for `X` proper and
  geometrically integral over a field `K`, the structure map `K ⟶ Γ(X, 𝒪_X)` is an isomorphism.
- `AlgebraicGeometry.isIso_ΓSpecIso_inv_comp_snd_appTop` (blueprint
  `lem:cube-global-sections-base-change`) — for such an `X` and a `K`-algebra `A`, the structure
  map `A ⟶ Γ(X ×_K Spec A, 𝒪)` is an isomorphism.

## Implementation notes

* `AlgebraicGeometry.isPushout_appTop_of_flat` is the special case `U = ⊤` of
  `AlgebraicGeometry.isPushout_app_of_isCompact`, proved in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks` by induction on a finite affine cover:
  `Γ(X, 𝒪_X)` is the equaliser of the two restriction maps between the sections over the members
  of the cover and the sections over their pairwise intersections — affine again because `X` is
  separated — and a flat base change preserves that equaliser.
* The canonical map of `prop:cube-global-sections-flat-base-change` is packaged as a
  `CategoryTheory.IsPushout` square in `CommRingCat` rather than as an explicit ring map out of a
  tensor product. This needs no auxiliary definition and no algebra instances on `Γ(X, 𝒪_X)`:
  the four maps of the square are the two structure maps and the two `appTop`s of the projections
  out of the pullback, and the square commutes by functoriality of `appTop`.
  `CommRingCat.isPushout_tensorProduct` identifies the pushout with the tensor product, which is
  how `isIso_ΓSpecIso_inv_comp_appTop_of_geometricallyIntegral` uses it.
* Mathlib `v4.33.1` has no bundled `IsFiniteType` for morphisms of schemes, so "of finite type" is
  spelled out as `LocallyOfFiniteType` together with `QuasiCompact`.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MorphismProperty TensorProduct

namespace AlgebraicGeometry

universe u

variable {X Y Z S : Scheme.{u}}

/-- Geometric integrality is stable under composition, provided the first morphism is flat, the
second is locally of finite type, and both are universally open. The last three hypotheses are
automatic for the structure morphisms of varieties over a field. -/
lemma GeometricallyIntegral.comp (f : X ⟶ Y) (g : Y ⟶ Z) [GeometricallyIntegral f]
    [GeometricallyIntegral g] [Flat f] [LocallyOfFiniteType g]
    [UniversallyOpen f] [UniversallyOpen g] :
    GeometricallyIntegral (f ≫ g) :=
  have := GeometricallyReduced.comp f g
  have := GeometricallyIrreducible.comp f g
  .of_geometricallyReduced_of_geometricallyIrreducible _

/-- A morphism `f : X ⟶ S` exhibits `X` as a *variety over* `S` if it is separated, of finite
type and geometrically integral. -/
class IsVariety (f : X ⟶ S) : Prop extends
    IsSeparated f, LocallyOfFiniteType f, QuasiCompact f, GeometricallyIntegral f

instance (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [GeometricallyIntegral f] : IsVariety f := ⟨⟩

/-- `IsVariety` is an abbreviation: its four components are recovered by typeclass inference. -/
example (f : X ⟶ S) [IsVariety f] :
    IsSeparated f ∧ LocallyOfFiniteType f ∧ QuasiCompact f ∧ GeometricallyIntegral f :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

section Field

variable {K : Type u} [Field K]

/-- A geometrically integral scheme over a field is integral. -/
lemma GeometricallyIntegral.isIntegral (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f] :
    IsIntegral X :=
  GeometricallyIntegral.isIntegral_of_subsingleton f

/-- A variety over a field is integral. -/
lemma IsVariety.isIntegral (f : X ⟶ Spec (.of K)) [IsVariety f] : IsIntegral X :=
  GeometricallyIntegral.isIntegral f

/-- A variety over a field is irreducible. -/
lemma IsVariety.irreducibleSpace (f : X ⟶ Spec (.of K)) [IsVariety f] : IrreducibleSpace X :=
  have := IsVariety.isIntegral f
  inferInstance

/-- A variety over a field is connected. -/
lemma IsVariety.connectedSpace (f : X ⟶ Spec (.of K)) [IsVariety f] : ConnectedSpace X :=
  have := IsVariety.irreducibleSpace f
  inferInstance

/-- A variety over a field is reduced. -/
lemma IsVariety.isReduced (f : X ⟶ Spec (.of K)) [IsVariety f] : IsReduced X :=
  have := IsVariety.isIntegral f
  inferInstance

/-- A variety over a field is non-empty. -/
lemma IsVariety.nonempty (f : X ⟶ Spec (.of K)) [IsVariety f] : Nonempty X :=
  have := IsVariety.irreducibleSpace f
  inferInstance

end Field

section Product

variable {K : Type u} [Field K] (πX : X ⟶ Spec (.of K)) (πY : Y ⟶ Spec (.of K))

/-- **A product of two varieties over a field is a variety.**

This is the first half of `lem:cube-product-variety`; the second half is that a product of proper
varieties is proper, which typeclass inference already knows. -/
instance IsVariety.comp_fst [IsVariety πX] [IsVariety πY] :
    IsVariety (pullback.fst πX πY ≫ πX) :=
  have := GeometricallyIntegral.comp (pullback.fst πX πY) πX
  inferInstance

/-- A product of two proper varieties over a field is proper over the field. -/
example [IsVariety πX] [IsVariety πY] [IsProper πX] [IsProper πY] :
    IsProper (pullback.fst πX πY ≫ πX) := inferInstance

/-- The slice inclusion `j_{y₀} : X ⟶ X × Y` determined by a rational point `y₀` of `Y`. -/
def sliceInclusionFst (y₀ : Spec (.of K) ⟶ Y) (hy₀ : y₀ ≫ πY = 𝟙 _) : X ⟶ pullback πX πY :=
  pullback.lift (𝟙 X) (πX ≫ y₀) (by simp [hy₀])

@[reassoc (attr := simp)]
lemma sliceInclusionFst_fst (y₀ : Spec (.of K) ⟶ Y) (hy₀ : y₀ ≫ πY = 𝟙 _) :
    sliceInclusionFst πX πY y₀ hy₀ ≫ pullback.fst πX πY = 𝟙 X := by
  simp [sliceInclusionFst]

/-- The slice inclusion `j_{x₀} : Y ⟶ X × Y` determined by a rational point `x₀` of `X`. -/
def sliceInclusionSnd (x₀ : Spec (.of K) ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 _) : Y ⟶ pullback πX πY :=
  pullback.lift (πY ≫ x₀) (𝟙 Y) (by simp [hx₀])

@[reassoc (attr := simp)]
lemma sliceInclusionSnd_snd (x₀ : Spec (.of K) ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 _) :
    sliceInclusionSnd πX πY x₀ hx₀ ≫ pullback.snd πX πY = 𝟙 Y := by
  simp [sliceInclusionSnd]

/-- A rational point of a `K`-scheme is a closed immersion; Mathlib knows this already, since
`Spec K` is a subsingleton. -/
example (y₀ : Spec (.of K) ⟶ Y) (hy₀ : y₀ ≫ πY = 𝟙 _) : IsClosedImmersion y₀ :=
  isClosedImmersion_of_comp_eq_id πY y₀ hy₀

/-- **A slice inclusion is a closed immersion.** -/
instance [IsSeparated πY] (y₀ : Spec (.of K) ⟶ Y) (hy₀ : y₀ ≫ πY = 𝟙 _) :
    IsClosedImmersion (sliceInclusionFst πX πY y₀ hy₀) :=
  IsClosedImmersion.of_comp_eq_id (f := pullback.fst πX πY) (by simp)

/-- **A slice inclusion is a closed immersion.** -/
instance [IsSeparated πX] (x₀ : Spec (.of K) ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 _) :
    IsClosedImmersion (sliceInclusionSnd πX πY x₀ hx₀) :=
  IsClosedImmersion.of_comp_eq_id (f := pullback.snd πX πY) (by simp)

end Product

section Projection

variable {T : Scheme.{u}} {K : Type u} [Field K] (πX : X ⟶ Spec (.of K)) (t : T ⟶ Spec (.of K))

/-- `X × T` is locally noetherian as soon as `T` is; this is
`lem:cube-projection-proper-flat`(1). -/
example [LocallyOfFiniteType πX] [IsLocallyNoetherian T] : IsLocallyNoetherian (pullback πX t) :=
  inferInstance

/-- `X × T` is of finite type over `K` as soon as `T` is; this is
`lem:cube-projection-proper-flat`(1). -/
example [LocallyOfFiniteType πX] [QuasiCompact πX] [LocallyOfFiniteType t] [QuasiCompact t] :
    LocallyOfFiniteType (pullback.snd πX t ≫ t) ∧ QuasiCompact (pullback.snd πX t ≫ t) :=
  ⟨inferInstance, inferInstance⟩

/-- The projection `p_T : X × T ⟶ T` is proper, flat and of finite type; this is
`lem:cube-projection-proper-flat`(2). -/
example [IsProper πX] : IsProper (pullback.snd πX t) ∧ Flat (pullback.snd πX t) ∧
    LocallyOfFiniteType (pullback.snd πX t) ∧ QuasiCompact (pullback.snd πX t) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The projection `p_T : X × T ⟶ T` is a closed map; this is
`lem:cube-projection-proper-flat`(2). -/
example [IsProper πX] : IsClosedMap (pullback.snd πX t) := (pullback.snd πX t).isClosedMap

set_option backward.isDefEq.respectTransparency.types false in
/-- The fibre of `p_T : X × T ⟶ T` over `s : T` is proper over the residue field `κ(s)`; this is
part of `lem:cube-projection-proper-flat`(3). -/
example [IsProper πX] (s : T) : IsProper ((pullback.snd πX t).fiberToSpecResidueField s) :=
  MorphismProperty.pullback_snd _ _ inferInstance

/-- The fibre of `p_T : X × T ⟶ T` over `s : T` is geometrically integral over the residue field
`κ(s)`, hence integral; this is the rest of `lem:cube-projection-proper-flat`(3). -/
example [GeometricallyIntegral πX] (s : T) :
    GeometricallyIntegral ((pullback.snd πX t).fiberToSpecResidueField s) ∧
      IsIntegral ((pullback.snd πX t).fiber s) :=
  ⟨inferInstance, inferInstance⟩

end Projection

section GlobalSections

variable {K : Type u} [Field K]

/-- **Global sections and flat base change of the ground ring.**

For `X` a quasi-compact separated scheme over `Spec R` and `φ : R ⟶ R'` flat, the square of
global sections
```
  R  ⟶ Γ(X, 𝒪_X)
  ↓         ↓
  R' ⟶ Γ(X ×_{Spec R} Spec R', 𝒪)
```
is a pushout of commutative rings, that is `Γ(X ×_{Spec R} Spec R', 𝒪) = Γ(X, 𝒪_X) ⊗[R] R'`.

This is `prop:cube-global-sections-flat-base-change` of the blueprint, and the degree-zero case
of Stacks tag `02KH`. -/
@[stacks 02KH]
theorem isPushout_appTop_of_flat {R R' : CommRingCat.{u}} (φ : R ⟶ R') [Flat (Spec.map φ)]
    (f : X ⟶ Spec R) [QuasiCompact f] [IsSeparated f] :
    IsPushout ((Scheme.ΓSpecIso R).inv ≫ f.appTop) φ
      (pullback.fst f (Spec.map φ)).appTop
      ((Scheme.ΓSpecIso R').inv ≫ (pullback.snd f (Spec.map φ)).appTop) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have h := isPushout_app_of_isCompact φ f (U := ⊤) (by simpa using isCompact_univ)
  simpa [Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app] using h

/-- **The global sections of a proper geometrically integral scheme over a field.**

For `X` proper and geometrically integral over a field `K`, the structure morphism induces an
isomorphism `K ≅ Γ(X, 𝒪_X)`. This is `lem:cube-global-sections-general` of the blueprint, and
Stacks tag `0BUG` part (8). -/
@[stacks 0BUG "(8)"]
theorem isIso_ΓSpecIso_inv_comp_appTop_of_geometricallyIntegral (π : X ⟶ Spec (.of K))
    [IsProper π] [GeometricallyIntegral π] :
    IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop) := by
  set u : CommRingCat.of K ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop with hu
  let _ : Algebra K ↥Γ(X, ⊤) := u.hom.toAlgebra
  set φ : CommRingCat.of K ⟶ CommRingCat.of (AlgebraicClosure K) :=
    CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))
  have hint : IsIntegral (pullback π (Spec.map φ)) :=
    pullback_of_geometrically ‹GeometricallyIntegral π›.geometrically_isIntegral
      (AlgebraicClosure K) (Spec.map φ)
  have hiso : IsIso ((Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure K))).inv ≫
      (pullback.snd π (Spec.map φ)).appTop) :=
    isIso_ΓSpecIso_inv_comp_appTop (pullback.snd π (Spec.map φ))
  have H := (isPushout_appTop_of_flat φ π).flip
  have hpt := CommRingCat.isPushout_tensorProduct K (AlgebraicClosure K) ↥Γ(X, ⊤)
  have key : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := K) (A := AlgebraicClosure K) (B := ↥Γ(X, ⊤))) ≫
      (hpt.isoIsPushout _ _ H).hom = _ :=
    hpt.inl_isoIsPushout_hom _ _ H
  have hbij : Function.Bijective
      (algebraMap (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] ↥Γ(X, ⊤))) := by
    have hIso : IsIso (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := K) (A := AlgebraicClosure K) (B := ↥Γ(X, ⊤)))) := by
      rw [← IsIso.eq_comp_inv] at key
      rw [key]
      infer_instance
    rwa [ConcreteCategory.isIso_iff_bijective] at hIso
  have h1 : Module.finrank (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] ↥Γ(X, ⊤)) = 1 :=
    Module.finrank_of_bijective_algebraMap hbij
  rw [Module.finrank_baseChange] at h1
  rw [hu, ConcreteCategory.isIso_iff_bijective]
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h1

/-- **The global sections of a proper variety after a base change of the ground field.**

For `X` proper and geometrically integral over a field `K` and `A` a `K`-algebra, the structure
morphism induces an isomorphism `A ≅ Γ(X ×_K Spec A, 𝒪)`. This is
`lem:cube-global-sections-base-change` of the blueprint. -/
theorem isIso_ΓSpecIso_inv_comp_snd_appTop (π : X ⟶ Spec (.of K)) [IsProper π]
    [GeometricallyIntegral π] (A : Type u) [CommRing A] [Algebra K A] :
    IsIso ((Scheme.ΓSpecIso (.of A)).inv ≫
      (pullback.snd π (Spec.map (CommRingCat.ofHom (algebraMap K A)))).appTop) :=
  (isPushout_appTop_of_flat (CommRingCat.ofHom (algebraMap K A)) π).isIso_inr_of_isIso
    (isIso_ΓSpecIso_inv_comp_appTop_of_geometricallyIntegral π)

end GlobalSections

end AlgebraicGeometry
