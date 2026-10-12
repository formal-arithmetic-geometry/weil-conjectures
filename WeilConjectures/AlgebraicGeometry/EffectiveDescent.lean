/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Sites.Over
public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.AffineLocal
public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.Gluing
public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.Group
public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.Neighbourhood
public import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent

/-!
# Effective descent for schemes

Let `p : X ⟶ Y` be a morphism of schemes. This file collects the descent statements for schemes
over `X` equipped with a descent datum relative to `p` (in the transport form
`CategoryTheory.Over.DescentDatum`) that are needed to descend the Jacobian of a curve from a
finite separable extension of the base field.

## Main statements

- `CategoryTheory.Over.DescentDatum.isEffective_of_isFinite`: along a surjective finite locally
  free morphism, descent data on schemes in which every finite set of points lies in an affine open
  (for instance projective schemes over a field) are effective (blueprint
  `thm-pd-effective-descent`).
- `CategoryTheory.Over.DescentDatum.existsUnique_hom_of_isPullback`: compatible morphisms descend
  (blueprint `lem-pd-morphisms-descend`).
- `CategoryTheory.Over.DescentDatum.exists_commGrpObj_of_isPullback`: compatible group scheme
  structures descend (blueprint `lem-pd-group-scheme-descent`), uniquely
  (`CategoryTheory.Over.DescentDatum.grpObj_ext_of_isPullback`).
- `AlgebraicGeometry.isProper_smoothOfRelativeDimension_geometricallyIntegral_of_isPullback`:
  properness, smoothness of relative dimension `n` and geometric integrality descend along a field
  extension (blueprint `thm-pd-fpqc-local-properties`), and so does connectedness
  (`AlgebraicGeometry.connectedSpace_of_isPullback`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace CategoryTheory.Over.DescentDatum

open AlgebraicGeometry

variable {X Y : Scheme.{u}} {p : X ⟶ Y}

/-- **Effective descent for quasi-projective schemes.** Let `p : X ⟶ Y` be a surjective finite
locally free morphism and let `V` be a scheme over `X` in which every finite set of points lies in
an affine open, as is the case for a projective scheme over a field (Stacks 01ZY). Then every
descent datum on `V` relative to `p` is effective.

This is Stacks 0CCJ, via the criterion of Stacks 0CCI: the hypothesis on `V` is stronger than the
one needed there, which only asks it of the finite sets of points lying over one point of `Y`.

(blueprint: `thm-pd-effective-descent`) -/
theorem isEffective_of_isFinite [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
    [Surjective p] {V : Over X}
    (hV : ∀ s : Set V.left, s.Finite → ∃ U : V.left.Opens, IsAffineOpen U ∧ s ⊆ U)
    (D : Over.DescentDatum p V) : D.IsEffective := by
  refine isEffective_of_forall_exists_mem fun v ↦ ?_
  obtain ⟨U, hv, hU, hUa, W, hW, hUW⟩ := D.exists_isInvariant_isAffineOpen hV v
  exact ⟨U, hU, hv, D.isEffective_restrict_of_isAffineOpen hU hUa hW hUW⟩

/-- **Morphisms descend.** Let `p : X ⟶ Y` be faithfully flat and quasi-compact, and let `V`, `W`
be schemes over `X` with descent data `D`, `E` that are effective, with descended schemes `V₀`,
`W₀` over `Y` and projections `qV`, `qW`. Then every morphism `ψ : V ⟶ W` over `X` compatible with
the two descent data is the base change of a unique morphism `ψ₀ : V₀ ⟶ W₀` over `Y`.

This is the full faithfulness of base change into descent data, Stacks 02W0.

(blueprint: `lem-pd-morphisms-descend`) -/
theorem existsUnique_hom_of_isPullback [Flat p] [Surjective p] [QuasiCompact p] {V W : Over X}
    (D : Over.DescentDatum p V) (E : Over.DescentDatum p W) {V₀ W₀ : Over Y}
    (qV : V.left ⟶ V₀.left) (hqV : IsPullback qV V.hom V₀.hom p)
    (hDV : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      (D.transport f₁ f₂ h a).left ≫ qV = a.left ≫ qV)
    (qW : W.left ⟶ W₀.left) (hqW : IsPullback qW W.hom W₀.hom p)
    (hEW : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ W),
      (E.transport f₁ f₂ h a).left ≫ qW = a.left ≫ qW)
    (ψ : V ⟶ W)
    (hψ : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      E.transport f₁ f₂ h (a ≫ ψ) = D.transport f₁ f₂ h a ≫ ψ) :
    ∃! ψ₀ : V₀ ⟶ W₀, ψ.left ≫ qW = qV ≫ ψ₀.left := by
  obtain ⟨g₀, hg₀, hu⟩ := D.existsUnique_desc_of_isPullback hqV hDV (ψ.left ≫ qW)
    fun f₁ f₂ h a ↦ by simpa [hψ] using hEW f₁ f₂ h (a ≫ ψ)
  obtain ⟨_, _, hY⟩ := D.existsUnique_desc_of_isPullback hqV hDV (V.hom ≫ p)
    fun f₁ f₂ h a ↦ by simp [h]
  have hg₀Y : g₀ ≫ W₀.hom = V₀.hom := by
    refine (hY _ ?_).trans (hY V₀.hom hqV.w).symm
    dsimp only
    rw [reassoc_of% hg₀, hqW.w, Over.w_assoc]
  refine ⟨Over.homMk g₀ hg₀Y, hg₀.symm, fun ψ₀ hψ₀ ↦ ?_⟩
  ext
  exact hu _ hψ₀.symm

/-- The point `qV ∘ a` of `V₀` over `Y` induced by a point `a` of `V` over `f`, for a projection
`qV : V ⟶ V₀` exhibiting `V` as the base change of `V₀` along `p`. -/
abbrev descendPoint {V : Over X} {V₀ : Over Y} {qV : V.left ⟶ V₀.left}
    (hqV : IsPullback qV V.hom V₀.hom p) {T : Scheme.{u}} {f : T ⟶ X} (a : Over.mk f ⟶ V) :
    Over.mk (f ≫ p) ⟶ V₀ :=
  Over.homMk (a.left ≫ qV) (by
    simp only [Over.mk_hom, Category.assoc, hqV.w]
    rw [← Category.assoc, Over.w a]
    rfl)

/-- **The descended scheme is a group scheme.** Let `p : X ⟶ Y` be faithfully flat and
quasi-compact, let `V` be a scheme over `X` with an effective descent datum `D`, with descended
scheme `V₀` and projection `qV`, and let `V` carry a commutative group scheme structure whose
multiplication and unit are compatible with `D`. Then `V₀` carries a commutative group scheme
structure over `Y` whose base change is the given one: `qV` maps products of points of `V` to
products of points of `V₀`. Such a structure is unique
(`CategoryTheory.Over.DescentDatum.grpObj_ext_of_isPullback`).

(blueprint: `lem-pd-group-scheme-descent`) -/
theorem exists_commGrpObj_of_isPullback [Flat p] [Surjective p] [QuasiCompact p] {V : Over X}
    [CommGrpObj V] (D : Over.DescentDatum p V) {V₀ : Over Y} (qV : V.left ⟶ V₀.left)
    (hqV : IsPullback qV V.hom V₀.hom p)
    (hDV : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      (D.transport f₁ f₂ h a).left ≫ qV = a.left ≫ qV)
    (hμ : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a b : Over.mk f₁ ⟶ V),
      D.transport f₁ f₂ h (lift a b ≫ μ[V]) =
        lift (D.transport f₁ f₂ h a) (D.transport f₁ f₂ h b) ≫ μ[V])
    (hη : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p),
      D.transport f₁ f₂ h (toUnit _ ≫ η[V]) = toUnit _ ≫ η[V]) :
    ∃ _ : CommGrpObj V₀, ∀ {T : Scheme.{u}} (f : T ⟶ X) (a b : Over.mk f ⟶ V),
      descendPoint hqV (lift a b ≫ μ[V]) =
        lift (descendPoint hqV a) (descendPoint hqV b) ≫ μ[V₀] := by
  let := CommGrpObj.ofRepresentableBy V₀ (D.descendedPresheaf hqV hDV hμ hη)
    (D.descendedRepresentableBy hqV hDV hμ hη)
  refine ⟨this, fun f a b ↦ ?_⟩
  have hmul (x y : Over.mk (f ≫ p) ⟶ V₀) :
      lift x y ≫ μ[V₀] = (D.homCommGroup hqV hDV hμ hη _).mul x y :=
    (((D.descendedPresheaf hqV hDV hμ hη).map (lift x y).op).hom.map_mul
      (fst V₀ V₀) (snd V₀ V₀)).trans
      (congrArg₂ (D.homCommGroup hqV hDV hμ hη _).mul (lift_fst x y) (lift_snd x y))
  exact (D.descendPoint'_mul hqV hDV hμ hη a b).trans (hmul _ _).symm

/-- **The descended group scheme structure is unique.** Let `p : X ⟶ Y` be flat and surjective,
let `V` be a monoid scheme over `X` and let `qV : V ⟶ V₀` exhibit `V` as the base change of `V₀`
along `p`. Then there is at most one group scheme structure on `V₀` over `Y` whose base change is
the given one, in the sense that `qV` maps products of points of `V` to products of points of
`V₀` (as for the structure of `CategoryTheory.Over.DescentDatum.exists_commGrpObj_of_isPullback`):
base change along the faithfully flat `p` is injective on morphisms.

(blueprint: `lem-pd-group-scheme-descent`, the uniqueness clause) -/
theorem grpObj_ext_of_isPullback [Flat p] [Surjective p] {V : Over X} [MonObj V] {V₀ : Over Y}
    {qV : V.left ⟶ V₀.left} (hqV : IsPullback qV V.hom V₀.hom p) (G₁ G₂ : GrpObj V₀)
    (h₁ : ∀ {T : Scheme.{u}} (f : T ⟶ X) (a b : Over.mk f ⟶ V),
      descendPoint hqV (lift a b ≫ μ[V]) =
        lift (descendPoint hqV a) (descendPoint hqV b) ≫ G₁.mul)
    (h₂ : ∀ {T : Scheme.{u}} (f : T ⟶ X) (a b : Over.mk f ⟶ V),
      descendPoint hqV (lift a b ≫ μ[V]) =
        lift (descendPoint hqV a) (descendPoint hqV b) ≫ G₂.mul) :
    G₁ = G₂ := by
  -- the points of `V` over `V₀ ×_Y V₀ ×_Y X` lifting the two projections
  let π := pullback.fst (V₀ ⊗ V₀).hom p
  have hπ (c : V₀ ⊗ V₀ ⟶ V₀) :
      (π ≫ c.left) ≫ V₀.hom = pullback.snd (V₀ ⊗ V₀).hom p ≫ p := by
    rw [Category.assoc, Over.w c, pullback.condition]
  let a (c : V₀ ⊗ V₀ ⟶ V₀) : Over.mk (pullback.snd (V₀ ⊗ V₀).hom p) ⟶ V :=
    Over.homMk (hqV.lift (π ≫ c.left) _ (hπ c)) (hqV.lift_snd _ _ _)
  have key : lift (descendPoint hqV (a (fst V₀ V₀))) (descendPoint hqV (a (snd V₀ V₀))) =
      Over.homMk π pullback.condition := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_ <;>
    · ext
      simp [a, π]
  have hμ : π ≫ G₁.mul.left = π ≫ G₂.mul.left := by
    have := (h₁ _ (a (fst V₀ V₀)) (a (snd V₀ V₀))).symm.trans (h₂ _ _ _)
    rw [key] at this
    exact congrArg (·.left) this
  have := Flat.epi_of_flat_of_surjective π
  exact GrpObj.ext _ _ (MonObj.ext _ _ (Over.OverMorphism.ext ((cancel_epi π).1 hμ)))

end CategoryTheory.Over.DescentDatum

namespace AlgebraicGeometry

/-- **Properties of morphisms are local in the fpqc topology on the target.** Let `k ⊆ K` be a
field extension and let `Z` be a scheme over `k` whose base change `Z_K` is proper, smooth of
relative dimension `n` and geometrically integral over `K`. Then so is `Z` over `k`.

For properness and smoothness this is Stacks 02YJ, 02VL, 02KL and 05B5, the morphism
`Spec K ⟶ Spec k` being faithfully flat and quasi-compact; the relative dimension is read off on
fibres. Geometric integrality descends because for every field `Ω` over `k` there is a field `L`
containing both `Ω` and `K`, and `Z_L ⟶ Z_Ω` is faithfully flat: reducedness descends along it
and irreducibility passes to the image.

The blueprint states this for finite extensions and lists finite type, smoothness, properness and
connectedness; the form here holds for any field extension and carries the properties used to
recognise an abelian variety of dimension `g`.

(blueprint: `thm-pd-fpqc-local-properties`) -/
theorem isProper_smoothOfRelativeDimension_geometricallyIntegral_of_isPullback {k K : Type u}
    [Field k] [Field K] [Algebra k K] {Z Z' : Scheme.{u}} (z : Z ⟶ Spec (.of k))
    (z' : Z' ⟶ Spec (.of K)) (q : Z' ⟶ Z)
    (h : IsPullback q z' z (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (n : ℕ)
    [IsProper z'] [SmoothOfRelativeDimension n z'] [GeometricallyIntegral z'] :
    IsProper z ∧ SmoothOfRelativeDimension n z ∧ GeometricallyIntegral z :=
  isProper_smoothOfRelativeDimension_geometricallyIntegral_of_isPullback_aux z z' q h n

/-- **Connectedness descends along a field extension.** Let `k ⊆ K` be a field extension and let
`Z` be a scheme over `k` whose base change `Z_K` is connected. Then `Z` is connected, being the
image of `Z_K` under the surjective projection `Z_K ⟶ Z`.

Together with
`AlgebraicGeometry.isProper_smoothOfRelativeDimension_geometricallyIntegral_of_isPullback`
this gives the connectedness clause of the blueprint statement.

(blueprint: `thm-pd-fpqc-local-properties`, the connectedness clause) -/
theorem connectedSpace_of_isPullback {k K : Type u} [Field k] [Field K] [Algebra k K]
    {Z Z' : Scheme.{u}} (z : Z ⟶ Spec (.of k)) (z' : Z' ⟶ Spec (.of K)) (q : Z' ⟶ Z)
    (h : IsPullback q z' z (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [ConnectedSpace Z'] : ConnectedSpace Z := by
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    ⟨fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  have : Surjective q := MorphismProperty.of_isPullback h.flip this
  exact q.surjective.connectedSpace q.continuous

end AlgebraicGeometry
