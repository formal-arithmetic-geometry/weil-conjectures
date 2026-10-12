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
  structures descend (blueprint `lem-pd-group-scheme-descent`).
- `AlgebraicGeometry.isProper_smoothOfRelativeDimension_geometricallyIntegral_of_isPullback`:
  properness, smoothness of relative dimension `n` and geometric integrality descend along a field
  extension (blueprint `thm-pd-fpqc-local-properties`).
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

/-- **The descended scheme is a group scheme.** Let `p : X ⟶ Y` be faithfully flat and
quasi-compact, let `V` be a scheme over `X` with an effective descent datum `D`, with descended
scheme `V₀` and projection `qV`, and let `V` carry a group scheme structure whose multiplication
and unit are compatible with `D`. Then `V₀` carries a unique group scheme structure over `Y`
whose base change is the given one, in the sense that `qV` maps products of points of `V` to
products of points of `V₀`.

Existence comes from the Yoneda lemma applied to the invariant points of `V`; uniqueness from
the injectivity of base change on morphisms (`liftPoint_injective`).

(blueprint: `lem-pd-group-scheme-descent`) -/
theorem existsUnique_grpObj_of_isPullback [Flat p] [Surjective p] [QuasiCompact p] {V : Over X}
    [GrpObj V] (D : Over.DescentDatum p V) {V₀ : Over Y} (qV : V.left ⟶ V₀.left)
    (hqV : IsPullback qV V.hom V₀.hom p)
    (hDV : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      (D.transport f₁ f₂ h a).left ≫ qV = a.left ≫ qV)
    (hμ : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a b : Over.mk f₁ ⟶ V),
      D.transport f₁ f₂ h (lift a b ≫ μ[V]) =
        lift (D.transport f₁ f₂ h a) (D.transport f₁ f₂ h b) ≫ μ[V])
    (hη : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p),
      D.transport f₁ f₂ h (toUnit _ ≫ η[V]) = toUnit _ ≫ η[V]) :
    ∃! _ : GrpObj V₀, ∀ {T : Scheme.{u}} (f : T ⟶ X) (a b : Over.mk f ⟶ V),
      descendPoint hqV (lift a b ≫ μ[V]) =
        lift (descendPoint hqV a) (descendPoint hqV b) ≫ μ[V₀] := by
  let G := GrpObj.ofRepresentableBy V₀ (D.descendedPresheaf hqV hDV hμ hη)
    (D.descendedRepresentableBy hqV hDV hμ hη)
  have hG {T : Scheme.{u}} (f : T ⟶ X) (a b : Over.mk f ⟶ V) :
      descendPoint hqV (lift a b ≫ μ[V]) =
        lift (descendPoint hqV a) (descendPoint hqV b) ≫ μ[V₀] := by
    have hmul (x y : Over.mk (f ≫ p) ⟶ V₀) :
        lift x y ≫ μ[V₀] = (D.homGroup hqV hDV hμ hη _).mul x y :=
      (((D.descendedPresheaf hqV hDV hμ hη).map (lift x y).op).hom.map_mul
        (fst V₀ V₀) (snd V₀ V₀)).trans
        (congrArg₂ (D.homGroup hqV hDV hμ hη _).mul (lift_fst x y) (lift_snd x y))
    exact (D.descendPoint_mul hqV hDV hμ hη a b).trans (hmul _ _).symm
  exact ⟨G, hG, fun G' hG' ↦ GrpObj.ext_of_mul_eq
    (mul_eq_of_descendPoint_mul hqV G'.toMonObj G.toMonObj hG' hG)⟩

/-- **The descended scheme is a commutative group scheme.** Let `p : X ⟶ Y` be faithfully flat
and quasi-compact, let `V` be a scheme over `X` with an effective descent datum `D`, with
descended scheme `V₀` and projection `qV`, and let `V` carry a commutative group scheme structure
whose multiplication and unit are compatible with `D`. Then `V₀` carries a commutative group
scheme structure over `Y` whose base change is the given one: `qV` maps products of points of `V`
to products of points of `V₀`. Such a structure is unique by
`existsUnique_grpObj_of_isPullback`.

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
  obtain ⟨G, hG, -⟩ := D.existsUnique_grpObj_of_isPullback qV hqV hDV hμ hη
  have : IsCommMonObj V₀ := (isCommMonObj_iff_isMulCommutative V₀).2 fun T ↦
    ⟨⟨fun x y ↦ liftPoint_injective hqV (by
      rw [liftPoint_mul_of_descendPoint_mul hqV hG, liftPoint_mul_of_descendPoint_mul hqV hG,
        mul_comm])⟩⟩
  exact ⟨{ }, hG⟩

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

end AlgebraicGeometry
