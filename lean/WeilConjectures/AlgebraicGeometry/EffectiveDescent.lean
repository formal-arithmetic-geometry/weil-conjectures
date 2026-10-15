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
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Sheaf.FieldTheory.CommonExtensionFields
import Sheaf.RingTheory.RelativeSmoothDimensionDescent
import Sheaf.AlgebraicGeometry.InvariantAffineNeighbourhoods
import Sheaf.AlgebraicGeometry.InvariantAffineDescentGluing
import Sheaf.AlgebraicGeometry.CommMonoidDescent
import Sheaf.AlgebraicGeometry.IsProperOfFieldBaseChange
import Sheaf.AlgebraicGeometry.FpqcDescendQuasiCompact
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum

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
  apply isEffective_of_invariant_affine_neighbourhoods D
  intro v
  obtain ⟨U, hv, hU, hB, hstable⟩ := exists_invariant_affine_neighbourhood hV D v
  exact ⟨U, hv, hU, hB, hstable⟩

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
  have : Flat qV := MorphismProperty.of_isPullback hqV.flip inferInstance
  have : Surjective qV := MorphismProperty.of_isPullback hqV.flip inferInstance
  have : QuasiCompact qV := MorphismProperty.of_isPullback hqV.flip inferInstance
  have hc : ∀ {T : Scheme.{u}} (a b : T ⟶ V.left),
      a ≫ qV = b ≫ qV → a ≫ (ψ.left ≫ qW) = b ≫ (ψ.left ≫ qW) := by
    intro T a b hab
    have hf : (a ≫ V.hom) ≫ p = (b ≫ V.hom) ≫ p := by
      simpa only [Category.assoc, ← hqV.w] using congrArg (· ≫ V₀.hom) hab
    let aa : Over.mk (a ≫ V.hom) ⟶ V := Over.homMk a
    let bb : Over.mk (b ≫ V.hom) ⟶ V := Over.homMk b
    have ht : D.transport (a ≫ V.hom) (b ≫ V.hom) hf aa = bb := by
      ext : 1
      apply hqV.hom_ext
      · exact (hDV _ _ hf aa).trans hab
      · simp
    have hw := hEW (a ≫ V.hom) (b ≫ V.hom) hf (aa ≫ ψ)
    rw [hψ, ht] at hw
    exact hw.symm
  let ψ₀ := EffectiveEpi.desc qV (ψ.left ≫ qW) hc
  have hfac : qV ≫ ψ₀ = ψ.left ≫ qW := EffectiveEpi.fac _ _ _
  have hover : ψ₀ ≫ W₀.hom = V₀.hom := by
    apply (cancel_epi qV).1
    rw [← Category.assoc, hfac, Category.assoc, hqW.w, ← Category.assoc,
      Over.w ψ, hqV.w]
  refine ⟨Over.homMk ψ₀ hover, hfac.symm, ?_⟩
  intro z hz
  ext : 1
  apply (cancel_epi qV).1
  exact hz.symm.trans hfac.symm

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
products of points of `V₀`. Such a structure is unique, by the same token.

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
  obtain ⟨M, hcomm, hprod, hunit⟩ :=
    exists_commMonObj_of_effective_projection D qV hqV hDV hμ hη
  let : MonObj V₀ := M
  have : IsCommMonObj V₀ := hcomm
  have hinv : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
      (a : Over.mk f₁ ⟶ V),
      D.transport f₁ f₂ h (a ≫ ι[V]) = D.transport f₁ f₂ h a ≫ ι[V] := by
    intro T f₁ f₂ h a
    let F : (Over.mk f₁ ⟶ V) →* (Over.mk f₂ ⟶ V) :=
      { toFun := D.transport f₁ f₂ h
        map_one' := hη f₁ f₂ h
        map_mul' := hμ f₁ f₂ h }
    exact F.map_inv a
  obtain ⟨i₀, hi₀, _⟩ := existsUnique_hom_of_isPullback D D qV hqV hDV
    qV hqV hDV ι[V] hinv
  let a : Over.mk V.hom ⟶ V := Over.homMk (𝟙 V.left)
  let q₀ := descendPoint hqV a
  have hia : descendPoint hqV (a ≫ ι[V]) = q₀ ≫ i₀ := by
    ext : 1
    simpa [a, q₀, descendPoint] using hi₀
  have hleft : lift (q₀ ≫ i₀) q₀ ≫ μ[V₀] = toUnit _ ≫ η[V₀] := by
    rw [← hia]
    calc
      lift (descendPoint hqV (a ≫ ι[V])) (descendPoint hqV a) ≫ μ[V₀] =
          descendPoint hqV (lift (a ≫ ι[V]) a ≫ μ[V]) := by
        ext : 1
        exact (hprod V.hom (a ≫ ι[V]) a).symm
      _ = descendPoint hqV (toUnit _ ≫ η[V]) := by
        congr 1
        simp [a]
      _ = toUnit _ ≫ η[V₀] := by
        ext : 1
        exact hunit V.hom
  have hright : lift q₀ (q₀ ≫ i₀) ≫ μ[V₀] = toUnit _ ≫ η[V₀] := by
    rw [← hia]
    calc
      lift (descendPoint hqV a) (descendPoint hqV (a ≫ ι[V])) ≫ μ[V₀] =
          descendPoint hqV (lift a (a ≫ ι[V]) ≫ μ[V]) := by
        ext : 1
        exact (hprod V.hom a (a ≫ ι[V])).symm
      _ = descendPoint hqV (toUnit _ ≫ η[V]) := by
        congr 1
        simp [a]
      _ = toUnit _ ≫ η[V₀] := by
        ext : 1
        exact hunit V.hom
  have : Flat qV := MorphismProperty.of_isPullback hqV.flip inferInstance
  have : Surjective qV := MorphismProperty.of_isPullback hqV.flip inferInstance
  have : QuasiCompact qV := MorphismProperty.of_isPullback hqV.flip inferInstance
  let G : GrpObj V₀ :=
    { M with
      inv := i₀
      left_inv := by
        ext : 1
        apply (cancel_epi qV).1
        have hh : q₀ ≫ (lift i₀ (𝟙 V₀) ≫ μ[V₀]) =
            q₀ ≫ (toUnit V₀ ≫ η[V₀]) := by
          simpa only [← Category.assoc, comp_lift, Category.comp_id,
            comp_toUnit] using hleft
        have hq₀ : q₀.left = qV := by simp [q₀, a, descendPoint]
        simpa only [Over.comp_left, hq₀] using congrArg Over.Hom.left hh
      right_inv := by
        ext : 1
        apply (cancel_epi qV).1
        have hh : q₀ ≫ (lift (𝟙 V₀) i₀ ≫ μ[V₀]) =
            q₀ ≫ (toUnit V₀ ≫ η[V₀]) := by
          simpa only [← Category.assoc, comp_lift, Category.comp_id,
            comp_toUnit] using hright
        have hq₀ : q₀.left = qV := by simp [q₀, a, descendPoint]
        simpa only [Over.comp_left, hq₀] using congrArg Over.Hom.left hh }
  let : GrpObj V₀ := G
  refine ⟨inferInstance, ?_⟩
  intro T f a b
  ext : 1
  exact hprod f a b

end CategoryTheory.Over.DescentDatum

namespace AlgebraicGeometry

private theorem integral_of_flat_surjective {A B : Scheme.{u}} (f : A ⟶ B)
    [Flat f] [Surjective f] [IsIntegral A] : IsIntegral B := by
  have : IrreducibleSpace B := f.surjective.irreducibleSpace f.continuous
  have (b : B) : _root_.IsReduced (B.presheaf.stalk b) := by
    obtain ⟨a, rfl⟩ := f.surjective b
    let φ := (f.stalkMap a).hom
    let := φ.toAlgebra
    have : IsLocalHom (algebraMap (B.presheaf.stalk (f a)) (A.presheaf.stalk a)) :=
      inferInstanceAs (IsLocalHom (f.stalkMap a).hom)
    have : Module.Flat (B.presheaf.stalk (f a)) (A.presheaf.stalk a) := Flat.stalkMap f a
    have : Module.FaithfullyFlat (B.presheaf.stalk (f a)) (A.presheaf.stalk a) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact isReduced_of_injective φ (FaithfulSMul.algebraMap_injective
      (B.presheaf.stalk (f a)) (A.presheaf.stalk a))
  have : IsReduced B := isReduced_of_isReduced_stalk B
  exact isIntegral_of_irreducibleSpace_of_isReduced B

private theorem geometricallyIntegral_of_field_pullback {k K : Type u}
    [Field k] [Field K] [Algebra k K] {Z Z' : Scheme.{u}} (z : Z ⟶ Spec (.of k))
    (z' : Z' ⟶ Spec (.of K)) (q : Z' ⟶ Z)
    (h : IsPullback q z' z (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [GeometricallyIntegral z'] : GeometricallyIntegral z := by
  rw [GeometricallyIntegral.eq_geometrically]
  rw [geometrically_iff_of_commRing]
  intro L _ _ A a b hs
  obtain ⟨M, hM, hMk, i, j, _, _⟩ := Field.exists_common_extension k K L
  let im := Spec.map (CommRingCat.ofHom i.toRingHom)
  let jm := Spec.map (CommRingCat.ofHom j.toRingHom)
  let pk := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let pl := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have hij : im ≫ pk = jm ≫ pl := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact (i.commutes x).trans (j.commutes x).symm
  let W := pullback z' im
  let w₁ : W ⟶ Z' := pullback.fst z' im
  let w₂ : W ⟶ Spec (.of M) := pullback.snd z' im
  have hw : IsPullback w₁ w₂ z' im := .of_hasPullback z' im
  have hi : IsIntegral W := GeometricallyIntegral.geometrically_isIntegral
    im w₁ w₂ hw
  have ht : IsPullback (w₁ ≫ q) w₂ z (jm ≫ pl) := by
    rw [← hij]
    exact hw.paste_horiz h
  let r : W ⟶ A := hs.lift (w₁ ≫ q) (w₂ ≫ jm) (by
    simpa only [Category.assoc] using ht.w)
  have hra : r ≫ a = w₁ ≫ q := by simp [r]
  have hrb : r ≫ b = w₂ ≫ jm := by simp [r]
  have hr : IsPullback r w₂ b jm := by
    apply IsPullback.of_right (h₁₂ := a) (v₁₃ := z) (h₂₂ := pl)
    · simpa only [hra] using ht
    · exact hrb
    · exact hs
  have : Flat jm := by
    dsimp [jm]
    infer_instance
  have : Surjective jm := by
    dsimp [jm]
    infer_instance
  have : Flat r := MorphismProperty.of_isPullback hr.flip inferInstance
  have : Surjective r := MorphismProperty.of_isPullback hr.flip inferInstance
  exact integral_of_flat_surjective r

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
    IsProper z ∧ SmoothOfRelativeDimension n z ∧ GeometricallyIntegral z := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hp : (Surjective p ∧ Flat p) ∧ QuasiCompact p := by
    dsimp [p]
    exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension n) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  let : MorphismProperty.DescendsAlong (@SmoothOfRelativeDimension n)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    HasRingHomProperty.descendsAlong_flat
      (RingHom.locally_standardSmoothOfRelativeDimension_codescendsAlong_faithfullyFlat n)
  have hdim : SmoothOfRelativeDimension n z :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := @SmoothOfRelativeDimension n)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h.flip hp inferInstance
  have : Smooth z := SmoothOfRelativeDimension.smooth n z
  have hqc' : QuasiCompact (pullback.snd z p) := by
    have heq : pullback.snd z p = h.isoPullback.inv ≫ z' := by
      simp [p]
    rw [heq]
    infer_instance
  have hqc : QuasiCompact z := quasiCompact_of_fpqc_baseChange p z
  have hproper' : IsProper (pullback.snd z p) := by
    have heq : pullback.snd z p = h.isoPullback.inv ≫ z' := by
      simp [p]
    rw [heq]
    infer_instance
  have hproper : IsProper z := isProper_of_field_baseChange (K := K) z
  exact ⟨hproper, hdim, geometricallyIntegral_of_field_pullback z z' q h⟩

end AlgebraicGeometry
