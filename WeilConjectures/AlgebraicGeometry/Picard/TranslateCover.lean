/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Scheme

/-!
# The Picard scheme is covered by translates of its chart

Let `k` be a separably closed field, `X` a smooth projective curve over `k` and `σ` a
`k`-rational point of `X`. The Picard functor `Pic_{X/k}` is represented by a group scheme `A`
(`AlgebraicGeometry.isRepresentable_picardFunctor`), which also represents the `σ`-normalized
Picard functor `G = Pic_{X/k,σ}`. Let `F ⊆ G` be the open subfunctor of classes with invertible
direct image (`AlgebraicGeometry.picardFunctorInvertibleDirectImage`). We show that `A` is locally
of finite type over `k` and is covered by open subschemes representing the translates
`M⁻¹F = {ℒ | M ⊗ ℒ ∈ F}` of `F` by classes `M ∈ G(k)`.

## Main statements

- `AlgebraicGeometry.exists_opens_mul_mem_iff_of_representable_open_subfunctor`: in the
  representability criterion `AlgebraicGeometry.isRepresentable_of_representable_open_subfunctor`,
  the representing scheme is covered by open subschemes representing translates of `F`.
- `AlgebraicGeometry.exists_representableBy_picardFunctor_and_opens_translate`: the Picard scheme
  of a smooth projective curve over a separably closed field is locally of finite type and is
  covered by open subschemes representing the translates of `F`.

## References

* [Stacks, Tag 0B9Q], [Stacks, Tag 0B9Z]
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- **The representing scheme is covered by translates of the open subfunctor.** In the situation
of `AlgebraicGeometry.isRepresentable_of_representable_open_subfunctor`, let `A'` represent `G`.
Then every point `a` of `A'` lies in an open subscheme `U ⊆ A'` representing a translate
`g'⁻¹F = {x | g' x ∈ F}` of `F` by a class `g' ∈ G(k)`: a morphism `c : T ⟶ A'` factors through
`U` if and only if `g'|_T` times the class of `c` lies in `F(T)`. -/
theorem exists_opens_mul_mem_iff_of_representable_open_subfunctor
    (G : (Over (Spec (.of k)))ᵒᵖ ⥤ GrpCat.{u + 1})
    (F : Subfunctor (G ⋙ forget GrpCat.{u + 1}))
    (hFopen : (IsOpenImmersion.inverseImage (Over.forget (Spec (.of k)))).relative
      uliftYoneda.{u + 1} F.ι)
    (hgen : ∀ (K : Type u) [Field K] [Algebra k K]
      (g : G.obj (.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))))),
      ∃ g' : G.obj (.op (Over.mk (𝟙 (Spec (.of k))))),
        (G.map (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
            (by simp) : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶
              Over.mk (𝟙 (Spec (.of k)))).op).hom g' * g ∈
          F.obj (.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))))
    {A' : Over (Spec (.of k))} (e' : (G ⋙ forget GrpCat.{u + 1}).RepresentableBy A')
    (a : A'.left) :
    ∃ (g' : G.obj (op (Over.mk (𝟙 (Spec (.of k)))))) (U : A'.left.Opens), a ∈ U ∧
      ∀ {W : Over (Spec (.of k))} (c : W ⟶ A'),
        (G.map (Over.homMk W.hom (by simp) : W ⟶ Over.mk (𝟙 (Spec (.of k)))).op).hom g' *
            (show G.obj (op W) from e'.homEquiv c) ∈ F.obj (op W) ↔ Set.range c.left ⊆ U := by
  let P := G ⋙ forget GrpCat.{u + 1}
  -- restriction of a `k`-point `g ∈ G(k)` to `T`
  let r (T : Over (Spec (.of k))) (g : G.obj (op (Over.mk (𝟙 (Spec (.of k)))))) :
      G.obj (op T) :=
    (G.map (Over.homMk T.hom (by simp) : T ⟶ Over.mk (𝟙 (Spec (.of k)))).op).hom g
  have hr {T W : Over (Spec (.of k))} (c : W ⟶ T) (g) : (G.map c.op).hom (r T g) = r W g := by
    simp only [r, ← GrpCat.comp_apply, ← G.map_comp, ← op_comp]
    congr 4
    ext
    simp
  have hP {T W : Over (Spec (.of k))} (c : W ⟶ T) (y : G.obj (op T)) :
      P.map c.op y = (G.map c.op).hom y := rfl
  let x : G.obj (op A') := e'.homEquiv (𝟙 A')
  have he' {W : Over (Spec (.of k))} (c : W ⟶ A') : e'.homEquiv c = (G.map c.op).hom x := by
    rw [← Category.comp_id c, e'.homEquiv_comp]
    rfl
  -- the residue field of `a`, and a class `g' ∈ G(k)` translating `x` into `F` at `a`
  let K := A'.left.residueField a
  let φ : CommRingCat.of k ⟶ K := Spec.preimage (A'.left.fromSpecResidueField a ≫ A'.hom)
  let : Algebra k K := φ.hom.toAlgebra
  have hK : Spec.map (CommRingCat.ofHom (algebraMap k K)) =
      A'.left.fromSpecResidueField a ≫ A'.hom := by
    rw [← Spec.map_preimage (A'.left.fromSpecResidueField a ≫ A'.hom)]
    rfl
  let pa : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A' :=
    Over.homMk (A'.left.fromSpecResidueField a) hK.symm
  obtain ⟨g', hg'⟩ := hgen K (P.map pa.op x)
  -- the open `U ⊆ A'` over which `r g' * x` lies in `F`
  obtain ⟨U, hU⟩ := exists_opens_of_relative_isOpenImmersion hFopen A' (r A' g' * x)
  have hUiff {W : Over (Spec (.of k))} (c : W ⟶ A') :
      r W g' * (show G.obj (op W) from e'.homEquiv c) ∈ F.obj (op W) ↔ Set.range c.left ⊆ U := by
    rw [← hU, he']
    simp only [P, hP, map_mul, hr]
  refine ⟨g', U, ?_, hUiff⟩
  have ha : Set.range pa.left ⊆ U := by
    rw [← hUiff, he']
    exact hg'
  exact ha (Scheme.range_fromSpecResidueField a ▸ Set.mem_singleton a)

section Curve

variable [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [GeometricallyIntegral (X ↘ Spec (.of k))]

/-- **Representability of the Picard functor, with its chart and translates.** Let `X` be a smooth
projective geometrically integral curve over a separably closed field `k`, and let `σ` be a
`k`-rational point of `X`. Then `Pic_{X/k}` is represented by a group scheme `A` locally of finite
type over `k`, which is also a representing object for the `σ`-normalized Picard functor
`G = Pic_{X/k,σ}` by `e'`. Let `F ⊆ G` be the open subfunctor of classes with invertible direct
image (`AlgebraicGeometry.picardFunctorInvertibleDirectImage`). Then `A` is covered by open
subschemes `U` representing the translates `M⁻¹F = {ℒ | M ⊗ ℒ ∈ F}`, `M ∈ G(k)`: a morphism
`c : T ⟶ A` factors through `U` if and only if `M|_T` times the class `e' c` lies in `F(T)`. -/
theorem exists_representableBy_picardFunctor_and_opens_translate [IsSepClosed k]
    [∀ T : Over (Spec (.of k)),
      HasInjectiveResolutions (pullback (X ↘ Spec (.of k)) T.hom).Modules]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ X ↘ Spec (.of k) = 𝟙 _) :
    ∃ (A : Over (Spec (.of k))) (_ : GrpObj A)
      (_ : (picardFunctor (X ↘ Spec (.of k))).obj.RepresentableBy A)
      (e' : (picardFunctorNormalizedGrp (X ↘ Spec (.of k)) σ hσ ⋙
        forget GrpCat.{u + 1}).RepresentableBy A),
      LocallyOfFiniteType A.hom ∧
      ∀ a : A.left, ∃ (M : (picardFunctorNormalizedGrp (X ↘ Spec (.of k)) σ hσ).obj
          (op (Over.mk (𝟙 (Spec (.of k)))))) (U : A.left.Opens), a ∈ U ∧
        ∀ {T : Over (Spec (.of k))} (c : T ⟶ A),
          ((picardFunctorNormalizedGrp (X ↘ Spec (.of k)) σ hσ).map
              (Over.homMk T.hom (by simp) : T ⟶ Over.mk (𝟙 (Spec (.of k)))).op).hom M *
              (show (picardFunctorNormalizedGrp (X ↘ Spec (.of k)) σ hσ).obj (op T) from
                e'.homEquiv c) ∈
            (picardFunctorInvertibleDirectImage (X ↘ Spec (.of k)) σ hσ).obj (op T) ↔
          Set.range c.left ⊆ U := by
  set f := X ↘ Spec (.of k)
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
  obtain ⟨A, _, e, -, -, hA, -⟩ := representability_picardFunctor (k := k) (X := X)
  let e' : (picardFunctorNormalizedGrp f σ hσ ⋙ forget GrpCat.{u + 1}).RepresentableBy A :=
    e.ofIso (nonempty_picardFunctorNormalized_iso_picardFunctor σ hσ).some.symm
  exact ⟨A, inferInstance, e, e', hA, fun a ↦
    exists_opens_mul_mem_iff_of_representable_open_subfunctor _ _
      (isOpenImmersion_picardFunctorInvertibleDirectImage_ι f σ hσ)
      (exists_mul_mem_picardFunctorInvertibleDirectImage σ hσ) e' a⟩

end Curve

end AlgebraicGeometry
