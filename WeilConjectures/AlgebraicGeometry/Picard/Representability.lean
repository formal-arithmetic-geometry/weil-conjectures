/-
Copyright (c) 2026 Orchestra Agent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Representability
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.Picard.Defs

/-!
# Representability of the Picard functor of a smooth projective curve

Let `k` be a separably closed field, let `f : X ⟶ Spec k` be a smooth projective curve and let
`σ` be a `k`-rational point of `X`.  Write `G = Pic_{X/k,σ}` for the `σ`-normalized Picard
functor (`AlgebraicGeometry.picardFunctorNormalized`).  This file states the four steps of the
representability argument:

* the subfunctor `F ⊆ G` cut out by the condition that `Rf_{T,*} ℒ` is an invertible
  `𝒪_T`-module placed in degree `0`;
* `F ⊆ G` is representable by open immersions;
* the general criterion: a Zariski sheaf of groups with a representable open subfunctor that
  generates it under translation is representable by a group scheme;
* the resulting representability of `Pic_{X/k}`.

## Main definitions

- `AlgebraicGeometry.picardFunctorF`: the subfunctor `F ⊆ Pic_{X/k,σ}` (blueprint
  `sk-def-picard-f`).

## Main statements

- `AlgebraicGeometry.isOpenImmersion_picardFunctorF_ι`: `F` is an open subfunctor of
  `Pic_{X/k,σ}` (blueprint `sk-lem-picard-f-open`).
- `AlgebraicGeometry.isRepresentable_of_representable_open_subfunctor`: the representability
  criterion (blueprint `sk-thm-picard-criterion`).
- `AlgebraicGeometry.isRepresentable_picardFunctor`: the Picard functor of a smooth projective
  curve over a separably closed field is representable by a group scheme (blueprint
  `sk-thm-picard-main`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Blueprint `sk-def-picard-f`: The subfunctor `F`

Let `k` be a separably closed field, let `f : X ⟶ Spec k` be a smooth projective curve of genus
`g` with a `k`-rational point `σ`, and let `G = Pic_{X/k,σ}` be the `σ`-normalized Picard
functor.  The subfunctor `F ⊆ G` is
`F(T) = {ℒ ∈ G(T) | Rf_{T,*} ℒ is an invertible 𝒪_T-module placed in degree 0}`,
where `f_T : X_T ⟶ T` is the base change of `f`.

There is no derived category of `X.Modules` available, so the condition "`Rf_{T,*} ℒ` is an
invertible module in degree `0`" is spelled out concretely: `R⁰f_{T,*} ℒ` is invertible and
`R^q f_{T,*} ℒ = 0` for all `q > 0`.  The higher direct images are the right derived functors
of `AlgebraicGeometry.Scheme.Modules.pushforward f_T`; they are used inline rather than through
a named definition, to avoid competing with the `R^q f_*` of the cohomology block.

A class `ℒ ∈ Pic (X_T)` is represented by the canonical sheaf of modules
`(fromSkeleton _).obj ℒ.val` attached to its isomorphism class, and the condition only depends
on the isomorphism class, so this is well defined.  Being a `CategoryTheory.Subfunctor`, `F`
comes with the inclusion natural transformation `(picardFunctorF f σ hσ).ι` into
`(picardFunctorNormalized f σ hσ).toFunctor`. -/
noncomputable def picardFunctorF (f : X ⟶ Spec (.of k)) (σ : Spec (.of k) ⟶ X)
    (hσ : σ ≫ f = 𝟙 (Spec (.of k)))
    [∀ T : Over (Spec (.of k)), HasInjectiveResolutions (Limits.pullback f T.hom).Modules] :
    Subfunctor (picardFunctorNormalized f σ hσ).toFunctor where
  obj T :=
    {L | SheafOfModules.IsInvertible
          (((Modules.pushforward (Limits.pullback.snd f T.unop.hom)).rightDerived 0).obj
            ((fromSkeleton _).obj (L : (picardPresheaf f).obj T).val)) ∧
      ∀ q : ℕ, 0 < q →
        IsZero (((Modules.pushforward (Limits.pullback.snd f T.unop.hom)).rightDerived q).obj
          ((fromSkeleton _).obj (L : (picardPresheaf f).obj T).val))}
  map := by
    -- Cohomology and base change; not proved here.
    sorry

/-- Blueprint `sk-lem-picard-f-open`: `F` is an open subfunctor

The inclusion `F ⊆ G = Pic_{X/k,σ}` is a subfunctor by construction
(`AlgebraicGeometry.picardFunctorF`), and it is representable by open immersions.

Since `F` and `G` are presheaves on the category `Over (Spec k)` of `k`-schemes with values in
`Type (u + 1)`, the property is expressed through `CategoryTheory.MorphismProperty.relative` for
the functor `CategoryTheory.uliftYoneda.{u + 1}` rather than through
`CategoryTheory.MorphismProperty.presheaf`, which is the special case of `yoneda` and therefore
only applies to `Type u`-valued presheaves.  The morphism property on `Over (Spec k)` is the
inverse image of `AlgebraicGeometry.IsOpenImmersion` under `CategoryTheory.Over.forget`. -/
theorem isOpenImmersion_picardFunctorF_ι [IsSepClosed k] (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIntegral f]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 (Spec (.of k)))
    [∀ T : Over (Spec (.of k)), HasInjectiveResolutions (Limits.pullback f T.hom).Modules] :
    (IsOpenImmersion.inverseImage (Over.forget (Spec (.of k)))).relative
      uliftYoneda.{u + 1} (picardFunctorF f σ hσ).ι := by
  sorry

/-- Blueprint `sk-thm-picard-criterion`: The criterion: a functor generated by a representable
open subfunctor

Let `G : (Sch/k)ᵒᵖ ⥤ Grp` be a presheaf of groups on the category of `k`-schemes such that

1. `G` is a Zariski sheaf;
2. there is a subfunctor `F ⊆ G` with
   (a) `F` representable,
   (b) the inclusion `F ⊆ G` representable by open immersions,
   (c) *generation*: for every field extension `K/k` and every `g ∈ G(K)` there is a
       `g' ∈ G(k)` with `g' g ∈ F(K)`.

Then `G` is representable by a group scheme over `k`.

The group-valued formulation `(Over (Spec k))ᵒᵖ ⥤ GrpCat` is the one used here: it is what makes
the product `g' g` in (2)(c) available, and it is the shape expected by
`CategoryTheory.GrpObj.ofRepresentableBy`.  The underlying presheaf of sets is
`G ⋙ forget GrpCat`, and `F` is a `CategoryTheory.Subfunctor` of it.  As in
`AlgebraicGeometry.isOpenImmersion_picardFunctorF_ι`, representability by open immersions is
`CategoryTheory.MorphismProperty.relative` for `CategoryTheory.uliftYoneda`. -/
theorem isRepresentable_of_representable_open_subfunctor
    (G : (Over (Spec (.of k)))ᵒᵖ ⥤ GrpCat.{u + 1})
    (F : Subfunctor (G ⋙ forget GrpCat.{u + 1}))
    (hG : Presheaf.IsSheaf (Scheme.zariskiTopology.over (Spec (.of k)))
      (G ⋙ forget GrpCat.{u + 1}))
    (hFrep : F.toFunctor.IsRepresentable)
    (hFopen : (IsOpenImmersion.inverseImage (Over.forget (Spec (.of k)))).relative
      uliftYoneda.{u + 1} F.ι)
    (hgen : ∀ (K : Type u) (_ : Field K) (_ : Algebra k K)
      (g : G.obj (.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))))),
      ∃ g' : G.obj (.op (Over.mk (𝟙 (Spec (.of k))))),
        (G.map (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
            (by simp) : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶
              Over.mk (𝟙 (Spec (.of k)))).op).hom g' * g ∈
          F.obj (.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))))) :
    ∃ (A : Over (Spec (.of k))) (_ : GrpObj A),
      Nonempty ((G ⋙ forget GrpCat.{u + 1}).RepresentableBy A) := by
  sorry

/-- Blueprint `sk-thm-picard-main`: The Picard functor of a smooth projective curve over a
separably closed field is representable

Let `k` be a separably closed field and let `f : X ⟶ Spec k` be a smooth projective curve.  Then
the Picard functor `Pic_{X/k} = AlgebraicGeometry.picardFunctor f` is representable, and the
representing object is a group scheme over `k`, i.e. it carries a `CategoryTheory.GrpObj`
structure in `Over (Spec k)`. -/
theorem isRepresentable_picardFunctor [IsSepClosed k] (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIntegral f] :
    (picardFunctor f).obj.IsRepresentable ∧
      ∃ (A : Over (Spec (.of k))) (_ : GrpObj A),
        Nonempty ((picardFunctor f).obj.RepresentableBy A) := by
  sorry

end AlgebraicGeometry
