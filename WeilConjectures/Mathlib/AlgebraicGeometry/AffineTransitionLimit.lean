/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation

/-!
# Cofiltered limits of schemes with affine transition morphisms

## Noetherian approximation of quasi-compact quasi-separated schemes

A *Noetherian approximation* of a scheme `S` is a cofiltered system of schemes of finite type
over `ℤ` with affine transition morphisms, together with a limit cone over the system with
point `S` (`AlgebraicGeometry.Scheme.NoetherianApproximation`). The stages of such a system
are Noetherian schemes (`AlgebraicGeometry.Scheme.NoetherianApproximation.isNoetherian_obj`).

Absolute Noetherian approximation (Stacks Project Tag 01ZA) asserts that every
quasi-compact quasi-separated scheme admits a Noetherian approximation
(`AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`).

In this file we prove the affine case: for an affine scheme `S`, the spectra of the
finitely generated `ℤ`-subalgebras of `Γ(S, ⊤)` form a Noetherian approximation
(`AlgebraicGeometry.Scheme.NoetherianApproximation.ofIsAffine`). The key algebraic input
is that `Γ(S, ⊤)` is the filtered colimit of its finitely generated `ℤ`-subalgebras
(`CommRingCat.isColimitFgSubalgebraCocone`), and the geometric translation is that `Spec`,
being a right adjoint, preserves limits.

Throughout, "of finite type over `ℤ`" is spelled out as `LocallyOfFiniteType` of the
structure morphism `specULiftZIsTerminal.from X : X ⟶ Spec ℤ` together with
`CompactSpace X`.

(Blueprint: `def:nagata-noetherian-inverse-system`, `prop:nagata-noetherian-inverse-system`.)

## Checking the limit property locally on a stage

Mathlib's `AlgebraicGeometry.isLimitOpensCone` says that a limit cone over a cofiltered diagram
`{Dᵢ}` of schemes restricts, over any open `V ⊆ Dᵢ`, to a limit cone over the diagram of the
preimages of `V`. Here we prove the converse: a cone `c` over `{Dᵢ}` is a limit cone as soon as
its restrictions to the members of an open cover of one stage, and to their pairwise
intersections, are limit cones (`AlgebraicGeometry.isLimitOfIsLimitOpensCone`). No assumption on
the transition morphisms is needed. This is how the limit property of the system constructed for
Tag 01ZA is verified, chart by chart.

## The stages of the induction step of absolute Noetherian approximation

The general case of Tag 01ZA is proved by induction over a finite affine cover, extending an
approximation of a quasi-compact open `U` of `X` across one more affine open `V`
(Stacks Project Tag 07RN). The data of one induction step is bundled into
`AlgebraicGeometry.Scheme.NoetherianApproximation.ExtensionData`, and the index category of
the extended system is the category
`AlgebraicGeometry.Scheme.NoetherianApproximation.ExtensionData.Stage` of *stages*: a stage
consists of an index `j` of the approximation of `U`, lifts to the stage `j` of finitely many
sections of `V` whose basic opens cover `W = U ⊓ V`, and a finitely generated `ℤ`-subalgebra
`A` of the fiber product `Γ(X, V) ×_{Γ(W, 𝒪)} Γ(Wⱼ, 𝒪)` big enough that `Wⱼ` becomes a
quasi-affine open of `Spec A` (`Stage.isOpenImmersion_toSpec`, Tags 01Z7 and 01Z9).

The two structural facts that drive the induction are that the stages form a cofiltered
category, and that the functor `ExtensionData.stageIndex` remembering the underlying index is
initial; so limits over the system of the `Wⱼ` may be computed over the category of stages.

## Descending schemes of finite presentation along an inverse limit of affine schemes

Let `{Dᵢ}` be a cofiltered inverse system of affine schemes with affine transition maps. If `X`
is an affine scheme that is locally of finite presentation over `lim Dᵢ`, then `X` is the base
change of an affine scheme that is locally of finite presentation over one of the `Dᵢ`
(`AlgebraicGeometry.Scheme.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine`).

The same holds for an arbitrary scheme `X` of finite presentation over `lim Dᵢ`, and more
generally over a limit of quasi-compact quasi-separated schemes
(`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation`, Stacks Project Tag 01ZM):
one covers `X` by finitely many affine opens, each lying over an affine open of a fixed stage,
and glues the finite-stage models of the charts over a common stage. The two auxiliary steps
are that a quasi-compact open of `X` descends to a stage
(`AlgebraicGeometry.exists_descendsAtWithOpen`) and that two finite-stage models of the
same scheme become isomorphic at a later stage
(`AlgebraicGeometry.exists_iso_of_isPullback`).

## References

- [Stacks: Tag 01Z7](https://stacks.math.columbia.edu/tag/01Z7)
- [Stacks: Tag 01Z9](https://stacks.math.columbia.edu/tag/01Z9)
- [Stacks: Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
- [Stacks: Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
- [Stacks: Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section FiniteTypeOverInt

/-- `Spec ℤ` is a locally Noetherian scheme. -/
instance isLocallyNoetherian_spec_uliftInt :
    IsLocallyNoetherian (Spec <| .of <| ULift.{u} ℤ) :=
  have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  inferInstance

/-- The spectrum of a `ℤ`-algebra of finite type is locally of finite type over `Spec ℤ`. -/
instance locallyOfFiniteType_specULiftZIsTerminal_from (R : Type u) [CommRing R]
    [Algebra.FiniteType ℤ R] :
    LocallyOfFiniteType (specULiftZIsTerminal.from (Spec <| .of R)) := by
  have hφ : RingHom.FiniteType ((algebraMap ℤ R).comp (ULift.ringEquiv (R := ℤ)).toRingHom) :=
    (RingHom.finiteType_algebraMap.mpr ‹_›).comp
      (RingHom.FiniteType.of_surjective _ ULift.ringEquiv.surjective)
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      ((algebraMap ℤ R).comp (ULift.ringEquiv (R := ℤ)).toRingHom))) :=
    HasRingHomProperty.Spec_iff.mpr hφ
  rwa [specULiftZIsTerminal.hom_ext (specULiftZIsTerminal.from _) (Spec.map _)]

end FiniteTypeOverInt

/-- A **Noetherian approximation** of a scheme `S`: a cofiltered system of schemes of finite
type over `ℤ` with affine transition morphisms, exhibiting `S` as the limit of the system.
The stages are automatically Noetherian, see
`AlgebraicGeometry.Scheme.NoetherianApproximation.isNoetherian_obj`.

```
              S
    π.app i  ↙         ↘  π.app j
  D.obj i  ─────────⟶  D.obj j
                D.map f
```

By absolute Noetherian approximation (Stacks Project Tag 01ZA,
`AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`), every quasi-compact
quasi-separated scheme admits one.
(Blueprint: `def:nagata-noetherian-inverse-system`.) -/
structure Scheme.NoetherianApproximation (S : Scheme.{u}) where
  /-- The index category of the inverse system. -/
  I : Type u
  /-- The category structure on the index type. -/
  [smallCategory : SmallCategory I]
  /-- The index category is cofiltered. -/
  [isCofiltered : IsCofiltered I]
  /-- The diagram of stages. -/
  D : I ⥤ Scheme.{u}
  /-- Every stage is locally of finite type over `ℤ`. -/
  locallyOfFiniteType_obj (i : I) : LocallyOfFiniteType (specULiftZIsTerminal.from (D.obj i))
  /-- Every stage is quasi-compact; together with `locallyOfFiniteType_obj` this says that
  every stage is of finite type over `ℤ`. -/
  compactSpace_obj (i : I) : CompactSpace (D.obj i)
  /-- The transition morphisms of the system are affine. -/
  isAffineHom_map {i j : I} (f : i ⟶ j) : IsAffineHom (D.map f)
  /-- The projections from `S` to the stages. -/
  π : (Functor.const I).obj S ⟶ D
  /-- `S` is the limit of its stages. -/
  isLimit : IsLimit (Cone.mk S π)

namespace Scheme.NoetherianApproximation

attribute [instance] smallCategory isCofiltered locallyOfFiniteType_obj compactSpace_obj
  isAffineHom_map

variable {S : Scheme.{u}}

/-- The stages of a Noetherian approximation are Noetherian schemes: they are of finite type
over the Noetherian ring `ℤ`. -/
instance isNoetherian_obj (N : S.NoetherianApproximation) (i : N.I) : IsNoetherian (N.D.obj i) :=
  have := LocallyOfFiniteType.isLocallyNoetherian (specULiftZIsTerminal.from (N.D.obj i))
  ⟨⟩

/-- Transport a Noetherian approximation along an isomorphism of schemes. -/
noncomputable def ofIso {S' : Scheme.{u}} (e : S ≅ S') (N : S.NoetherianApproximation) :
    S'.NoetherianApproximation where
  I := N.I
  D := N.D
  locallyOfFiniteType_obj := N.locallyOfFiniteType_obj
  compactSpace_obj := N.compactSpace_obj
  isAffineHom_map := N.isAffineHom_map
  π := (Functor.const N.I).map e.inv ≫ N.π
  isLimit := N.isLimit.ofIsoLimit <| Cone.ext e fun i ↦ by simp

/-- Restrict a Noetherian approximation to the over category of one of its indices. -/
noncomputable def over (N : S.NoetherianApproximation) (i : N.I) :
    S.NoetherianApproximation where
  I := Over i
  D := Over.forget i ⋙ N.D
  locallyOfFiniteType_obj _ := N.locallyOfFiniteType_obj _
  compactSpace_obj _ := N.compactSpace_obj _
  isAffineHom_map _ := N.isAffineHom_map _
  π := Functor.whiskerLeft (Over.forget i) N.π
  isLimit := (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) (Cone.mk S N.π)).symm N.isLimit

@[simp] lemma over_I (N : S.NoetherianApproximation) (i : N.I) : (N.over i).I = Over i := rfl

@[simp] lemma over_D (N : S.NoetherianApproximation) (i : N.I) :
    (N.over i).D = Over.forget i ⋙ N.D := rfl

@[simp] lemma over_π_app (N : S.NoetherianApproximation) (i : N.I) (j : Over i) :
    (N.over i).π.app j = N.π.app j.left := rfl

variable (S : Scheme.{u}) [IsAffine S]

/-- **Noetherian approximation of an affine scheme**: the spectra of the finitely
generated `ℤ`-subalgebras of `Γ(S, ⊤)` form a cofiltered system of schemes of finite type
over `ℤ` with affine transition maps whose limit is `S`. This is the affine case of Stacks
Project Tag 01ZA.

For `A ≤ B` the transition morphism `Spec ↥B ⟶ Spec ↥A` is `Spec.map` of the inclusion:

```
              S
    π.app B  ↙         ↘  π.app A
  Spec ↥B  ─────────⟶  Spec ↥A
```
-/
noncomputable def ofIsAffine : S.NoetherianApproximation where
  I := {A : Subalgebra ℤ Γ(S, ⊤) // A.FG}ᵒᵖ
  D := (CommRingCat.fgSubalgebraDiagram Γ(S, ⊤)).op ⋙ Scheme.Spec
  locallyOfFiniteType_obj i :=
    have : Algebra.FiniteType ℤ i.unop.1 := (Subalgebra.fg_iff_finiteType _).mp i.unop.2
    inferInstanceAs (LocallyOfFiniteType (specULiftZIsTerminal.from (Spec (.of i.unop.1))))
  compactSpace_obj i := inferInstanceAs (CompactSpace (Spec (CommRingCat.of i.unop.1)))
  isAffineHom_map f := inferInstanceAs (IsAffineHom (Spec.map _))
  π := (Functor.const _).map S.isoSpec.hom ≫
    (Scheme.Spec.mapCone (CommRingCat.fgSubalgebraCocone Γ(S, ⊤)).op).π
  isLimit :=
    (isLimitOfPreserves Scheme.Spec (CommRingCat.isColimitFgSubalgebraCocone Γ(S, ⊤)).op).ofIsoLimit
      (Cone.ext S.isoSpec.symm fun A ↦ by simp)

end Scheme.NoetherianApproximation

section IsLimitOfOpensCone

/-!
### Checking the limit property locally on a stage

Let `D` be a cofiltered diagram of schemes and `c` a cone over `D`. If the restrictions of
`c` to the members of an open cover of some stage `D.obj i₀` (and to their pairwise
intersections) are limit cones, then `c` is a limit cone. This is a converse to
`AlgebraicGeometry.isLimitOpensCone`.
-/

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- (Implementation) The open cover of the point of a cone `s` over `D` by the preimages of a
covering family of opens of the stage `D.obj i₀`. -/
@[reducible] noncomputable def preimageCover (i₀ : I) {σ : Type*} (U : σ → (D.obj i₀).Opens)
    (hU : ⨆ a, U a = ⊤) (s : Cone D) : s.pt.OpenCover :=
  Scheme.Cover.mkOfCovers σ (fun a ↦ (s.π.app i₀ ⁻¹ᵁ U a).toScheme)
    (fun a ↦ Scheme.Opens.ι _)
    (fun x ↦ by
      have : s.π.app i₀ x ∈ ⨆ a, U a := by rw [hU]; trivial
      obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp this
      exact ⟨a, ⟨x, ha⟩, rfl⟩)

variable {c} in
/-- (Implementation) The universal morphism to the restriction of `c` to an open `V` of the
stage `D.obj i₀`, composed back into the tower of the cone `c`, agrees with the cone `s`. -/
lemma lift_opensCone_ι_comp {i₀ : I} {V : (D.obj i₀).Opens}
    (hV : IsLimit (opensCone D c i₀ V)) (s : Cone D) (j : Over i₀) :
    hV.lift (opensCone D s i₀ V) ≫ (c.π.app i₀ ⁻¹ᵁ V).ι ≫ c.π.app j.left =
      (s.π.app i₀ ⁻¹ᵁ V).ι ≫ s.π.app j.left := by
  have h1 := congrArg (· ≫ (D.map j.hom ⁻¹ᵁ V).ι) (hV.fac (opensCone D s i₀ V) j)
  simp only [opensCone_π_app, Category.assoc, Scheme.Hom.resLE_comp_ι] at h1
  simpa using h1

variable {c} in
/-- (Implementation) Compatibility of the local universal morphisms on overlaps. -/
lemma glueMorphisms_compat {i₀ : I} {σ : Type*} {U : σ → (D.obj i₀).Opens}
    (h : ∀ a, IsLimit (opensCone D c i₀ (U a)))
    (h₂ : ∀ a b, IsLimit (opensCone D c i₀ (U a ⊓ U b))) (s : Cone D) (a b : σ) :
    pullback.fst ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) ≫
        ((h a).lift (opensCone D s i₀ (U a)) ≫ (c.π.app i₀ ⁻¹ᵁ U a).ι) =
      pullback.snd _ _ ≫ ((h b).lift (opensCone D s i₀ (U b)) ≫ (c.π.app i₀ ⁻¹ᵁ U b).ι) := by
  have hq' : pullback.fst ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) ≫
      (s.π.app i₀ ⁻¹ᵁ U a).ι = pullback.snd _ _ ≫ (s.π.app i₀ ⁻¹ᵁ U b).ι :=
    pullback.condition
  have hqmem (t : ↑(pullback ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι))) :
      s.π.app i₀ ((pullback.fst ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) ≫
        (s.π.app i₀ ⁻¹ᵁ U a).ι) t) ∈ U a ⊓ U b := by
    constructor
    · rw [Scheme.Hom.comp_apply]
      exact (pullback.fst ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) t).2
    · rw [hq', Scheme.Hom.comp_apply]
      exact (pullback.snd ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) t).2
  have h0 : ∀ (x : σ), (h x).lift (opensCone D s i₀ (U x)) ≫
      (c.π.app i₀ ⁻¹ᵁ U x).ι ≫ c.π.app i₀ = (s.π.app i₀ ⁻¹ᵁ U x).ι ≫ s.π.app i₀ :=
    fun x ↦ lift_opensCone_ι_comp D (h x) s (Over.mk (𝟙 i₀))
  have key : ∀ (e : pullback ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) ⟶ c.pt),
      e ≫ c.π.app i₀ = (pullback.fst _ _ ≫ (s.π.app i₀ ⁻¹ᵁ U a).ι) ≫ s.π.app i₀ →
      Set.range e ⊆ Set.range ((c.π.app i₀ ⁻¹ᵁ (U a ⊓ U b)).ι) := by
    rintro e he - ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (e ≫ c.π.app i₀) t ∈ U a ⊓ U b
    rw [he]
    exact hqmem t
  have he_a : (pullback.fst ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) ≫
      ((h a).lift (opensCone D s i₀ (U a)) ≫ (c.π.app i₀ ⁻¹ᵁ U a).ι)) ≫ c.π.app i₀ =
      (pullback.fst _ _ ≫ (s.π.app i₀ ⁻¹ᵁ U a).ι) ≫ s.π.app i₀ := by
    simp only [Category.assoc]
    rw [h0 a]
  have he_b : (pullback.snd ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) ≫
      ((h b).lift (opensCone D s i₀ (U b)) ≫ (c.π.app i₀ ⁻¹ᵁ U b).ι)) ≫ c.π.app i₀ =
      (pullback.fst _ _ ≫ (s.π.app i₀ ⁻¹ᵁ U a).ι) ≫ s.π.app i₀ := by
    simp only [Category.assoc]
    rw [h0 b, reassoc_of% hq']
  rw [show pullback.fst ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) ≫
        ((h a).lift (opensCone D s i₀ (U a)) ≫ (c.π.app i₀ ⁻¹ᵁ U a).ι) =
      IsOpenImmersion.lift ((c.π.app i₀ ⁻¹ᵁ (U a ⊓ U b)).ι) _ (key _ he_a) ≫
        (c.π.app i₀ ⁻¹ᵁ (U a ⊓ U b)).ι from (IsOpenImmersion.lift_fac _ _ _).symm,
    show pullback.snd ((s.π.app i₀ ⁻¹ᵁ U a).ι) ((s.π.app i₀ ⁻¹ᵁ U b).ι) ≫
        ((h b).lift (opensCone D s i₀ (U b)) ≫ (c.π.app i₀ ⁻¹ᵁ U b).ι) =
      IsOpenImmersion.lift ((c.π.app i₀ ⁻¹ᵁ (U a ⊓ U b)).ι) _ (key _ he_b) ≫
        (c.π.app i₀ ⁻¹ᵁ (U a ⊓ U b)).ι from (IsOpenImmersion.lift_fac _ _ _).symm]
  congr 1
  apply (h₂ a b).hom_ext
  intro j
  rw [← cancel_mono (D.map j.hom ⁻¹ᵁ (U a ⊓ U b)).ι]
  simp only [opensCone_π_app, Category.assoc, Scheme.Hom.resLE_comp_ι]
  rw [IsOpenImmersion.lift_fac_assoc, IsOpenImmersion.lift_fac_assoc]
  simp only [Category.assoc]
  rw [lift_opensCone_ι_comp D (h a) s j, lift_opensCone_ι_comp D (h b) s j,
    reassoc_of% hq']

/-- **Being a limit cone is local on a stage.** Let `{Dᵢ}` be a cofiltered diagram of schemes and
let `c` be a cone over it. Suppose some stage `D.obj i₀` has an open cover `{U a}` such that the
restriction of `c` to every `U a`, and to every intersection `U a ⊓ U b`, is a limit cone. Then
`c` is a limit cone.

This is a converse to `AlgebraicGeometry.isLimitOpensCone`. -/
noncomputable def isLimitOfIsLimitOpensCone [IsCofiltered I] (i₀ : I) {σ : Type*}
    (U : σ → (D.obj i₀).Opens) (hU : ⨆ a, U a = ⊤)
    (h : ∀ a, IsLimit (opensCone D c i₀ (U a)))
    (h₂ : ∀ a b, IsLimit (opensCone D c i₀ (U a ⊓ U b))) : IsLimit c where
  lift s := (preimageCover D i₀ U hU s).glueMorphisms
    (fun a ↦ (h a).lift (opensCone D s i₀ (U a)) ≫ (c.π.app i₀ ⁻¹ᵁ U a).ι)
    (glueMorphisms_compat D h h₂ s)
  fac s j := by
    obtain ⟨k, fkj, fki₀, -⟩ := IsCofilteredOrEmpty.cone_objs j i₀
    rw [← c.w fkj, ← s.w fkj, ← Category.assoc]
    congr 1
    apply (preimageCover D i₀ U hU s).hom_ext
    intro a
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms]
    change ((h a).lift (opensCone D s i₀ (U a)) ≫ (c.π.app i₀ ⁻¹ᵁ U a).ι) ≫ c.π.app k =
      (s.π.app i₀ ⁻¹ᵁ U a).ι ≫ s.π.app k
    rw [Category.assoc]
    exact lift_opensCone_ι_comp D (h a) s (Over.mk fki₀)
  uniq s m hm := by
    apply (preimageCover D i₀ U hU s).hom_ext
    intro a
    rw [Scheme.Cover.ι_glueMorphisms]
    change (s.π.app i₀ ⁻¹ᵁ U a).ι ≫ m =
      (h a).lift (opensCone D s i₀ (U a)) ≫ (c.π.app i₀ ⁻¹ᵁ U a).ι
    have hrange : Set.range ((s.π.app i₀ ⁻¹ᵁ U a).ι ≫ m) ⊆
        Set.range ((c.π.app i₀ ⁻¹ᵁ U a).ι) := by
      rintro - ⟨t, rfl⟩
      rw [Scheme.Opens.range_ι]
      change (((s.π.app i₀ ⁻¹ᵁ U a).ι ≫ m) ≫ c.π.app i₀) t ∈ U a
      rw [Category.assoc, hm i₀]
      exact t.2
    have hma : IsOpenImmersion.lift ((c.π.app i₀ ⁻¹ᵁ U a).ι)
        ((s.π.app i₀ ⁻¹ᵁ U a).ι ≫ m) hrange = (h a).lift (opensCone D s i₀ (U a)) := by
      apply (h a).hom_ext
      intro j
      rw [← cancel_mono (D.map j.hom ⁻¹ᵁ U a).ι]
      simp only [opensCone_π_app, Category.assoc, Scheme.Hom.resLE_comp_ι]
      rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, hm j.left]
      exact (lift_opensCone_ι_comp D (h a) s j).symm
    rw [← hma, IsOpenImmersion.lift_fac]

@[reassoc]
lemma opensDiagram_map_ι (i : I) (U : (D.obj i).Opens) {j j' : Over i} (k : j ⟶ j') :
    (opensDiagram D i U).map k ≫ Scheme.Opens.ι (D.map j'.hom ⁻¹ᵁ U) =
      Scheme.Opens.ι (D.map j.hom ⁻¹ᵁ U) ≫ D.map k.left :=
  (opensDiagramι D i U).naturality k

@[reassoc]
lemma opensCone_π_ι (c : Cone D) (i : I) (U : (D.obj i).Opens) (j : Over i) :
    (opensCone D c i U).π.app j ≫ Scheme.Opens.ι (D.map j.hom ⁻¹ᵁ U) =
      Scheme.Opens.ι (c.π.app i ⁻¹ᵁ U) ≫ c.π.app j.left :=
  Scheme.Hom.resLE_comp_ι _ _

end IsLimitOfOpensCone

namespace Scheme.NoetherianApproximation

/-!
### The induction step of absolute Noetherian approximation

Following the proof of Stacks Project Tag 07RN, we extend a Noetherian approximation of a
quasi-compact open `U` of a quasi-separated scheme `X` to a Noetherian approximation of
`U ∪ V` for an affine open `V`. The extension is built from *stages*: a stage consists of an
index `j` of (the restriction to a coslice of) the approximation of `U`, a lift `r` of the
generators of `W = U ⊓ V` to sections at the stage `j`, and a finitely generated
`ℤ`-subalgebra `A` of `Γ(X, V) × Γ(Wⱼ, ⊤)` — an algebraic incarnation of the fiber product
`Γ(V) ×_{Γ(W)} Γ(Wⱼ)` of Stacks 07RN. The scheme attached to a stage is the pushout of
`Dⱼ ⟵ Wⱼ ⟶ Spec A` along open immersions.
-/

/-- (Implementation) The setup for the induction step of absolute Noetherian approximation
(Stacks Project Tag 07RN): a quasi-separated scheme `X` covered by a quasi-compact open `U`
carrying a Noetherian approximation `N` and an affine open `V`; the intersection `U ⊓ V`
is descended to a quasi-compact open `W₀` at a stage `i₀` of `N`, and is exhibited as a
finite union of basic opens of sections `b l` of `V`. -/
structure ExtensionData where
  /-- The ambient scheme. -/
  X : Scheme.{u}
  /-- The ambient scheme is quasi-separated. -/
  [qs : QuasiSeparatedSpace X]
  /-- The already approximated quasi-compact open. -/
  U : X.Opens
  /-- The new affine open. -/
  V : X.Opens
  hUV : U ⊔ V = ⊤
  hV : IsAffineOpen V
  /-- A Noetherian approximation of `U`. -/
  N : U.toScheme.NoetherianApproximation
  /-- The stage of `N` at which `U ⊓ V` is descended. -/
  i₀ : N.I
  /-- The descended intersection. -/
  W₀ : (N.D.obj i₀).Opens
  hW₀c : IsCompact (W₀ : Set (N.D.obj i₀))
  hW₀ : N.π.app i₀ ⁻¹ᵁ W₀ = U.ι ⁻¹ᵁ V
  /-- The number of chosen generators of the intersection. -/
  n : ℕ
  /-- The chosen generators of the intersection: sections of `V` whose basic opens
  cover `U ⊓ V`. -/
  b : Fin n → Γ(X, V)
  hb (l : Fin n) : X.basicOpen (b l) ≤ U ⊓ V
  hb' : U ⊓ V = ⨆ l, X.basicOpen (b l)

namespace ExtensionData

attribute [instance] qs

variable (E : ExtensionData.{u})

/-- (Implementation) The limit cone of the approximation of `U`. -/
abbrev cone : Cone E.N.D := Cone.mk _ E.N.π

/-- (Implementation) `W = U ⊓ V` as an open of `U`. -/
abbrev WU : E.U.toScheme.Opens := E.N.π.app E.i₀ ⁻¹ᵁ E.W₀

/-- (Implementation) The system of the descended intersections `Wⱼ`. -/
noncomputable abbrev WD : Over E.i₀ ⥤ Scheme.{u} := opensDiagram E.N.D E.i₀ E.W₀

/-- (Implementation) The cone exhibiting `W` as the limit of the `Wⱼ`. -/
noncomputable abbrev Wc : Cone E.WD := opensCone E.N.D E.cone E.i₀ E.W₀

/-- (Implementation) `W` is the limit of the `Wⱼ`. -/
noncomputable def isLimitWc : IsLimit E.Wc :=
  isLimitOpensCone E.N.D E.cone E.N.isLimit E.i₀ E.W₀

instance (j : Over E.i₀) : CompactSpace (E.WD.obj j) :=
  isCompact_iff_compactSpace.mp
    (QuasiCompact.isCompact_preimage (f := E.N.D.map j.hom) _ E.W₀.2 E.hW₀c)

instance (j : Over E.i₀) : IsLocallyNoetherian (E.WD.obj j) := by
  have : IsLocallyNoetherian (E.N.D.obj j.left) := (E.N.isNoetherian_obj j.left).1
  exact isLocallyNoetherian_of_isOpenImmersion (Scheme.Opens.ι _)

/-- (Implementation) The restriction of a section of `V` to `W`, viewed inside the limit of
the `Wⱼ`. -/
noncomputable def sV : Γ(E.X, E.V) ⟶ Γ(E.Wc.pt, ⊤) :=
  (E.WU.ι ≫ E.U.ι).appLE E.V ⊤ (by
    rw [Scheme.Hom.comp_preimage, ← E.hW₀, Scheme.Opens.ι_preimage_self])

/-- (Implementation) The restriction of a section at the stage `j` to the limit `W`. -/
noncomputable abbrev t (j : Over E.i₀) : Γ(E.WD.obj j, ⊤) ⟶ Γ(E.Wc.pt, ⊤) :=
  (E.Wc.π.app j).appTop

/-- (Implementation) The transition map on sections of the system `Wⱼ`. -/
noncomputable abbrev res {j j' : Over E.i₀} (f : j' ⟶ j) :
    Γ(E.WD.obj j, ⊤) ⟶ Γ(E.WD.obj j', ⊤) :=
  (E.WD.map f).appTop

lemma t_res {j j' : Over E.i₀} (f : j' ⟶ j) (x : Γ(E.WD.obj j, ⊤)) :
    E.t j' (E.res f x) = E.t j x := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, E.Wc.w f]

lemma res_res {j j' j'' : Over E.i₀} (f : j' ⟶ j) (g : j'' ⟶ j') (x : Γ(E.WD.obj j, ⊤)) :
    E.res g (E.res f x) = E.res (g ≫ f) x := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Functor.map_comp]

/-- (Implementation) A stage of the extended system: an index `j`, a lift `r` of the
generators of `W` to `Wⱼ` such that the basic opens of the `r l` form an affine cover of
`Wⱼ`, and a finitely generated `ℤ`-subalgebra `A` of `Γ(X, V) × Γ(Wⱼ, ⊤)` contained in the
fiber product over `Γ(W, ⊤)`, containing the tautological elements `(b l, r l)` and
generating all the local rings of the cover (condition `hgen`, ensuring that `Wⱼ ⟶ Spec A`
is an open immersion). -/
structure Stage where
  /-- The underlying index. -/
  j : Over E.i₀
  /-- The lifts of the generators of the intersection. -/
  r : Fin E.n → Γ(E.WD.obj j, ⊤)
  hr (l : Fin E.n) : E.t j (r l) = E.sV (E.b l)
  hcov : ⨆ l, (E.WD.obj j).basicOpen (r l) = ⊤
  haff (l : Fin E.n) : IsAffineOpen ((E.WD.obj j).basicOpen (r l))
  /-- The finite-stage coefficient algebra. -/
  A : Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤))
  hA : ∀ p ∈ A, E.sV p.1 = E.t j p.2
  hAfg : A.FG
  hmem (l : Fin E.n) : (E.b l, r l) ∈ A
  hgen (l : Fin E.n) (z : Γ(E.WD.obj j, (E.WD.obj j).basicOpen (r l))) :
    ∃ (m : ℕ) (p : Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)), p ∈ A ∧
      ((E.WD.obj j).presheaf.map (homOfLE le_top).op).hom p.2 =
        z * ((E.WD.obj j).presheaf.map (homOfLE le_top).op).hom (r l) ^ m

/-- (Implementation) A morphism of stages over a morphism of underlying indices: the lifts
`r` are compatible, and the coefficient algebra of the target maps into that of the
source. -/
@[ext] structure Stage.Hom (T T' : E.Stage) where
  /-- The underlying index morphism. -/
  base : T.j ⟶ T'.j
  res_r (l : Fin E.n) : E.res base (T'.r l) = T.r l
  map_mem (p : Γ(E.X, E.V) × Γ(E.WD.obj T'.j, ⊤)) (hp : p ∈ T'.A) :
    (p.1, E.res base p.2) ∈ T.A

lemma res_id (j : Over E.i₀) (x : Γ(E.WD.obj j, ⊤)) : E.res (𝟙 j) x = x := by
  change ((E.WD.map (𝟙 j)).appTop).hom x = x
  rw [CategoryTheory.Functor.map_id]
  simp

instance : Category E.Stage where
  Hom := Stage.Hom E
  id T := ⟨𝟙 T.j, fun l ↦ E.res_id _ _, fun p hp ↦ by simpa [E.res_id] using hp⟩
  comp {T T' T''} f g := ⟨f.base ≫ g.base,
    fun l ↦ by rw [← E.res_res g.base f.base, g.res_r, f.res_r],
    fun p hp ↦ by
      have := f.map_mem _ (g.map_mem p hp)
      rwa [E.res_res] at this⟩
  id_comp f := Stage.Hom.ext (Category.id_comp f.base)
  comp_id f := Stage.Hom.ext (Category.comp_id f.base)
  assoc f g h := Stage.Hom.ext (Category.assoc f.base g.base h.base)

@[simp] lemma id_base (T : E.Stage) : (𝟙 T : T ⟶ T).base = 𝟙 T.j := rfl

@[simp] lemma comp_base {T T' T'' : E.Stage} (f : T ⟶ T') (g : T' ⟶ T'') :
    (f ≫ g).base = f.base ≫ g.base := rfl

@[ext] lemma stageHom_ext {T T' : E.Stage} {f g : T ⟶ T'} (h : f.base = g.base) : f = g :=
  Stage.Hom.ext h

variable {E}

/-- (Implementation) The ring map from the coefficient algebra of a stage to the sections
of `Wⱼ`. -/
noncomputable def Stage.ρ (T : E.Stage) : CommRingCat.of ↥T.A ⟶ Γ(E.WD.obj T.j, ⊤) :=
  CommRingCat.ofHom ((RingHom.snd _ _).comp (Subalgebra.val T.A).toRingHom)

@[simp] lemma Stage.ρ_apply (T : E.Stage) (a : ↥T.A) :
    T.ρ a = (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).2 := rfl

/-- (Implementation) The tautological element `(b l, r l)` of the coefficient algebra of a
stage. -/
def Stage.h (T : E.Stage) (l : Fin E.n) : ↥T.A := ⟨(E.b l, T.r l), T.hmem l⟩

@[simp] lemma Stage.coe_h (T : E.Stage) (l : Fin E.n) :
    (T.h l : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)) = (E.b l, T.r l) := rfl

/-- (Implementation) The morphism from `Wⱼ` to the spectrum of the coefficient algebra of a
stage. By `Stage.isOpenImmersion_toSpec` this is an open immersion. -/
noncomputable def Stage.toSpec (T : E.Stage) :
    E.WD.obj T.j ⟶ Spec (CommRingCat.of ↥T.A) :=
  (E.WD.obj T.j).toSpecΓ ≫ Spec.map T.ρ

lemma Stage.toSpec_preimage_basicOpen (T : E.Stage) (l : Fin E.n) :
    T.toSpec ⁻¹ᵁ PrimeSpectrum.basicOpen (T.h l) = (E.WD.obj T.j).basicOpen (T.r l) := by
  rw [Stage.toSpec, Scheme.Hom.comp_preimage, SpecMap_preimage_basicOpen,
    Scheme.toSpecΓ_preimage_basicOpen, Stage.ρ_apply, Stage.coe_h]

/-- (Implementation) The ring map from the coefficient algebra of a stage to the sections
of the basic open `Wⱼ(r l) ⊆ Wⱼ`. This realizes the sections over `Wⱼ(r l)` as the
localization of the coefficient algebra away from the tautological element `(b l, r l)`,
see `Stage.isLocalization_away`. -/
noncomputable def Stage.ρRes (T : E.Stage) (l : Fin E.n) :
    CommRingCat.of ↥T.A ⟶ Γ(E.WD.obj T.j, (E.WD.obj T.j).basicOpen (T.r l)) :=
  T.ρ ≫ (E.WD.obj T.j).presheaf.map (homOfLE le_top).op

@[simp] lemma Stage.ρRes_apply (T : E.Stage) (l : Fin E.n) (a : ↥T.A) :
    (T.ρRes l).hom a = ((E.WD.obj T.j).presheaf.map (homOfLE le_top).op).hom a.1.2 := rfl

/-- (Implementation) The image of `W = U ⊓ V` in `X`. -/
lemma opensRange_WUι_comp_Uι (E : ExtensionData.{u}) :
    (E.WU.ι ≫ E.U.ι).opensRange = E.U ⊓ E.V := by
  rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι, ExtensionData.WU, E.hW₀,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

lemma basicOpen_le_opensRange (E : ExtensionData.{u}) (l : Fin E.n) :
    E.X.basicOpen (E.b l) ≤ (E.WU.ι ≫ E.U.ι).opensRange :=
  (E.hb l).trans E.opensRange_WUι_comp_Uι.ge

/-- (Implementation) Restricting a section of `V` to `X.basicOpen (b l)` and pulling back
to `W` agrees with restricting the pullback to `W`. -/
lemma res_app_eq_sV_res (E : ExtensionData.{u}) (l : Fin E.n) :
    E.X.presheaf.map (homOfLE (E.X.basicOpen_le (E.b l))).op ≫
      (E.WU.ι ≫ E.U.ι).app (E.X.basicOpen (E.b l)) =
      E.sV ≫ E.WU.toScheme.presheaf.map (homOfLE le_top).op := by
  simp only [ExtensionData.sV, Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

/-- (Implementation) A section of `V` restricting to zero on `W` is annihilated by a power
of each of the chosen generators `b l`: the restriction `Γ(X, V) ⟶ Γ(W, 𝒪)` factors through
the localization `Γ(X, V) ⟶ Γ(X, X.basicOpen (b l))` because `X.basicOpen (b l) ≤ U ⊓ V`.
This is the key cancellation step in the proof of Stacks 01Z9. -/
lemma exists_pow_mul_eq_zero_of_sV_eq_zero (l : Fin E.n) {y : Γ(E.X, E.V)}
    (hy : E.sV y = 0) : ∃ K, E.b l ^ K * y = 0 := by
  haveI := E.hV.isLocalization_basicOpen (E.b l)
  suffices h0 : (E.X.presheaf.map (homOfLE (E.X.basicOpen_le (E.b l))).op) y = 0 by
    obtain ⟨⟨_, K, rfl⟩, hK⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (E.b l)) Γ(E.X, E.X.basicOpen (E.b l)) y).mp h0
    exact ⟨K, hK⟩
  have := (E.WU.ι ≫ E.U.ι).isIso_app _ (E.basicOpen_le_opensRange l)
  apply (ConcreteCategory.bijective_of_isIso
    ((E.WU.ι ≫ E.U.ι).app (E.X.basicOpen (E.b l)))).1
  rw [map_zero, ← CommRingCat.comp_apply, E.res_app_eq_sV_res l, CommRingCat.comp_apply, hy,
    map_zero]

set_option maxHeartbeats 1600000 in
-- The defeq checks between `algebraMap`s of the two `Algebra` structures in scope and the
-- structure sheaf restriction maps are expensive on the opens diagram of the approximation.
/-- (Implementation, Stacks 01Z9) The sections over the basic open `Wⱼ(r l)` are the
localization of the coefficient algebra of the stage away from the tautological element
`(b l, r l)`. Surjectivity is the condition `hgen` of the stage; injectivity combines the
qcqs lemma on `Wⱼ` with `exists_pow_mul_eq_zero_of_sV_eq_zero` on the `V`-component. -/
lemma Stage.isLocalization_away (T : E.Stage) (l : Fin E.n) :
    letI := (T.ρRes l).hom.toAlgebra
    IsLocalization.Away (T.h l)
      Γ(E.WD.obj T.j, (E.WD.obj T.j).basicOpen (T.r l)) := by
  letI := (T.ρRes l).hom.toAlgebra
  haveI := isLocalization_basicOpen_of_qcqs (X := E.WD.obj T.j) (U := ⊤)
    isCompact_univ isQuasiSeparated_univ (T.r l)
  refine ⟨fun ⟨_, m, rfl⟩ ↦ ?_, fun z ↦ ?_, fun {a a'} hd ↦ ?_⟩
  · simp only [RingHom.algebraMap_toAlgebra, map_pow]
    refine IsUnit.pow _ ?_
    exact RingedSpace.isUnit_res_basicOpen (E.WD.obj T.j).toRingedSpace (T.r l)
  · obtain ⟨m, p, hp, hres⟩ := T.hgen l z
    refine ⟨(⟨p, hp⟩, ⟨T.h l ^ m, m, rfl⟩), ?_⟩
    simp only [RingHom.algebraMap_toAlgebra, map_pow]
    exact hres.symm
  · -- The second components agree after multiplication by a power of `r l`.
    have hres : a.1.2 |_ (E.WD.obj T.j).basicOpen (T.r l) =
        a'.1.2 |_ (E.WD.obj T.j).basicOpen (T.r l) := hd
    obtain ⟨k, hk⟩ := exists_of_res_eq_of_qcqs_of_top hres
    have hk' : T.r l ^ k * (a.1.2 - a'.1.2) = 0 := by
      rw [mul_sub, sub_eq_zero]
      exact hk
    -- Push down to the intersection `W` and cancel the first components there.
    have hV0 : E.sV (E.b l ^ k * (a.1.1 - a'.1.1)) = 0 := by
      have ht := congrArg (E.t T.j) hk'
      rw [map_mul, map_pow, map_zero, T.hr] at ht
      rw [map_mul, map_pow, map_sub, T.hA _ a.2, T.hA _ a'.2, ← map_sub]
      exact ht
    obtain ⟨K, hK⟩ := E.exists_pow_mul_eq_zero_of_sV_eq_zero l hV0
    refine ⟨⟨T.h l ^ (K + k), K + k, rfl⟩, Subtype.ext (Prod.ext ?_ ?_)⟩
    · simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, Stage.coe_h, Prod.fst_mul,
        Prod.pow_fst]
      rw [← sub_eq_zero, ← mul_sub, pow_add, mul_assoc]
      exact hK
    · simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, Stage.coe_h, Prod.snd_mul,
        Prod.pow_snd]
      rw [← sub_eq_zero, ← mul_sub, pow_add, mul_assoc, hk', mul_zero]

/-- (Implementation) The heart of Stacks 07RN (via Tags 01Z7 and 01Z9): the morphism from
`Wⱼ` to the spectrum of the coefficient algebra of a stage is an open immersion. -/
instance Stage.isOpenImmersion_toSpec (T : E.Stage) : IsOpenImmersion T.toSpec := by
  refine IsZariskiLocalAtTarget.of_forall_source_exists_preimage _ fun x ↦ ?_
  have hx : x ∈ ⨆ l, (E.WD.obj T.j).basicOpen (T.r l) := by rw [T.hcov]; trivial
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨PrimeSpectrum.basicOpen (T.h l), (T.toSpec_preimage_basicOpen l).ge hl, ?_⟩
  suffices h : IsOpenImmersion (((E.WD.obj T.j).basicOpen (T.r l)).ι ≫ T.toSpec) by
    convert! h <;> rw [toSpec_preimage_basicOpen]
  have e : ((E.WD.obj T.j).basicOpen (T.r l)).ι ≫ T.toSpec =
      ((E.WD.obj T.j).basicOpen (T.r l)).toSpecΓ ≫ Spec.map (T.ρRes l) := by
    rw [Stage.toSpec, ← Category.assoc, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top,
      Category.assoc, ← Spec.map_comp, Stage.ρRes]
  rw [e]
  letI := (T.ρRes l).hom.toAlgebra
  haveI : IsLocalization.Away (T.h l)
      Γ(E.WD.obj T.j, (E.WD.obj T.j).basicOpen (T.r l)) := T.isLocalization_away l
  exact MorphismProperty.comp_mem _ (T.haff l).isoSpec.hom _ inferInstance
    (IsOpenImmersion.of_isLocalization (T.h l))

/-- (Implementation) The image of `Wⱼ ⟶ Spec A` is the union of the basic opens of the
tautological elements `(b l, r l)`. -/
lemma Stage.opensRange_toSpec (T : E.Stage) :
    T.toSpec.opensRange = ⨆ l, PrimeSpectrum.basicOpen (T.h l) := by
  refine le_antisymm ?_ (iSup_le fun l ↦ ?_)
  · rintro - ⟨x, rfl⟩
    have hx : x ∈ ⨆ l, (E.WD.obj T.j).basicOpen (T.r l) := by rw [T.hcov]; trivial
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨l, (T.toSpec_preimage_basicOpen l).ge hl⟩
  · have e : ((E.WD.obj T.j).basicOpen (T.r l)).ι ≫ T.toSpec =
        ((E.WD.obj T.j).basicOpen (T.r l)).toSpecΓ ≫ Spec.map (T.ρRes l) := by
      rw [Stage.toSpec, ← Category.assoc, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top,
        Category.assoc, ← Spec.map_comp, Stage.ρRes]
    letI := (T.ρRes l).hom.toAlgebra
    haveI : IsLocalization.Away (T.h l)
        Γ(E.WD.obj T.j, (E.WD.obj T.j).basicOpen (T.r l)) := T.isLocalization_away l
    haveI : IsIso (((E.WD.obj T.j).basicOpen (T.r l)).toSpecΓ) := by
      rw [← IsAffineOpen.isoSpec_hom (T.haff l)]
      infer_instance
    rintro p hp
    obtain ⟨q, hq⟩ : ∃ q, (Spec.map (T.ρRes l)).base q = p := by
      have h := PrimeSpectrum.localization_away_comap_range
        (S := Γ(E.WD.obj T.j, (E.WD.obj T.j).basicOpen (T.r l))) (T.h l)
      have hmem : p ∈ Set.range (PrimeSpectrum.comap (algebraMap ↥T.A
          Γ(E.WD.obj T.j, (E.WD.obj T.j).basicOpen (T.r l)))) := by
        rw [h]
        exact hp
      exact hmem
    obtain ⟨w, hw⟩ := (Scheme.Hom.homeomorph
      (((E.WD.obj T.j).basicOpen (T.r l)).toSpecΓ)).surjective q
    have hw' : (((E.WD.obj T.j).basicOpen (T.r l)).toSpecΓ) w = q := hw
    refine ⟨((E.WD.obj T.j).basicOpen (T.r l)).ι w, ?_⟩
    have h1 : (((E.WD.obj T.j).basicOpen (T.r l)).ι ≫ T.toSpec) w = p := by
      rw [e, Scheme.Hom.comp_apply, hw']
      exact hq
    rw [Scheme.Hom.comp_apply] at h1
    exact h1

/-!
#### Existence of stages

Following Stacks 01Z7, we produce stages: the sections of `Wⱼ` over a basic open `Wⱼ(r l)`
form a finitely generated `ℤ`-algebra, and each generator is, up to a power of `r l`, the
second component of an element of the fiber product `Γ(X, V) ×_{Γ(W)} Γ(Wⱼ)`. Adjoining
these elements to any finitely generated subalgebra of the fiber product yields a stage.
-/

/-- (Implementation) The fiber product `Γ(X, V) ×_{Γ(W, 𝒪)} Γ(Wⱼ, 𝒪)`, i.e. the pairs of
sections agreeing on `W`, as a subalgebra of the product ring. The coefficient algebra of a
stage at `j` is a finitely generated subalgebra of it. -/
noncomputable def fiberProduct (E : ExtensionData.{u}) (j : Over E.i₀) :
    Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)) :=
  AlgHom.equalizer (E.sV.hom.comp (RingHom.fst _ _)).toIntAlgHom
    ((E.t j).hom.comp (RingHom.snd _ _)).toIntAlgHom

lemma mem_fiberProduct_iff (E : ExtensionData.{u}) {j : Over E.i₀}
    (p : Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)) :
    p ∈ E.fiberProduct j ↔ E.sV p.1 = E.t j p.2 := Iff.rfl

/-- (Implementation) The basic open of `W` attached to a generator `b l` is the pullback of
the basic open of `X` attached to it. -/
lemma basicOpen_sV (E : ExtensionData.{u}) (l : Fin E.n) :
    E.Wc.pt.basicOpen (E.sV (E.b l)) =
      (E.WU.ι ≫ E.U.ι) ⁻¹ᵁ E.X.basicOpen (E.b l) := by
  simp only [ExtensionData.sV, Scheme.basicOpen_appLE, top_inf_eq]

/-- (Implementation) The basic opens of the chosen generators cover `W`. -/
lemma iSup_basicOpen_sV (E : ExtensionData.{u}) :
    ⨆ l, E.Wc.pt.basicOpen (E.sV (E.b l)) = ⊤ := by
  simp_rw [E.basicOpen_sV]
  rw [← Scheme.Hom.preimage_iSup, ← E.hb']
  refine eq_top_iff.mpr fun x _ ↦ ?_
  have : (E.WU.ι ≫ E.U.ι) x ∈ (E.WU.ι ≫ E.U.ι).opensRange := ⟨x, rfl⟩
  rw [E.opensRange_WUι_comp_Uι] at this
  exact this

/-- (Implementation) `Wⱼ` is of finite type over `ℤ`, being open in a stage of the
approximation of `U`. -/
instance (j : Over E.i₀) :
    LocallyOfFiniteType (specULiftZIsTerminal.from (E.WD.obj j)) := by
  rw [specULiftZIsTerminal.hom_ext (specULiftZIsTerminal.from (E.WD.obj j))
    ((E.N.D.map j.hom ⁻¹ᵁ E.W₀).ι ≫ specULiftZIsTerminal.from (E.N.D.obj j.left))]
  infer_instance

instance : CompactSpace E.Wc.pt := by
  have := isAffineHom_π_app E.N.D E.cone E.N.isLimit E.i₀
  exact isCompact_iff_compactSpace.mp
    (QuasiCompact.isCompact_preimage (f := E.N.π.app E.i₀) _ E.W₀.2 E.hW₀c)

instance : QuasiSeparatedSpace E.Wc.pt := by
  have : QuasiSeparatedSpace E.U.toScheme :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ E.U.2).mp (.of_quasiSeparatedSpace _)
  exact (isQuasiSeparated_iff_quasiSeparatedSpace _ E.WU.2).mp (.of_quasiSeparatedSpace _)

variable (E) in
/-- (Implementation) Restricting a global section of `W` to the basic open of `sV (b l)`
factors through the restriction to the pullback of `X.basicOpen (b l)`; the two opens are
equal by `basicOpen_sV`. -/
lemma restrict_basicOpen_sV_eq (l : Fin E.n) (x : Γ(E.Wc.pt, ⊤)) :
    x |_ E.Wc.pt.basicOpen (E.sV (E.b l)) =
      (E.Wc.pt.presheaf.map (eqToHom (E.basicOpen_sV l)).op)
        ((E.Wc.pt.presheaf.map (homOfLE le_top).op) x) := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp]
  exact congrArg
    (fun f : E.Wc.pt.basicOpen (E.sV (E.b l)) ⟶ (⊤ : E.Wc.pt.Opens) ↦
      (E.Wc.pt.presheaf.map f.op).hom x)
    (Subsingleton.elim _ _)

/-- (Implementation, Stacks 01Z7) Every section over a basic open `Wⱼ(r l)` is, up to a
power of `r l`, the restriction of the second component of an element of the fiber product
`Γ(X, V) ×_{Γ(W)} Γ(Wⱼ)`. -/
lemma exists_mem_fiberProduct_res_eq_mul_pow (E : ExtensionData.{u}) {j : Over E.i₀}
    {l : Fin E.n} {rl : Γ(E.WD.obj j, ⊤)} (hrl : E.t j rl = E.sV (E.b l))
    (z : Γ(E.WD.obj j, (E.WD.obj j).basicOpen rl)) :
    ∃ (m : ℕ) (p : Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)), p ∈ E.fiberProduct j ∧
      ((E.WD.obj j).presheaf.map (homOfLE le_top).op) p.2 =
        z * ((E.WD.obj j).presheaf.map (homOfLE le_top).op) rl ^ m := by
  classical
  -- Lift `z` to a global section `y` of `Wⱼ`, up to a power of `rl`.
  obtain ⟨m₀, y, hy⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated
    (E.WD.obj j) ⊤ isCompact_univ isQuasiSeparated_univ rl z
  -- The restriction of `t y` to the basic open of `W` comes from a section `zV` of
  -- `X.basicOpen (b l)`.
  have hiso := (E.WU.ι ≫ E.U.ι).isIso_app _ (E.basicOpen_le_opensRange l)
  obtain ⟨zV, hzV⟩ := (ConcreteCategory.bijective_of_isIso
    ((E.WU.ι ≫ E.U.ι).app (E.X.basicOpen (E.b l)))).2
    ((E.WU.toScheme.presheaf.map (homOfLE le_top).op) (E.t j y))
  -- Write `zV` as `v₀ / (b l) ^ K` using that `V` is affine.
  haveI := E.hV.isLocalization_basicOpen (E.b l)
  obtain ⟨⟨v₀, ⟨_, K, rfl⟩⟩, hv⟩ := IsLocalization.surj (M := Submonoid.powers (E.b l)) zV
  rw [map_pow] at hv
  -- Restricting sections of `V` to `X.basicOpen (b l)` and pulling back to `W` agrees with
  -- pulling back to `W` and restricting.
  have happ : ∀ x : Γ(E.X, E.V),
      ((E.WU.ι ≫ E.U.ι).app (E.X.basicOpen (E.b l)))
        ((algebraMap Γ(E.X, E.V) Γ(E.X, E.X.basicOpen (E.b l))) x) =
      (E.WU.toScheme.presheaf.map (homOfLE le_top).op) (E.sV x) := fun x ↦ by
    have h := congrArg
      (fun f : Γ(E.X, E.V) ⟶
          Γ(E.WU.toScheme, (E.WU.ι ≫ E.U.ι) ⁻¹ᵁ E.X.basicOpen (E.b l)) ↦ f x)
      (E.res_app_eq_sV_res l)
    dsimp only at h
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h
    exact h
  -- Transport the localization relation along the pullback to `W`.
  have e₁ := congrArg ((E.WU.ι ≫ E.U.ι).app (E.X.basicOpen (E.b l)) ·) hv
  dsimp only at e₁
  rw [map_mul, map_pow, happ, happ, hzV] at e₁
  have e₁' : (E.Wc.pt.presheaf.map (homOfLE le_top).op) (E.t j y) *
        (E.Wc.pt.presheaf.map (homOfLE le_top).op) (E.sV (E.b l)) ^ K =
      (E.Wc.pt.presheaf.map (homOfLE (le_top :
        (E.WU.ι ≫ E.U.ι) ⁻¹ᵁ E.X.basicOpen (E.b l) ≤ ⊤)).op) (E.sV v₀) := e₁
  -- `sV v₀` and `t (rl ^ K * y)` agree on the basic open of `sV (b l)`.
  have h6 : E.sV v₀ |_ E.Wc.pt.basicOpen (E.sV (E.b l)) =
      E.t j (rl ^ K * y) |_ E.Wc.pt.basicOpen (E.sV (E.b l)) := by
    rw [E.restrict_basicOpen_sV_eq, E.restrict_basicOpen_sV_eq]
    congr 1
    rw [map_mul, map_pow, hrl, map_mul, map_pow]
    linear_combination -e₁'
  -- Hence they agree after multiplication by a power of `sV (b l)`.
  obtain ⟨M, hM⟩ := exists_of_res_eq_of_qcqs_of_top (X := E.Wc.pt) h6
  -- Assemble the element of the fiber product.
  refine ⟨M + K + m₀, (E.b l ^ M * v₀, rl ^ (M + K) * y), ?_, ?_⟩
  · rw [E.mem_fiberProduct_iff]
    dsimp only
    rw [map_mul, map_pow, hM, ← hrl, ← map_pow, ← map_mul, ← mul_assoc, ← pow_add]
  · dsimp only
    rw [map_mul, map_pow]
    have hy' : ((E.WD.obj j).presheaf.map (homOfLE le_top).op) y =
        ((E.WD.obj j).presheaf.map (homOfLE le_top).op) rl ^ m₀ * z := hy
    rw [hy', pow_add, pow_add]
    ring

/-!
#### The category of stages

Following `lemma:nagata-valid-refinements-directed`, the stages form a nonempty cofiltered
category: any finitely generated subalgebra of the fiber product can be enlarged to satisfy
the generation condition (Stacks 01Z7), lifts of the generators exist at a common index by
the section-descent lemmas for the limit `W = lim Wⱼ`, and the covering and affineness
conditions descend from the limit by Stacks 01Z4.
-/

instance (j : Over E.i₀) : IsNoetherian (E.WD.obj j) := ⟨⟩

/-- (Implementation) The identity on the `V`-component times restriction on the section
component, as a morphism of `ℤ`-algebras. It maps the fiber product at `j` into the fiber
product at `j'`. -/
noncomputable def resAlgHom {j j' : Over E.i₀} (k : j' ⟶ j) :
    (Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)) →ₐ[ℤ] Γ(E.X, E.V) × Γ(E.WD.obj j', ⊤) :=
  ((RingHom.id Γ(E.X, E.V)).prodMap (E.res k).hom).toIntAlgHom

@[simp] lemma resAlgHom_apply {j j' : Over E.i₀} (k : j' ⟶ j)
    (p : Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)) :
    resAlgHom k p = (p.1, E.res k p.2) := rfl

lemma resAlgHom_mem_fiberProduct {j j' : Over E.i₀} (k : j' ⟶ j)
    {p : Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)} (hp : p ∈ E.fiberProduct j) :
    resAlgHom k p ∈ E.fiberProduct j' := by
  rw [E.mem_fiberProduct_iff] at hp ⊢
  rw [resAlgHom_apply, E.t_res]
  exact hp

lemma Stage.A_le_fiberProduct (T : E.Stage) : T.A ≤ E.fiberProduct T.j :=
  fun p hp ↦ (E.mem_fiberProduct_iff p).mpr (T.hA p hp)

variable (E)

/-- (Implementation) The data of a stage without its coefficient algebra: an index `j` and
lifts `r` of the generators of the intersection such that the basic opens of the `r l` form
an affine cover of `Wⱼ`. -/
structure PreStage where
  /-- The underlying index. -/
  j : Over E.i₀
  /-- The lifts of the generators of the intersection. -/
  r : Fin E.n → Γ(E.WD.obj j, ⊤)
  hr (l : Fin E.n) : E.t j (r l) = E.sV (E.b l)
  hcov : ⨆ l, (E.WD.obj j).basicOpen (r l) = ⊤
  haff (l : Fin E.n) : IsAffineOpen ((E.WD.obj j).basicOpen (r l))

variable {E}

/-- (Implementation) The pre-stage underlying a stage. -/
def Stage.toPreStage (T : E.Stage) : E.PreStage :=
  ⟨T.j, T.r, T.hr, T.hcov, T.haff⟩

/-- (Implementation) Pre-stages restrict along morphisms of indices. -/
noncomputable def PreStage.restrict (P : E.PreStage) {j' : Over E.i₀} (k : j' ⟶ P.j) :
    E.PreStage where
  j := j'
  r l := E.res k (P.r l)
  hr l := by rw [E.t_res, P.hr]
  hcov := by
    have h : ∀ l, (E.WD.obj j').basicOpen (E.res k (P.r l)) =
        E.WD.map k ⁻¹ᵁ ((E.WD.obj P.j).basicOpen (P.r l)) :=
      fun l ↦ (Scheme.preimage_basicOpen_top (E.WD.map k) (P.r l)).symm
    simp_rw [h, ← Scheme.Hom.preimage_iSup, P.hcov, Scheme.Hom.preimage_top]
  haff l := by
    rw [show (E.WD.obj j').basicOpen (E.res k (P.r l)) =
        E.WD.map k ⁻¹ᵁ ((E.WD.obj P.j).basicOpen (P.r l)) from
      (Scheme.preimage_basicOpen_top (E.WD.map k) (P.r l)).symm]
    exact (P.haff l).preimage _

/-- (Implementation, Stacks 01Z7) For every pre-stage and every generator index `l`, there
is a finite subset of the fiber product such that every subalgebra containing it and the
tautological pair `(b l, r l)` satisfies the generation condition of a stage at `l`: the
sections over the affine basic open `Wⱼ(r l)` form a finitely generated `ℤ`-algebra, and
every generator is, up to a power of `r l`, the section component of an element of the
fiber product. -/
lemma PreStage.exists_finset_hgen (P : E.PreStage) (l : Fin E.n) :
    ∃ s : Finset (Γ(E.X, E.V) × Γ(E.WD.obj P.j, ⊤)),
      (∀ q ∈ s, q ∈ E.fiberProduct P.j) ∧
      ∀ A : Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj P.j, ⊤)),
        (E.b l, P.r l) ∈ A → (∀ q ∈ s, q ∈ A) →
        ∀ z : Γ(E.WD.obj P.j, (E.WD.obj P.j).basicOpen (P.r l)),
          ∃ (m : ℕ) (p : Γ(E.X, E.V) × Γ(E.WD.obj P.j, ⊤)), p ∈ A ∧
            ((E.WD.obj P.j).presheaf.map (homOfLE le_top).op).hom p.2 =
              z * ((E.WD.obj P.j).presheaf.map (homOfLE le_top).op).hom (P.r l) ^ m := by
  classical
  have hft : Algebra.FiniteType ℤ Γ(E.WD.obj P.j, (E.WD.obj P.j).basicOpen (P.r l)) :=
    IsAffineOpen.algebra_finiteType_of_locallyOfFiniteType
      (f := specULiftZIsTerminal.from (E.WD.obj P.j)) (P.haff l)
  obtain ⟨s₀, hs₀⟩ := hft.1
  choose m p hp₁ hp₂ using fun z : s₀ ↦
    E.exists_mem_fiberProduct_res_eq_mul_pow (P.hr l) (z : _)
  refine ⟨s₀.attach.image p, fun q hq ↦ ?_, ?_⟩
  · obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hq
    exact hp₁ z
  · intro A hbr hsub z
    set ρ := ((E.WD.obj P.j).presheaf.map
      (homOfLE (le_top : (E.WD.obj P.j).basicOpen (P.r l) ≤ ⊤)).op).hom with hρ
    let S : Subalgebra ℤ Γ(E.WD.obj P.j, (E.WD.obj P.j).basicOpen (P.r l)) :=
      { carrier := {z | ∃ (m : ℕ) (p : Γ(E.X, E.V) × Γ(E.WD.obj P.j, ⊤)), p ∈ A ∧
          ρ p.2 = z * ρ (P.r l) ^ m}
        one_mem' := ⟨0, 1, one_mem A, by simp⟩
        zero_mem' := ⟨0, 0, zero_mem A, by simp⟩
        mul_mem' := by
          rintro z₁ z₂ ⟨m₁, p₁, h₁, e₁⟩ ⟨m₂, p₂, h₂, e₂⟩
          refine ⟨m₁ + m₂, p₁ * p₂, mul_mem h₁ h₂, ?_⟩
          change ρ (p₁.2 * p₂.2) = _
          rw [map_mul, e₁, e₂]
          ring
        add_mem' := by
          rintro z₁ z₂ ⟨m₁, p₁, h₁, e₁⟩ ⟨m₂, p₂, h₂, e₂⟩
          refine ⟨m₁ + m₂, p₁ * (E.b l, P.r l) ^ m₂ + p₂ * (E.b l, P.r l) ^ m₁,
            add_mem (mul_mem h₁ (pow_mem hbr m₂)) (mul_mem h₂ (pow_mem hbr m₁)), ?_⟩
          change ρ (p₁.2 * P.r l ^ m₂ + p₂.2 * P.r l ^ m₁) = _
          rw [map_add, map_mul, map_mul, map_pow, map_pow, e₁, e₂]
          ring
        algebraMap_mem' := fun c ↦ ⟨0, algebraMap ℤ _ c, A.algebraMap_mem c, by
          change ρ (algebraMap ℤ _ c) = _
          rw [pow_zero, mul_one]
          exact map_intCast ρ c⟩ }
    have hS : Algebra.adjoin ℤ (↑s₀ : Set _) ≤ S := by
      refine Algebra.adjoin_le fun z hz ↦ ?_
      exact ⟨m ⟨z, hz⟩, p ⟨z, hz⟩,
        hsub _ (Finset.mem_image.mpr ⟨⟨z, hz⟩, Finset.mem_attach _ _, rfl⟩), hp₂ ⟨z, hz⟩⟩
    have := hS (hs₀ ▸ Algebra.mem_top (R := ℤ) (x := z))
    exact this

/-- (Implementation, Stacks 01Z7) Enlarge a finitely generated subalgebra of the fiber
product containing the tautological pairs to the coefficient algebra of a stage over a
given pre-stage. -/
noncomputable def PreStage.mkStage (P : E.PreStage)
    (A₀ : Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj P.j, ⊤)))
    (hA₀ : A₀ ≤ E.fiberProduct P.j) (hfg : A₀.FG)
    (hmem : ∀ l, (E.b l, P.r l) ∈ A₀) : E.Stage where
  j := P.j
  r := P.r
  hr := P.hr
  hcov := P.hcov
  haff := P.haff
  A := A₀ ⊔ Algebra.adjoin ℤ (⋃ l, ↑(P.exists_finset_hgen l).choose)
  hA p hp := by
    have h : A₀ ⊔ Algebra.adjoin ℤ (⋃ l, ↑(P.exists_finset_hgen l).choose) ≤
        E.fiberProduct P.j := by
      refine sup_le hA₀ (Algebra.adjoin_le fun q hq ↦ ?_)
      obtain ⟨l, hql⟩ := Set.mem_iUnion.mp hq
      exact (P.exists_finset_hgen l).choose_spec.1 q hql
    exact (E.mem_fiberProduct_iff p).mp (h hp)
  hAfg := hfg.sup (Subalgebra.fg_def.mpr
    ⟨_, Set.finite_iUnion fun l ↦ (P.exists_finset_hgen l).choose.finite_toSet, rfl⟩)
  hmem l := Algebra.mem_sup_left (hmem l)
  hgen l z :=
    (P.exists_finset_hgen l).choose_spec.2 _
      (Algebra.mem_sup_left (hmem l))
      (fun q hq ↦ Algebra.mem_sup_right
        (Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨l, hq⟩))) z

@[simp] lemma PreStage.mkStage_j (P : E.PreStage) (A₀) (hA₀) (hfg) (hmem) :
    (P.mkStage A₀ hA₀ hfg hmem).j = P.j := rfl

@[simp] lemma PreStage.mkStage_r (P : E.PreStage) (A₀) (hA₀) (hfg) (hmem) :
    (P.mkStage A₀ hA₀ hfg hmem).r = P.r := rfl

lemma PreStage.le_mkStage_A (P : E.PreStage) (A₀) (hA₀) (hfg) (hmem) :
    A₀ ≤ (P.mkStage A₀ hA₀ hfg hmem).A := le_sup_left

/-- (Implementation) The minimal stage over a pre-stage: adjoin the tautological pairs and
close up under the generation condition. -/
noncomputable def PreStage.stage (P : E.PreStage) : E.Stage :=
  P.mkStage (Algebra.adjoin ℤ (Set.range fun l ↦ (E.b l, P.r l)))
    (Algebra.adjoin_le (by rintro p ⟨l, rfl⟩; exact (E.mem_fiberProduct_iff _).mpr (P.hr l).symm))
    (Subalgebra.fg_def.mpr ⟨_, Set.finite_range _, rfl⟩)
    (fun l ↦ Algebra.subset_adjoin ⟨l, rfl⟩)

@[simp] lemma PreStage.stage_j (P : E.PreStage) : P.stage.j = P.j := rfl

/-- (Implementation) Restrict a stage along a morphism of indices, adjoining an extra
finitely generated subalgebra of the fiber product. -/
noncomputable def Stage.restrict (T : E.Stage) {j' : Over E.i₀} (k : j' ⟶ T.j)
    (A' : Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj j', ⊤)))
    (hA' : A' ≤ E.fiberProduct j') (hfg : A'.FG) : E.Stage :=
  (T.toPreStage.restrict k).mkStage (T.A.map (resAlgHom k) ⊔ A')
    (sup_le (by rintro p ⟨q, hq, rfl⟩; exact resAlgHom_mem_fiberProduct k (T.A_le_fiberProduct hq))
      hA')
    ((T.hAfg.map _).sup hfg)
    (fun l ↦ Algebra.mem_sup_left ⟨(E.b l, T.r l), T.hmem l, rfl⟩)

@[simp] lemma Stage.restrict_j (T : E.Stage) {j' : Over E.i₀} (k : j' ⟶ T.j)
    (A') (hA') (hfg) : (T.restrict k A' hA' hfg).j = j' := rfl

@[simp] lemma Stage.restrict_r (T : E.Stage) {j' : Over E.i₀} (k : j' ⟶ T.j)
    (A') (hA') (hfg) (l : Fin E.n) :
    (T.restrict k A' hA' hfg).r l = E.res k (T.r l) := rfl

lemma Stage.le_restrict_A (T : E.Stage) {j' : Over E.i₀} (k : j' ⟶ T.j)
    (A') (hA') (hfg) : A' ≤ (T.restrict k A' hA' hfg).A :=
  le_trans le_sup_right ((T.toPreStage.restrict k).le_mkStage_A _ _ _ _)

/-- (Implementation) The canonical morphism from a restricted stage. -/
noncomputable def Stage.restrictHom (T : E.Stage) {j' : Over E.i₀} (k : j' ⟶ T.j)
    (A') (hA') (hfg) : T.restrict k A' hA' hfg ⟶ T where
  base := k
  res_r _ := rfl
  map_mem p hp := (T.toPreStage.restrict k).le_mkStage_A _ _ _ _
    (Algebra.mem_sup_left ⟨p, hp, rfl⟩)

@[simp] lemma Stage.restrictHom_base (T : E.Stage) {j' : Over E.i₀} (k : j' ⟶ T.j)
    (A') (hA') (hfg) : (T.restrictHom k A' hA' hfg).base = k := rfl

variable (E)

/-- (Implementation) A finite-conjunction helper: a family of index-stable properties, each
attainable below any index, is attained jointly below any index. -/
private lemma exists_hom_forall {j₂ : Over E.i₀}
    (P : ∀ (j' : Over E.i₀), (j' ⟶ j₂) → Fin E.n → Prop)
    (hstab : ∀ {j j' : Over E.i₀} (k' : j' ⟶ j) (k : j ⟶ j₂) (l : Fin E.n),
      P j k l → P j' (k' ≫ k) l)
    (hex : ∀ (j : Over E.i₀) (k : j ⟶ j₂) (l : Fin E.n),
      ∃ (j' : Over E.i₀) (k' : j' ⟶ j), P j' (k' ≫ k) l) :
    ∃ (j : Over E.i₀) (k : j ⟶ j₂), ∀ l, P j k l := by
  classical
  suffices h : ∀ s : Finset (Fin E.n), ∃ (j : Over E.i₀) (k : j ⟶ j₂), ∀ l ∈ s, P j k l by
    obtain ⟨j, k, hj⟩ := h Finset.univ
    exact ⟨j, k, fun l ↦ hj l (Finset.mem_univ l)⟩
  intro s
  induction s using Finset.induction with
  | empty => exact ⟨j₂, 𝟙 j₂, by simp⟩
  | insert a s ha ih =>
    obtain ⟨j, k, hj⟩ := ih
    obtain ⟨j', k', hj'⟩ := hex j k a
    refine ⟨j', k' ≫ k, fun l hl ↦ ?_⟩
    rcases Finset.mem_insert.mp hl with rfl | hl
    · exact hj'
    · exact hstab k' k l (hj l hl)

/-- (Implementation) The lifts of the generators of the intersection exist at a common
index below any given index. -/
lemma exists_r (j₀ : Over E.i₀) :
    ∃ (j : Over E.i₀) (_ : j ⟶ j₀) (r : Fin E.n → Γ(E.WD.obj j, ⊤)),
      ∀ l, E.t j (r l) = E.sV (E.b l) := by
  have hex : ∀ (j : Over E.i₀) (l : Fin E.n),
      ∃ (j' : Over E.i₀) (_ : j' ⟶ j) (r : Γ(E.WD.obj j', ⊤)), E.t j' r = E.sV (E.b l) := by
    intro j l
    obtain ⟨i, r₀, hr₀⟩ := exists_appTop_π_eq_of_isLimit E.WD E.Wc E.isLimitWc (E.sV (E.b l))
    obtain ⟨j', kj, ki, -⟩ := IsCofilteredOrEmpty.cone_objs j i
    exact ⟨j', kj, E.res ki r₀, by rw [E.t_res]; exact hr₀.symm⟩
  obtain ⟨j, k, h⟩ := E.exists_hom_forall (j₂ := j₀)
    (fun j' _ l ↦ ∃ r, E.t j' r = E.sV (E.b l))
    (fun {j j'} k' k l hl ↦ by
      obtain ⟨r, hr⟩ := hl
      exact ⟨E.res k' r, by rw [E.t_res]; exact hr⟩)
    (fun j k l ↦ by
      obtain ⟨j', k', r, hr⟩ := hex j l
      exact ⟨j', k', r, hr⟩)
  choose r hr using h
  exact ⟨j, k, r, hr⟩

/-- (Implementation) The basic opens of the limit lifts of the generators are affine: they
are the basic opens of the affine `V`, transported into the limit `W`. -/
lemma isAffineOpen_basicOpen_sV (l : Fin E.n) :
    IsAffineOpen (E.Wc.pt.basicOpen (E.sV (E.b l))) := by
  rw [E.basicOpen_sV]
  exact (E.hV.basicOpen (E.b l)).preimage_of_isOpenImmersion _
    (by rw [E.opensRange_WUι_comp_Uι]; exact E.hb l)

/-- (Implementation) Below any index, there is a pre-stage: lifts of the generators whose
basic opens are affine and cover. The covering condition descends from the limit by
`exists_map_eq_top`, and affineness by descending the affine limit basic open
(Stacks 01Z4). -/
lemma exists_preStage_hom (j₀ : Over E.i₀) :
    ∃ (P : E.PreStage), Nonempty (P.j ⟶ j₀) := by
  -- Step 1: lifts with the covering condition.
  obtain ⟨j₁, k₁, r, hr⟩ := E.exists_r j₀
  have hU : E.Wc.π.app j₁ ⁻¹ᵁ (⨆ l, (E.WD.obj j₁).basicOpen (r l)) = ⊤ := by
    rw [Scheme.Hom.preimage_iSup]
    simp_rw [Scheme.preimage_basicOpen_top]
    have h : ∀ l, (E.Wc.π.app j₁).appTop (r l) = E.sV (E.b l) := hr
    simp_rw [h]
    exact E.iSup_basicOpen_sV
  obtain ⟨j₂, k₂, hk₂⟩ := exists_map_eq_top E.WD E.Wc E.isLimitWc _ hU
  set r₂ : Fin E.n → Γ(E.WD.obj j₂, ⊤) := fun l ↦ E.res k₂ (r l) with hr₂def
  have hr₂ : ∀ l, E.t j₂ (r₂ l) = E.sV (E.b l) := fun l ↦ by rw [hr₂def, E.t_res, hr]
  have hcov₂ : ⨆ l, (E.WD.obj j₂).basicOpen (r₂ l) = ⊤ := by
    have hb : ∀ l, (E.WD.obj j₂).basicOpen (r₂ l) =
        E.WD.map k₂ ⁻¹ᵁ ((E.WD.obj j₁).basicOpen (r l)) :=
      fun l ↦ (Scheme.preimage_basicOpen_top (E.WD.map k₂) (r l)).symm
    simp_rw [hb, ← Scheme.Hom.preimage_iSup, hk₂]
  -- Step 2: affineness of the basic opens, by descending the affine limit basic open
  -- and equalizing (Stacks 01Z4).
  have hex : ∀ (j : Over E.i₀) (k : j ⟶ j₂) (l : Fin E.n),
      ∃ (ja : Over E.i₀) (ka : ja ⟶ j),
        IsAffineOpen ((E.WD.obj ja).basicOpen (E.res (ka ≫ k) (r₂ l))) := by
    intro j k l
    obtain ⟨i, O, hO, hOeq⟩ := exists_isAffineOpen_preimage_eq E.WD E.Wc E.isLimitWc _
      (E.isAffineOpen_basicOpen_sV l)
    obtain ⟨j', kj, ki, -⟩ := IsCofilteredOrEmpty.cone_objs j i
    have hpre : E.Wc.π.app j' ⁻¹ᵁ ((E.WD.obj j').basicOpen (E.res (kj ≫ k) (r₂ l))) =
        E.Wc.π.app j' ⁻¹ᵁ (E.WD.map ki ⁻¹ᵁ O) := by
      rw [Scheme.preimage_basicOpen_top, ← Scheme.Hom.comp_preimage, E.Wc.w ki, hOeq]
      congr 1
      exact (E.t_res (kj ≫ k) (r₂ l)).trans (hr₂ l)
    obtain ⟨j'', k'', heq⟩ := exists_map_preimage_eq_map_preimage E.WD E.Wc E.isLimitWc
      (TopologicalSpace.NoetherianSpace.isCompact _)
      (TopologicalSpace.NoetherianSpace.isCompact _) hpre
    refine ⟨j'', k'' ≫ kj, ?_⟩
    have e : (E.WD.obj j'').basicOpen (E.res ((k'' ≫ kj) ≫ k) (r₂ l)) =
        E.WD.map k'' ⁻¹ᵁ ((E.WD.obj j').basicOpen (E.res (kj ≫ k) (r₂ l))) := by
      rw [Scheme.preimage_basicOpen_top]
      congr 1
      rw [Category.assoc]
      exact (E.res_res (kj ≫ k) k'' _).symm
    rw [e, heq]
    exact (hO.preimage (E.WD.map ki)).preimage (E.WD.map k'')
  obtain ⟨j₃, k₃, h₃⟩ := E.exists_hom_forall (j₂ := j₂)
    (fun j' k l ↦ IsAffineOpen ((E.WD.obj j').basicOpen (E.res k (r₂ l))))
    (fun {j j'} k' k l hl ↦ by
      have e : (E.WD.obj j').basicOpen (E.res (k' ≫ k) (r₂ l)) =
          E.WD.map k' ⁻¹ᵁ ((E.WD.obj j).basicOpen (E.res k (r₂ l))) := by
        rw [Scheme.preimage_basicOpen_top]
        congr 1
        exact (E.res_res k k' _).symm
      rw [e]
      exact hl.preimage _)
    hex
  have hcov₃ : ⨆ l, (E.WD.obj j₃).basicOpen (E.res k₃ (r₂ l)) = ⊤ := by
    have hb : ∀ l, (E.WD.obj j₃).basicOpen (E.res k₃ (r₂ l)) =
        E.WD.map k₃ ⁻¹ᵁ ((E.WD.obj j₂).basicOpen (r₂ l)) :=
      fun l ↦ (Scheme.preimage_basicOpen_top (E.WD.map k₃) (r₂ l)).symm
    simp_rw [hb, ← Scheme.Hom.preimage_iSup, hcov₂, Scheme.Hom.preimage_top]
  exact ⟨⟨j₃, fun l ↦ E.res k₃ (r₂ l), fun l ↦ by rw [E.t_res, hr₂], hcov₃, h₃⟩,
    ⟨(k₃ ≫ k₂) ≫ k₁⟩⟩

/-- (Implementation) Equalize two families of sections with equal limit restrictions at a
common finer index. -/
lemma exists_hom_res_eq {j₂ : Over E.i₀} (x y : Fin E.n → Γ(E.WD.obj j₂, ⊤))
    (h : ∀ l, E.t j₂ (x l) = E.t j₂ (y l)) :
    ∃ (j : Over E.i₀) (k : j ⟶ j₂), ∀ l, E.res k (x l) = E.res k (y l) := by
  apply E.exists_hom_forall (fun j k l ↦ E.res k (x l) = E.res k (y l))
  · intro j j' k' k l hl
    exact (E.res_res k k' _).symm.trans
      ((congrArg (fun z ↦ E.res k' z) hl).trans (E.res_res k k' _))
  · intro j k l
    have hcpt : IsCompact ((⊤ : (E.WD.obj j).Opens) : Set (E.WD.obj j)) := isCompact_univ
    obtain ⟨j', k', hk'⟩ := exists_app_map_eq_map_of_isLimit E.WD E.Wc E.isLimitWc hcpt
      (E.res k (x l)) (E.res k (y l))
      (show E.t j (E.res k (x l)) = E.t j (E.res k (y l)) by rw [E.t_res, E.t_res, h])
    refine ⟨j', k', ?_⟩
    exact (E.res_res k k' _).symm.trans (hk'.trans (E.res_res k k' _))

instance : Nonempty E.Stage := by
  obtain ⟨P, -⟩ := E.exists_preStage_hom (Over.mk (𝟙 E.i₀))
  exact ⟨P.stage⟩

instance : IsCofilteredOrEmpty E.Stage where
  cone_objs T₁ T₂ := by
    obtain ⟨j', k₁, k₂, -⟩ := IsCofilteredOrEmpty.cone_objs T₁.j T₂.j
    obtain ⟨j, k, hk⟩ := E.exists_hom_res_eq (fun l ↦ E.res k₁ (T₁.r l))
      (fun l ↦ E.res k₂ (T₂.r l)) (fun l ↦ by rw [E.t_res, E.t_res, T₁.hr, T₂.hr])
    have hmap : T₂.A.map (resAlgHom (k ≫ k₂)) ≤ E.fiberProduct j := by
      rintro p ⟨q, hq, rfl⟩
      exact resAlgHom_mem_fiberProduct _ (T₂.A_le_fiberProduct hq)
    refine ⟨T₁.restrict (k ≫ k₁) (T₂.A.map (resAlgHom (k ≫ k₂))) hmap (T₂.hAfg.map _),
      T₁.restrictHom _ _ _ _, ⟨k ≫ k₂, fun l ↦ ?_, fun p hp ↦ ?_⟩, trivial⟩
    · exact (E.res_res k₂ k _).symm.trans ((hk l).symm.trans (E.res_res k₁ k _))
    · exact T₁.le_restrict_A _ _ _ _ ⟨p, hp, rfl⟩
  cone_maps T₁ T₂ f g := by
    obtain ⟨j', k, hk⟩ := IsCofilteredOrEmpty.cone_maps f.base g.base
    refine ⟨T₁.restrict k ⊥ bot_le Subalgebra.fg_bot, T₁.restrictHom _ _ _ _, ?_⟩
    exact E.stageHom_ext (by simpa using hk)

instance : IsCofiltered E.Stage where

/-- (Implementation) The index functor from stages to the base indices. By
`exists_preStage_hom` and the restriction construction it is initial: limits over the
system of the `Wⱼ` may be computed over the category of stages. -/
@[simps] def stageIndex : E.Stage ⥤ Over E.i₀ where
  obj T := T.j
  map f := f.base

instance : E.stageIndex.Initial := by
  apply Functor.initial_of_exists_of_isCofiltered
  · intro j
    obtain ⟨P, ⟨k⟩⟩ := E.exists_preStage_hom j
    exact ⟨P.stage, ⟨k⟩⟩
  · intro j T s s'
    obtain ⟨j', k, hk⟩ := IsCofilteredOrEmpty.cone_maps s s'
    exact ⟨T.restrict k ⊥ bot_le Subalgebra.fg_bot, T.restrictHom _ _ _ _, by simpa using hk⟩

variable {E}

/-- (Implementation) The open immersion of `Wⱼ` into the stage `Dⱼ`. -/
noncomputable abbrev Wι (E : ExtensionData.{u}) (j : Over E.i₀) :
    E.WD.obj j ⟶ E.N.D.obj j.left :=
  (opensDiagramι E.N.D E.i₀ E.W₀).app j

instance (E : ExtensionData.{u}) (j : Over E.i₀) : IsOpenImmersion (E.Wι j) :=
  inferInstanceAs (IsOpenImmersion ((opensDiagramι E.N.D E.i₀ E.W₀).app j))

@[reassoc]
lemma WD_map_Wι {j j' : Over E.i₀} (k : j ⟶ j') :
    E.WD.map k ≫ E.Wι j' = E.Wι j ≫ E.N.D.map k.left :=
  (opensDiagramι E.N.D E.i₀ E.W₀).naturality k

/-- (Implementation) The first projection from the coefficient algebra of a stage to the
sections of `V`. -/
noncomputable def Stage.φ (T : E.Stage) : CommRingCat.of ↥T.A ⟶ Γ(E.X, E.V) :=
  CommRingCat.ofHom ((RingHom.fst _ _).comp (Subalgebra.val T.A).toRingHom)

@[simp] lemma Stage.φ_apply (T : E.Stage) (a : ↥T.A) :
    T.φ a = (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).1 := rfl

/-- (Implementation) The map of coefficient algebras attached to a morphism of stages. -/
noncomputable def Stage.Hom.algHom {T T' : E.Stage} (f : T ⟶ T') :
    CommRingCat.of ↥T'.A ⟶ CommRingCat.of ↥T.A :=
  CommRingCat.ofHom
    ((AlgHom.codRestrict ((resAlgHom f.base).comp T'.A.val) T.A
      (fun a ↦ f.map_mem _ a.2)).toRingHom)

@[simp] lemma Stage.Hom.algHom_coe {T T' : E.Stage} (f : T ⟶ T') (a : ↥T'.A) :
    ((f.algHom a : ↥T.A) : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)) =
      ((a : Γ(E.X, E.V) × Γ(E.WD.obj T'.j, ⊤)).1,
        E.res f.base (a : Γ(E.X, E.V) × Γ(E.WD.obj T'.j, ⊤)).2) := rfl

lemma Stage.Hom.algHom_ρ {T T' : E.Stage} (f : T ⟶ T') :
    f.algHom ≫ T.ρ = T'.ρ ≫ E.res f.base := rfl

lemma Stage.Hom.algHom_φ {T T' : E.Stage} (f : T ⟶ T') :
    f.algHom ≫ T.φ = T'.φ := rfl

@[simp] lemma Stage.Hom.algHom_id (T : E.Stage) : (𝟙 T : T ⟶ T).algHom = 𝟙 _ := by
  ext a
  · rfl
  · rw [Stage.Hom.algHom_coe]
    exact E.res_id _ _

@[simp] lemma Stage.Hom.algHom_comp {T T' T'' : E.Stage} (f : T ⟶ T') (g : T' ⟶ T'') :
    (f ≫ g).algHom = g.algHom ≫ f.algHom := by
  ext a
  · rfl
  · rw [Stage.Hom.algHom_coe]
    exact (E.res_res g.base f.base _).symm

@[reassoc (attr := simp)]
lemma Stage.Hom.SpecMap_φ {T T' : E.Stage} (f : T ⟶ T') :
    Spec.map T.φ ≫ Spec.map f.algHom = Spec.map T'.φ := by
  rw [← Spec.map_comp, Stage.Hom.algHom_φ]

lemma Stage.toSpec_comp_SpecMap_algHom {T T' : E.Stage} (f : T ⟶ T') :
    T.toSpec ≫ Spec.map f.algHom = E.WD.map f.base ≫ T'.toSpec := by
  rw [Stage.toSpec, Stage.toSpec, Category.assoc, ← Spec.map_comp, Stage.Hom.algHom_ρ,
    Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc]

set_option maxHeartbeats 1600000 in
-- Elaborating the pushout functor forces repeated defeq checks between the two
-- `Algebra` structures on the coefficient algebra of a stage.
/-- (Implementation) The system of stage schemes: the scheme attached to a stage is the
gluing of the Noetherian stage `Dⱼ` and the affine scheme `Spec A` along `Wⱼ`. -/
noncomputable def stageDiagram (E : ExtensionData.{u}) : E.Stage ⥤ Scheme.{u} where
  obj T := pushout (E.Wι T.j) T.toSpec
  map {T T'} f := pushout.map _ _ _ _ (E.N.D.map f.base.left) (Spec.map f.algHom)
    (E.WD.map f.base) (WD_map_Wι f.base).symm (Stage.toSpec_comp_SpecMap_algHom f)
  map_id T := by
    have hb : (𝟙 T : T ⟶ T).base.left = 𝟙 T.j.left := rfl
    have h2 := Stage.Hom.algHom_id T
    refine pushout.hom_ext ?_ ?_
    · rw [pushout.inl_desc, hb, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    · rw [pushout.inr_desc, h2, Spec.map_id, Category.id_comp, Category.comp_id]
  map_comp {T T' T''} f g := by
    have hb : (f ≫ g).base.left = f.base.left ≫ g.base.left := rfl
    have h2 := Stage.Hom.algHom_comp f g
    refine pushout.hom_ext ?_ ?_
    · simp only [pushout.inl_desc, pushout.inl_desc_assoc, hb, CategoryTheory.Functor.map_comp,
        Category.assoc]
    · simp only [pushout.inr_desc, pushout.inr_desc_assoc, h2, Spec.map_comp, Category.assoc]

@[simp] lemma stageDiagram_obj (T : E.Stage) :
    E.stageDiagram.obj T = pushout (E.Wι T.j) T.toSpec := rfl

@[reassoc (attr := simp)]
lemma inl_stageDiagram_map {T T' : E.Stage} (f : T ⟶ T') :
    pushout.inl (E.Wι T.j) T.toSpec ≫ E.stageDiagram.map f =
      E.N.D.map f.base.left ≫ pushout.inl (E.Wι T'.j) T'.toSpec :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma inr_stageDiagram_map {T T' : E.Stage} (f : T ⟶ T') :
    pushout.inr (E.Wι T.j) T.toSpec ≫ E.stageDiagram.map f =
      Spec.map f.algHom ≫ pushout.inr (E.Wι T'.j) T'.toSpec :=
  pushout.inr_desc _ _ _


@[simp] lemma opensRange_Wι (E : ExtensionData.{u}) (j : Over E.i₀) :
    (E.Wι j).opensRange = E.N.D.map j.hom ⁻¹ᵁ E.W₀ :=
  Scheme.Opens.opensRange_ι _

/-- (Implementation) The `Wⱼ`-squares of the system of stages are cartesian. -/
lemma isPullback_Wι {T T' : E.Stage} (f : T ⟶ T') :
    IsPullback (E.WD.map f.base) (E.Wι T.j) (E.Wι T'.j) (E.N.D.map f.base.left) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (WD_map_Wι f.base).symm ?_
  rw [opensRange_Wι, opensRange_Wι, ← Scheme.Hom.comp_preimage, ← E.N.D.map_comp, Over.w f.base]

set_option maxHeartbeats 1600000 in
-- The basic opens of the tautological elements have to be compared through
-- `Spec.map` of the coefficient algebra map, which unfolds the stage structure.
/-- (Implementation) The `Spec A`-squares of the system of stages are cartesian. -/
lemma isPullback_toSpec {T T' : E.Stage} (f : T ⟶ T') :
    IsPullback (E.WD.map f.base) T.toSpec T'.toSpec (Spec.map f.algHom) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (Stage.toSpec_comp_SpecMap_algHom f) ?_
  rw [T.opensRange_toSpec, T'.opensRange_toSpec, Scheme.Hom.preimage_iSup]
  refine iSup_congr fun l ↦ ?_
  rw [SpecMap_preimage_basicOpen]
  congr 1
  refine Subtype.ext ?_
  rw [Stage.Hom.algHom_coe, Stage.coe_h, Stage.coe_h, f.res_r]

lemma isPullback_pushout_inl {T T' : E.Stage} (f : T ⟶ T') :
    IsPullback (E.N.D.map f.base.left) (pushout.inl (E.Wι T.j) T.toSpec)
      (pushout.inl (E.Wι T'.j) T'.toSpec) (E.stageDiagram.map f) :=
  isPullback_pushout_map_inl_of_isPullback (E.Wι T'.j) T'.toSpec (E.Wι T.j) T.toSpec
    (E.N.D.map f.base.left) (Spec.map f.algHom) (E.WD.map f.base) (WD_map_Wι f.base)
    (Stage.toSpec_comp_SpecMap_algHom f).symm (isPullback_toSpec f)

lemma isPullback_pushout_inr {T T' : E.Stage} (f : T ⟶ T') :
    IsPullback (Spec.map f.algHom) (pushout.inr (E.Wι T.j) T.toSpec)
      (pushout.inr (E.Wι T'.j) T'.toSpec) (E.stageDiagram.map f) :=
  isPullback_pushout_map_inr_of_isPullback (E.Wι T'.j) T'.toSpec (E.Wι T.j) T.toSpec
    (E.N.D.map f.base.left) (Spec.map f.algHom) (E.WD.map f.base) (WD_map_Wι f.base)
    (Stage.toSpec_comp_SpecMap_algHom f).symm (isPullback_Wι f)

instance (T : E.Stage) : CompactSpace (E.stageDiagram.obj T) :=
  inferInstanceAs (CompactSpace ↑(pushout (E.Wι T.j) T.toSpec))

instance (T : E.Stage) :
    LocallyOfFiniteType (specULiftZIsTerminal.from (Spec (CommRingCat.of ↥T.A))) :=
  have : Algebra.FiniteType ℤ ↥T.A := (Subalgebra.fg_iff_finiteType _).mp T.hAfg
  inferInstanceAs (LocallyOfFiniteType (specULiftZIsTerminal.from (Spec (.of ↥T.A))))

instance (T : E.Stage) :
    LocallyOfFiniteType (specULiftZIsTerminal.from (E.stageDiagram.obj T)) := by
  rw [specULiftZIsTerminal.hom_ext (specULiftZIsTerminal.from (E.stageDiagram.obj T))
    (pushout.desc (specULiftZIsTerminal.from (E.N.D.obj T.j.left))
      (specULiftZIsTerminal.from (Spec (CommRingCat.of ↥T.A)))
      (specULiftZIsTerminal.hom_ext _ _))]
  exact IsZariskiLocalAtSource.pushout_desc (E.Wι T.j) T.toSpec _ inferInstance inferInstance

instance isAffineHom_stageDiagram_map {T T' : E.Stage} (f : T ⟶ T') :
    IsAffineHom (E.stageDiagram.map f) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsAffineHom)
    (IsOpenImmersion.pushoutCover (E.Wι T'.j) T'.toSpec)
  rintro (_ | _)
  · change IsAffineHom (pullback.snd (E.stageDiagram.map f) (pushout.inl (E.Wι T'.j) T'.toSpec))
    refine (MorphismProperty.cancel_left_of_respectsIso (@IsAffineHom)
      (isPullback_pushout_inl f).flip.isoPullback.hom _).mp ?_
    rw [(isPullback_pushout_inl f).flip.isoPullback_hom_snd]
    infer_instance
  · change IsAffineHom (pullback.snd (E.stageDiagram.map f) (pushout.inr (E.Wι T'.j) T'.toSpec))
    refine (MorphismProperty.cancel_left_of_respectsIso (@IsAffineHom)
      (isPullback_pushout_inr f).flip.isoPullback.hom _).mp ?_
    rw [(isPullback_pushout_inr f).flip.isoPullback_hom_snd]
    infer_instance


/-! ### The cone -/

lemma sVle (E : ExtensionData.{u}) : (⊤ : E.Wc.pt.Opens) ≤ (E.WU.ι ≫ E.U.ι) ⁻¹ᵁ E.V := by
  rw [Scheme.Hom.comp_preimage, ← E.hW₀, Scheme.Opens.ι_preimage_self]

lemma sV_eq (E : ExtensionData.{u}) :
    E.sV = (E.WU.ι ≫ E.U.ι).appLE E.V ⊤ E.sVle := rfl

lemma range_WUι_comp_Uι_subset (E : ExtensionData.{u}) :
    Set.range (E.WU.ι ≫ E.U.ι) ⊆ Set.range E.V.ι := by
  rw [Scheme.Opens.range_ι]
  rintro - ⟨x, rfl⟩
  have hx : (E.WU.ι ≫ E.U.ι) x ∈ (E.WU.ι ≫ E.U.ι).opensRange := ⟨x, rfl⟩
  rw [E.opensRange_WUι_comp_Uι] at hx
  exact hx.2

/-- (Implementation) The canonical morphism from the intersection `W = U ⊓ V` to `V`. -/
noncomputable def ζ (E : ExtensionData.{u}) : E.Wc.pt ⟶ E.V.toScheme :=
  IsOpenImmersion.lift E.V.ι (E.WU.ι ≫ E.U.ι) E.range_WUι_comp_Uι_subset

@[reassoc (attr := simp)]
lemma ζ_ι (E : ExtensionData.{u}) : E.ζ ≫ E.V.ι = E.WU.ι ≫ E.U.ι :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc]
lemma Wc_π_Wι (E : ExtensionData.{u}) (j : Over E.i₀) :
    E.Wc.π.app j ≫ E.Wι j = E.WU.ι ≫ E.N.π.app j.left :=
  Scheme.Hom.resLE_comp_ι _ _

lemma toSpecΓ_ζ (E : ExtensionData.{u}) :
    E.ζ ≫ E.V.toSpecΓ = E.Wc.pt.toSpecΓ ≫ Spec.map E.sV := by
  haveI : IsIso ((⊤ : E.Wc.pt.Opens).ι) := by
    rw [← Scheme.topIso_hom]; infer_instance
  have hres : (E.WU.ι ≫ E.U.ι).resLE E.V ⊤ E.sVle = (⊤ : E.Wc.pt.Opens).ι ≫ E.ζ := by
    rw [← cancel_mono E.V.ι, Scheme.Hom.resLE_comp_ι, Category.assoc, E.ζ_ι]
  have h := Scheme.Opens.toSpecΓ_SpecMap_appLE (E.WU.ι ≫ E.U.ι) E.V (⊤ : E.Wc.pt.Opens) E.sVle
  rw [← E.sV_eq, hres, Scheme.Opens.toSpecΓ_top, Category.assoc, Category.assoc] at h
  exact ((cancel_epi ((⊤ : E.Wc.pt.Opens).ι)).mp h).symm

/-- (Implementation) Comparing `W` with `Spec A` via `V` and via `Wⱼ` gives the same
morphism: this is where the fiber product condition on the coefficient algebra enters. -/
@[reassoc]
lemma Stage.ζ_toSpecΓ_SpecMap_φ (T : E.Stage) :
    E.ζ ≫ E.V.toSpecΓ ≫ Spec.map T.φ = E.Wc.π.app T.j ≫ T.toSpec := by
  rw [Stage.toSpec, ← Category.assoc E.ζ, E.toSpecΓ_ζ, Category.assoc, ← Spec.map_comp,
    ← Category.assoc (E.Wc.π.app T.j), Scheme.toSpecΓ_naturality, Category.assoc,
    ← Spec.map_comp]
  congr 2
  ext a
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply]
  exact T.hA _ a.2

/-- (Implementation) The open cover of `X` by `U` and `V`. -/
noncomputable def cover (E : ExtensionData.{u}) : E.X.OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun b ↦ (bif b then E.U else E.V).toScheme)
    (fun b ↦ (bif b then E.U else E.V).ι)
    (fun x ↦ by
      have hx : x ∈ E.U ⊔ E.V := by rw [E.hUV]; trivial
      rcases TopologicalSpace.Opens.mem_sup.mp hx with h | h
      · exact ⟨true, ⟨x, h⟩, rfl⟩
      · exact ⟨false, ⟨x, h⟩, rfl⟩)
    (fun b ↦ by cases b <;> exact inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι _)))

@[simp] lemma cover_f_true (E : ExtensionData.{u}) : E.cover.f true = E.U.ι := rfl

@[simp] lemma cover_f_false (E : ExtensionData.{u}) : E.cover.f false = E.V.ι := rfl

/-- (Implementation) The morphism `U ⟶ Sₜ` of the cone. -/
noncomputable def Stage.fromU (T : E.Stage) : E.U.toScheme ⟶ E.stageDiagram.obj T :=
  E.N.π.app T.j.left ≫ pushout.inl (E.Wι T.j) T.toSpec

/-- (Implementation) The morphism `V ⟶ Sₜ` of the cone. -/
noncomputable def Stage.fromV (T : E.Stage) : E.V.toScheme ⟶ E.stageDiagram.obj T :=
  E.V.toSpecΓ ≫ Spec.map T.φ ≫ pushout.inr (E.Wι T.j) T.toSpec

lemma Stage.WUι_fromU (T : E.Stage) : E.WU.ι ≫ T.fromU = E.ζ ≫ T.fromV := by
  rw [Stage.fromU, Stage.fromV, ← E.Wc_π_Wι_assoc T.j, pushout.condition,
    T.ζ_toSpecΓ_SpecMap_φ_assoc]

/-- (Implementation) The isomorphism between `U ⊓ V` and the intersection `W`. -/
noncomputable def θ (E : ExtensionData.{u}) : (E.U ⊓ E.V).toScheme ≅ E.Wc.pt :=
  IsOpenImmersion.isoOfRangeEq (E.X.homOfLE (inf_le_left : E.U ⊓ E.V ≤ E.U)) E.WU.ι (by
    rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange, Scheme.opensRange_homOfLE,
      Scheme.Opens.opensRange_ι, ExtensionData.WU, E.hW₀]
    congr 1
    rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq])

@[reassoc (attr := simp)]
lemma θ_hom_WUι (E : ExtensionData.{u}) :
    E.θ.hom ≫ E.WU.ι = E.X.homOfLE (inf_le_left : E.U ⊓ E.V ≤ E.U) :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]
lemma θ_hom_ζ (E : ExtensionData.{u}) :
    E.θ.hom ≫ E.ζ = E.X.homOfLE (inf_le_right : E.U ⊓ E.V ≤ E.V) := by
  rw [← cancel_mono E.V.ι, Category.assoc, E.ζ_ι, ← Category.assoc, E.θ_hom_WUι,
    Scheme.homOfLE_ι, Scheme.homOfLE_ι]

@[reassoc (attr := simp)]
lemma θ_inv_homOfLE (E : ExtensionData.{u}) :
    E.θ.inv ≫ E.X.homOfLE (inf_le_left : E.U ⊓ E.V ≤ E.U) = E.WU.ι := by
  rw [← E.θ_hom_WUι, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
lemma θ_inv_infι (E : ExtensionData.{u}) : E.θ.inv ≫ (E.U ⊓ E.V).ι = E.WU.ι ≫ E.U.ι := by
  rw [← Scheme.homOfLE_ι E.X (inf_le_left : E.U ⊓ E.V ≤ E.U), ← Category.assoc,
    θ_inv_homOfLE]

lemma Stage.homOfLE_fromU (T : E.Stage) {W : E.X.Opens} (h₁ : W ≤ E.U) (h₂ : W ≤ E.V) :
    E.X.homOfLE h₁ ≫ T.fromU = E.X.homOfLE h₂ ≫ T.fromV := by
  rw [← E.X.homOfLE_homOfLE (le_inf h₁ h₂) (inf_le_left : E.U ⊓ E.V ≤ E.U),
    ← E.X.homOfLE_homOfLE (le_inf h₁ h₂) (inf_le_right : E.U ⊓ E.V ≤ E.V), Category.assoc,
    Category.assoc, ← E.θ_hom_WUι, ← E.θ_hom_ζ, Category.assoc, Category.assoc, T.WUι_fromU]

/-- (Implementation) The morphism from `X` to the stage scheme of a stage: it restricts to
the projection of the approximation of `U` on `U`, and to the map induced by the first
projection of the coefficient algebra on `V`. -/
noncomputable def Stage.fromX (T : E.Stage) : E.X ⟶ E.stageDiagram.obj T :=
  E.cover.glueMorphisms (fun b ↦ match b with | true => T.fromU | false => T.fromV) (by
    rintro (_ | _) (_ | _)
    · change pullback.fst E.V.ι E.V.ι ≫ T.fromV = pullback.snd E.V.ι E.V.ι ≫ T.fromV
      rw [(cancel_mono E.V.ι).mp
        (pullback.condition : pullback.fst E.V.ι E.V.ι ≫ _ = pullback.snd _ _ ≫ _)]
    · change pullback.fst E.V.ι E.U.ι ≫ T.fromV = pullback.snd E.V.ι E.U.ι ≫ T.fromU
      rw [← cancel_epi (isPullback_opens_inf E.V E.U).isoPullback.hom, ← Category.assoc,
        ← Category.assoc, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_snd]
      exact (T.homOfLE_fromU inf_le_right inf_le_left).symm
    · change pullback.fst E.U.ι E.V.ι ≫ T.fromU = pullback.snd E.U.ι E.V.ι ≫ T.fromV
      rw [← cancel_epi (isPullback_opens_inf E.U E.V).isoPullback.hom, ← Category.assoc,
        ← Category.assoc, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_snd]
      exact T.homOfLE_fromU inf_le_left inf_le_right
    · change pullback.fst E.U.ι E.U.ι ≫ T.fromU = pullback.snd E.U.ι E.U.ι ≫ T.fromU
      rw [(cancel_mono E.U.ι).mp
        (pullback.condition : pullback.fst E.U.ι E.U.ι ≫ _ = pullback.snd _ _ ≫ _)])


@[reassoc (attr := simp)]
lemma Stage.Uι_fromX (T : E.Stage) : E.U.ι ≫ T.fromX = T.fromU :=
  E.cover.ι_glueMorphisms _ _ true

@[reassoc (attr := simp)]
lemma Stage.Vι_fromX (T : E.Stage) : E.V.ι ≫ T.fromX = T.fromV :=
  E.cover.ι_glueMorphisms _ _ false

@[reassoc]
lemma N_π_naturality (E : ExtensionData.{u}) {i i' : E.N.I} (g : i ⟶ i') :
    E.N.π.app i ≫ E.N.D.map g = E.N.π.app i' :=
  E.cone.w g

/-- (Implementation) The cone with point `X` over the system of stage schemes. -/
noncomputable def stageCone (E : ExtensionData.{u}) : Cone E.stageDiagram where
  pt := E.X
  π :=
    { app := fun T ↦ T.fromX
      naturality := fun T T' f ↦ by
        change 𝟙 E.X ≫ T'.fromX = T.fromX ≫ E.stageDiagram.map f
        rw [Category.id_comp]
        refine E.cover.hom_ext _ _ fun b ↦ ?_
        cases b
        · simp only [cover_f_false, Stage.Vι_fromX, Stage.Vι_fromX_assoc, Stage.fromV,
            Category.assoc, inr_stageDiagram_map, Stage.Hom.SpecMap_φ_assoc]
        · simp only [cover_f_true, Stage.Uι_fromX, Stage.Uι_fromX_assoc, Stage.fromU,
            Category.assoc, inl_stageDiagram_map, E.N_π_naturality_assoc] }

@[simp] lemma stageCone_pt (E : ExtensionData.{u}) : E.stageCone.pt = E.X := rfl

@[simp] lemma stageCone_π_app (E : ExtensionData.{u}) (T : E.Stage) :
    E.stageCone.π.app T = T.fromX := rfl


/-! ### The two charts of a stage scheme -/

/-- (Implementation) The chart of a stage scheme coming from the Noetherian stage `Dⱼ`. -/
noncomputable abbrev Stage.chartU (T : E.Stage) : (E.stageDiagram.obj T).Opens :=
  (pushout.inl (E.Wι T.j) T.toSpec).opensRange

/-- (Implementation) The chart of a stage scheme coming from `Spec A`. -/
noncomputable abbrev Stage.chartV (T : E.Stage) : (E.stageDiagram.obj T).Opens :=
  (pushout.inr (E.Wι T.j) T.toSpec).opensRange

lemma Stage.chartU_sup_chartV (T : E.Stage) : T.chartU ⊔ T.chartV = ⊤ :=
  opensRange_pushout_inl_sup_opensRange_pushout_inr _ _

lemma Stage.preimage_chartU {T T' : E.Stage} (f : T ⟶ T') :
    E.stageDiagram.map f ⁻¹ᵁ T'.chartU = T.chartU :=
  preimage_opensRange_pushout_inl_of_isPullback _ _ _ _ _ _ _ (WD_map_Wι f.base)
    (Stage.toSpec_comp_SpecMap_algHom f).symm (isPullback_toSpec f)

lemma Stage.preimage_chartV {T T' : E.Stage} (f : T ⟶ T') :
    E.stageDiagram.map f ⁻¹ᵁ T'.chartV = T.chartV :=
  preimage_opensRange_pushout_inr_of_isPullback _ _ _ _ _ _ _ (WD_map_Wι f.base)
    (Stage.toSpec_comp_SpecMap_algHom f).symm (isPullback_Wι f)

lemma Stage.chartU_inf_chartV (T : E.Stage) :
    T.chartU ⊓ T.chartV = (E.Wι T.j ≫ pushout.inl (E.Wι T.j) T.toSpec).opensRange := by
  rw [Scheme.Hom.opensRange_comp (E.Wι T.j) (pushout.inl (E.Wι T.j) T.toSpec),
    ← preimage_opensRange_pushout_inr (E.Wι T.j) T.toSpec,
    Scheme.Hom.image_preimage_eq_opensRange_inf]

lemma Stage.fromX_preimage_chartU (T : E.Stage) : T.fromX ⁻¹ᵁ T.chartU = E.U := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · have hmem : x ∈ E.U ⊔ E.V := by rw [E.hUV]; trivial
    rcases TopologicalSpace.Opens.mem_sup.mp hmem with h | h
    · exact h
    · -- `x` lies in `V`; its image in `Spec A` lies in the image of `Wⱼ`, hence in one of
      -- the basic opens of the generators, which are contained in `U`.
      obtain ⟨y, hy⟩ : ∃ y, pushout.inl (E.Wι T.j) T.toSpec y = T.fromX x := hx
      set x' : E.V.toScheme := ⟨x, h⟩ with hx'
      have hfV : T.fromX x = pushout.inr (E.Wι T.j) T.toSpec
          (Spec.map T.φ (E.V.toSpecΓ x')) :=
        calc T.fromX x = (E.V.ι ≫ T.fromX) x' := rfl
          _ = T.fromV x' := by rw [Stage.Vι_fromX]
          _ = _ := rfl
      rw [hfV] at hy
      obtain ⟨w, -, hw⟩ := (pushout_inl_eq_inr_iff (E.Wι T.j) T.toSpec _ _).mp hy
      have hq : Spec.map T.φ (E.V.toSpecΓ x') ∈ T.toSpec.opensRange := ⟨w, hw⟩
      rw [T.opensRange_toSpec] at hq
      obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp hq
      have hl' : E.V.toSpecΓ x' ∈ Spec.map T.φ ⁻¹ᵁ PrimeSpectrum.basicOpen (T.h l) := hl
      rw [SpecMap_preimage_basicOpen] at hl'
      have hb : (T.φ (T.h l) : Γ(E.X, E.V)) = E.b l := rfl
      rw [hb] at hl'
      have : x' ∈ E.V.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen (E.b l) := hl'
      rw [Scheme.Opens.toSpecΓ_preimage_basicOpen] at this
      exact ((E.hb l) this).1
  · change T.fromX x ∈ T.chartU
    have h1 : T.fromX x = pushout.inl (E.Wι T.j) T.toSpec
        (E.N.π.app T.j.left (⟨x, hx⟩ : E.U.toScheme)) :=
      calc T.fromX x = (E.U.ι ≫ T.fromX) (⟨x, hx⟩ : E.U.toScheme) := rfl
        _ = T.fromU (⟨x, hx⟩ : E.U.toScheme) := by rw [Stage.Uι_fromX]
        _ = _ := rfl
    rw [h1]
    exact ⟨_, rfl⟩

lemma Stage.fromX_preimage_chartV (T : E.Stage) : T.fromX ⁻¹ᵁ T.chartV = E.V := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · have hmem : x ∈ E.U ⊔ E.V := by rw [E.hUV]; trivial
    rcases TopologicalSpace.Opens.mem_sup.mp hmem with h | h
    · obtain ⟨y, hy⟩ : ∃ y, pushout.inr (E.Wι T.j) T.toSpec y = T.fromX x := hx
      set x' : E.U.toScheme := ⟨x, h⟩ with hx'
      have hfU : T.fromX x = pushout.inl (E.Wι T.j) T.toSpec (E.N.π.app T.j.left x') :=
        calc T.fromX x = (E.U.ι ≫ T.fromX) x' := rfl
          _ = T.fromU x' := by rw [Stage.Uι_fromX]
          _ = _ := rfl
      rw [hfU] at hy
      obtain ⟨w, hw, -⟩ := (pushout_inl_eq_inr_iff (E.Wι T.j) T.toSpec _ _).mp hy.symm
      have hp : E.N.π.app T.j.left x' ∈ (E.Wι T.j).opensRange := ⟨w, hw⟩
      rw [opensRange_Wι] at hp
      have hp' : E.N.π.app E.i₀ x' ∈ E.W₀ := by
        rw [← E.N_π_naturality T.j.hom, Scheme.Hom.comp_apply]
        exact hp
      have : x' ∈ E.N.π.app E.i₀ ⁻¹ᵁ E.W₀ := hp'
      rw [E.hW₀] at this
      exact this
    · exact h
  · change T.fromX x ∈ T.chartV
    have h1 : T.fromX x = pushout.inr (E.Wι T.j) T.toSpec
        (Spec.map T.φ (E.V.toSpecΓ (⟨x, hx⟩ : E.V.toScheme))) :=
      calc T.fromX x = (E.V.ι ≫ T.fromX) (⟨x, hx⟩ : E.V.toScheme) := rfl
        _ = T.fromV (⟨x, hx⟩ : E.V.toScheme) := by rw [Stage.Vι_fromX]
        _ = _ := rfl
    rw [h1]
    exact ⟨_, rfl⟩

lemma Stage.fromX_preimage_chartU_inf_chartV (T : E.Stage) :
    T.fromX ⁻¹ᵁ (T.chartU ⊓ T.chartV) = E.U ⊓ E.V := by
  rw [Scheme.Hom.preimage_inf, T.fromX_preimage_chartU, T.fromX_preimage_chartV]


/-! ### The limit property, chart by chart -/

/-- (Implementation) The system of Noetherian stages `Dⱼ`, indexed by the stages below a
fixed stage. -/
noncomputable abbrev baseDiagram (E : ExtensionData.{u}) (T₀ : E.Stage) :
    Over T₀ ⥤ Scheme.{u} :=
  Over.forget T₀ ⋙ E.stageIndex ⋙ Over.forget E.i₀ ⋙ E.N.D

/-- (Implementation) `U` is the limit of the Noetherian stages `Dⱼ` indexed by the stages
below a fixed stage: the index functor is initial. -/
noncomputable def isLimitBaseCone (E : ExtensionData.{u}) (T₀ : E.Stage) :
    IsLimit (E.cone.whisker (Over.forget T₀ ⋙ E.stageIndex ⋙ Over.forget E.i₀)) :=
  (Functor.Initial.isLimitWhiskerEquiv _ E.cone).symm E.N.isLimit

set_option maxHeartbeats 1600000 in
-- Naturality of the chart isomorphism unfolds the pushout of every stage below `T₀`.
/-- (Implementation) The `U`-chart of a stage scheme is `Dⱼ`, compatibly with the
transition morphisms. -/
noncomputable def chartUIso (E : ExtensionData.{u}) (T₀ : E.Stage) :
    E.baseDiagram T₀ ≅ opensDiagram E.stageDiagram T₀ T₀.chartU :=
  NatIso.ofComponents
    (fun S ↦ IsOpenImmersion.isoOfRangeEq (pushout.inl (E.Wι S.left.j) S.left.toSpec)
      (Scheme.Opens.ι (E.stageDiagram.map S.hom ⁻¹ᵁ T₀.chartU))
      (by rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange,
        Scheme.Opens.opensRange_ι, Stage.preimage_chartU S.hom]))
    (fun {S S'} k ↦ by
      rw [← cancel_mono (Scheme.Opens.ι (E.stageDiagram.map S'.hom ⁻¹ᵁ T₀.chartU))]
      simp only [Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac,
        opensDiagram_map_ι, IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, inl_stageDiagram_map]
      rfl)

set_option maxHeartbeats 1600000 in
-- Transporting the limit along the chart isomorphism compares two cones on the
-- opens diagram of the pushout.
/-- (Implementation) The restriction of the stage cone to the `U`-chart is a limit cone. -/
noncomputable def isLimitOpensConeChartU (E : ExtensionData.{u}) (T₀ : E.Stage) :
    IsLimit (opensCone E.stageDiagram E.stageCone T₀ T₀.chartU) :=
  IsLimit.equivOfNatIsoOfIso (E.chartUIso T₀)
    (E.cone.whisker (Over.forget T₀ ⋙ E.stageIndex ⋙ Over.forget E.i₀))
    (opensCone E.stageDiagram E.stageCone T₀ T₀.chartU)
    (Cone.ext (E.X.isoOfEq T₀.fromX_preimage_chartU.symm) (fun S ↦ by
      rw [← cancel_mono (Scheme.Opens.ι (E.stageDiagram.map S.hom ⁻¹ᵁ T₀.chartU))]
      simp only [Cone.postcompose_obj_π, NatTrans.comp_app, Cone.whisker_π,
        Category.assoc, chartUIso, NatIso.ofComponents_hom_app,
        IsOpenImmersion.isoOfRangeEq_hom_fac, opensCone_π_ι, Scheme.isoOfEq_hom_ι_assoc]
      exact (Stage.Uι_fromX S.left).symm))
    (E.isLimitBaseCone T₀)


/-- (Implementation) The system of intersections `Wⱼ`, indexed by the stages below a fixed
stage. -/
noncomputable abbrev interDiagram (E : ExtensionData.{u}) (T₀ : E.Stage) :
    Over T₀ ⥤ Scheme.{u} :=
  Over.forget T₀ ⋙ E.stageIndex ⋙ E.WD

/-- (Implementation) `W = U ⊓ V` is the limit of the `Wⱼ` indexed by the stages below a
fixed stage. -/
noncomputable def isLimitInterCone (E : ExtensionData.{u}) (T₀ : E.Stage) :
    IsLimit (E.Wc.whisker (Over.forget T₀ ⋙ E.stageIndex)) :=
  (Functor.Initial.isLimitWhiskerEquiv _ E.Wc).symm E.isLimitWc

set_option maxHeartbeats 1600000 in
-- Naturality of the overlap isomorphism unfolds the pushout of every stage below `T₀`.
/-- (Implementation) The overlap of the two charts of a stage scheme is `Wⱼ`, compatibly
with the transition morphisms. -/
noncomputable def interIso (E : ExtensionData.{u}) (T₀ : E.Stage) :
    E.interDiagram T₀ ≅ opensDiagram E.stageDiagram T₀ (T₀.chartU ⊓ T₀.chartV) :=
  NatIso.ofComponents
    (fun S ↦ IsOpenImmersion.isoOfRangeEq
      (E.Wι S.left.j ≫ pushout.inl (E.Wι S.left.j) S.left.toSpec)
      (Scheme.Opens.ι (E.stageDiagram.map S.hom ⁻¹ᵁ (T₀.chartU ⊓ T₀.chartV)))
      (by rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange,
        Scheme.Opens.opensRange_ι, Scheme.Hom.preimage_inf, Stage.preimage_chartU S.hom,
        Stage.preimage_chartV S.hom, Stage.chartU_inf_chartV]))
    (fun {S S'} k ↦ by
      rw [← cancel_mono (Scheme.Opens.ι (E.stageDiagram.map S'.hom ⁻¹ᵁ
        (T₀.chartU ⊓ T₀.chartV)))]
      have h : (E.interDiagram T₀).map k = E.WD.map k.left.base := rfl
      simp only [h, Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac,
        opensDiagram_map_ι, IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, inl_stageDiagram_map,
        WD_map_Wι_assoc])

set_option maxHeartbeats 1600000 in
-- Transporting the limit along the overlap isomorphism compares two cones on the
-- opens diagram of the pushout.
/-- (Implementation) The restriction of the stage cone to the overlap of the two charts is a
limit cone. -/
noncomputable def isLimitOpensConeInter (E : ExtensionData.{u}) (T₀ : E.Stage) :
    IsLimit (opensCone E.stageDiagram E.stageCone T₀ (T₀.chartU ⊓ T₀.chartV)) :=
  IsLimit.equivOfNatIsoOfIso (E.interIso T₀)
    (E.Wc.whisker (Over.forget T₀ ⋙ E.stageIndex))
    (opensCone E.stageDiagram E.stageCone T₀ (T₀.chartU ⊓ T₀.chartV))
    (Cone.ext (E.θ.symm ≪≫ E.X.isoOfEq T₀.fromX_preimage_chartU_inf_chartV.symm) (fun S ↦ by
      rw [← cancel_mono (Scheme.Opens.ι (E.stageDiagram.map S.hom ⁻¹ᵁ
        (T₀.chartU ⊓ T₀.chartV)))]
      simp only [Cone.postcompose_obj_π, NatTrans.comp_app, Cone.whisker_π,
        Functor.whiskerLeft_app, Category.assoc, interIso, NatIso.ofComponents_hom_app,
        IsOpenImmersion.isoOfRangeEq_hom_fac, opensCone_π_ι, Iso.trans_hom,
        Scheme.isoOfEq_hom_ι_assoc, Iso.symm_hom, θ_inv_infι_assoc, stageCone_π_app]
      exact (E.Wc_π_Wι_assoc S.left.j _).trans (by rw [Stage.Uι_fromX, Stage.fromU])))
    (E.isLimitInterCone T₀)
/-! ### The `Spec A`-chart: the sections of `V` are the colimit of the coefficient algebras -/

/-- (Implementation) Every section of `V` occurs in the coefficient algebra of some stage. -/
lemma exists_stage_mem_A (E : ExtensionData.{u}) (β : Γ(E.X, E.V)) :
    ∃ (T : E.Stage) (a : ↥T.A), (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).1 = β := by
  obtain ⟨T₁⟩ := (inferInstance : Nonempty E.Stage)
  obtain ⟨j₁, x₁, hx₁⟩ := exists_appTop_π_eq_of_isLimit E.WD E.Wc E.isLimitWc (E.sV β)
  obtain ⟨j₂, k₁, k₂, -⟩ := IsCofilteredOrEmpty.cone_objs T₁.j j₁
  have hxt : E.t j₂ (E.res k₂ x₁) = E.sV β := by rw [E.t_res]; exact hx₁.symm
  have hle : Algebra.adjoin ℤ {(β, E.res k₂ x₁)} ≤ E.fiberProduct j₂ :=
    Algebra.adjoin_le (by rintro p rfl; exact (E.mem_fiberProduct_iff _).mpr hxt.symm)
  have hfg : (Algebra.adjoin ℤ {(β, E.res k₂ x₁)}).FG :=
    Subalgebra.fg_def.mpr ⟨_, Set.finite_singleton _, rfl⟩
  exact ⟨T₁.restrict k₁ _ hle hfg,
    ⟨(β, E.res k₂ x₁), T₁.le_restrict_A k₁ _ hle hfg (Algebra.subset_adjoin rfl)⟩, rfl⟩

/-- (Implementation) Two elements of a coefficient algebra whose components agree are
equal. -/
lemma Stage.Hom.algHom_eq_of {T T' : E.Stage} (f : T' ⟶ T) (a b : ↥T.A)
    (h1 : (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).1 =
      (b : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).1)
    (h2 : E.res f.base (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).2 =
      E.res f.base (b : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).2) :
    f.algHom a = f.algHom b :=
  Subtype.ext (by rw [Stage.Hom.algHom_coe, Stage.Hom.algHom_coe, h1, h2])

/-- (Implementation) Two elements of a coefficient algebra with the same `V`-component become
equal at a later stage: their `Wⱼ`-components agree on the intersection `W`, hence already at
a finite stage. -/
lemma exists_hom_algHom_eq (E : ExtensionData.{u}) (T : E.Stage) (a b : ↥T.A)
    (h : (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).1 =
      (b : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).1) :
    ∃ (T' : E.Stage) (f : T' ⟶ T), f.algHom a = f.algHom b := by
  have ht : E.t T.j (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).2 =
      E.t T.j (b : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).2 := by
    rw [← T.hA _ a.2, ← T.hA _ b.2, h]
  have hcpt : IsCompact ((⊤ : (E.WD.obj T.j).Opens) : Set (E.WD.obj T.j)) := isCompact_univ
  obtain ⟨j', k, hk⟩ := exists_app_map_eq_map_of_isLimit E.WD E.Wc E.isLimitWc hcpt _ _ ht
  exact ⟨T.restrict k ⊥ bot_le Subalgebra.fg_bot,
    T.restrictHom k ⊥ bot_le Subalgebra.fg_bot, Stage.Hom.algHom_eq_of _ a b h hk⟩

/-- (Implementation) The system of coefficient algebras of the stages, as a diagram in the
opposite category of commutative rings. -/
noncomputable def algOp (E : ExtensionData.{u}) : E.Stage ⥤ CommRingCatᵒᵖ where
  obj T := Opposite.op (CommRingCat.of ↥T.A)
  map f := (f.algHom).op
  map_id T := Quiver.Hom.unop_inj (Stage.Hom.algHom_id T)
  map_comp f g := Quiver.Hom.unop_inj (Stage.Hom.algHom_comp f g)

/-- (Implementation) `Γ(X, V)` as a cocone on the system of coefficient algebras. -/
noncomputable def algCocone (E : ExtensionData.{u}) : Cocone E.algOp.leftOp where
  pt := Γ(E.X, E.V)
  ι :=
    { app := fun T ↦ T.unop.φ
      naturality := fun _ _ f ↦
        (Stage.Hom.algHom_φ f.unop).trans (Category.comp_id _).symm }

set_option maxHeartbeats 1600000 in
-- Reflecting the colimit through the forgetful functor unfolds the subalgebra
-- coercions of every stage.
/-- (Implementation) `Γ(X, V)` is the filtered colimit of the coefficient algebras of the
stages: every section of `V` occurs at some stage, and two elements with the same
`V`-component become equal at a later stage. -/
noncomputable def isColimitAlgCocone (E : ExtensionData.{u}) : IsColimit E.algCocone := by
  have : ReflectsColimit E.algOp.leftOp (CategoryTheory.forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (CategoryTheory.forget CommRingCat.{u}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ (fun β ↦ ?_) (fun T a b hab ↦ ?_)
  · obtain ⟨T, a, ha⟩ := E.exists_stage_mem_A β
    exact ⟨Opposite.op T, a, ha.symm⟩
  · obtain ⟨T', f, hf⟩ := E.exists_hom_algHom_eq T.unop a b hab
    exact ⟨Opposite.op T', f.op, hf⟩

/-- (Implementation) The system of the spectra of the coefficient algebras. -/
noncomputable abbrev specDiagram (E : ExtensionData.{u}) : E.Stage ⥤ Scheme.{u} :=
  E.algOp ⋙ Scheme.Spec

/-- (Implementation) `V ≅ Spec Γ(X, V)` as a cone on the spectra of the coefficient
algebras. -/
noncomputable def specCone (E : ExtensionData.{u}) : Cone E.specDiagram :=
  Scheme.Spec.mapCone (Limits.coneOfCoconeLeftOp E.algCocone)

lemma specCone_pt (E : ExtensionData.{u}) : E.specCone.pt = Spec Γ(E.X, E.V) := rfl

lemma specCone_π_app (E : ExtensionData.{u}) (T : E.Stage) :
    E.specCone.π.app T = Spec.map T.φ := rfl

/-- (Implementation) `Spec Γ(X, V)` is the limit of the spectra of the coefficient
algebras. -/
noncomputable def isLimitSpecCone (E : ExtensionData.{u}) : IsLimit E.specCone :=
  isLimitOfPreserves Scheme.Spec
    (Limits.isLimitConeOfCoconeLeftOp E.algOp E.isColimitAlgCocone)

@[reassoc (attr := simp)]
lemma isoSpec_inv_toSpecΓ (E : ExtensionData.{u}) :
    E.hV.isoSpec.inv ≫ E.V.toSpecΓ = 𝟙 _ := by
  rw [← IsAffineOpen.isoSpec_hom E.hV, Iso.inv_hom_id]

set_option maxHeartbeats 1600000 in
-- Naturality of the chart isomorphism unfolds the pushout of every stage below `T₀`.
/-- (Implementation) The `Spec A`-chart of a stage scheme is `Spec A`, compatibly with the
transition morphisms. -/
noncomputable def chartVIso (E : ExtensionData.{u}) (T₀ : E.Stage) :
    Over.forget T₀ ⋙ E.specDiagram ≅ opensDiagram E.stageDiagram T₀ T₀.chartV :=
  NatIso.ofComponents
    (fun S ↦ IsOpenImmersion.isoOfRangeEq (pushout.inr (E.Wι S.left.j) S.left.toSpec)
      (Scheme.Opens.ι (E.stageDiagram.map S.hom ⁻¹ᵁ T₀.chartV))
      (by rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange,
        Scheme.Opens.opensRange_ι, Stage.preimage_chartV S.hom]))
    (fun {S S'} k ↦ by
      rw [← cancel_mono (Scheme.Opens.ι (E.stageDiagram.map S'.hom ⁻¹ᵁ T₀.chartV))]
      simp only [Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac,
        opensDiagram_map_ι, IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, inr_stageDiagram_map]
      rfl)

set_option maxHeartbeats 1600000 in
-- Transporting the limit along the chart isomorphism compares two cones on the
-- opens diagram of the pushout.
/-- (Implementation) The restriction of the stage cone to the `Spec A`-chart is a limit
cone. -/
noncomputable def isLimitOpensConeChartV (E : ExtensionData.{u}) (T₀ : E.Stage) :
    IsLimit (opensCone E.stageDiagram E.stageCone T₀ T₀.chartV) :=
  IsLimit.equivOfNatIsoOfIso (E.chartVIso T₀)
    (E.specCone.whisker (Over.forget T₀))
    (opensCone E.stageDiagram E.stageCone T₀ T₀.chartV)
    (Cone.ext (E.hV.isoSpec.symm ≪≫ E.X.isoOfEq T₀.fromX_preimage_chartV.symm) (fun S ↦ by
      rw [← cancel_mono (Scheme.Opens.ι (E.stageDiagram.map S.hom ⁻¹ᵁ T₀.chartV))]
      simp only [Cone.postcompose_obj_π, NatTrans.comp_app, Cone.whisker_π,
        Functor.whiskerLeft_app, Category.assoc, chartVIso, NatIso.ofComponents_hom_app,
        IsOpenImmersion.isoOfRangeEq_hom_fac, opensCone_π_ι, Iso.trans_hom,
        Scheme.isoOfEq_hom_ι_assoc, Iso.symm_hom, stageCone_π_app]
      rw [Stage.Vι_fromX, Stage.fromV, isoSpec_inv_toSpecΓ_assoc]
      exact congrArg (fun g ↦ g ≫ pushout.inr (E.Wι S.left.j) S.left.toSpec)
        (specCone_π_app E S.left)))
    ((Functor.Initial.isLimitWhiskerEquiv _ E.specCone).symm E.isLimitSpecCone)

/-- (Implementation) The two charts of a stage scheme, as a family indexed by `Bool`. -/
noncomputable def charts (E : ExtensionData.{u}) (T₀ : E.Stage) (b : Bool) :
    (E.stageDiagram.obj T₀).Opens :=
  bif b then T₀.chartU else T₀.chartV

set_option maxHeartbeats 1600000 in
-- Each of the four cases unfolds the pushout defining the stage scheme.
/-- (Implementation) The stage cone is a limit cone: its restrictions to the two charts of a
stage scheme and to their overlap are limit cones. -/
noncomputable def isLimitStageConeOfStage (E : ExtensionData.{u}) (T₀ : E.Stage) :
    IsLimit E.stageCone := by
  refine isLimitOfIsLimitOpensCone E.stageDiagram E.stageCone T₀ (E.charts T₀) ?_
    (fun b ↦ ?_) (fun b b' ↦ ?_)
  · rw [iSup_bool_eq]
    exact T₀.chartU_sup_chartV
  · cases b
    exacts [E.isLimitOpensConeChartV T₀, E.isLimitOpensConeChartU T₀]
  · cases b <;> cases b'
    · change IsLimit (opensCone E.stageDiagram E.stageCone T₀ (T₀.chartV ⊓ T₀.chartV))
      rw [inf_idem]
      exact E.isLimitOpensConeChartV T₀
    · change IsLimit (opensCone E.stageDiagram E.stageCone T₀ (T₀.chartV ⊓ T₀.chartU))
      rw [inf_comm]
      exact E.isLimitOpensConeInter T₀
    · exact E.isLimitOpensConeInter T₀
    · change IsLimit (opensCone E.stageDiagram E.stageCone T₀ (T₀.chartU ⊓ T₀.chartU))
      rw [inf_idem]
      exact E.isLimitOpensConeChartU T₀

/-- (Implementation) The stage cone is a limit cone. -/
noncomputable def isLimitStageCone (E : ExtensionData.{u}) : IsLimit E.stageCone :=
  E.isLimitStageConeOfStage (Classical.arbitrary E.Stage)

/-- (Implementation) The Noetherian approximation of `X = U ∪ V` extending a given
approximation of `U` across the affine open `V`. This is the induction step of
Stacks Project Tag 07RN. -/
noncomputable def approximation (E : ExtensionData.{u}) : E.X.NoetherianApproximation where
  I := E.Stage
  D := E.stageDiagram
  locallyOfFiniteType_obj _ := inferInstance
  compactSpace_obj _ := inferInstance
  isAffineHom_map _ := inferInstance
  π := E.stageCone.π
  isLimit := E.isLimitStageCone

end ExtensionData

end Scheme.NoetherianApproximation

/-- (Implementation) A finite supremum of quasi-compact opens is quasi-compact. -/
private lemma isCompact_finset_sup {X : Scheme.{u}} (s : Finset X.Opens)
    (hs : ∀ V ∈ s, IsCompact (V : Set X)) : IsCompact ((s.sup id : X.Opens) : Set X) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sup_insert]
      refine IsCompact.union (hs a (Finset.mem_insert_self a s)) ?_
      exact ih fun V hV ↦ hs V (Finset.mem_insert_of_mem hV)

open Scheme.NoetherianApproximation in
/-- (Implementation) **Absolute Noetherian approximation** for a finite union of affine
opens of a quasi-separated scheme, by induction on the number of members of the union
(Stacks Project Tag 07RN). -/
private lemma nonempty_noetherianApproximation_finsetSup {X : Scheme.{u}}
    [QuasiSeparatedSpace X] (s : Finset X.Opens) (hs : ∀ V ∈ s, IsAffineOpen V) :
    Nonempty ((s.sup id : X.Opens).toScheme.NoetherianApproximation) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sup_empty]
      have h : IsAffine ((⊥ : X.Opens).toScheme) := isAffineOpen_bot X
      exact ⟨Scheme.NoetherianApproximation.ofIsAffine _⟩
  | insert a s ha ih =>
      obtain ⟨N₀⟩ := ih fun V hV ↦ hs V (Finset.mem_insert_of_mem hV)
      have haff : IsAffineOpen a := hs a (Finset.mem_insert_self a s)
      have hsaff : ∀ V ∈ s, IsAffineOpen V := fun V hV ↦ hs V (Finset.mem_insert_of_mem hV)
      rw [Finset.sup_insert, id]
      set Y : X.Opens := a ⊔ s.sup id with hYdef
      haveI : QuasiSeparatedSpace Y.toScheme :=
        (isQuasiSeparated_iff_quasiSeparatedSpace _ Y.2).mp (.of_quasiSeparatedSpace _)
      set U : Y.toScheme.Opens := Y.ι ⁻¹ᵁ (s.sup id) with hUdef
      set V : Y.toScheme.Opens := Y.ι ⁻¹ᵁ a with hVdef
      have hUV : U ⊔ V = ⊤ := by
        rw [hUdef, hVdef, ← Scheme.Hom.preimage_sup, sup_comm, ← hYdef,
          Scheme.Opens.ι_preimage_self]
      have hVaff : IsAffineOpen V := by
        refine haff.preimage_of_isOpenImmersion Y.ι ?_
        rw [Scheme.Opens.opensRange_ι]
        exact le_sup_left
      -- the approximation of `U`, transported from the induction hypothesis
      have hrange : Set.range (X.homOfLE (le_sup_right : s.sup id ≤ Y)) =
          Set.range (Scheme.Opens.ι U) := by
        rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange,
          Scheme.opensRange_homOfLE, Scheme.Opens.opensRange_ι]
      have N : U.toScheme.NoetherianApproximation :=
        N₀.ofIso (IsOpenImmersion.isoOfRangeEq _ _ hrange)
      -- the intersection `U ⊓ V` is quasi-compact
      have hsc : IsCompact ((s.sup id : X.Opens) : Set X) :=
        isCompact_finset_sup s fun V hV ↦ (hsaff V hV).isCompact
      have hinfc : IsCompact (((s.sup id ⊓ a : X.Opens)) : Set X) := by
        rw [TopologicalSpace.Opens.coe_inf]
        exact QuasiSeparatedSpace.inter_isCompact _ _ (s.sup id).2 hsc a.2 haff.isCompact
      have hUVc : IsCompact ((U ⊓ V : Y.toScheme.Opens) : Set Y.toScheme) := by
        have he : (U ⊓ V : Y.toScheme.Opens) = Y.ι ⁻¹ᵁ (s.sup id ⊓ a) := by
          rw [hUdef, hVdef, Scheme.Hom.preimage_inf]
        rw [he]
        refine Y.ι.isOpenEmbedding.isInducing.isCompact_preimage' hinfc ?_
        rw [Scheme.Opens.range_ι]
        exact le_trans inf_le_left le_sup_right
      have hUVc' : IsCompact ((U.ι ⁻¹ᵁ V : U.toScheme.Opens) : Set U.toScheme) := by
        have he : (U.ι ⁻¹ᵁ V : U.toScheme.Opens) = U.ι ⁻¹ᵁ (U ⊓ V) := by
          rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq]
        rw [he]
        refine U.ι.isOpenEmbedding.isInducing.isCompact_preimage' hUVc ?_
        rw [Scheme.Opens.range_ι]
        exact inf_le_left
      obtain ⟨i₀, W₀, hW₀c, hW₀⟩ :=
        exists_preimage_eq N.D (Cone.mk _ N.π) N.isLimit _ hUVc'
      -- the generators of the intersection
      obtain ⟨t, ht⟩ := hVaff.exists_finset_basicOpen_eq hUVc inf_le_right
      obtain ⟨m, eq⟩ : ∃ m, Nonempty ({x // x ∈ t} ≃ Fin m) := ⟨t.card, ⟨t.equivFin⟩⟩
      obtain ⟨eq⟩ := eq
      have hcov : (U ⊓ V : Y.toScheme.Opens) =
          ⨆ l : Fin m, Y.toScheme.basicOpen ((eq.symm l : {x // x ∈ t}) :
            Γ(Y.toScheme, V)) := by
        have h1 : (⨆ f ∈ t, Y.toScheme.basicOpen f) =
            ⨆ x : {x // x ∈ t}, Y.toScheme.basicOpen (x : Γ(Y.toScheme, V)) :=
          iSup_subtype' (p := fun x : Γ(Y.toScheme, V) ↦ x ∈ t)
            (f := fun x _ ↦ Y.toScheme.basicOpen x)
        rw [ht, h1, ← Equiv.iSup_comp (g := fun x : {x // x ∈ t} ↦
          Y.toScheme.basicOpen (x : Γ(Y.toScheme, V))) eq.symm]
      exact ⟨Scheme.NoetherianApproximation.ExtensionData.approximation
        { X := Y.toScheme, U := U, V := V, hUV := hUV, hV := hVaff, N := N, i₀ := i₀,
          W₀ := W₀, hW₀c := hW₀c, hW₀ := hW₀, n := m,
          b := fun l ↦ ((eq.symm l : {x // x ∈ t}) : Γ(Y.toScheme, V)),
          hb := fun l ↦ hcov ▸ le_iSup (fun l : Fin m ↦ Y.toScheme.basicOpen
            ((eq.symm l : {x // x ∈ t}) : Γ(Y.toScheme, V))) l,
          hb' := hcov }⟩

/-- **Absolute Noetherian approximation** (Stacks Project Tag 01ZA): every quasi-compact
quasi-separated scheme is the limit of a cofiltered system of schemes of finite type over
`ℤ` with affine transition morphisms.

The affine case is `AlgebraicGeometry.Scheme.NoetherianApproximation.ofIsAffine`. The
general case follows by induction over a finite affine cover: each step extends an
approximation of a quasi-compact open across one more affine open, see
`AlgebraicGeometry.Scheme.NoetherianApproximation.ExtensionData.approximation`.
(Blueprint: `prop:nagata-noetherian-inverse-system`.) -/
@[stacks 01ZA]
theorem Scheme.nonempty_noetherianApproximation (S : Scheme.{u})
    [CompactSpace S] [QuasiSeparatedSpace S] :
    Nonempty S.NoetherianApproximation := by
  classical
  obtain ⟨Us, hUsB, hUsfin, hUs⟩ :=
    S.isBasis_affineOpens.exists_finite_of_isCompact (U := ⊤) (by simpa using isCompact_univ)
  obtain ⟨N⟩ := nonempty_noetherianApproximation_finsetSup hUsfin.toFinset
    (fun V hV ↦ hUsB (hUsfin.mem_toFinset.mp hV))
  rw [Finset.sup_id_eq_sSup, hUsfin.coe_toFinset, ← hUs] at N
  exact ⟨N.ofIso S.topIso⟩

section BaseChangeLimit

/-!
### Base change of a cofiltered limit

A cofiltered limit `lim Dⱼ` of schemes stays a limit after base change along a morphism
`p : Y ⟶ Dᵢ` to one of the stages: `Y ×_{Dᵢ} lim Dⱼ` is the limit of the system
`{ Y ×_{Dᵢ} Dⱼ }_{j ≤ i}`. This is `AlgebraicGeometry.isLimitBaseChangeCone`; it is what
makes the results on cofiltered limits of schemes available for the descent of a scheme
over `lim Dⱼ` to a finite stage.
-/

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
variable {i : I} {Y : Scheme.{u}} (p : Y ⟶ D.obj i)

set_option backward.defeqAttrib.useBackward true in
/-- (Implementation) The base change `{ Y ×_{Dᵢ} Dⱼ }_{j ≤ i}` of the diagram `{ Dⱼ }` along a
morphism `p : Y ⟶ Dᵢ`. -/
@[simps] noncomputable def baseChangeDiagram : Over i ⥤ Scheme.{u} where
  obj j := pullback p (D.map j.hom)
  map {j k} f := pullback.map _ _ _ _ (𝟙 Y) (D.map f.left) (𝟙 _)
    (by simp) (by simp [← D.map_comp, Over.w f])
  map_id j := by apply pullback.hom_ext <;> simp
  map_comp f g := by apply pullback.hom_ext <;> simp

set_option backward.defeqAttrib.useBackward true in
/-- (Implementation) The projection from the base changed diagram to the original diagram. -/
@[simps] noncomputable def baseChangeDiagramπ :
    baseChangeDiagram D p ⟶ Over.forget i ⋙ D where
  app j := pullback.snd _ _

set_option backward.defeqAttrib.useBackward true in
/-- (Implementation) The cone with point `Y ×_{Dᵢ} lim Dⱼ` over the base changed diagram. -/
@[simps] noncomputable def baseChangeCone : Cone (baseChangeDiagram D p) where
  pt := pullback p (c.π.app i)
  π.app j := pullback.map _ _ _ _ (𝟙 Y) (c.π.app j.left) (𝟙 _) (by simp) (by simp)
  π.naturality {j k} f := by apply pullback.hom_ext <;> simp

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma baseChangeDiagram_map_fst {j k : Over i} (f : j ⟶ k) :
    (baseChangeDiagram D p).map f ≫ pullback.fst p (D.map k.hom) =
      pullback.fst p (D.map j.hom) := by
  simp [baseChangeDiagram]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma baseChangeDiagram_map_snd {j k : Over i} (f : j ⟶ k) :
    (baseChangeDiagram D p).map f ≫ pullback.snd p (D.map k.hom) =
      pullback.snd p (D.map j.hom) ≫ D.map f.left := by
  simp [baseChangeDiagram]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma baseChangeCone_π_app_fst (j : Over i) :
    (baseChangeCone D c p).π.app j ≫ pullback.fst p (D.map j.hom) =
      pullback.fst p (c.π.app i) := by
  simp [baseChangeCone]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma baseChangeCone_π_app_snd (j : Over i) :
    (baseChangeCone D c p).π.app j ≫ pullback.snd p (D.map j.hom) =
      pullback.snd p (c.π.app i) ≫ c.π.app j.left := by
  simp [baseChangeCone]

set_option backward.defeqAttrib.useBackward true in
lemma isPullback_baseChangeDiagram_map {j k : Over i} (f : j ⟶ k) :
    IsPullback ((baseChangeDiagram D p).map f) (pullback.snd p (D.map j.hom))
      (pullback.snd p (D.map k.hom)) (D.map f.left) :=
  isPullback_pullback_map _ _ _ _ (by rw [← D.map_comp, Over.w f])

set_option backward.defeqAttrib.useBackward true in
lemma isPullback_baseChangeCone_π (j : Over i) :
    IsPullback ((baseChangeCone D c p).π.app j) (pullback.snd p (c.π.app i))
      ((baseChangeDiagramπ D p).app j) (c.π.app j.left) :=
  isPullback_pullback_map _ _ _ _ (c.w j.hom)

attribute [local instance] CategoryTheory.isConnected_of_hasTerminal

include c in
/-- **Base change of a cofiltered limit of schemes.** If `lim Dⱼ` is a cofiltered limit and
`p : Y ⟶ Dᵢ`, then `Y ×_{Dᵢ} lim Dⱼ` is the limit of the system `{ Y ×_{Dᵢ} Dⱼ }_{j ≤ i}`. -/
noncomputable def isLimitBaseChangeCone [IsCofiltered I] (hc : IsLimit c) :
    IsLimit (baseChangeCone D c p) :=
  isLimitOfIsPullbackOfIsConnected (baseChangeDiagramπ D p) _ (c.whisker (Over.forget i))
    { hom := pullback.snd p (c.π.app i)
      w := fun j ↦ by simp }
    (isPullback_baseChangeCone_π D c p)
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc)

instance [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] {j k : Over i} (f : j ⟶ k) :
    IsAffineHom ((baseChangeDiagram D p).map f) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_baseChangeDiagram_map D p f).flip
    inferInstance

end BaseChangeLimit

section FinitePresentation

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)

include hc in
/-- **Objects of finite presentation descend to a finite stage, affine case.**

Let `{Dᵢ}` be a cofiltered inverse system of affine schemes with affine transition maps and
let `X` be an affine scheme that is locally of finite presentation over `lim Dᵢ`. Then `X` is
the base change of an affine scheme `Y` that is locally of finite presentation over some
`Dᵢ`. -/
@[stacks 01ZM]
lemma Scheme.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, IsAffine (D.obj i)]
    {X : Scheme.{u}} [IsAffine X] (g : X ⟶ c.pt) [LocallyOfFinitePresentation g] :
    ∃ (i : I) (Y : Scheme.{u}) (_ : IsAffine Y) (p : Y ⟶ D.obj i)
      (_ : LocallyOfFinitePresentation p) (h : X ⟶ Y), IsPullback h g p (c.π.app i) := by
  have hcpt : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  -- Reduce to the case where `X` is the spectrum of a ring.
  wlog hX : ∃ A, X = Spec A generalizing X
  · obtain ⟨i, Y, hYaff, p, hp, h, hsq⟩ := this (X := Spec Γ(X, ⊤)) (X.isoSpec.inv ≫ g) ⟨_, rfl⟩
    refine ⟨i, Y, hYaff, p, hp, X.isoSpec.hom ≫ h, ?_⟩
    simpa using (IsPullback.of_horiz_isIso (fst := X.isoSpec.hom) (snd := g)
      (f := X.isoSpec.inv ≫ g) (g := 𝟙 c.pt) ⟨by simp⟩).paste_horiz hsq
  obtain ⟨A, rfl⟩ := hX
  -- Reduce to the case where the diagram is the spectrum of a diagram of rings.
  wlog hD : ∃ D' : I ⥤ CommRingCatᵒᵖ, D = D' ⋙ Scheme.Spec generalizing D
  · let e : D ⟶ D ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec := D.whiskerLeft ΓSpec.adjunction.unit
    have inst (i) : IsIso (e.app i) := IsAffine.affine
    have inst : IsIso e := NatIso.isIso_of_isIso_app e
    have inst (i) : IsAffine ((D ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec).obj i) :=
      inferInstanceAs (IsAffine (Spec _))
    have inst : ∀ {i j : I} (f : i ⟶ j),
        IsAffineHom ((D ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec).map f) := fun f ↦ inferInstance
    haveI hg : @LocallyOfFinitePresentation (Spec A)
        ((Cone.postcompose (asIso e).hom).obj c).pt g := ‹_›
    obtain ⟨i, Y, hYaff, p, hp, h, hsq⟩ :=
      this _ _ ((IsLimit.postcomposeHomEquiv (asIso e) c).symm hc)
      hcpt g ⟨D ⋙ Scheme.Γ.rightOp, rfl⟩
    have : LocallyOfFinitePresentation (p ≫ inv (e.app i)) := by
      have := hp; infer_instance
    refine ⟨i, Y, hYaff, p ≫ inv (e.app i), this, h, ?_⟩
    refine hsq.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso (e.app i)).symm
      (by simp) (Category.comp_id g) (by simp) ?_
    change (c.π.app i ≫ e.app i) ≫ inv (e.app i) = 𝟙 _ ≫ c.π.app i
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    exact (Category.id_comp (c.π.app i)).symm
  obtain ⟨D, rfl⟩ := hD
  -- Reduce to the case where the limit cone is the spectrum of a colimit cocone of rings.
  wlog hc' : ∃ c' : Cocone D.leftOp, c = Scheme.Spec.mapCone (coneOfCoconeLeftOp c')
    generalizing c
  · let β : c.pt ≅ Spec Γ(c.pt, ⊤) := c.pt.isoSpec
    let φ : ∀ i : Iᵒᵖ, D.leftOp.obj i ⟶ Γ(c.pt, ⊤) :=
      fun i ↦ (Scheme.Spec.preimage (β.inv ≫ c.π.app i.unop)).unop
    have hφ : ∀ i : Iᵒᵖ, Spec.map (φ i) = β.inv ≫ c.π.app i.unop :=
      fun i ↦ Scheme.Spec.map_preimage _
    let c' : Cocone D.leftOp :=
      { pt := Γ(c.pt, ⊤)
        ι :=
        { app := φ
          naturality i j f := by
            apply Quiver.Hom.op_inj
            apply Scheme.Spec.map_injective
            change Spec.map (D.leftOp.map f ≫ φ j) = Spec.map (φ i ≫ 𝟙 _)
            rw [Spec.map_comp, Spec.map_comp, hφ, hφ, Spec.map_id, Category.id_comp]
            exact (Category.assoc _ _ _).trans (congrArg (β.inv ≫ ·) (c.w f.unop)) } }
    have hcc : c ≅ Scheme.Spec.mapCone (coneOfCoconeLeftOp c') :=
      Cone.ext β fun i ↦ by
        change c.π.app i = β.hom ≫ Spec.map (φ (Opposite.op i))
        rw [hφ]
        exact (Iso.hom_inv_id_assoc β (c.π.app i)).symm
    obtain ⟨i, Y, hYaff, p, hp, h, hsq⟩ := this (Scheme.Spec.mapCone (coneOfCoconeLeftOp c'))
      (IsLimit.ofIsoLimit hc hcc) (inferInstanceAs (IsAffine (Spec Γ(c.pt, ⊤))))
      (g ≫ β.hom) ⟨c', rfl⟩
    refine ⟨i, Y, hYaff, p, hp, h, ?_⟩
    refine hsq.of_iso (Iso.refl _) (Iso.refl _) β.symm (Iso.refl _) (by simp) (by simp)
      (by simp) ?_
    change Spec.map (φ (Opposite.op i)) ≫ 𝟙 _ = β.inv ≫ c.π.app i
    rw [Category.comp_id]
    exact hφ (Opposite.op i)
  obtain ⟨c', rfl⟩ := hc'
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  replace hc := isColimitOfConeOfCoconeLeftOp _ (isLimitOfReflects Scheme.Spec hc)
  obtain ⟨i, T, γ, hγ, h, hpush⟩ := CommRingCat.exists_isPushout_of_finitePresentation
    D.leftOp c' hc ψ (HasRingHomProperty.Spec_iff.mp ‹LocallyOfFinitePresentation (Spec.map ψ)›)
  refine ⟨i.unop, Spec T, inferInstance, Spec.map γ, HasRingHomProperty.Spec_iff.mpr hγ,
    Spec.map h, ?_⟩
  exact (isPullback_SpecMap_of_isPushout _ _ _ _ hpush).flip

end FinitePresentation

section FinitePresentationDescent

/-!
### Descending a scheme of finite presentation to a finite stage

Let `{Dⱼ}` be a cofiltered inverse system of quasi-compact quasi-separated schemes with affine
transition maps and let `X` be of finite presentation over `lim Dⱼ`. Then `X` is the base change
of a scheme of finite presentation over one of the stages (Stacks Project Tag 01ZM,
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation`).

The affine case is
`AlgebraicGeometry.Scheme.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine`. It
covers an affine `X` lying over an affine open `V` of a stage, by base changing the whole system
to `V` (`AlgebraicGeometry.DescendsToStage.of_isAffine`). The general case is an induction over
a finite cover of `X` by such affine opens: at each step one has to glue two
finite-stage models along a descent of their intersection. The gluing data is produced by
`AlgebraicGeometry.exists_descendsAtWithOpen` (a quasi-compact open descends) and
`AlgebraicGeometry.exists_iso_of_isPullback` (two finite-stage models of the same scheme become
isomorphic at a later stage), the gluing itself is the pushout of two open immersions of
`AlgebraicGeometry.pushoutOpensDesc`, and that the glued morphism is again cartesian is
`AlgebraicGeometry.isPullback_of_opensRange_sup_eq_top`.
-/

section Descent

set_option backward.defeqAttrib.useBackward true

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
  [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]

instance baseChange_compactSpace {k k' : I} (f : k' ⟶ k) {Y : Scheme.{u}} (p : Y ⟶ D.obj k)
    [CompactSpace Y] : CompactSpace ↥(pullback p (D.map f)) :=
  have : IsAffineHom (pullback.fst p (D.map f)) := MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiCompact (pullback.fst p (D.map f)) := inferInstance
  QuasiCompact.compactSpace_of_compactSpace (pullback.fst p (D.map f))

instance baseChange_quasiSeparatedSpace {k k' : I} (f : k' ⟶ k) {Y : Scheme.{u}} (p : Y ⟶ D.obj k)
    [QuasiSeparatedSpace Y] : QuasiSeparatedSpace ↥(pullback p (D.map f)) :=
  have : IsAffineHom (pullback.fst p (D.map f)) := MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiSeparated (pullback.fst p (D.map f)) := inferInstance
  quasiSeparatedSpace_of_quasiSeparated (pullback.fst p (D.map f))

instance baseChangeDiagram_compactSpace {k : I} {Y : Scheme.{u}} (p : Y ⟶ D.obj k)
    [CompactSpace Y] (j : Over k) : CompactSpace ↥((baseChangeDiagram D p).obj j) :=
  inferInstanceAs (CompactSpace ↥(pullback p (D.map j.hom)))

instance baseChangeDiagram_quasiSeparatedSpace {k : I} {Y : Scheme.{u}} (p : Y ⟶ D.obj k)
    [QuasiSeparatedSpace Y] (j : Over k) : QuasiSeparatedSpace ↥((baseChangeDiagram D p).obj j) :=
  inferInstanceAs (QuasiSeparatedSpace ↥(pullback p (D.map j.hom)))

variable (D) in
/-- (Implementation) The structure morphism of the base changed diagram to the stage `i`. -/
@[simps] noncomputable def baseChangeDiagramStructure {i : I} {Y : Scheme.{u}} (p : Y ⟶ D.obj i) :
    baseChangeDiagram D p ⟶ (Functor.const (Over i)).obj (D.obj i) where
  app j := pullback.fst _ _ ≫ p

include hc in
/-- (Implementation) **Two finite-stage models of a scheme over the limit become isomorphic at
a later stage.** -/
lemma exists_iso_of_isPullback {X : Scheme.{u}} {g : X ⟶ c.pt} {k : I}
    {Y₁ Y₂ : Scheme.{u}} {p₁ : Y₁ ⟶ D.obj k} {p₂ : Y₂ ⟶ D.obj k} {h₁ : X ⟶ Y₁} {h₂ : X ⟶ Y₂}
    [LocallyOfFinitePresentation p₁] [LocallyOfFinitePresentation p₂]
    [CompactSpace Y₁] [QuasiSeparatedSpace Y₁] [CompactSpace Y₂] [QuasiSeparatedSpace Y₂]
    (H₁ : IsPullback h₁ g p₁ (c.π.app k)) (H₂ : IsPullback h₂ g p₂ (c.π.app k)) :
    ∃ (k' : I) (f : k' ⟶ k), ∀ {Y₁' Y₂' : Scheme.{u}} {p₁' : Y₁' ⟶ D.obj k'} {q₁ : Y₁' ⟶ Y₁}
      {p₂' : Y₂' ⟶ D.obj k'} {q₂ : Y₂' ⟶ Y₂} {h₁' : X ⟶ Y₁'} {h₂' : X ⟶ Y₂'},
      IsPullback q₁ p₁' p₁ (D.map f) → h₁' ≫ q₁ = h₁ → h₁' ≫ p₁' = g ≫ c.π.app k' →
      IsPullback q₂ p₂' p₂ (D.map f) → h₂' ≫ q₂ = h₂ → h₂' ≫ p₂' = g ≫ c.π.app k' →
      ∃ e : Y₁' ≅ Y₂', e.hom ≫ p₂' = p₁' ∧ h₁' ≫ e.hom = h₂' := by
  classical
  have hi₁fst : H₁.isoPullback.hom ≫ pullback.fst p₁ (c.π.app k) = h₁ :=
    IsPullback.isoPullback_hom_fst _
  have hi₁snd : H₁.isoPullback.hom ≫ pullback.snd p₁ (c.π.app k) = g :=
    IsPullback.isoPullback_hom_snd _
  have hi₂fst : H₂.isoPullback.hom ≫ pullback.fst p₂ (c.π.app k) = h₂ :=
    IsPullback.isoPullback_hom_fst _
  have hi₂snd : H₂.isoPullback.hom ≫ pullback.snd p₂ (c.π.app k) = g :=
    IsPullback.isoPullback_hom_snd _
  have hinvg₁ : H₁.isoPullback.inv ≫ g = pullback.snd p₁ (c.π.app k) := by
    rw [Iso.inv_comp_eq, hi₁snd]
  have hinvg₂ : H₂.isoPullback.inv ≫ g = pullback.snd p₂ (c.π.app k) := by
    rw [Iso.inv_comp_eq, hi₂snd]
  -- descend the two comparison morphisms
  obtain ⟨j₁, u₁, hu₁a, hu₁t⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (baseChangeDiagram D p₁) (baseChangeDiagramStructure D p₁) p₂ (baseChangeCone D c p₁)
      (isLimitBaseChangeCone D c p₁ hc) (H₁.isoPullback.inv ≫ h₂) (by
    ext j
    change ((baseChangeCone D c p₁).π.app j ≫ pullback.fst p₁ (D.map j.hom)) ≫ p₁ =
      (H₁.isoPullback.inv ≫ h₂) ≫ p₂
    rw [baseChangeCone_π_app_fst, Category.assoc, H₂.w, ← Category.assoc, hinvg₁]
    exact pullback.condition)
  obtain ⟨j₂, u₂, hu₂a, hu₂t⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (baseChangeDiagram D p₂) (baseChangeDiagramStructure D p₂) p₁ (baseChangeCone D c p₂)
      (isLimitBaseChangeCone D c p₂ hc) (H₂.isoPullback.inv ≫ h₁) (by
    ext j
    change ((baseChangeCone D c p₂).π.app j ≫ pullback.fst p₂ (D.map j.hom)) ≫ p₂ =
      (H₂.isoPullback.inv ≫ h₁) ≫ p₁
    rw [baseChangeCone_π_app_fst, Category.assoc, H₁.w, ← Category.assoc, hinvg₂]
    exact pullback.condition)
  -- move them to a common stage
  set j₃ := IsCofiltered.min j₁ j₂ with hj₃
  set m₁ : j₃ ⟶ j₁ := IsCofiltered.minToLeft j₁ j₂ with hm₁
  set m₂ : j₃ ⟶ j₂ := IsCofiltered.minToRight j₁ j₂ with hm₂
  have hu₁t' : u₁ ≫ p₂ = pullback.fst p₁ (D.map j₁.hom) ≫ p₁ := hu₁t
  have hu₂t' : u₂ ≫ p₁ = pullback.fst p₂ (D.map j₂.hom) ≫ p₂ := hu₂t
  set v₁ : (baseChangeDiagram D p₁).obj j₃ ⟶ (baseChangeDiagram D p₂).obj j₃ :=
    pullback.lift ((baseChangeDiagram D p₁).map m₁ ≫ u₁) (pullback.snd p₁ (D.map j₃.hom))
      (by rw [Category.assoc, hu₁t', baseChangeDiagram_map_fst_assoc]
          exact pullback.condition) with hv₁def
  set v₂ : (baseChangeDiagram D p₂).obj j₃ ⟶ (baseChangeDiagram D p₁).obj j₃ :=
    pullback.lift ((baseChangeDiagram D p₂).map m₂ ≫ u₂) (pullback.snd p₂ (D.map j₃.hom))
      (by rw [Category.assoc, hu₂t', baseChangeDiagram_map_fst_assoc]
          exact pullback.condition) with hv₂def
  have hv₁fst : v₁ ≫ pullback.fst p₂ (D.map j₃.hom) = (baseChangeDiagram D p₁).map m₁ ≫ u₁ :=
    pullback.lift_fst ..
  have hv₁snd : v₁ ≫ pullback.snd p₂ (D.map j₃.hom) = pullback.snd p₁ (D.map j₃.hom) :=
    pullback.lift_snd ..
  have hv₂fst : v₂ ≫ pullback.fst p₁ (D.map j₃.hom) = (baseChangeDiagram D p₂).map m₂ ≫ u₂ :=
    pullback.lift_fst ..
  have hv₂snd : v₂ ≫ pullback.snd p₁ (D.map j₃.hom) = pullback.snd p₂ (D.map j₃.hom) :=
    pullback.lift_snd ..
  -- after base change to the limit they are the identifications with `X`
  have key₁ : (baseChangeCone D c p₁).π.app j₃ ≫ v₁ =
      H₁.isoPullback.inv ≫ H₂.isoPullback.hom ≫ (baseChangeCone D c p₂).π.app j₃ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hv₁fst, ← Category.assoc, (baseChangeCone D c p₁).w m₁, hu₁a,
        Category.assoc, Category.assoc, baseChangeCone_π_app_fst, hi₂fst]
    · rw [Category.assoc, hv₁snd, baseChangeCone_π_app_snd, Category.assoc, Category.assoc,
        baseChangeCone_π_app_snd, ← Category.assoc H₂.isoPullback.hom, hi₂snd,
        ← Category.assoc, hinvg₁]
  have key₂ : (baseChangeCone D c p₂).π.app j₃ ≫ v₂ =
      H₂.isoPullback.inv ≫ H₁.isoPullback.hom ≫ (baseChangeCone D c p₁).π.app j₃ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hv₂fst, ← Category.assoc, (baseChangeCone D c p₂).w m₂, hu₂a,
        Category.assoc, Category.assoc, baseChangeCone_π_app_fst, hi₁fst]
    · rw [Category.assoc, hv₂snd, baseChangeCone_π_app_snd, Category.assoc, Category.assoc,
        baseChangeCone_π_app_snd, ← Category.assoc H₁.isoPullback.hom, hi₁snd,
        ← Category.assoc, hinvg₂]
  have hw₁ : (baseChangeCone D c p₁).π.app j₃ ≫ v₁ ≫ v₂ = (baseChangeCone D c p₁).π.app j₃ := by
    rw [← Category.assoc, key₁, Category.assoc, Category.assoc, key₂, Iso.hom_inv_id_assoc,
      Iso.inv_hom_id_assoc]
  have hw₂ : (baseChangeCone D c p₂).π.app j₃ ≫ v₂ ≫ v₁ = (baseChangeCone D c p₂).π.app j₃ := by
    rw [← Category.assoc, key₂, Category.assoc, Category.assoc, key₁, Iso.hom_inv_id_assoc,
      Iso.inv_hom_id_assoc]
  -- the two composites become the identity at a later stage
  obtain ⟨j₄, n₁, hn₁⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
      (baseChangeDiagram D p₁) (baseChangeDiagramStructure D p₁) p₁ (baseChangeCone D c p₁)
      (isLimitBaseChangeCone D c p₁ hc)
      (v₁ ≫ v₂ ≫ pullback.fst p₁ (D.map j₃.hom)) (pullback.fst p₁ (D.map j₃.hom))
      (by
        change pullback.fst p₁ (D.map j₃.hom) ≫ p₁ = _
        rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc v₂, hv₂snd,
          ← Category.assoc, hv₁snd, ← pullback.condition])
      rfl
      (by
        have h := congrArg (· ≫ pullback.fst p₁ (D.map j₃.hom)) hw₁
        simp only [Category.assoc] at h ⊢
        exact h)
  obtain ⟨j₅, n₂, hn₂⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
      (baseChangeDiagram D p₂) (baseChangeDiagramStructure D p₂) p₂ (baseChangeCone D c p₂)
      (isLimitBaseChangeCone D c p₂ hc)
      (v₂ ≫ v₁ ≫ pullback.fst p₂ (D.map j₃.hom)) (pullback.fst p₂ (D.map j₃.hom))
      (by
        change pullback.fst p₂ (D.map j₃.hom) ≫ p₂ = _
        rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc v₁, hv₁snd,
          ← Category.assoc, hv₂snd, ← pullback.condition])
      rfl
      (by
        have h := congrArg (· ≫ pullback.fst p₂ (D.map j₃.hom)) hw₂
        simp only [Category.assoc] at h ⊢
        exact h)
  obtain ⟨j₇, e, he⟩ := IsCofilteredOrEmpty.cone_maps
    (IsCofiltered.minToLeft j₄ j₅ ≫ n₁) (IsCofiltered.minToRight j₄ j₅ ≫ n₂)
  obtain ⟨t, ht₁, ht₂⟩ : ∃ t : j₇ ⟶ j₃, t = (e ≫ IsCofiltered.minToLeft j₄ j₅) ≫ n₁ ∧
      t = (e ≫ IsCofiltered.minToRight j₄ j₅) ≫ n₂ :=
    ⟨_, rfl, by rw [Category.assoc, he, Category.assoc]⟩
  have hcomp₁ : (baseChangeDiagram D p₁).map t ≫ v₁ ≫ v₂ ≫ pullback.fst p₁ (D.map j₃.hom) =
      (baseChangeDiagram D p₁).map t ≫ pullback.fst p₁ (D.map j₃.hom) := by
    rw [ht₁]
    simp only [Functor.map_comp, Category.assoc]
    rw [hn₁]
  have hcomp₂ : (baseChangeDiagram D p₂).map t ≫ v₂ ≫ v₁ ≫ pullback.fst p₂ (D.map j₃.hom) =
      (baseChangeDiagram D p₂).map t ≫ pullback.fst p₂ (D.map j₃.hom) := by
    rw [ht₂]
    simp only [Functor.map_comp, Category.assoc]
    rw [hn₂]
  -- the isomorphism at the stage `j₇`
  set V₁ : (baseChangeDiagram D p₁).obj j₇ ⟶ (baseChangeDiagram D p₂).obj j₇ :=
    pullback.lift ((baseChangeDiagram D p₁).map t ≫ v₁ ≫ pullback.fst p₂ (D.map j₃.hom))
      (pullback.snd p₁ (D.map j₇.hom))
      (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc v₁, hv₁snd,
            ← Category.assoc, baseChangeDiagram_map_snd, Category.assoc, ← D.map_comp,
            Over.w t]) with hV₁def
  set V₂ : (baseChangeDiagram D p₂).obj j₇ ⟶ (baseChangeDiagram D p₁).obj j₇ :=
    pullback.lift ((baseChangeDiagram D p₂).map t ≫ v₂ ≫ pullback.fst p₁ (D.map j₃.hom))
      (pullback.snd p₂ (D.map j₇.hom))
      (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc v₂, hv₂snd,
            ← Category.assoc, baseChangeDiagram_map_snd, Category.assoc, ← D.map_comp,
            Over.w t]) with hV₂def
  have hV₁fst : V₁ ≫ pullback.fst p₂ (D.map j₇.hom) =
      (baseChangeDiagram D p₁).map t ≫ v₁ ≫ pullback.fst p₂ (D.map j₃.hom) := pullback.lift_fst ..
  have hV₁snd : V₁ ≫ pullback.snd p₂ (D.map j₇.hom) = pullback.snd p₁ (D.map j₇.hom) :=
    pullback.lift_snd ..
  have hV₂fst : V₂ ≫ pullback.fst p₁ (D.map j₇.hom) =
      (baseChangeDiagram D p₂).map t ≫ v₂ ≫ pullback.fst p₁ (D.map j₃.hom) := pullback.lift_fst ..
  have hV₂snd : V₂ ≫ pullback.snd p₁ (D.map j₇.hom) = pullback.snd p₂ (D.map j₇.hom) :=
    pullback.lift_snd ..
  have hnat₁ : V₁ ≫ (baseChangeDiagram D p₂).map t = (baseChangeDiagram D p₁).map t ≫ v₁ := by
    apply pullback.hom_ext
    · rw [Category.assoc, baseChangeDiagram_map_fst, hV₁fst, Category.assoc]
    · rw [Category.assoc, baseChangeDiagram_map_snd, ← Category.assoc, hV₁snd,
        Category.assoc, hv₁snd, baseChangeDiagram_map_snd]
  have hnat₂ : V₂ ≫ (baseChangeDiagram D p₁).map t = (baseChangeDiagram D p₂).map t ≫ v₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, baseChangeDiagram_map_fst, hV₂fst, Category.assoc]
    · rw [Category.assoc, baseChangeDiagram_map_snd, ← Category.assoc, hV₂snd,
        Category.assoc, hv₂snd, baseChangeDiagram_map_snd]
  have hVV₁ : V₁ ≫ V₂ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hV₂fst, ← Category.assoc, hnat₁]
      simp only [Category.assoc]
      rw [hcomp₁, baseChangeDiagram_map_fst, Category.id_comp]
    · rw [Category.assoc, hV₂snd, hV₁snd, Category.id_comp]
  have hVV₂ : V₂ ≫ V₁ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hV₁fst, ← Category.assoc, hnat₂]
      simp only [Category.assoc]
      rw [hcomp₂, baseChangeDiagram_map_fst, Category.id_comp]
    · rw [Category.assoc, hV₁snd, hV₂snd, Category.id_comp]
  have key₁' : (baseChangeCone D c p₁).π.app j₃ ≫ v₁ ≫ pullback.fst p₂ (D.map j₃.hom) =
      H₁.isoPullback.inv ≫ h₂ := by
    rw [← Category.assoc, key₁, Category.assoc, Category.assoc, baseChangeCone_π_app_fst, hi₂fst]
  have hcompat : (H₁.isoPullback.hom ≫ (baseChangeCone D c p₁).π.app j₇) ≫ V₁ =
      H₂.isoPullback.hom ≫ (baseChangeCone D c p₂).π.app j₇ := by
    apply pullback.hom_ext
    · have hlhs : ((H₁.isoPullback.hom ≫ (baseChangeCone D c p₁).π.app j₇) ≫ V₁) ≫
          pullback.fst p₂ (D.map j₇.hom) = h₂ := by
        simp only [Category.assoc, hV₁fst]
        rw [← Category.assoc ((baseChangeCone D c p₁).π.app j₇), (baseChangeCone D c p₁).w t,
          key₁', Iso.hom_inv_id_assoc]
      have hrhs : (H₂.isoPullback.hom ≫ (baseChangeCone D c p₂).π.app j₇) ≫
          pullback.fst p₂ (D.map j₇.hom) = h₂ := by
        rw [Category.assoc, baseChangeCone_π_app_fst, hi₂fst]
      rw [hlhs, hrhs]
    · rw [Category.assoc, Category.assoc, hV₁snd, baseChangeCone_π_app_snd, ← Category.assoc,
        hi₁snd, Category.assoc, baseChangeCone_π_app_snd, ← Category.assoc, hi₂snd]
  -- transport to arbitrary models of the base changes
  refine ⟨j₇.left, j₇.hom, ?_⟩
  intro Y₁' Y₂' p₁' q₁ p₂' q₂ h₁' h₂' HH₁ hh₁ hh₁' HH₂ hh₂ hh₂'
  have hα₁fst : HH₁.isoPullback.hom ≫ pullback.fst p₁ (D.map j₇.hom) = q₁ :=
    IsPullback.isoPullback_hom_fst _
  have hα₁snd : HH₁.isoPullback.hom ≫ pullback.snd p₁ (D.map j₇.hom) = p₁' :=
    IsPullback.isoPullback_hom_snd _
  have hα₂fst : HH₂.isoPullback.hom ≫ pullback.fst p₂ (D.map j₇.hom) = q₂ :=
    IsPullback.isoPullback_hom_fst _
  have hα₂snd : HH₂.isoPullback.hom ≫ pullback.snd p₂ (D.map j₇.hom) = p₂' :=
    IsPullback.isoPullback_hom_snd _
  have hh₁α : h₁' ≫ HH₁.isoPullback.hom =
      H₁.isoPullback.hom ≫ (baseChangeCone D c p₁).π.app j₇ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hα₁fst, hh₁, Category.assoc, baseChangeCone_π_app_fst, hi₁fst]
    · rw [Category.assoc, hα₁snd, hh₁', Category.assoc, baseChangeCone_π_app_snd,
        ← Category.assoc, hi₁snd]
  have hh₂α : h₂' ≫ HH₂.isoPullback.hom =
      H₂.isoPullback.hom ≫ (baseChangeCone D c p₂).π.app j₇ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hα₂fst, hh₂, Category.assoc, baseChangeCone_π_app_fst, hi₂fst]
    · rw [Category.assoc, hα₂snd, hh₂', Category.assoc, baseChangeCone_π_app_snd,
        ← Category.assoc, hi₂snd]
  refine ⟨HH₁.isoPullback ≪≫ ⟨V₁, V₂, hVV₁, hVV₂⟩ ≪≫ HH₂.isoPullback.symm, ?_, ?_⟩
  · change HH₁.isoPullback.hom ≫ V₁ ≫ HH₂.isoPullback.inv ≫ p₂' = p₁'
    rw [show HH₂.isoPullback.inv ≫ p₂' = pullback.snd p₂ (D.map j₇.hom) by
      rw [Iso.inv_comp_eq, hα₂snd], hV₁snd, hα₁snd]
  · change h₁' ≫ HH₁.isoPullback.hom ≫ V₁ ≫ HH₂.isoPullback.inv = h₂'
    rw [← Category.assoc, ← Category.assoc, hh₁α, hcompat, ← hh₂α, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]

variable (D c) in
/-- (Implementation) The comparison morphism to the base change of a finite-stage model. -/
noncomputable def isPullbackLift {k k' : I} (f : k' ⟶ k) {X Y : Scheme.{u}} {g : X ⟶ c.pt}
    {p : Y ⟶ D.obj k} {h : X ⟶ Y} (H : IsPullback h g p (c.π.app k)) :
    X ⟶ pullback p (D.map f) :=
  pullback.lift h (g ≫ c.π.app k') (by rw [H.w, ← c.w f, Category.assoc])

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
@[reassoc (attr := simp)]
lemma isPullbackLift_fst {k k' : I} (f : k' ⟶ k) {X Y : Scheme.{u}} {g : X ⟶ c.pt}
    {p : Y ⟶ D.obj k} {h : X ⟶ Y} (H : IsPullback h g p (c.π.app k)) :
    isPullbackLift D c f H ≫ pullback.fst p (D.map f) = h := pullback.lift_fst ..

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
@[reassoc (attr := simp)]
lemma isPullbackLift_snd {k k' : I} (f : k' ⟶ k) {X Y : Scheme.{u}} {g : X ⟶ c.pt}
    {p : Y ⟶ D.obj k} {h : X ⟶ Y} (H : IsPullback h g p (c.π.app k)) :
    isPullbackLift D c f H ≫ pullback.snd p (D.map f) = g ≫ c.π.app k' := pullback.lift_snd ..

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
lemma isPullback_isPullbackLift {k k' : I} (f : k' ⟶ k) {X Y : Scheme.{u}} {g : X ⟶ c.pt}
    {p : Y ⟶ D.obj k} {h : X ⟶ Y} (H : IsPullback h g p (c.π.app k)) :
    IsPullback (isPullbackLift D c f H) g (pullback.snd p (D.map f)) (c.π.app k') := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback p (D.map f))
  rw [isPullbackLift_fst, c.w f]
  exact H


variable (D c) in
/-- (Implementation) The property that `g : X ⟶ lim Dⱼ` is the base change along
`lim Dⱼ ⟶ D_k` of a scheme of finite presentation over the stage `D_k`. -/
def DescendsAt (k : I) {X : Scheme.{u}} (g : X ⟶ c.pt) : Prop :=
  ∃ (Y : Scheme.{u}) (p : Y ⟶ D.obj k) (h : X ⟶ Y), LocallyOfFinitePresentation p ∧
    CompactSpace Y ∧ QuasiSeparatedSpace Y ∧ IsPullback h g p (c.π.app k)

variable (D c) in
/-- (Implementation) Refinement of `AlgebraicGeometry.DescendsAt` remembering a descent of a
quasi-compact open `W ⊆ X` to a quasi-compact open of the finite-stage model. -/
def DescendsAtWithOpen (k : I) {X : Scheme.{u}} (g : X ⟶ c.pt) (W : X.Opens) : Prop :=
  ∃ (Y : Scheme.{u}) (p : Y ⟶ D.obj k) (h : X ⟶ Y) (O : Y.Opens),
    LocallyOfFinitePresentation p ∧ CompactSpace Y ∧ QuasiSeparatedSpace Y ∧
      IsPullback h g p (c.π.app k) ∧ IsCompact (O : Set Y) ∧ h ⁻¹ᵁ O = W

variable (D c) in
/-- (Implementation) The property that `g : X ⟶ lim Dⱼ` is the base change of a scheme of
finite presentation over one of the stages. -/
def DescendsToStage {X : Scheme.{u}} (g : X ⟶ c.pt) : Prop := ∃ k, DescendsAt D c k g

omit [IsCofiltered I] in
lemma DescendsAt.mono {k k' : I} (f : k' ⟶ k) {X : Scheme.{u}} {g : X ⟶ c.pt}
    (H : DescendsAt D c k g) : DescendsAt D c k' g := by
  obtain ⟨Y, p, h, hp, hcpt, hqs, hsq⟩ := H
  haveI := hp; haveI := hcpt; haveI := hqs
  exact ⟨pullback p (D.map f), pullback.snd _ _, isPullbackLift D c f hsq, inferInstance,
    inferInstance, inferInstance, isPullback_isPullbackLift f hsq⟩

omit [IsCofiltered I] in
lemma DescendsAtWithOpen.mono {k k' : I} (f : k' ⟶ k) {X : Scheme.{u}} {g : X ⟶ c.pt}
    {W : X.Opens} (H : DescendsAtWithOpen D c k g W) : DescendsAtWithOpen D c k' g W := by
  obtain ⟨Y, p, h, O, hp, hcpt, hqs, hsq, hOc, hO⟩ := H
  haveI := hp; haveI := hcpt; haveI := hqs
  haveI : QuasiCompact (pullback.fst p (D.map f)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  refine ⟨pullback p (D.map f), pullback.snd _ _, isPullbackLift D c f hsq,
    pullback.fst p (D.map f) ⁻¹ᵁ O, inferInstance, inferInstance, inferInstance,
    isPullback_isPullbackLift f hsq,
    QuasiCompact.isCompact_preimage _ O.isOpen hOc, ?_⟩
  rw [← Scheme.Hom.comp_preimage, isPullbackLift_fst, hO]

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
lemma DescendsAtWithOpen.descendsAt {k : I} {X : Scheme.{u}} {g : X ⟶ c.pt} {W : X.Opens}
    (H : DescendsAtWithOpen D c k g W) : DescendsAt D c k g := by
  obtain ⟨Y, p, h, O, hp, hcpt, hqs, hsq, -, -⟩ := H
  exact ⟨Y, p, h, hp, hcpt, hqs, hsq⟩

include hc in
/-- (Implementation) A quasi-compact open of a scheme over the limit descends to a
finite stage (Stacks Project Tag 01ZB). -/
lemma exists_descendsAtWithOpen {k : I} {X : Scheme.{u}} {g : X ⟶ c.pt}
    (H : DescendsAt D c k g) (W : X.Opens) (hW : IsCompact (W : Set X)) :
    ∃ k' : I, DescendsAtWithOpen D c k' g W := by
  obtain ⟨Y, p, h, hp, hcpt, hqs, hsq⟩ := H
  haveI := hp; haveI := hcpt; haveI := hqs
  have hlim : IsLimit ((baseChangeCone D c p).extend hsq.isoPullback.hom) :=
    (isLimitBaseChangeCone D c p hc).ofIsoLimit
      (Cone.ext hsq.isoPullback.symm (fun j ↦ by simp))
  obtain ⟨j, O, hOc, hO⟩ := exists_preimage_eq (baseChangeDiagram D p) _ hlim W hW
  refine ⟨j.left, pullback p (D.map j.hom), pullback.snd _ _, isPullbackLift D c j.hom hsq, O,
    inferInstance, inferInstance, inferInstance, isPullback_isPullbackLift j.hom hsq, hOc, ?_⟩
  have hmap : isPullbackLift D c j.hom hsq =
      ((baseChangeCone D c p).extend hsq.isoPullback.hom).π.app j := by
    apply pullback.hom_ext <;>
      simp [Cone.extend, IsPullback.isoPullback_hom_fst]
  rw [← hO, hmap]

include hc in
/-- (Implementation) **An affine scheme of finite presentation over the limit that lies over an
affine open of one of the stages descends to a finite stage.**

The system is base changed to the affine open `V ⊆ Dᵢ₀`: the base changed system has affine
stages, so the affine case
`AlgebraicGeometry.Scheme.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine`
applies to it. -/
lemma DescendsToStage.of_isAffine {i₀ : I} {X : Scheme.{u}} [IsAffine X] (g : X ⟶ c.pt)
    [LocallyOfFinitePresentation g] {V : (D.obj i₀).Opens} (hV : IsAffineOpen V)
    (q : X ⟶ V.toScheme) (hq : q ≫ V.ι = g ≫ c.π.app i₀) : DescendsToStage D c g := by
  haveI : IsAffine V.toScheme := hV
  haveI : ∀ j : Over i₀, IsAffine ((baseChangeDiagram D V.ι).obj j) := fun j ↦
    inferInstanceAs (IsAffine (pullback V.ι (D.map j.hom)))
  have hsnd : pullback.lift q g hq ≫ pullback.snd V.ι (c.π.app i₀) = g := pullback.lift_snd ..
  have hmono : MorphismProperty.monomorphisms Scheme.{u} (pullback.snd V.ι (c.π.app i₀)) :=
    inferInstanceAs (Mono _)
  have hcomp : LocallyOfFinitePresentation
      (pullback.lift q g hq ≫ pullback.snd V.ι (c.π.app i₀)) := by
    rw [hsnd]
    exact ‹LocallyOfFinitePresentation g›
  haveI : @LocallyOfFinitePresentation X (baseChangeCone D c V.ι).pt (pullback.lift q g hq) :=
    MorphismProperty.of_postcomp (W := @LocallyOfFinitePresentation)
      (W' := MorphismProperty.monomorphisms Scheme.{u}) _ (pullback.snd V.ι (c.π.app i₀))
      hmono hcomp
  obtain ⟨j, Y, hYaff, p, hp, h, hsq⟩ :=
    Scheme.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine
      (baseChangeDiagram D V.ι) (baseChangeCone D c V.ι)
      (isLimitBaseChangeCone D c V.ι hc) (pullback.lift q g hq)
  haveI := hYaff
  haveI := hp
  haveI : IsOpenImmersion ((baseChangeDiagramπ D V.ι).app j) :=
    inferInstanceAs (IsOpenImmersion (pullback.snd V.ι (D.map j.hom)))
  have hP : LocallyOfFinitePresentation (p ≫ (baseChangeDiagramπ D V.ι).app j) := inferInstance
  refine ⟨j.left, Y, p ≫ (baseChangeDiagramπ D V.ι).app j, h, hP, inferInstance,
    inferInstance, ?_⟩
  rw [← hsnd]
  exact hsq.paste_vert (isPullback_baseChangeCone_π D c V.ι j)

include hc in
/-- (Implementation) An affine open of a scheme over the limit that lies over an affine open of
one of the stages descends to a finite stage. -/
lemma DescendsToStage.of_isAffineOpen {i₀ : I} {X : Scheme.{u}} (g : X ⟶ c.pt)
    [LocallyOfFinitePresentation g] {W : X.Opens} (hW : IsAffineOpen W)
    {V : (D.obj i₀).Opens} (hV : IsAffineOpen V) (hle : W ≤ (g ≫ c.π.app i₀) ⁻¹ᵁ V) :
    DescendsToStage D c (W.ι ≫ g) := by
  haveI : IsAffine W.toScheme := hW
  refine DescendsToStage.of_isAffine hc _ hV ((g ≫ c.π.app i₀).resLE V W hle) ?_
  rw [Scheme.Hom.resLE_comp_ι, Category.assoc]

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
lemma DescendsToStage.comp_iso {X X' : Scheme.{u}} (e : X' ≅ X) {g : X ⟶ c.pt}
    (H : DescendsToStage D c g) : DescendsToStage D c (e.hom ≫ g) := by
  obtain ⟨k, Y, p, h, hp, hcpt, hqs, hsq⟩ := H
  refine ⟨k, Y, p, e.hom ≫ h, hp, hcpt, hqs, ?_⟩
  have hiso : IsPullback e.hom (e.hom ≫ g) g (𝟙 c.pt) := IsPullback.of_horiz_isIso ⟨by simp⟩
  simpa using hiso.paste_horiz hsq


include hc in
/-- (Implementation) **The two-open gluing step**: if a scheme over the limit is covered by
two opens with quasi-compact intersection, each of which descends to a finite stage, then it
descends to a finite stage. -/
lemma DescendsToStage.of_sup_eq_top {Z : Scheme.{u}} (gZ : Z ⟶ c.pt) (U V : Z.Opens)
    (hUV : U ⊔ V = ⊤) (hWc : IsCompact ((U ⊓ V : Z.Opens) : Set Z))
    (hU : DescendsToStage D c (U.ι ≫ gZ)) (hV : DescendsToStage D c (V.ι ≫ gZ)) :
    DescendsToStage D c gZ := by
  obtain ⟨k₁, hU⟩ := hU
  obtain ⟨k₂, hV⟩ := hV
  -- the intersection is quasi-compact in each of the two charts
  have hWU : IsCompact ((U.ι ⁻¹ᵁ V : U.toScheme.Opens) : Set U.toScheme) := by
    have he : (U.ι ⁻¹ᵁ V : U.toScheme.Opens) = U.ι ⁻¹ᵁ (U ⊓ V) := by
      rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq]
    rw [he]
    refine U.ι.isOpenEmbedding.isInducing.isCompact_preimage' hWc ?_
    rw [Scheme.Opens.range_ι]
    exact inf_le_left
  have hWV : IsCompact ((V.ι ⁻¹ᵁ U : V.toScheme.Opens) : Set V.toScheme) := by
    have he : (V.ι ⁻¹ᵁ U : V.toScheme.Opens) = V.ι ⁻¹ᵁ (U ⊓ V) := by
      rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, inf_top_eq]
    rw [he]
    refine V.ι.isOpenEmbedding.isInducing.isCompact_preimage' hWc ?_
    rw [Scheme.Opens.range_ι]
    exact inf_le_right
  -- descend the intersection inside both charts, over a common stage
  obtain ⟨k₃, hU⟩ := exists_descendsAtWithOpen hc hU _ hWU
  obtain ⟨k₄, hV⟩ := exists_descendsAtWithOpen hc hV _ hWV
  replace hU := hU.mono (IsCofiltered.minToLeft k₃ k₄)
  replace hV := hV.mono (IsCofiltered.minToRight k₃ k₄)
  set k := IsCofiltered.min k₃ k₄ with hk
  obtain ⟨YU, pU, hUh, OU, hpU, hcU, hqU, HU, hOUc, hOU⟩ := hU
  obtain ⟨YV, pV, hVh, OV, hpV, hcV, hqV, HV, hOVc, hOV⟩ := hV
  haveI := hpU; haveI := hcU; haveI := hqU; haveI := hpV; haveI := hcV; haveI := hqV
  haveI : CompactSpace OU.toScheme := isCompact_iff_compactSpace.mp hOUc
  haveI : CompactSpace OV.toScheme := isCompact_iff_compactSpace.mp hOVc
  haveI : QuasiSeparatedSpace OU.toScheme :=
    QuasiSeparatedSpace.of_isOpenEmbedding OU.ι.isOpenEmbedding
  haveI : QuasiSeparatedSpace OV.toScheme :=
    QuasiSeparatedSpace.of_isOpenEmbedding OV.ι.isOpenEmbedding
  -- the two descended models of the intersection
  have hrangeU : (Scheme.Opens.infHomLeft U V).opensRange = U.ι ⁻¹ᵁ V := by
    rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self,
      top_inf_eq]
  have hrangeV : (Scheme.Opens.infHomRight U V).opensRange = V.ι ⁻¹ᵁ U := by
    rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self,
      inf_top_eq]
  have hsubU : Set.range (Scheme.Opens.infHomLeft U V ≫ hUh) ⊆ Set.range OU.ι := by
    rintro - ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change hUh ((Scheme.Opens.infHomLeft U V) x) ∈ OU
    have : (Scheme.Opens.infHomLeft U V) x ∈ hUh ⁻¹ᵁ OU := by
      rw [hOU, ← hrangeU]
      exact ⟨x, rfl⟩
    exact this
  have hsubV : Set.range (Scheme.Opens.infHomRight U V ≫ hVh) ⊆ Set.range OV.ι := by
    rintro - ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change hVh ((Scheme.Opens.infHomRight U V) x) ∈ OV
    have : (Scheme.Opens.infHomRight U V) x ∈ hVh ⁻¹ᵁ OV := by
      rw [hOV, ← hrangeV]
      exact ⟨x, rfl⟩
    exact this
  set aU₀ : (U ⊓ V : Z.Opens).toScheme ⟶ OU.toScheme :=
    IsOpenImmersion.lift OU.ι (Scheme.Opens.infHomLeft U V ≫ hUh) hsubU with haU₀
  set aV₀ : (U ⊓ V : Z.Opens).toScheme ⟶ OV.toScheme :=
    IsOpenImmersion.lift OV.ι (Scheme.Opens.infHomRight U V ≫ hVh) hsubV with haV₀
  have HaU : IsPullback aU₀ (Scheme.Opens.infHomLeft U V) OU.ι hUh :=
    IsOpenImmersion.isPullback _ _ _ _ (IsOpenImmersion.lift_fac _ _ hsubU).symm
      (by rw [Scheme.Opens.opensRange_ι, hOU, hrangeU])
  have HaV : IsPullback aV₀ (Scheme.Opens.infHomRight U V) OV.ι hVh :=
    IsOpenImmersion.isPullback _ _ _ _ (IsOpenImmersion.lift_fac _ _ hsubV).symm
      (by rw [Scheme.Opens.opensRange_ι, hOV, hrangeV])
  have HWU : IsPullback aU₀ ((U ⊓ V : Z.Opens).ι ≫ gZ) (OU.ι ≫ pU) (c.π.app k) := by
    have h := HaU.paste_vert HU
    rwa [← Category.assoc, Scheme.homOfLE_ι] at h
  have HWV : IsPullback aV₀ ((U ⊓ V : Z.Opens).ι ≫ gZ) (OV.ι ≫ pV) (c.π.app k) := by
    have h := HaV.paste_vert HV
    rwa [← Category.assoc, Scheme.homOfLE_ι] at h
  -- the two models of the intersection agree at a later stage
  obtain ⟨k', f', hiso⟩ := exists_iso_of_isPullback hc HWU HWV
  -- base change everything to that stage
  set YU' := pullback pU (D.map f') with hYU'
  set YV' := pullback pV (D.map f') with hYV'
  set pU' : YU' ⟶ D.obj k' := pullback.snd pU (D.map f') with hpU'
  set pV' : YV' ⟶ D.obj k' := pullback.snd pV (D.map f') with hpV'
  set hU' : U.toScheme ⟶ YU' := isPullbackLift D c f' HU with hhU'
  set hV' : V.toScheme ⟶ YV' := isPullbackLift D c f' HV with hhV'
  have HU' : IsPullback hU' (U.ι ≫ gZ) pU' (c.π.app k') := isPullback_isPullbackLift f' HU
  have HV' : IsPullback hV' (V.ι ≫ gZ) pV' (c.π.app k') := isPullback_isPullbackLift f' HV
  set OU' : YU'.Opens := pullback.fst pU (D.map f') ⁻¹ᵁ OU with hOU'
  set OV' : YV'.Opens := pullback.fst pV (D.map f') ⁻¹ᵁ OV with hOV'
  have HqU : IsPullback (pullback.fst pU (D.map f') ∣_ OU) (OU'.ι ≫ pU') (OU.ι ≫ pU)
      (D.map f') :=
    (isPullback_morphismRestrict (pullback.fst pU (D.map f')) OU).paste_vert
      (IsPullback.of_hasPullback pU (D.map f'))
  have HqV : IsPullback (pullback.fst pV (D.map f') ∣_ OV) (OV'.ι ≫ pV') (OV.ι ≫ pV)
      (D.map f') :=
    (isPullback_morphismRestrict (pullback.fst pV (D.map f')) OV).paste_vert
      (IsPullback.of_hasPullback pV (D.map f'))
  set h₁' : (U ⊓ V : Z.Opens).toScheme ⟶ OU'.toScheme :=
    HqU.lift aU₀ ((U ⊓ V : Z.Opens).ι ≫ gZ ≫ c.π.app k')
      (by rw [HWU.w]; simp only [Category.assoc]; rw [c.w f']) with hh₁'
  set h₂' : (U ⊓ V : Z.Opens).toScheme ⟶ OV'.toScheme :=
    HqV.lift aV₀ ((U ⊓ V : Z.Opens).ι ≫ gZ ≫ c.π.app k')
      (by rw [HWV.w]; simp only [Category.assoc]; rw [c.w f']) with hh₂'
  obtain ⟨e, he₁, he₂⟩ := hiso (h₁' := h₁') (h₂' := h₂') HqU
    (by rw [hh₁']; exact IsPullback.lift_fst ..)
    (by rw [hh₁', IsPullback.lift_snd, Category.assoc]) HqV
    (by rw [hh₂']; exact IsPullback.lift_fst ..)
    (by rw [hh₂', IsPullback.lift_snd, Category.assoc])
  -- glue the two charts along the descended intersection
  have hOU'c : IsCompact ((OU' : YU'.Opens) : Set YU') := by
    haveI : QuasiCompact (pullback.fst pU (D.map f')) :=
      MorphismProperty.pullback_fst _ _ inferInstance
    rw [hOU']
    exact QuasiCompact.isCompact_preimage _ OU.isOpen hOUc
  haveI : CompactSpace ↥(OU'.toScheme) := isCompact_iff_compactSpace.mp hOU'c
  have hcomm : OU'.ι ≫ pU' = (e.hom ≫ OV'.ι) ≫ pV' := by rw [Category.assoc, he₁]
  have hpreU : hU' ⁻¹ᵁ OU' = U.ι ⁻¹ᵁ V := by
    rw [hOU', ← Scheme.Hom.comp_preimage, hhU', isPullbackLift_fst, hOU]
  have hpreV : hV' ⁻¹ᵁ OV' = V.ι ⁻¹ᵁ U := by
    rw [hOV', ← Scheme.Hom.comp_preimage, hhV', isPullbackLift_fst, hOV]
  have hcommU : Scheme.Opens.infHomLeft U V ≫ hU' = h₁' ≫ OU'.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, hhU', isPullbackLift_fst, Category.assoc,
        ← morphismRestrict_ι (pullback.fst pU (D.map f')) OU, ← Category.assoc, hh₁',
        IsPullback.lift_fst, haU₀, IsOpenImmersion.lift_fac]
    · rw [Category.assoc, hhU', isPullbackLift_snd, Category.assoc]
      change _ = h₁' ≫ OU'.ι ≫ pU'
      rw [← Category.assoc, hh₁', IsPullback.lift_snd, Category.assoc,
        ← Category.assoc (Scheme.Opens.infHomLeft U V), Scheme.homOfLE_ι]
  have hcommV' : Scheme.Opens.infHomRight U V ≫ hV' = h₂' ≫ OV'.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, hhV', isPullbackLift_fst, Category.assoc,
        ← morphismRestrict_ι (pullback.fst pV (D.map f')) OV, ← Category.assoc, hh₂',
        IsPullback.lift_fst, haV₀, IsOpenImmersion.lift_fac]
    · rw [Category.assoc, hhV', isPullbackLift_snd, Category.assoc]
      change _ = h₂' ≫ OV'.ι ≫ pV'
      rw [← Category.assoc, hh₂', IsPullback.lift_snd, Category.assoc,
        ← Category.assoc (Scheme.Opens.infHomRight U V), Scheme.homOfLE_ι]
  have hcommV : Scheme.Opens.infHomRight U V ≫ hV' = h₁' ≫ e.hom ≫ OV'.ι := by
    rw [← Category.assoc, he₂, hcommV']
  have HsqU : IsPullback h₁' (Scheme.Opens.infHomLeft U V) OU'.ι hU' :=
    IsOpenImmersion.isPullback _ _ _ _ hcommU
      (by rw [Scheme.Opens.opensRange_ι, hpreU, hrangeU])
  have HsqV : IsPullback h₁' (Scheme.Opens.infHomRight U V) (e.hom ≫ OV'.ι) hV' :=
    IsOpenImmersion.isPullback _ _ _ _ hcommV
      (by
        rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι, hpreV, hrangeV])
  -- the glued finite-stage model
  have hf : h₁' ≫ OU'.ι = Scheme.Opens.infHomLeft U V ≫ hU' := hcommU.symm
  have hg : h₁' ≫ (e.hom ≫ OV'.ι) = Scheme.Opens.infHomRight U V ≫ hV' := hcommV.symm
  set p : pushout OU'.ι (e.hom ≫ OV'.ι) ⟶ D.obj k' := pushout.desc pU' pV' hcomm with hp
  set ρ := pushout.map (Scheme.Opens.infHomLeft U V)
    (Scheme.Opens.infHomRight U V) OU'.ι (e.hom ≫ OV'.ι) hU' hV' h₁'
    hf.symm hg.symm with hρ
  have hchartU := isPullback_pushout_map_inl_of_isPullback OU'.ι (e.hom ≫ OV'.ι)
    (Scheme.Opens.infHomLeft U V) (Scheme.Opens.infHomRight U V)
    hU' hV' h₁' hf hg HsqV
  have hchartV := isPullback_pushout_map_inr_of_isPullback OU'.ι (e.hom ≫ OV'.ι)
    (Scheme.Opens.infHomLeft U V) (Scheme.Opens.infHomRight U V)
    hU' hV' h₁' hf hg HsqU
  have hw : ρ ≫ p = (pushoutOpensDesc U V ≫ gZ) ≫ c.π.app k' := by
    apply pushout.hom_ext
    · rw [← Category.assoc, hρ, pushout.inl_desc, Category.assoc, hp, pushout.inl_desc]
      have hw' := HU'.w
      simp only [Category.assoc] at hw' ⊢
      rw [inl_pushoutOpensDesc_assoc]
      exact hw'
    · rw [← Category.assoc, hρ, pushout.inr_desc, Category.assoc, hp, pushout.inr_desc]
      have hw' := HV'.w
      simp only [Category.assoc] at hw' ⊢
      rw [inr_pushoutOpensDesc_assoc]
      exact hw'
  have hmain : IsPullback ρ (pushoutOpensDesc U V ≫ gZ) p (c.π.app k') := by
    refine isPullback_of_opensRange_sup_eq_top hw (pushout.inl OU'.ι (e.hom ≫ OV'.ι))
      (pushout.inr OU'.ι (e.hom ≫ OV'.ι))
      (opensRange_pushout_inl_sup_opensRange_pushout_inr OU'.ι (e.hom ≫ OV'.ι))
      hchartU hchartV ?_ ?_
    · rw [inl_pushoutOpensDesc_assoc, hp, pushout.inl_desc]
      exact HU'
    · rw [inr_pushoutOpensDesc_assoc, hp, pushout.inr_desc]
      exact HV'
  haveI := isIso_pushoutOpensDesc U V hUV
  refine ⟨k', pushout OU'.ι (e.hom ≫ OV'.ι), p, inv (pushoutOpensDesc U V) ≫ ρ,
    IsZariskiLocalAtSource.pushout_desc OU'.ι (e.hom ≫ OV'.ι) hcomm inferInstance inferInstance,
    inferInstance,
    quasiSeparatedSpace_pushout OU'.ι (e.hom ≫ OV'.ι), ?_⟩
  have hiso : IsPullback (inv (pushoutOpensDesc U V)) gZ (pushoutOpensDesc U V ≫ gZ)
      (𝟙 c.pt) := IsPullback.of_horiz_isIso ⟨by simp⟩
  simpa using hiso.paste_horiz hmain

include hc in
/-- (Implementation) **Descent to a finite stage for a finite union of affine opens**, each of
which lies over an affine open of the stage `i₀`. -/
lemma descendsToStage_finsetSup {X : Scheme.{u}} [QuasiSeparatedSpace X] {i₀ : I} (g : X ⟶ c.pt)
    [LocallyOfFinitePresentation g] (s : Finset X.Opens)
    (hs : ∀ W ∈ s, IsAffineOpen W ∧
      ∃ V : (D.obj i₀).Opens, IsAffineOpen V ∧ W ≤ (g ≫ c.π.app i₀) ⁻¹ᵁ V) :
    DescendsToStage D c ((s.sup id : X.Opens).ι ≫ g) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sup_empty]
      exact DescendsToStage.of_isAffineOpen hc g (isAffineOpen_bot X)
        (isAffineOpen_bot (D.obj i₀)) bot_le
  | insert a s ha ih =>
      obtain ⟨haff, Va, hVa, hale⟩ := hs a (Finset.mem_insert_self a s)
      have hsaff : ∀ W ∈ s, IsAffineOpen W ∧
          ∃ V : (D.obj i₀).Opens, IsAffineOpen V ∧ W ≤ (g ≫ c.π.app i₀) ⁻¹ᵁ V :=
        fun W hW ↦ hs W (Finset.mem_insert_of_mem hW)
      rw [Finset.sup_insert, id]
      set Z : X.Opens := a ⊔ s.sup id with hZ
      haveI : QuasiSeparatedSpace Z.toScheme :=
        QuasiSeparatedSpace.of_isOpenEmbedding Z.ι.isOpenEmbedding
      set U : Z.toScheme.Opens := Z.ι ⁻¹ᵁ (s.sup id) with hUdef
      set V : Z.toScheme.Opens := Z.ι ⁻¹ᵁ a with hVdef
      have hUV : U ⊔ V = ⊤ := by
        rw [hUdef, hVdef, ← Scheme.Hom.preimage_sup, sup_comm, ← hZ,
          Scheme.Opens.ι_preimage_self]
      -- the intersection is quasi-compact
      have hsc : IsCompact ((s.sup id : X.Opens) : Set X) :=
        isCompact_finset_sup s fun W hW ↦ (hsaff W hW).1.isCompact
      have hinfc : IsCompact (((s.sup id ⊓ a : X.Opens)) : Set X) := by
        rw [TopologicalSpace.Opens.coe_inf]
        exact QuasiSeparatedSpace.inter_isCompact _ _ (s.sup id).2 hsc a.2 haff.isCompact
      have hUVc : IsCompact ((U ⊓ V : Z.toScheme.Opens) : Set Z.toScheme) := by
        have he : (U ⊓ V : Z.toScheme.Opens) = Z.ι ⁻¹ᵁ (s.sup id ⊓ a) := by
          rw [hUdef, hVdef, Scheme.Hom.preimage_inf]
        rw [he]
        refine Z.ι.isOpenEmbedding.isInducing.isCompact_preimage' hinfc ?_
        rw [Scheme.Opens.range_ι]
        exact le_trans inf_le_left le_sup_right
      refine DescendsToStage.of_sup_eq_top hc (Z.ι ≫ g) U V hUV hUVc ?_ ?_
      · -- the first open is the union over `s`, which descends by the induction hypothesis
        have hrange : Set.range (U.ι ≫ Z.ι) = Set.range (s.sup id : X.Opens).ι := by
          rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange]
          congr 1
          simp only [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι, hUdef,
            Scheme.Hom.image_preimage_eq_opensRange_inf, hZ]
          exact inf_eq_right.mpr (le_sup_right : (s.sup id : X.Opens) ≤ a ⊔ s.sup id)
        have := DescendsToStage.comp_iso
          (IsOpenImmersion.isoOfRangeEq (U.ι ≫ Z.ι) (s.sup id : X.Opens).ι hrange) (ih hsaff)
        rwa [← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, Category.assoc] at this
      · -- the second open is affine and lies over an affine open of the stage `i₀`
        refine DescendsToStage.of_isAffineOpen hc (Z.ι ≫ g) ?_ hVa ?_
        · refine haff.preimage_of_isOpenImmersion Z.ι ?_
          rw [Scheme.Opens.opensRange_ι, hZ]
          exact le_sup_left
        · rw [Category.assoc, Scheme.Hom.comp_preimage]
          exact Z.ι.preimage_mono hale

set_option backward.isDefEq.respectTransparency false in
include hc in
/-- **Schemes of finite presentation over a cofiltered limit of quasi-compact quasi-separated
schemes descend to a finite stage** (Stacks Project Tag 01ZM). Let `{Dⱼ}` be a cofiltered
inverse system of quasi-compact quasi-separated schemes with affine transition maps and let
`X` be of finite presentation over `lim Dⱼ`. Then `X` is the base change of a scheme `Y` of
finite presentation over one of the `Dⱼ`.

The affine case is
`AlgebraicGeometry.Scheme.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine`; the
general case follows by induction over a finite cover of `X` by affine opens each of which
lies over an affine open of a fixed stage, gluing the descended charts over a common stage.
(Blueprint: `lemma:nagata-finite-presentation-descends`.) -/
@[stacks 01ZM]
theorem Scheme.exists_isPullback_of_finitePresentation [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {X : Scheme.{u}} (g : X ⟶ c.pt)
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g] :
    ∃ (i : I) (Y : Scheme.{u}) (p : Y ⟶ D.obj i) (_ : LocallyOfFinitePresentation p)
      (_ : QuasiCompact p) (_ : QuasiSeparated p) (h : X ⟶ Y),
      IsPullback h g p (c.π.app i) := by
  classical
  obtain ⟨i₀⟩ : Nonempty I := IsCofiltered.nonempty
  have := isAffineHom_π_app _ _ hc
  haveI : CompactSpace c.pt := QuasiCompact.compactSpace_of_compactSpace (c.π.app i₀)
  haveI : QuasiSeparatedSpace c.pt := quasiSeparatedSpace_of_quasiSeparated (c.π.app i₀)
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace g
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated g
  obtain ⟨Us, hUsB, hUsfin, hUs⟩ :=
    (isBasis_affineOpens_le_preimage (g ≫ c.π.app i₀)).exists_finite_of_isCompact
      (U := ⊤) (by simpa using isCompact_univ)
  have H := descendsToStage_finsetSup hc (i₀ := i₀) g hUsfin.toFinset
    (fun W hW ↦ hUsB (hUsfin.mem_toFinset.mp hW))
  rw [Finset.sup_id_eq_sSup, hUsfin.coe_toFinset, ← hUs] at H
  replace H := DescendsToStage.comp_iso X.topIso.symm H
  rw [Iso.symm_hom, ← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp] at H
  obtain ⟨i, Y, p, h, hp, hcpt, hqs, hsq⟩ := H
  haveI := hp; haveI := hcpt; haveI := hqs
  exact ⟨i, Y, p, hp, inferInstance, inferInstance, h, hsq⟩

end Descent

end FinitePresentationDescent


end AlgebraicGeometry
