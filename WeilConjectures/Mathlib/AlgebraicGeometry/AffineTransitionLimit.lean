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
(`AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, currently a stated
obligation, see below).

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

## Descending schemes of finite presentation along an inverse limit of affine schemes

If `X ⟶ lim Dᵢ` is an affine morphism that is locally of finite presentation, where `{Dᵢ}` is
a cofiltered inverse system of affine schemes with affine transition maps, then `X` is the
base change of a scheme of finite presentation over one of the `Dᵢ`
(`AlgebraicGeometry.Scheme.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine`).

## References

- [Stacks: Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
- [Stacks: Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
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

end IsLimitOfOpensCone

/-- **Absolute Noetherian approximation** (Stacks Project Tag 01ZA): every quasi-compact
quasi-separated scheme is the limit of a cofiltered system of schemes of finite type over
`ℤ` with affine transition morphisms.

The affine case is `AlgebraicGeometry.Scheme.NoetherianApproximation.ofIsAffine`. The
general case glues stage systems over a finite affine cover; its proof is a stated
obligation of the Nagata compactification chapter.
(Blueprint: `prop:nagata-noetherian-inverse-system`.) -/
-- TODO(taxis issue 190): prove the general case. Until it is proved, do not use this theorem
-- to derive instances.
@[stacks 01ZA]
theorem Scheme.nonempty_noetherianApproximation (S : Scheme.{u})
    [CompactSpace S] [QuasiSeparatedSpace S] :
    Nonempty S.NoetherianApproximation := by
  sorry

section FinitePresentation

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)

include hc in
/-- **Objects of finite presentation descend to a finite stage, affine case.**

Let `{Dᵢ}` be a cofiltered inverse system of affine schemes with affine transition maps and
let `X` be an affine scheme that is locally of finite presentation over `lim Dᵢ`. Then `X` is
the base change of a scheme `Y` that is locally of finite presentation over some `Dᵢ`. -/
@[stacks 01ZM]
lemma Scheme.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, IsAffine (D.obj i)]
    {X : Scheme.{u}} [IsAffine X] (g : X ⟶ c.pt) [LocallyOfFinitePresentation g] :
    ∃ (i : I) (Y : Scheme.{u}) (p : Y ⟶ D.obj i) (_ : LocallyOfFinitePresentation p)
      (h : X ⟶ Y), IsPullback h g p (c.π.app i) := by
  have hcpt : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  -- Reduce to the case where `X` is the spectrum of a ring.
  wlog hX : ∃ A, X = Spec A generalizing X
  · obtain ⟨i, Y, p, hp, h, hsq⟩ := this (X := Spec Γ(X, ⊤)) (X.isoSpec.inv ≫ g) ⟨_, rfl⟩
    refine ⟨i, Y, p, hp, X.isoSpec.hom ≫ h, ?_⟩
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
    obtain ⟨i, Y, p, hp, h, hsq⟩ := this _ _ ((IsLimit.postcomposeHomEquiv (asIso e) c).symm hc)
      hcpt g ⟨D ⋙ Scheme.Γ.rightOp, rfl⟩
    have : LocallyOfFinitePresentation (p ≫ inv (e.app i)) := by
      have := hp; infer_instance
    refine ⟨i, Y, p ≫ inv (e.app i), this, h, ?_⟩
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
    obtain ⟨i, Y, p, hp, h, hsq⟩ := this (Scheme.Spec.mapCone (coneOfCoconeLeftOp c'))
      (IsLimit.ofIsoLimit hc hcc) (inferInstanceAs (IsAffine (Spec Γ(c.pt, ⊤))))
      (g ≫ β.hom) ⟨c', rfl⟩
    refine ⟨i, Y, p, hp, h, ?_⟩
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
  refine ⟨i.unop, Spec T, Spec.map γ, HasRingHomProperty.Spec_iff.mpr hγ, Spec.map h, ?_⟩
  exact (isPullback_SpecMap_of_isPushout _ _ _ _ hpush).flip

end FinitePresentation

end AlgebraicGeometry
