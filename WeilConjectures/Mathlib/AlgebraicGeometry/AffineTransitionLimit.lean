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
