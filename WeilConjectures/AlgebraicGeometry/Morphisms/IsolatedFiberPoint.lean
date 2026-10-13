/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Residue fields at isolated points of fibres

Source: Stacks Project, Morphisms, Lemmas 01TH and 01TG
(blueprint: `lem-weil-pbc-isolated-fibre-point-residue-finite`) and their stability under base
change.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

/-- An isolated point of a fibre of a locally finite type morphism has finite residue
field extension. Source: Stacks Project, Morphisms, Lemma 01TH, (2) implies (1),
and Lemma 01TG (blueprint: `lem-weil-pbc-isolated-fibre-point-residue-finite`). -/
theorem finiteDimensional_residueField_of_isOpen_singleton_asFiber
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X)
    (hx : IsOpen ({f.asFiber x} : Set (f.fiber (f x)))) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    FiniteDimensional (S.residueField (f x)) (X.residueField x) := by
  let := (f.residueFieldMap x).hom.toAlgebra
  have hq : (f.stalkMap x).hom.QuasiFinite :=
    (f.quasiFiniteAt_iff_isOpen_singleton_asFiber).mpr hx
  have hr : (X.residue x).hom.QuasiFinite :=
    RingHom.QuasiFinite.of_finite (RingHom.Finite.of_surjective _ (X.residue_surjective x))
  have hc := hr.comp hq
  rw [← CommRingCat.hom_comp, ← residue_residueFieldMap] at hc
  have hi := RingHom.QuasiFinite.of_comp hc
  let : Algebra.QuasiFinite (S.residueField (f x)) (X.residueField x) := hi
  exact Module.Finite.of_quasiFinite

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry

private theorem isOpen_singleton_of_field_pullback
    {k K : Type u} [Field k] [Field K] {F T : Scheme.{u}}
    (p : F ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (q : Spec (.of K) ⟶ Spec (.of k)) (h : T ⟶ F) (b : T ⟶ Spec (.of K))
    (hp : IsPullback h b p q) (z : T) (hz : IsOpen ({h z} : Set F)) :
    IsOpen ({z} : Set T) := by
  let U : F.Opens := ⟨{h z}, hz⟩
  have : Subsingleton U.toScheme := by
    change Subsingleton ↥({h z} : Set F)
    infer_instance
  have : LocallyQuasiFinite (U.ι ≫ p) :=
    LocallyQuasiFinite.of_injective (fun a a' _ ↦ Subsingleton.elim a a')
  have hpU := (isPullback_morphismRestrict h U).paste_vert hp
  have : LocallyQuasiFinite ((h ⁻¹ᵁ U).ι ≫ b) :=
    MorphismProperty.of_isPullback hpU inferInstance
  have : IsLocallyArtinian (h ⁻¹ᵁ U).toScheme :=
    IsLocallyArtinian.of_locallyQuasiFinite ((h ⁻¹ᵁ U).ι ≫ b)
  let zU : (h ⁻¹ᵁ U).toScheme := ⟨z, Set.mem_singleton _⟩
  simpa [Set.image_singleton, zU] using
    (h ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap ({zU} : Set (h ⁻¹ᵁ U).toScheme)
      (isOpen_discrete _)

/-- **Isolated points of fibres stay isolated after base change.** If `x` is an isolated point
of its fibre for a morphism `f` locally of finite type, then every point `x'` of `X ×_S S'` over
`x` is isolated in its fibre over `S'` (Stacks, Tags 01TM (1) and 01TH).
(blueprint: `lem-weil-pbc-isolated-fibre-point-base-change`) -/
theorem isOpen_singleton_asFiber_pullbackSnd
    {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (x' : ↥(pullback f g))
    (hx : IsOpen ({f.asFiber (pullback.fst f g x')} :
      Set (f.fiber (f (pullback.fst f g x'))))) :
    IsOpen ({(pullback.snd f g).asFiber x'} :
      Set ((pullback.snd f g).fiber ((pullback.snd f g) x'))) := by
  let y := pullback.snd f g x'
  let h : (pullback.snd f g).fiber y ⟶ f.fiber (g y) :=
    pullback.map (pullback.snd f g) (S'.fromSpecResidueField y) f
      (S.fromSpecResidueField (g y)) (pullback.fst f g)
      (Spec.map (g.residueFieldMap y)) g (pullback.condition.symm) (by simp)
  have hp := isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback f g) y
  have hc : f (pullback.fst f g x') = g y := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun a : pullback f g ⟶ S ↦ a x') pullback.condition
  have hz : IsOpen ({h ((pullback.snd f g).asFiber x')} : Set (f.fiber (g y))) := by
    have hxo : IsOpen ({⟨pullback.fst f g x', rfl⟩} :
        Set (f ⁻¹' {f (pullback.fst f g x')})) := by
      simpa [Set.image_singleton, Scheme.Hom.asFiber] using
        (f.fiberHomeo (f (pullback.fst f g x'))).isOpenMap _ hx
    rw [← (f.fiberHomeo (g y)).isOpen_image, Set.image_singleton]
    have hi : f.fiberι (g y) (h ((pullback.snd f g).asFiber x')) =
        pullback.fst f g x' := by
      have hh : h ≫ f.fiberι (g y) =
          (pullback.snd f g).fiberι y ≫ pullback.fst f g := pullback.lift_fst _ _ _
      simpa only [y, Scheme.Hom.comp_apply, Scheme.Hom.fiberι_asFiber] using
        congrArg (fun a : (pullback.snd f g).fiber y ⟶ X ↦
          a ((pullback.snd f g).asFiber x')) hh
    have hpoint : f.fiberHomeo (g y) (h ((pullback.snd f g).asFiber x')) =
        ⟨pullback.fst f g x', hc⟩ := Subtype.ext hi
    rw [hpoint]
    let e := Homeomorph.setCongr
      (show f ⁻¹' {f (pullback.fst f g x')} = f ⁻¹' {g y} by rw [hc])
    have hepoint : e ⟨pullback.fst f g x', rfl⟩ = ⟨pullback.fst f g x', hc⟩ := by
      apply Subtype.ext
      simp [e, Homeomorph.setCongr]
    simpa only [Set.image_singleton, hepoint] using e.isOpenMap _ hxo
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (g y)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField (g y))))
  exact isOpen_singleton_of_field_pullback (f.fiberToSpecResidueField (g y))
    (Spec.map (g.residueFieldMap y)) h ((pullback.snd f g).fiberToSpecResidueField y)
    hp ((pullback.snd f g).asFiber x') hz

end AlgebraicGeometry
