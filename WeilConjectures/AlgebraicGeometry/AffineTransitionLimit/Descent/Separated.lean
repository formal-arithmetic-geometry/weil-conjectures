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
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.Descent.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.Descent.FinitePresentation
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# Separated finite-stage models

A finite presentation model of a separated morphism to a cofiltered limit is separated at a later
stage, so a separated scheme of finite presentation over the limit has a separated finite-stage
model (`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`,
Stacks Project Tag 01ZQ). Morphisms between schemes of finite presentation over the limit
descend as well (`AlgebraicGeometry.Scheme.exists_pullback_hom_of_isLimit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
section FinitePresentationDescent
section Descent

set_option backward.defeqAttrib.useBackward true
variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
  [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]

include hc in
/-- **A finite-presentation model of a separated morphism is separated at a later stage.**

If `X ⟶ lim Dⱼ` is separated and `p : Y ⟶ D_k` is a finite presentation model of it at the
stage `k`, then the base change of the model to some later stage `k' ⟶ k` is separated.
(Blueprint: `lemma:nagata-separated-descent-stage-exists`.) -/
lemma Scheme.exists_isSeparated_pullback_snd {k : I} [CompactSpace (D.obj k)]
    [QuasiSeparatedSpace (D.obj k)] {Y : Scheme.{u}} {p : Y ⟶ D.obj k}
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    {X : Scheme.{u}} {g : X ⟶ c.pt} [IsSeparated g] {h : X ⟶ Y}
    (H : IsPullback h g p (c.π.app k)) :
    ∃ (k' : I) (f : k' ⟶ k), IsSeparated (pullback.snd p (D.map f)) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated p
  have : QuasiCompact (pullback.snd p p) := MorphismProperty.pullback_snd _ _ ‹_›
  have : QuasiSeparated (pullback.snd p p) := MorphismProperty.pullback_snd _ _ ‹_›
  have : CompactSpace ↥(pullback p p) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd p p)
  have : QuasiSeparatedSpace ↥(pullback p p) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd p p)
  -- The diagonal of the model, as a morphism of schemes over the stage.
  let γ : Over.mk p ⟶ Over.mk (pullback.snd p p ≫ p) :=
    Over.homMk (pullback.diagonal p) (by simp)
  have : LocallyOfFinitePresentation γ.left :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.diagonal p))
  have : QuasiCompact γ.left := inferInstanceAs (QuasiCompact (pullback.diagonal p))
  have : QuasiSeparated γ.left := inferInstanceAs (QuasiSeparated (pullback.diagonal p))
  -- The base change of the model to the limit is separated, being isomorphic to `g`.
  have hsep : IsSeparated (pullback.fst (c.π.app k) p) := by
    refine (MorphismProperty.arrow_mk_iso_iff @IsSeparated
      (Arrow.isoMk (H.isoPullback ≪≫ pullbackSymmetry p (c.π.app k)) (Iso.refl _) ?_)).mp
      ‹IsSeparated g›
    simp
  -- Hence the base change of the diagonal to the limit is a closed immersion.
  have hlim : IsClosedImmersion (pullback.diagonal (pullback.fst (c.π.app k) p)) :=
    inferInstance
  rw [diagonal_pullback_fst] at hlim
  have hS : IsClosedImmersion ((Over.pullback (c.π.app k)).map γ).left :=
    (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ _).mp
      ((MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion _ _).mp hlim)
  have : CompactSpace ↥((Over.mk (pullback.snd p p ≫ p) : Over (D.obj k)).left) :=
    ‹CompactSpace ↥(pullback p p)›
  have : QuasiSeparatedSpace ↥((Over.mk (pullback.snd p p ≫ p) : Over (D.obj k)).left) :=
    ‹QuasiSeparatedSpace ↥(pullback p p)›
  obtain ⟨k', f, tail⟩ := Scheme.exists_isClosedImmersion_overPullbackMap hc γ hS
  have htail := tail (𝟙 k')
  rw [Category.id_comp] at htail
  -- Hence the diagonal of the stage model is a closed immersion.
  have hdiag : IsClosedImmersion (pullback.diagonal (pullback.fst (D.map f) p)) := by
    rw [diagonal_pullback_fst]
    exact (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion _ _).mpr
      ((MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ _).mpr htail)
  refine ⟨k', f, ?_⟩
  have : IsSeparated (pullback.fst (D.map f) p) := ⟨hdiag⟩
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsSeparated
    (pullbackSymmetry (D.map f) p).hom, pullbackSymmetry_hom_comp_snd]
  infer_instance

include hc in
/-- **A separated morphism of finite presentation over the limit descends to a finite stage**
(Stacks 01ZQ).

Let `{Dⱼ}` be a cofiltered inverse system of quasi-compact quasi-separated schemes with affine
transition maps and let `X` be separated and of finite presentation over `lim Dⱼ`. Then `X` is
the base change of a scheme that is separated and of finite presentation over one of the
stages. (Blueprint: `lemma:nagata-separated-eventually`.) -/
@[stacks 01ZQ]
theorem Scheme.exists_isPullback_of_finitePresentation_of_isSeparated
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    {X : Scheme.{u}} (g : X ⟶ c.pt)
    [LocallyOfFinitePresentation g] [QuasiCompact g] [IsSeparated g] :
    ∃ (i : I) (Y : Scheme.{u}) (p : Y ⟶ D.obj i) (_ : LocallyOfFinitePresentation p)
      (_ : QuasiCompact p) (_ : IsSeparated p) (h : X ⟶ Y),
      IsPullback h g p (c.π.app i) := by
  obtain ⟨i, Y, p, hp₁, hp₂, hp₃, h, H⟩ := Scheme.exists_isPullback_of_finitePresentation hc g
  have := hp₁; have := hp₂; have := hp₃
  obtain ⟨i', f, hsep⟩ := Scheme.exists_isSeparated_pullback_snd hc H
  exact ⟨i', pullback p (D.map f), pullback.snd p (D.map f), inferInstance, inferInstance,
    hsep, isPullbackLift D c f H, isPullback_isPullbackLift f H⟩

include hc in
/-- **Morphisms between schemes of finite presentation descend to a finite stage**
(Stacks Project Tag 01ZM, part (2)). Let `{Dⱼ}` be a cofiltered inverse system of quasi-compact
quasi-separated schemes with affine transition maps, and let `V`, `W` be of finite presentation
over a stage `Dᵢ`. Every morphism `V ×_{Dᵢ} lim Dⱼ ⟶ W ×_{Dᵢ} lim Dⱼ` over `lim Dⱼ`, given here by
its composite `ψ` with the projection to `W`, is the base change of a morphism
`V ×_{Dᵢ} Dⱼ ⟶ W ×_{Dᵢ} Dⱼ` over some later stage `Dⱼ`.

Part (1) is `AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation`, part (3) is
`AlgebraicGeometry.Scheme.exists_pullback_fst_comp_eq_of_isLimit`.

(blueprint: `thm-pd-spreading-out`) -/
@[stacks 01ZM]
theorem Scheme.exists_pullback_hom_of_isLimit [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {i : I} {V W : Scheme.{u}} (pV : V ⟶ D.obj i)
    (pW : W ⟶ D.obj i) [LocallyOfFinitePresentation pV] [QuasiCompact pV] [QuasiSeparated pV]
    [LocallyOfFinitePresentation pW] [QuasiCompact pW] [QuasiSeparated pW]
    (ψ : pullback pV (c.π.app i) ⟶ W) (hψ : ψ ≫ pW = pullback.fst pV (c.π.app i) ≫ pV) :
    ∃ (j : I) (f : j ⟶ i) (ψj : pullback pV (D.map f) ⟶ W),
      ψj ≫ pW = pullback.fst pV (D.map f) ≫ pV ∧
        pullback.map pV (c.π.app i) pV (D.map f) (𝟙 V) (c.π.app j) (𝟙 _) (by simp)
          (by simp) ≫ ψj = ψ := by
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace pV
  have : QuasiSeparatedSpace V := quasiSeparatedSpace_of_quasiSeparated pV
  obtain ⟨j, g, hga, hgt⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (baseChangeDiagram D pV) (baseChangeDiagramStructure D pV) pW (baseChangeCone D c pV)
    (isLimitBaseChangeCone D c pV hc) ψ (by
      ext j
      change ((baseChangeCone D c pV).π.app j ≫ pullback.fst pV (D.map j.hom)) ≫ pV = ψ ≫ pW
      rw [baseChangeCone_π_app_fst, hψ])
  exact ⟨j.left, j.hom, g, hgt, hga⟩

include hc in
/-- **Equalities of morphisms between schemes of finite presentation descend to a finite stage**
(Stacks Project Tag 01ZM, part (3)). Let `{Dⱼ}` be a cofiltered inverse system of quasi-compact
quasi-separated schemes with affine transition maps, let `V`, `W` be of finite presentation over a
stage `Dᵢ` and let `ψ χ : V ⟶ W` be morphisms over `Dᵢ` whose base changes to `lim Dⱼ` agree.
Then their base changes to some later stage `Dⱼ` agree.

(blueprint: `thm-pd-spreading-out`) -/
@[stacks 01ZM]
theorem Scheme.exists_pullback_fst_comp_eq_of_isLimit [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {i : I} {V W : Scheme.{u}} (pV : V ⟶ D.obj i)
    (pW : W ⟶ D.obj i) [LocallyOfFinitePresentation pV] [QuasiCompact pV] [QuasiSeparated pV]
    [LocallyOfFinitePresentation pW] [QuasiCompact pW] [QuasiSeparated pW] (ψ χ : V ⟶ W)
    (hψ : ψ ≫ pW = pV) (hχ : χ ≫ pW = pV)
    (h : pullback.fst pV (c.π.app i) ≫ ψ = pullback.fst pV (c.π.app i) ≫ χ) :
    ∃ (j : I) (f : j ⟶ i), pullback.fst pV (D.map f) ≫ ψ = pullback.fst pV (D.map f) ≫ χ := by
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace pV
  have : QuasiSeparatedSpace V := quasiSeparatedSpace_of_quasiSeparated pV
  obtain ⟨k, hk, heq⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (baseChangeDiagram D pV) (baseChangeDiagramStructure D pV) pW (baseChangeCone D c pV)
    (isLimitBaseChangeCone D c pV hc) (i := Over.mk (𝟙 i))
    (pullback.fst _ _ ≫ ψ) (pullback.fst _ _ ≫ χ)
    (by simp [baseChangeDiagramStructure, hψ]) (by simp [baseChangeDiagramStructure, hχ])
    (by rw [baseChangeCone_π_app_fst_assoc, baseChangeCone_π_app_fst_assoc, h])
  refine ⟨k.left, k.hom, ?_⟩
  simpa using heq

end Descent

end FinitePresentationDescent

end AlgebraicGeometry
