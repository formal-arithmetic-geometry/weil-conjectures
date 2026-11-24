/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.ProperFinitePresentationClosedLimitEnvelope

/-! # Proper schemes as limits of proper finitely presented schemes

## References

* [Stacks Project, Tag 09ZR](https://stacks.math.columbia.edu/tag/09ZR)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A proper scheme over a qcqs base is a directed inverse limit of proper finitely
presented schemes over that base, with closed immersions as transitions and projections.
In particular it embeds as a closed subscheme of a proper finitely presented scheme
(Stacks, Tag 09ZR). -/
theorem exists_proper_finitePresentation_closedImmersion_limit
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    (∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : Iᵒᵖ ⥤ Scheme.{u}) (p : D ⟶ (Functor.const Iᵒᵖ).obj S)
      (π : (Functor.const Iᵒᵖ).obj X ⟶ D),
      (∀ i : Iᵒᵖ, IsProper (p.app i) ∧ LocallyOfFinitePresentation (p.app i) ∧
        QuasiCompact (p.app i) ∧ QuasiSeparated (p.app i)) ∧
      (∀ (i j : Iᵒᵖ) (a : i ⟶ j), IsClosedImmersion (D.map a)) ∧
      (∀ i : Iᵒᵖ, IsClosedImmersion (π.app i) ∧ π.app i ≫ p.app i = f) ∧
      Nonempty (IsLimit (Cone.mk X π))) ∧
    (∃ (Y : Scheme.{u}) (i : X ⟶ Y) (g : Y ⟶ S),
      IsClosedImmersion i ∧ IsProper g ∧ LocallyOfFinitePresentation g ∧
        QuasiCompact g ∧ QuasiSeparated g ∧ i ≫ g = f) := by
  obtain ⟨Y, i, g, hi, hg, hfp, hqc, hqs, hw⟩ :=
    exists_proper_finitePresentation_closedImmersion_envelope f
  have := hi
  have := hg
  have := hfp
  have := hqc
  have := hqs
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated g
  refine ⟨?_, Y, i, g, hi, hg, hfp, hqc, hqs, hw⟩
  let p : i.ker.fgSubDiagram ⟶ (Functor.const _).obj S :=
    { app J := (J.unop : Y.IdealSheafData).subschemeι ≫ g
      naturality := by
        intro J J' a
        simp }
  let π := (Functor.const _).map i.toImage ≫ i.ker.fgSubCone.π
  refine ⟨i.ker.FGSub, inferInstance, inferInstance, inferInstance,
    i.ker.fgSubDiagram, p, π, ?_, ?_, ?_, ?_⟩
  · intro J
    change IsProper ((J.unop : Y.IdealSheafData).subschemeι ≫ g) ∧
      LocallyOfFinitePresentation ((J.unop : Y.IdealSheafData).subschemeι ≫ g) ∧
      QuasiCompact ((J.unop : Y.IdealSheafData).subschemeι ≫ g) ∧
      QuasiSeparated ((J.unop : Y.IdealSheafData).subschemeι ≫ g)
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  · intro J J' a
    infer_instance
  · intro J
    constructor
    · change IsClosedImmersion (i.toImage ≫ i.ker.fgSubCone.π.app J)
      infer_instance
    · change (i.toImage ≫ i.ker.fgSubCone.π.app J) ≫
        (J.unop : Y.IdealSheafData).subschemeι ≫ g = f
      simpa using hw
  · exact ⟨i.ker.isLimitFgSubCone.ofIsoLimit
      (Cone.ext (asIso i.toImage).symm fun J ↦ by simp [π])⟩

end AlgebraicGeometry
