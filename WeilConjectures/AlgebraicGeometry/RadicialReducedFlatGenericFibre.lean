/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

import WeilConjectures.AlgebraicGeometry.RadicialSeparatingGenericField
import WeilConjectures.FieldTheory.SeparablyGeneratedTensorReduced

/-! # The radicial extension step for a reduced affine flat family

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
* [Stacks Project, Tag 030R](https://stacks.math.columbia.edu/tag/030R)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace AlgebraicGeometry

private theorem geometricallyReduced_spec_of_isSeparablyGenerated
    (k F : Type u) [Field k] [Field F] [Algebra k F]
    (hF : Algebra.IsSeparablyGenerated k F) :
    GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap k F))) := by
  refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro K _ _
  have : _root_.IsReduced (TensorProduct k F K) :=
    Algebra.isReduced_tensorProduct_of_isSeparablyGenerated k F K hF
  exact isReduced_of_isOpenImmersion (pullbackSpecIso k F K).hom

private theorem geometricallyReduced_of_schemeTheoreticallyDominant
    {k : Type u} [Field k] {W X : Scheme.{u}}
    (h : W ⟶ X) (p : X ⟶ Spec (.of k))
    [IsSchemeTheoreticallyDominant h] [QuasiCompact h]
    (hred : GeometricallyReduced (h ≫ p)) : GeometricallyReduced p := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro K _ y
  let a := pullback.fst p y
  have : Flat a := inferInstance
  have : IsReduced (pullback h a) := by
    let e := pullbackRightPullbackFstIso p y h
    have : IsReduced (pullback (h ≫ p) y) :=
      hred.geometrically_isReduced _ _ _ (.of_hasPullback _ _)
    exact isReduced_of_isOpenImmersion e.hom
  exact IsSchemeTheoreticallyDominant.isReduced (pullback.snd h a)

/-- After the first flat shrinking, a finite radicial extension of the base makes
its reduced pullback geometrically reduced at the generic point. -/
theorem exists_radicial_reduced_flat_generic_fibre
    {Z S : Scheme.{u}} [IsAffine Z] [IsReduced Z] [IsAffine S] [IsIntegral S]
    (g : Z ⟶ S) [Flat g] [LocallyOfFinitePresentation g]
    (η : S) (hη : IsGenericPoint η Set.univ)
    (hgeom : GeometricallyIrreducible (g.fiberToSpecResidueField η)) :
    ∃ (S' : Scheme.{u}) (q : S' ⟶ S),
      IsAffine S' ∧ IsIntegral S' ∧ IsUniversalHomeomorphism q ∧
      ∃ η' : S', IsGenericPoint η' Set.univ ∧ q η' = η ∧
        GeometricallyReduced
          (((pullback g q).nilradical.subschemeι ≫ pullback.snd g q).fiberToSpecResidueField
            η') := by
  obtain ⟨S', q, hS', hI', hq', η', hqη', F, hF, aF, h, hdom, hqc, hsep, heq⟩ :=
    exists_radicial_separating_generic_field g η hη hgeom
  let : Field F := hF
  let : Algebra (S'.residueField η') F := aF
  have hred : GeometricallyReduced
      (((pullback g q).nilradical.subschemeι ≫ pullback.snd g q).fiberToSpecResidueField
        η') := by
    apply geometricallyReduced_of_schemeTheoreticallyDominant h
    rw [heq]
    exact geometricallyReduced_spec_of_isSeparablyGenerated _ _ hsep
  let e := IsUniversalHomeomorphism.homeomorph q
  have hη' : IsGenericPoint η' Set.univ := by
    rw [isGenericPoint_iff_specializes]
    intro y
    simp only [Set.mem_univ, iff_true]
    apply e.isInducing.specializes_iff.mp
    change q η' ⤳ q y
    rw [hqη']
    exact hη.specializes (Set.mem_univ _)
  exact ⟨S', q, hS', hI', hq', η', hη', hqη', hred⟩

end AlgebraicGeometry
