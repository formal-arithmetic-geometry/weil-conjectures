/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.FieldTheory.SeparableExtension

import WeilConjectures.FieldTheory.MakeSeparablyGenerated
import WeilConjectures.AlgebraicGeometry.GenericFibreDominantField
import WeilConjectures.AlgebraicGeometry.PurelyInseparableGenericBaseSpread
import WeilConjectures.AlgebraicGeometry.ReducedGenericFibreFieldEmbedding

/-! # A separating generic field after a radicial base extension

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
* [Stacks Project, Tag 030R](https://stacks.math.columbia.edu/tag/030R)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace AlgebraicGeometry

/-- The reduced generic pullback embeds in a separably generated field after a radicial
base extension. No geometric reducedness of the fibre is asserted here. -/
theorem exists_radicial_separating_generic_field
    {Z S : Scheme.{u}} [IsAffine Z] [IsReduced Z] [IsAffine S] [IsIntegral S]
    (g : Z ⟶ S) [Flat g] [LocallyOfFinitePresentation g]
    (η : S) (hη : IsGenericPoint η Set.univ)
    (hgeom : GeometricallyIrreducible (g.fiberToSpecResidueField η)) :
    ∃ (S' : Scheme.{u}) (q : S' ⟶ S),
      IsAffine S' ∧ IsIntegral S' ∧ IsUniversalHomeomorphism q ∧
      ∃ η' : S', q η' = η ∧
        ∃ (F : Type u) (hF : Field F) (aF : Algebra (S'.residueField η') F),
          letI := hF
          letI := aF
          ∃ h : Spec (.of F) ⟶
              ((pullback g q).nilradical.subschemeι ≫ pullback.snd g q).fiber η',
            IsSchemeTheoreticallyDominant h ∧ QuasiCompact h ∧
            Algebra.IsSeparablyGenerated (S'.residueField η') F ∧
            h ≫ ((pullback g q).nilradical.subschemeι ≫
              pullback.snd g q).fiberToSpecResidueField η' =
                Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField η') F)) := by
  classical
  obtain ⟨L, hL, aL, hfg, j, hj, hjbase⟩ :=
    exists_generic_fibre_dominant_field g η hη hgeom
  let _ := hL
  let _ := aL
  obtain ⟨k', hk', akk', E, hE, aLE, akE, hfin, hpure, _, _, hsep, hsquare⟩ :=
    FieldExtension.exists_finitePurelyInseparable_separablyGenerated
      (S.residueField η) L hfg
  let _ := hk'
  let _ := akk'
  let _ := hE
  let _ := aLE
  let _ := akE
  have _ := hfin
  have _ := hpure
  obtain ⟨S', q, hA, hI, hU, η', hq, hη', e, he⟩ :=
    exists_purely_inseparable_generic_base_spread η hη k'
  have _ := hA
  have _ := hI
  obtain ⟨aE, h, hdom, hsep', hbase⟩ :=
    exists_reduced_generic_fibre_field_embedding g q η η' hq hη' L k' E
      j hj hjbase e he hsquare hsep
  let _ := aE
  exact ⟨S', q, hA, hI, hU, η', hq, E, hE, aE, h, hdom, inferInstance, hsep', hbase⟩

end AlgebraicGeometry
