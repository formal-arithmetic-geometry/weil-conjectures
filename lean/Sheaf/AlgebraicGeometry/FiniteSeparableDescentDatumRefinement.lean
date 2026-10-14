/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.IntermediateField.Basic
import Sheaf.AlgebraicGeometry.FiniteSeparableUniversalTransportModel
import Sheaf.AlgebraicGeometry.DescentDatumFromUniversalTransport
import WeilConjectures.AlgebraicGeometry.BaseChangeNorm

/-!
# Spreading a descent datum on an existing finite model

Source: Stacks Project, Tag 01ZM (2), (3); Tag 023V.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

/-- Enlarge a finite separable model to carry a descended transport datum.

Proof: spread the universal transport morphism over the double base product. It is natural
 by pullback functoriality. The identity and cocycle equations are checked after successively
 lifting the one or three base maps along `Spec ks → Spec L`. These pullbacks are faithfully
 flat, hence epimorphisms, so their cancellation proves the equations over `L` itself.

Source: Stacks Project, Tags 01ZM (2), 023V and 02VW.
(blueprint: lem-pd-finite-separable-datum-refinement) -/
theorem exists_finiteSeparable_descentDatum_refinement
    {k ks : Type u} [Field k] [Field ks] [Algebra k ks] [IsSepClosure k ks]
    (K : IntermediateField k ks) [FiniteDimensional k K] [Algebra.IsSeparable k K]
    (JK : Over (Spec (.of K))) [LocallyOfFinitePresentation JK.hom]
    [QuasiCompact JK.hom] [QuasiSeparated JK.hom]
    (Js : Over (Spec (.of ks))) (q : Js.left ⟶ JK.left)
    (hq : IsPullback q Js.hom JK.hom (Spec.map (CommRingCat.ofHom (algebraMap K ks))))
    (E : Over.DescentDatum (Spec.map (CommRingCat.ofHom (algebraMap k ks))) Js) :
    ∃ (L : IntermediateField k ks), FiniteDimensional k L ∧ Algebra.IsSeparable k L ∧
      ∃ (hKL : K ≤ L) (JL : Over (Spec (.of L))) (r : JL.left ⟶ JK.left),
        IsPullback r JL.hom JK.hom
          (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion hKL).toRingHom)) ∧
        ∃ (qL : Js.left ⟶ JL.left)
          (hqL : IsPullback qL Js.hom JL.hom
            (Spec.map (CommRingCat.ofHom (algebraMap L ks))))
          (D : Over.DescentDatum (Spec.map (CommRingCat.ofHom (algebraMap k L))) JL),
          qL ≫ r = q ∧ D.IsBaseChange (by
            rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])
            hqL.w E := by
  obtain ⟨L, hL, hLs, hKL, JL, r, hr, qL, hqL, t, hcomp, ht, hcompat⟩ :=
    exists_finiteSeparable_universalTransportModel K JK Js q hq E
  let ι := Spec.map (CommRingCat.ofHom (algebraMap L ks))
  have : Flat ι := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Surjective ι := surjective_specMap_algebraMap_of_field
  have hp : ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) =
      Spec.map (CommRingCat.ofHom (algebraMap k ks)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  obtain ⟨D, hD⟩ :=
    exists_descentDatum_of_universalTransport hp JL Js qL hqL E t ht hcompat
  exact ⟨L, hL, hLs, hKL, JL, r, hr, qL, hqL, D, hcomp, hD⟩

end AlgebraicGeometry
