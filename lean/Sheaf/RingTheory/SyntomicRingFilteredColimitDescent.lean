/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q135
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Order.Directed
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
import Sheaf.Paper.NoetherianApproximation
import Sheaf.Paper.RelativeGlobalCompleteIntersectionBaseChange
import Sheaf.RingTheory.FilteredColimitFiniteData
import WeilConjectures.RingTheory.FinitePresentationModelStage
import WeilConjectures.RingTheory.RelativeGlobalCompleteIntersectionFlat
import Sheaf.RingTheory.SyntomicAtPrimeRelativeGlobalCompleteIntersection
import WeilConjectures.Algebra.LimitFinitePresentation.Colimits
import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation

/-!
# Descent of syntomic ring maps along filtered colimits

Source: Stacks Project, Algebra, Tag 0C33 (lemma-colimit-lci), syntomic case
(blueprint: lem-trf-syntomic-ring-filtered-colimit-descent).

## Main statements

* `exists_syntomic_ring_filtered_colimit_stage` states descent of flat finite-presentation
  maps with local complete-intersection fibres to one stage of a directed colimit.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Algebra

/-- Scalar extension of a ring along a specified ring homomorphism.
Source: Stacks Project, Algebra, Tag 0C33 (lemma-colimit-lci), syntomic case.
(blueprint: lem-trf-syntomic-ring-filtered-colimit-descent). -/
def tensorBaseChange (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
    (f : R →+* S) [Algebra R A] : Type u := by
  letI : Algebra R S := f.toAlgebra
  exact TensorProduct R S A

/-- The tensor base change carries its canonical commutative-ring structure.
Source: Stacks Project, Algebra, Tag 0C33 (lemma-colimit-lci), syntomic case.
(blueprint: lem-trf-syntomic-ring-filtered-colimit-descent). -/
instance tensorBaseChange.instCommRing (R S A : Type u) [CommRing R] [CommRing S]
    [CommRing A] (f : R →+* S) [Algebra R A] : CommRing (tensorBaseChange R S A f) := by
  letI : Algebra R S := f.toAlgebra
  change CommRing (TensorProduct R S A)
  exact inferInstance

/-- The scalar extension of a ring map along a specified ring homomorphism.
Source: Stacks Project, Algebra, Tag 0C33 (lemma-colimit-lci), syntomic case.
(blueprint: lem-trf-syntomic-ring-filtered-colimit-descent). -/
def tensorBaseChangeMap (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A]
    [CommRing B] (f : R →+* S) [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B) :
    tensorBaseChange R S A f →+* tensorBaseChange R S B f := by
  letI : Algebra R S := f.toAlgebra
  change TensorProduct R S A →+* TensorProduct R S B
  exact (Algebra.TensorProduct.map (AlgHom.id S S) φ).toRingHom

/-- The residue fibre ring of a ring map at a prime of its source.
Source: Stacks Project, Algebra, Tag 0C33 (lemma-colimit-lci), syntomic case.
(blueprint: lem-trf-syntomic-ring-filtered-colimit-descent). -/
def residueFiber (B C : Type u) [CommRing B] [CommRing C] (f : B →+* C)
    (p : Ideal B) [p.IsPrime] : Type u := by
  letI : Algebra B C := f.toAlgebra
  exact Ideal.Fiber p C

/-- Local complete intersection of the residue fibre, including its finite-type instance.
Source: Stacks Project, Algebra, Tag 0C33 (lemma-colimit-lci), syntomic case, with Tag 00SL.
(blueprint: lem-trf-syntomic-ring-filtered-colimit-descent). -/
def residueFiberIsLocalCompleteIntersection (B C : Type u) [CommRing B] [CommRing C]
    (f : B →+* C) (p : Ideal B) [p.IsPrime] : Prop := by
  letI : Algebra B C := f.toAlgebra
  letI : Algebra (Ideal.ResidueField p) (Ideal.Fiber p C) := inferInstance
  exact ∃ (_ : Algebra.FiniteType (Ideal.ResidueField p) (Ideal.Fiber p C)),
    @IsLocalCompleteIntersection (Ideal.ResidueField p) (Ideal.Fiber p C) _ _ _ ‹_›

/-- The three properties required of a scalar extension at one stage.
Source: Stacks Project, Algebra, Tag 0C33 (lemma-colimit-lci), syntomic case, with Tag 00SL.
(blueprint: lem-trf-syntomic-ring-filtered-colimit-descent). -/
def stageSyntomic {I : Type u} [Preorder I] (F : I ⥤ CommRingCat.{u})
    (i₀ i : I) (h : i₀ ≤ i) (B₀ C₀ : Type u) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀) : Prop := by
  let fᵢ : (F.obj i₀) →+* (F.obj i) := (F.map (homOfLE h)).hom
  let Bᵢ := tensorBaseChange (F.obj i₀) (F.obj i) B₀ fᵢ
  let Cᵢ := tensorBaseChange (F.obj i₀) (F.obj i) C₀ fᵢ
  let φᵢ := tensorBaseChangeMap (F.obj i₀) (F.obj i) B₀ C₀ fᵢ φ₀
  exact RingHom.Flat φᵢ ∧ RingHom.FinitePresentation φᵢ ∧
    ∀ (pᵢ : Ideal Bᵢ) [pᵢ.IsPrime],
      residueFiberIsLocalCompleteIntersection Bᵢ Cᵢ φᵢ pᵢ

/-- The canonical scalar-extension map at the colimit stage.
Source: Stacks Project, Algebra, Tag 0C33 (lemma-colimit-lci), syntomic case.
(blueprint: lem-trf-syntomic-ring-filtered-colimit-descent). -/
noncomputable def colimitBaseChangeMap {I : Type u} [Preorder I] (F : I ⥤ CommRingCat.{u})
    [HasColimit F] (i₀ : I) (B₀ C₀ : Type u) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀) :
    tensorBaseChange (F.obj i₀) ((colimit F : CommRingCat.{u}) : Type u) B₀
        (colimit.ι F i₀).hom →+*
      tensorBaseChange (F.obj i₀) ((colimit F : CommRingCat.{u}) : Type u) C₀
        (colimit.ι F i₀).hom :=
  tensorBaseChangeMap (F.obj i₀) ((colimit F : CommRingCat.{u}) : Type u) B₀ C₀
    (colimit.ι F i₀).hom φ₀

/--
(blueprint: lem-trf-syntomic-ring-filtered-colimit-descent) Stacks Project, Algebra,
Tag 0C33 (lemma-colimit-lci), syntomic case. A flat, finitely presented ring map whose
residue fibres are local complete intersections descends to a stage of a directed colimit.

Proof plan (blueprint steps): (1) use tensor pushout and finite-presentation colimit
lemmas to identify the colimits of the tensor base changes; (2) apply the flat-local
syntomic presentation criterion at each prime of the colimit; (3) choose a finite
principal-open complete-intersection cover and its unit-ideal relation; (4) lift the
finite relation to one stage by the filtered finite-data lemma; (5) approximate each
relative complete-intersection chart over a finitely presented coefficient ring; (6)
localize the finite stage and identify its base change with the chart; (7) descend each
chart comparison by the finite-presentation model-stage lemma; (8) pass to a common upper
bound and preserve the unit relation; (9) glue chart flatness using the local flat-map
criterion; (10) base change the charts to every residue fibre and use the defining local
complete-intersection predicate.  The named proof dependencies are the tensor pushout,
finite-presentation colimit/base-change, flat-local, syntomic-prime, finite-data,
relative-global-complete-intersection, localization, model-stage, and flat-map-local
criterion nodes listed in the DAG.
-/
theorem exists_syntomic_ring_filtered_colimit_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F] (i₀ : I)
    (B₀ C₀ : Type u) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀)
    (hφ₀ : RingHom.FinitePresentation φ₀.toRingHom)
    (hφ : RingHom.FinitePresentation
      (colimitBaseChangeMap F i₀ B₀ C₀ φ₀))
    (hflat : RingHom.Flat (colimitBaseChangeMap F i₀ B₀ C₀ φ₀))
    (hfibre : ∀ (p : Ideal (tensorBaseChange (F.obj i₀)
        ((colimit F : CommRingCat.{u}) : Type u) B₀ (colimit.ι F i₀).hom))
      [p.IsPrime],
      residueFiberIsLocalCompleteIntersection
        (tensorBaseChange (F.obj i₀) ((colimit F : CommRingCat.{u}) : Type u) B₀
          (colimit.ι F i₀).hom)
        (tensorBaseChange (F.obj i₀) ((colimit F : CommRingCat.{u}) : Type u) C₀
          (colimit.ι F i₀).hom)
        (colimitBaseChangeMap F i₀ B₀ C₀ φ₀) p) :
    ∃ (i : I) (h : i₀ ≤ i), stageSyntomic F i₀ i h B₀ C₀ φ₀ := by
  sorry

end Algebra
