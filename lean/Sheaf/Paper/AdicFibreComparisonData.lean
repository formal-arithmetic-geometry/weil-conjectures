/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.Paper.AdicStratifiedPullbackInterface
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.Constructible

/-! # Normalized fibre comparison data

Source: Bhatt--Scholze 6.8.4, 6.8.14 and 6.8.15
(blueprint: def-per-adic-fibre-comparison-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.AdicFibreComparison
open ContinuousRational

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]
  (R : ContinuousRational.Family.{u} l)

/-- The normalized finite-stage fibres are the dependency's intrinsic, lattice-normalized
fibres, simultaneously at every scheme and coefficient field.
Source: BS 6.8.4 (blueprint: def-per-adic-fibre-comparison-data). -/
abbrev Fibres := ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : FiniteTypeBase k),
  NormalizedFibre.Assertions l E (base l X) (R.realization E (base l X))

variable (E L : Type u) [Field E] [Field L] [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]

/-- Finite scalar extension preserves the actual localized heart.
Source: BS 6.8.14 (blueprint: def-per-adic-fibre-comparison-data).
Proof: the finite integral extension is finite free. Its derived tensor is exact, preserves
both standard halves and commutes with localization; hence it preserves their intersection. -/
theorem scalarHeart (i : E →ₐ[ℚ_[l]] L) (X : FiniteTypeBase k)
    (F : NormalizedFibre.Heart l E (base l X)) :
    (localizedT l L (base l X)).heart
      ((pbcRationalScalarExtension l E L i X.scheme
        (base l X).dimension (base l X).prime_unit).obj F.obj) := by
  sorry

/-- Literal restriction of the specified finite scalar functor to the full heart.
Source: BS 6.8.14 (blueprint: def-per-adic-fibre-comparison-data). -/
def heartScalar (i : E →ₐ[ℚ_[l]] L) (X : FiniteTypeBase k) :
    NormalizedFibre.Heart l E (base l X) ⥤ NormalizedFibre.Heart l L (base l X) :=
  ObjectProperty.lift (localizedT l L (base l X)).heart
    ((localizedT l E (base l X)).heart.ι ⋙ pbcRationalScalarExtension l E L i X.scheme
      (base l X).dimension (base l X).prime_unit) (scalarHeart l E L i X)

/-- The geometric point underneath a geometric morphism, using the recorded residue-field
identification. Source: BS 6.8.6 (blueprint: def-per-adic-fibre-comparison-data). -/
def underlying {X : Scheme.{u}} (κ : Type u) [Field κ] (x : Spec (.of κ) ⟶ X) : X :=
  (SpecToEquivOfField κ X x).1

/-- Rank-locus refinement, including the empty stratification and rank zero.
Source: BS 6.8.3, 6.8.6 (blueprint: def-per-adic-fibre-comparison-data). -/
structure RankStratification (X : Scheme.{u}) where
  strata : FiniteLocallyClosedStratification X
  rank : X → ℕ
  locally_constant : ∀ j : Fin strata.n, IsLocallyConstant (rank ∘ strata.immersion j)
  finite_image : (Set.range rank).Finite
  refinement : FiniteLocallyClosedStratification X
  refines : ∀ j : Fin refinement.n, ∃ i : Fin strata.n,
    refinement.stratum j ⊆ strata.stratum i
  constant_rank : ∀ j : Fin refinement.n, ∃ r : ℕ,
    ∀ x ∈ refinement.stratum j, rank x = r
  constructible : Topology.IsConstructible {x | rank x ≠ 0}
  positive : {x | rank x ≠ 0} = ⋃ j : Fin refinement.n,
    {x | x ∈ refinement.stratum j ∧ 0 < rank x}

/-- Finite-stage rank is the normalized fibre dimension, on a lisse stratification.
The comparison over a single underlying point is existential, with no chosen path.
Source: BS 6.8.4--6.8.6 (blueprint: def-per-adic-fibre-comparison-data). -/
structure FiniteRanks (ω : Fibres (k := k) l R) (X : FiniteTypeBase k)
    (F : NormalizedFibre.Heart l E (base l X)) where
  decomposition : RankStratification X.scheme
  lisse : ∀ j : Fin decomposition.strata.n,
    ((modulePull (decomposition.strata.immersion j)
      (NormalizedFibre.coefficient l E (decomposition.strata.immersion j))).obj
        ((NormalizedFibre.realize l E (base l X) (R.realization E (base l X))).obj F)
        ).IsFiniteLocallyFree
  dimension : ∀ (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ X.scheme),
    Module.finrank E (((ω E X).point κ x).functor.obj F) =
      decomposition.rank (underlying κ x)
  point_independence : ∀ (κ κ' : Type u) [Field κ] [IsAlgClosed κ]
    [Field κ'] [IsAlgClosed κ'] (x : Spec (.of κ) ⟶ X.scheme)
    (x' : Spec (.of κ') ⟶ X.scheme), underlying κ x = underlying κ' x' →
      Nonempty ((((ω E X).point κ x).functor.obj F) ≅
        (((ω E X).point κ' x').functor.obj F))
  support : ∀ (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ X.scheme),
    ¬ IsZero (((ω E X).point κ x).functor.obj F) ↔ decomposition.rank (underlying κ x) ≠ 0

/-- A local normalized tower comparison, retaining all finite pullback-stalk maps.
Source: Stacks 03Q1, BS 6.8.4(1)
(blueprint: def-per-adic-fibre-comparison-data). -/
def pulledStalkSystem {U V : Scheme.{u}} (g : V ⟶ U)
    (N : NormalizedFibre.Lattice l E U) (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ V) :
    (N.system ⋙ Etale.upperStar (ModuleCat.{u + 1}
      (Padic.coefficientExtensionIntegers l E)) g) ⋙
        (pointSmallEtale x).ulift.{u + 1}.sheafFiber ≅
      N.system ⋙ (pointSmallEtale (x ≫ g)).ulift.{u + 1}.sheafFiber :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft N.system
    (Etale.upperStarCompUliftSheafFiberIso
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) g x)

/-- The normalized isomorphism of stalk towers before taking the limit.
Source: Stacks 03Q1 (blueprint: def-per-adic-fibre-comparison-data). -/
def pullTowerIso {U V : Scheme.{u}} (g : V ⟶ U)
    (N : NormalizedFibre.Lattice l E U) (M : NormalizedFibre.Lattice l E V)
    (e : M.system ≅ N.system ⋙ Etale.upperStar
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ V) :
    M.system ⋙ (pointSmallEtale x).ulift.{u + 1}.sheafFiber
      (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ≅
    N.system ⋙ (pointSmallEtale (x ≫ g)).ulift.{u + 1}.sheafFiber
      (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) :=
  Functor.isoWhiskerRight e _ ≪≫ pulledStalkSystem l E g N κ x

/-- A limit comparison is fixed by its projections to every quotient-stalk comparison.
Source: BS 6.8.4(1) (blueprint: def-per-adic-fibre-comparison-data). -/
structure PullLimit {U V : Scheme.{u}} (g : V ⟶ U)
    (N : NormalizedFibre.Lattice l E U) (M : NormalizedFibre.Lattice l E V)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ V)
    (e : M.system ⋙ (pointSmallEtale x).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ≅
      N.system ⋙ (pointSmallEtale (x ≫ g)).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))) where
  iso : M.fiber l E κ x ≅ N.fiber l E κ (x ≫ g)
  projection : ∀ n : ℕ,
    iso.hom ≫ limit.π
        (N.system ⋙ (pointSmallEtale (x ≫ g)).ulift.{u + 1}.sheafFiber
          (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))) (op n) =
      limit.π (M.system ⋙ (pointSmallEtale x).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))) (op n) ≫
          e.hom.app (op n)

/-- Natural finite-stage pullback and scalar comparisons, stated for the actual heart
functors. Source: BS 6.8.4, 6.8.14--6.8.15
(blueprint: def-per-adic-fibre-comparison-data). -/
structure Comparisons (ω : Fibres (k := k) l R) where
  pull : ∀ {X Y : FiniteTypeBase k} (g : Y.scheme ⟶ X.scheme)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (y : Spec (.of κ) ⟶ Y.scheme),
    heartPull l E R g ⋙ ((ω E Y).point κ y).functor ≅
      ((ω E X).point κ (y ≫ g)).functor
  scalar : ∀ (i : E →ₐ[ℚ_[l]] L) (X : FiniteTypeBase k)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
    heartScalar l E L i X ⋙ ((ω L X).point κ x).functor ≅
      ((ω E X).point κ x).functor ⋙ ModuleCat.extendScalars i.toRingHom
  ranks : ∀ (X : FiniteTypeBase k) (F : NormalizedFibre.Heart l E (base l X)),
    FiniteRanks l R E ω X F
  scalar_rank : ∀ (i : E →ₐ[ℚ_[l]] L) (X : FiniteTypeBase k)
    (F : NormalizedFibre.Heart l E (base l X))
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
    Module.finrank L (((ω L X).point κ x).functor.obj ((heartScalar l E L i X).obj F)) =
      Module.finrank E (((ω E X).point κ x).functor.obj F)
  scalar_support : ∀ (i : E →ₐ[ℚ_[l]] L) (X : FiniteTypeBase k)
    (F : NormalizedFibre.Heart l E (base l X))
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
    IsZero (((ω L X).point κ x).functor.obj ((heartScalar l E L i X).obj F)) ↔
      IsZero (((ω E X).point κ x).functor.obj F)

variable (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The already specified heart inclusion with its shift parameters fixed explicitly.
Source: BS 6.8.14 (blueprint: def-per-adic-fibre-comparison-data). -/
def finiteHeartInclusion (X : FiniteTypeBase k) :
    NormalizedFibre.Heart l E (base l X) ⥤
      PbcRationalCategory X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E) :=
  (localizedT l E (base l X)).heart.ι

/-- A finite-stage heart object lies in the common-stage heart after the actual inclusion.
Source: BS 6.8.14 (blueprint: def-per-adic-fibre-comparison-data).
Proof: the common standard heart is the isomorphism closure of the finite-stage hearts,
by the recorded common-stage truncation theorem; apply it to the inclusion itself. -/
theorem stageHeartMem (X : FiniteTypeBase k) (A : Padic.FiniteCoefficientFields l Ω)
    (F : NormalizedFibre.Heart l (pbcFiniteField.{u} l Ω A) (base l X)) :
    (pbcQbarStandardT l Ω X.scheme).heart
      (((pbcScalarSystem l Ω X.scheme (base l X).dimension
        (base l X).prime_unit).ι A).obj F.obj) := by
  sorry

/-- Literal inclusion of the finite-stage heart into the common-stage heart.
Source: BS 6.8.14 (blueprint: def-per-adic-fibre-comparison-data). -/
def stageHeart (X : FiniteTypeBase k) (A : Padic.FiniteCoefficientFields l Ω) :=
  ObjectProperty.lift (pbcQbarStandardT l Ω X.scheme).heart
    (finiteHeartInclusion l (pbcFiniteField.{u} l Ω A) X ⋙
      (pbcScalarSystem l Ω X.scheme (base l X).dimension (base l X).prime_unit).ι A)
    (stageHeartMem l Ω X A)

/-- The canonical embedding of the existing small finite coefficient model.
Source: BS 6.8.14 (blueprint: def-per-adic-fibre-comparison-data). -/
def stageEmbedding (A : Padic.FiniteCoefficientFields l Ω) :
    pbcFiniteField.{u} l Ω A →+* Ω :=
  A.val.subtype.comp (Shrink.algEquiv ℚ_[l] A.val).toRingHom

/-- Exact common-stage fibres, normalized on every finite-stage heart and all its maps.
Source: BS 6.8.14 (blueprint: def-per-adic-fibre-comparison-data). -/
structure CommonPoint (ω : Fibres (k := k) l R) (X : FiniteTypeBase k)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme) where
  functor : (pbcQbarStandardT l Ω X.scheme).heart.FullSubcategory ⥤
    ModuleCat.{max (u + 1) v} Ω
  [additive : functor.Additive]
  finite : ∀ F, FiniteDimensional Ω (functor.obj F)
  exact : ∀ S : ShortComplex (pbcQbarStandardT l Ω X.scheme).heart.FullSubcategory,
    S.ShortExact → (S.map functor).ShortExact
  finite_stage : ∀ A : Padic.FiniteCoefficientFields l Ω,
    stageHeart l Ω X A ⋙ functor ≅
      ((ω (pbcFiniteField.{u} l Ω A) X).point κ x).functor ⋙
        ModuleCat.extendScalars (stageEmbedding l Ω A)

attribute [instance] CommonPoint.additive

/-- Common-stage lisse finite models and all geometric ranks, retaining independence from
geometric lifts. Source: BS 6.8.4, 6.8.6, 6.8.14
(blueprint: def-per-adic-fibre-comparison-data). -/
structure CommonRanks (ω : Fibres (k := k) l R)
    (V : ∀ (X : FiniteTypeBase k) (κ : Type u) [Field κ] [IsAlgClosed κ]
      (x : Spec (.of κ) ⟶ X.scheme), CommonPoint l R Ω ω X κ x)
    (X : FiniteTypeBase k) (F : (pbcQbarStandardT l Ω X.scheme).heart.FullSubcategory) where
  stage : Padic.FiniteCoefficientFields l Ω
  model : NormalizedFibre.Heart l (pbcFiniteField.{u} l Ω stage) (base l X)
  represents : F ≅ (stageHeart l Ω X stage).obj model
  decomposition : FiniteRanks l R (pbcFiniteField.{u} l Ω stage) ω X model
  dimension : ∀ (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ X.scheme), Module.finrank Ω ((V X κ x).functor.obj F) =
      decomposition.decomposition.rank (underlying κ x)
  point_independence : ∀ (κ κ' : Type u) [Field κ] [IsAlgClosed κ]
    [Field κ'] [IsAlgClosed κ'] (x : Spec (.of κ) ⟶ X.scheme)
    (x' : Spec (.of κ') ⟶ X.scheme), underlying κ x = underlying κ' x' →
      Nonempty (((V X κ x).functor.obj F) ≅ ((V X κ' x').functor.obj F))
  support : ∀ (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ X.scheme), ¬ IsZero ((V X κ x).functor.obj F) ↔
      decomposition.decomposition.rank (underlying κ x) ≠ 0

/-- The common-stage family and its simultaneous detection properties.
Source: BS 6.8.14 (blueprint: def-per-adic-fibre-comparison-data). -/
structure CommonAssertions (ω : Fibres (k := k) l R) where
  point : ∀ (X : FiniteTypeBase k) (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ X.scheme), CommonPoint l R Ω ω X κ x
  detects_zero : ∀ (X : FiniteTypeBase k)
    (F : (pbcQbarStandardT l Ω X.scheme).heart.FullSubcategory),
    (∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
      IsZero ((point X κ x).functor.obj F)) → IsZero F
  detects_iso : ∀ (X : FiniteTypeBase k)
    (F G : (pbcQbarStandardT l Ω X.scheme).heart.FullSubcategory) (f : F ⟶ G),
    (∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
      IsIso ((point X κ x).functor.map f)) → IsIso f
  detects_zero_map : ∀ (X : FiniteTypeBase k)
    (F G : (pbcQbarStandardT l Ω X.scheme).heart.FullSubcategory) (f : F ⟶ G),
    (∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
      (point X κ x).functor.map f = 0) → f = 0
  detects_short_exact : ∀ (X : FiniteTypeBase k)
    (S : ShortComplex (pbcQbarStandardT l Ω X.scheme).heart.FullSubcategory),
    S.ShortExact ↔ ∀ (κ : Type u) [Field κ] [IsAlgClosed κ]
      (x : Spec (.of κ) ⟶ X.scheme), (S.map (point X κ x).functor).ShortExact
  pull : ∀ {X Y : FiniteTypeBase k} (g : Y.scheme ⟶ X.scheme)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (y : Spec (.of κ) ⟶ Y.scheme),
    commonHeartPull l Ω g ⋙ (point Y κ y).functor ≅ (point X κ (y ≫ g)).functor
  ranks : ∀ (X : FiniteTypeBase k)
    (F : (pbcQbarStandardT l Ω X.scheme).heart.FullSubcategory),
    CommonRanks l R Ω ω point X F



end AlgebraicGeometry.Scheme.AdicFibreComparison
