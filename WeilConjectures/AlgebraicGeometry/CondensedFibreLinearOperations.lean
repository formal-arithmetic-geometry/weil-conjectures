/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.CondensedModuleLocalFrobenius
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartStratificationDefs
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.CondensedFibresExact
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.CategoryTheory.Monoidal.ModuleEqualizerInternalHom
public import WeilConjectures.AlgebraicGeometry.ModuleCupCanonicalHZeroIdentification
import WeilConjectures.AlgebraicGeometry.IntegralResidueOrdinaryMonoidal
import WeilConjectures.AlgebraicGeometry.ProEtalePullbackInternalHom
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeTensorExact
import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeInternalHomColimits
import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
import WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization
import WeilConjectures.AlgebraicGeometry.CondensedModulePullbackExact
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.Projective
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Subcanonical
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.Algebra.Homology.DerivedInternalHomMixedUniverses

/-! # Tensor and dual fibres of condensed Weil sheaves

Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/
sk-p-dl-a1-some-weight/lem-fd-realified-kernel-real.proof.md, Steps 1--2
(blueprint: lem-fd-condensed-fibre-linear-operations).

All modules, point sections and local operators are the recorded condensed constructions.
The comparison maps are normalized by tensoring sections and evaluating functionals.
Finite direct sums are represented by finite products in the abelian module category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.Endofunctor
open scoped CategoryTheory.Obj TensorProduct

namespace WeilConjectures.CondensedFibreLinear

open CondensedModule

/-- Tensor the two Weil data using the inverse pullback tensorator.
Source: latest blueprint, realified-kernel proof Step 2
(blueprint: lem-fd-condensed-fibre-linear-operations). -/
def tensorWeil (l : ℕ) [Fact l.Prime] {T : Scheme.{u}} (g : T ≅ T)
    (F L : IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) :
    IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom) :=
  IsoAlgebra.mk (F.carrier ⊗ L.carrier)
    ((Functor.Monoidal.μIso
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom) _ _).symm ≪≫
        tensorIso F.str L.str)

/-- The ordinary internal dual, with its evaluation-transpose contragredient datum.
Source: latest blueprint, realified-kernel proof Step 1, and the contragredient composite
of sk-def-sf-weil-complexes (blueprint: lem-fd-condensed-fibre-linear-operations). -/
def dualWeil (l : ℕ) [Fact l.Prime] {T : Scheme.{u}} (g : T ≅ T)
    (L : IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) :
    IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom) :=
  IsoAlgebra.mk ((ihom L.carrier).obj (𝟙_ (Modules l T)))
    (Functor.Monoidal.ihomObjIso
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom) L.carrier (𝟙_ _) ≪≫
      (ihom _).mapIso
        (Functor.Monoidal.εIso
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)).symm ≪≫
      (MonoidalClosed.internalHom.mapIso L.str.symm.op).app (𝟙_ _))

/-- A finite direct sum with the direct sum of the Weil data, using the finite product model.
Source: latest blueprint, realified-kernel proof Step 2
(blueprint: lem-fd-condensed-fibre-linear-operations). -/
def sumWeil (l : ℕ) [Fact l.Prime] {T : Scheme.{u}} (g : T ≅ T) (n : ℕ)
    (F : Fin n → IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) :
    IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom) :=
  IsoAlgebra.mk (∏ᶜ fun i ↦ (F i).carrier)
    (PreservesProduct.iso
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)
      (fun i ↦ (F i).carrier) ≪≫ Pi.mapIso (fun i ↦ (F i).str))

/-- The section obtained by tensoring two sections and applying the pullback tensorator.
Source: latest blueprint, realified-kernel proof Step 2
(blueprint: lem-fd-condensed-fibre-linear-operations). -/
def tensorSection (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k]
    {T : Scheme.{u}} (z : Spec (.of D.k) ⟶ T) (F L : Modules l T)
    (v : fibre l D F z) (w : fibre l D L z) : fibre l D (F ⊗ L) z :=
  (λ_ (𝟙_ (CondensedRing.PointMod l D.k))).inv ≫ (v ⊗ₘ w) ≫
    Functor.LaxMonoidal.μ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z) F L

/-- Evaluation of a fibre functional on a fibre vector, with the coefficient-unit comparison.
Source: latest blueprint, realified-kernel proof Step 1
(blueprint: lem-fd-condensed-fibre-linear-operations). -/
def evaluation (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k]
    {T : Scheme.{u}} (z : Spec (.of D.k) ⟶ T) (L : Modules l T)
    (f : fibre l D ((ihom L).obj (𝟙_ (Modules l T))) z) (v : fibre l D L z) :
    ULift.{u + 1} (PadicAlgCl l) :=
  (CondensedRing.pointSectionsUnitIso l D.k).inv
    ((CondensedRing.pointSections l D.k).map
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map
        ((ihom.ev L).app (𝟙_ _)) ≫
        (Functor.Monoidal.εIso
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z)).inv)
      (tensorSection l D z L _ v f))

/-- The canonical derived-to-ordinary tensor map on degree-zero modules.
Source: latest blueprint, realified-kernel proof Steps 1--2
(blueprint: lem-fd-condensed-fibre-linear-operations). -/
def derivedComparison (l : ℕ) [Fact l.Prime] {T : Scheme.{u}} (F L : Modules l T) :
    (DerivedCategory.singleFunctor (Modules l T) 0).obj F ⊗
      (DerivedCategory.singleFunctor (Modules l T) 0).obj L ⟶
        (DerivedCategory.singleFunctor (Modules l T) 0).obj (F ⊗ L) :=
  (tensorIso ((DerivedCategory.singleFunctorIsoCompQ (Modules l T) 0).app F)
    ((DerivedCategory.singleFunctorIsoCompQ (Modules l T) 0).app L)).hom ≫
    Functor.LaxMonoidal.μ DerivedCategory.Q
      ((CochainComplex.singleFunctor (Modules l T) 0).obj F)
      ((CochainComplex.singleFunctor (Modules l T) 0).obj L) ≫
    DerivedCategory.Q.map (DerivedCategory.moduleCup_singleTensorIso F L).hom ≫
    ((DerivedCategory.singleFunctorIsoCompQ (Modules l T) 0).app (F ⊗ L)).inv

set_option maxHeartbeats 800000 in
-- The dependent fibre tensor-section equation needs this elaboration budget.
/-- Natural fibre comparisons, specified by tensoring sections and by evaluation.
Source: latest blueprint, realified-kernel proof Steps 1--2
(blueprint: lem-fd-condensed-fibre-linear-operations). -/
structure Comparisons (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k]
    {T : Scheme.{u}} (g : T ≅ T) (z : Spec (.of D.k) ⟶ T) where
  tensor : ∀ (F L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)),
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) T F.carrier →
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) T L.carrier →
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L.carrier →
    fibre l D (F.carrier ⊗ L.carrier) z ≃ₗ[ULift.{u + 1} (PadicAlgCl l)]
      (fibre l D F.carrier z ⊗[ULift.{u + 1} (PadicAlgCl l)] fibre l D L.carrier z)
  tensor_sections : ∀ (F L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) hF hL hLis
      (v : fibre l D F.carrier z) (w : fibre l D L.carrier z),
    tensor F L hF hL hLis (tensorSection l D z F.carrier L.carrier v w) =
      TensorProduct.tmul (ULift.{u + 1} (PadicAlgCl l)) v w
  dual : ∀ (L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)),
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) T L.carrier →
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L.carrier →
    fibre l D ((ihom L.carrier).obj (𝟙_ (Modules l T))) z ≃ₗ[ULift.{u + 1} (PadicAlgCl l)]
      Module.Dual (ULift.{u + 1} (PadicAlgCl l)) (fibre l D L.carrier z)
  dual_evaluation : ∀ (L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) hL hLis f v,
    dual L hL hLis f v = evaluation l D z L.carrier f v
  tensor_natural : ∀ (F L F' L' : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) hF hL hLis hF' hL' hLis'
      (f : F.carrier ⟶ F'.carrier) (a : L.carrier ⟶ L'.carrier)
      (v : fibre l D (F.carrier ⊗ L.carrier) z),
    tensor F' L' hF' hL' hLis'
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
        CondensedRing.pointSections l D.k).map (f ⊗ₘ a) v) =
      TensorProduct.map
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          CondensedRing.pointSections l D.k).map f).hom
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          CondensedRing.pointSections l D.k).map a).hom (tensor F L hF hL hLis v)
  dual_natural : ∀ (L L' : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) hL hLis hL' hLis'
      (f : L.carrier ⟶ L'.carrier)
      (a : fibre l D ((ihom L'.carrier).obj (𝟙_ (Modules l T))) z) (v : fibre l D L.carrier z),
    dual L hL hLis
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
        CondensedRing.pointSections l D.k).map ((MonoidalClosed.pre f).app (𝟙_ _)) a) v =
      dual L' hL' hLis' a
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          CondensedRing.pointSections l D.k).map f v)

/-- Frobenius under the specified comparisons, including the finite-sum projections.
Source: latest blueprint, realified-kernel proof Steps 1--2
(blueprint: lem-fd-condensed-fibre-linear-operations). -/
structure WeilCompatibility (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    [IsAlgClosed D.k] {T : Scheme.{u}} (g : T ≅ T) (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower g.hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) (c : Comparisons l D g z) : Prop where
  tensor_frobenius : ∀ (F L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) hF hL hLis
      (v : fibre l D (F.carrier ⊗ L.carrier) z),
    c.tensor F L hF hL hLis
      ((CondensedModule.operator l D g.hom (F.carrier ⊗ L.carrier)
        (tensorWeil l g F L).str z n h).hom v) =
      TensorProduct.map (CondensedModule.operator l D g.hom F.carrier F.str z n h).hom
        (CondensedModule.operator l D g.hom L.carrier L.str z n h).hom
        (c.tensor F L hF hL hLis v)
  dual_frobenius : ∀ (L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) hL hLis
      (f : fibre l D ((ihom L.carrier).obj (𝟙_ (Modules l T))) z)
      (v : fibre l D L.carrier z),
    c.dual L hL hLis
      ((CondensedModule.operator l D g.hom ((ihom L.carrier).obj (𝟙_ (Modules l T)))
        (dualWeil l g L).str z n h).hom f) v =
      c.dual L hL hLis f
        ((CondensedModule.transport l D g.hom L.carrier L.str z z n h).inv.hom v)
  sum_frobenius : ∀ (r : ℕ) (F : Fin r → IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)),
    (∀ i, IsConstantModelConstructible (Profinite.padicAlgClRingObj l) T (F i).carrier) →
    IsIso (piComparison
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
        CondensedRing.pointSections l D.k) (fun i ↦ (F i).carrier)) ∧
    ∀ i : Fin r,
      CondensedModule.operator l D g.hom (∏ᶜ fun i ↦ (F i).carrier)
        (sumWeil l g r F).str z n h ≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          CondensedRing.pointSections l D.k).map (Pi.π (fun j ↦ (F j).carrier) i) =
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          CondensedRing.pointSections l D.k).map (Pi.π (fun j ↦ (F j).carrier) i) ≫
        CondensedModule.operator l D g.hom (F i).carrier (F i).str z n h

/-- All clauses of the fibre linear-operations lemma with the fixed condensed coefficients.
Source: latest blueprint, realified-kernel proof Steps 1--2
(blueprint: lem-fd-condensed-fibre-linear-operations). -/
def Assertions (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (T₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    [IsSeparated T₀.hom] : Prop :=
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  (∀ (L : IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius T₀).hom)),
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber T₀).left
      L.carrier →
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L.carrier →
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
      ((ihom L.carrier).obj (𝟙_ (Modules l (D.geometricFiber T₀).left)))) ∧
  (∀ (F L : IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius T₀).hom)),
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber T₀).left
      F.carrier →
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber T₀).left
      L.carrier →
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L.carrier →
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber T₀).left
      (F.carrier ⊗ L.carrier) ∧
      IsIso (derivedComparison l F.carrier L.carrier)) ∧
  ∀ (x : {x : T₀.left // x ∈ closedPoints T₀.left})
      (ι : T₀.left.residueField x.val →+* D.k)
      (hι : ι.comp (T₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k),
    ∃ c : Comparisons l D (D.geometricFrobenius T₀) (localClosedPoint D T₀ x ι hι),
      WeilCompatibility l D (D.geometricFrobenius T₀) (localClosedPoint D T₀ x ι hι)
        (localClosedPointDegree D T₀ x - 1) (localClosedPoint_return D T₀ x ι hι) c

/-- Tensor, dual and finite-sum fibres, with their canonical local geometric Frobenius.
Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/
sk-p-dl-a1-some-weight/lem-fd-realified-kernel-real.proof.md, Steps 1--2
(blueprint: lem-fd-condensed-fibre-linear-operations).

Proof:
1. On a finite-free trivializing slice, the internal dual is free on the dual basis.
Weakly-etale restriction commutes with this Hom (lem-proetale-pullback-internal-hom).
Finite-free tensor is exact (lem-weil-pbc-condensed-finite-free-tensor-exact), hence flat;
the internal-module/section-module equivalence and flat-single normalization
(lem-pur-flat-single-derived-normalization) identify the displayed derived comparison.
A finite common stratification from sk-lem-coefficient-heart makes the ordinary tensor
locally free of rank ab on each stratum, so it is constructible, including zero ranks.
2. Pull a local basis of L back to Spec k using exact module pullback. The field k is
strictly henselian and w-contractible (def-weil-pbc-henselian-terminology,
det-pe-wlocal-strict-contractible). Projectivity (det-pe-wcb-projective) splits a member
of its trivializing cover. Thus the pulled-back L has a global finite basis.
3. The canonical tensor-section comparison is the coordinate identity
Phi(F) tensor Lambda^r -> Phi(F)^r; its inverse sends (v_j) to sum v_j tensor e_j.
Exact additive fibres and the coefficient-unit identification are
lem-wf-condensed-fibres-exact. The section definition proves naturality and basis independence.
4. Pull back evaluation. On the trivializing slices it is the dual-basis pairing, and
finite products commute with exact additive pullback. Over the field point it is
sum a_j b_j, giving dual_evaluation and dual_natural by precomposition.
5. The tensor Weil datum is the inverse tensorator followed by the two given data.
The dual datum is evaluation-transpose, the unit comparison and precomposition with
the inverse datum, exactly sk-def-sf-weil-complexes. Local finite freeness makes ordinary
Hom exact, so a K-injective calculation (def-pur-derived-internal-hom) also identifies
this dual and its datum with the derived contragredient in degree zero.
6. Iterate the tensor datum d times with the pullback compositors of
det-def-sfb-module-pushforward-pullback. Point return reindexes both tensor factors
by the same map and fixes constant coefficients. The recorded operator of
def-weil-local-frobenius-trace therefore acts as the tensor of the two local operators.
7. Iterated evaluation gives (Bf)(Av)=f(v). Substituting A^{-1}v gives the displayed
inverse-transpose identity. Additive fibres preserve finite direct sums, and Weil
iteration and point return commute with their projections, giving block-diagonal
Frobenius. Empty sums and zero-rank duals have the zero fibre and its unique operator. -/
theorem condensed_fibre_linear_operations
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (T₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    [IsSeparated T₀.hom] : Assertions D l hl T₀ := by
  sorry

end WeilConjectures.CondensedFibreLinear
