/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativeCondensedModuleLocalFrobenius
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.StalkLowerStarProj
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.WeilObject.Sheaf.Stalk
public import WeilConjectures.ZetaSeries
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.ModuleObjects.ProEtaleCoefficients.ModuleEqualizerInternalHom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.ProEtalePullbackInternalHom
import WeilConjectures.ProperBaseChange.CondensedFiniteFreeTensorExact
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.Projective

/-! # Tensor and dual fibres of condensed Weil sheaves

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-deligne-laumon-a1/sec-purity-of-the-lisse-part-of-the-fourier-transform/
sk-p-dl-a1-some-weight/lem-fd-realified-kernel-real.proof.md, Steps 1--2
(blueprint: lem-fd-condensed-fibre-linear-operations-comparisons).

All modules, point sections and local operators are the recorded condensed constructions
of def-weil-local-frobenius-trace (`WeilConjectures.NativeCondensedModule`), used directly.
The comparison maps are normalized by tensoring sections and evaluating functionals.
Finite direct sums are represented by finite products in the abelian module category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.Endofunctor
open scoped CategoryTheory.Obj TensorProduct

namespace WeilConjectures.CondensedFibreComparisons

open WeilConjectures.NativeCondensedModule

/-- The coefficient inverse image is left exact, as its two sheaf inverse images are.
Source: Cartesian coefficient pullback
(blueprint: lem-fd-condensed-fibre-linear-operations-comparisons). -/
instance coefficientPullbackFiniteLimits (T : Scheme.{u}) :
    PreservesFiniteLimits (upperStarFromPoint T) := by
  unfold upperStarFromPoint pointUpperStar
  infer_instance

/-- The coefficient inverse image is additive by preservation of binary products.
Source: Cartesian coefficient pullback
(blueprint: lem-fd-condensed-fibre-linear-operations-comparisons). -/
instance coefficientPullbackAdditive (T : Scheme.{u}) : (upperStarFromPoint T).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Tensor the two Weil data using the inverse pullback tensorator.
Source: latest blueprint, realified-kernel proof Step 2
(blueprint: lem-fd-condensed-fibre-linear-operations-comparisons). -/
def tensorWeil (l : ℕ) [Fact l.Prime] {T : Scheme.{u}} (g : T ≅ T)
    (F L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) :
    IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom) :=
  IsoAlgebra.mk (F.carrier ⊗ L.carrier)
    ((Functor.Monoidal.μIso
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom) _ _).symm ≪≫
        tensorIso F.str L.str)

/-- The ordinary internal dual, with its evaluation-transpose contragredient datum.
Source: latest blueprint, realified-kernel proof Step 1, and the contragredient composite
of sk-def-sf-weil-complexes (blueprint: lem-fd-condensed-fibre-linear-operations-comparisons). -/
def dualWeil (l : ℕ) [Fact l.Prime] {T : Scheme.{u}} (g : T ≅ T)
    (L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) :
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
(blueprint: lem-fd-condensed-fibre-linear-operations-comparisons). -/
def sumWeil (l : ℕ) [Fact l.Prime] {T : Scheme.{u}} (g : T ≅ T) (I : Type u) [Finite I]
    (F : I → IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) :
    IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom) :=
  IsoAlgebra.mk (∏ᶜ fun i ↦ (F i).carrier)
    (PreservesProduct.iso
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)
      (fun i ↦ (F i).carrier) ≪≫ Pi.mapIso (fun i ↦ (F i).str))

/-- The section obtained by tensoring two sections and applying the pullback tensorator.
Source: latest blueprint, realified-kernel proof Step 2
(blueprint: lem-fd-condensed-fibre-linear-operations-comparisons). -/
def tensorSection (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k]
    {T : Scheme.{u}} (z : Spec (.of D.k) ⟶ T) (F L : Modules l T)
    (v : fibre l D F z) (w : fibre l D L z) : fibre l D (F ⊗ L) z :=
  (λ_ (𝟙_ (Modules l (Spec (.of D.k))))).inv ≫ (v ⊗ₘ w) ≫
    Functor.LaxMonoidal.μ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z) F L

/-- Evaluation as a section of the coefficient unit. Constants embed by pointUnitEndRingHom.
Source: evaluation normalization
(blueprint: lem-fd-condensed-fibre-linear-operations-comparisons).
-/
def evaluation (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k]
    {T : Scheme.{u}} (z : Spec (.of D.k) ⟶ T) (L : Modules l T)
    (f : fibre l D ((ihom L).obj (𝟙_ (Modules l T))) z) (v : fibre l D L z) :
    End (𝟙_ (Modules l (Spec (.of D.k)))) :=
  tensorSection l D z L _ v f ≫
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map
      ((ihom.ev L).app (𝟙_ _)) ≫
    (Functor.Monoidal.εIso
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z)).inv

set_option maxHeartbeats 800000 in
-- The dependent fibre tensor-section equation needs this elaboration budget.
/-- Natural fibre comparisons, specified by tensoring sections and by evaluation.
Source: latest blueprint, realified-kernel proof Steps 1--2
(blueprint: lem-fd-condensed-fibre-linear-operations-comparisons). -/
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
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom))
      hL hLis f v,
    pointUnitEndRingHom l D.k (dual L hL hLis f v).down =
      evaluation l D z L.carrier f v
  derived_dual : ∀ (L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)),
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) T L.carrier →
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L.carrier →
    let P := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom
    let S := DerivedCategory.singleFunctor (Modules l T) 0
    letI : P.mapDerivedCategory.Monoidal := Functor.Monoidal.transport
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.padicAlgClRingObj l) g.hom)
    let K := S.obj L.carrier
    let phi := (P.mapDerivedCategorySingleFunctor 0).app L.carrier ≪≫ S.mapIso L.str
    ∃ e : S.obj (dualWeil l g L).carrier ≅ (ihom K).obj (𝟙_ _),
      (P.mapDerivedCategorySingleFunctor 0).app (dualWeil l g L).carrier ≪≫
          S.mapIso (dualWeil l g L).str ≪≫ e =
        P.mapDerivedCategory.mapIso e ≪≫
          Functor.Monoidal.ihomObjIso P.mapDerivedCategory K (𝟙_ _) ≪≫
          (ihom (P.mapDerivedCategory.obj K)).mapIso
            (Functor.Monoidal.εIso P.mapDerivedCategory).symm ≪≫
          (MonoidalClosed.internalHom.mapIso phi.symm.op).app (𝟙_ _)
  tensor_natural : ∀ (F L F' L' : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom))
      hF hL hLis hF' hL' hLis'
      (f : F.carrier ⟶ F'.carrier) (a : L.carrier ⟶ L'.carrier)
      (v : fibre l D (F.carrier ⊗ L.carrier) z),
    tensor F' L' hF' hL' hLis'
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
        pointSections l D.k).map (f ⊗ₘ a) v) =
      TensorProduct.map
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          pointSections l D.k).map f).hom
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          pointSections l D.k).map a).hom (tensor F L hF hL hLis v)
  dual_natural : ∀ (L L' : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom))
      hL hLis hL' hLis'
      (f : L.carrier ⟶ L'.carrier)
      (a : fibre l D ((ihom L'.carrier).obj (𝟙_ (Modules l T))) z) (v : fibre l D L.carrier z),
    dual L hL hLis
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
        pointSections l D.k).map ((MonoidalClosed.pre f).app (𝟙_ _)) a) v =
      dual L' hL' hLis' a
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          pointSections l D.k).map f v)

/-- Frobenius under the specified comparisons, including the finite-sum projections.
Source: latest blueprint, realified-kernel proof Steps 1--2
(blueprint: lem-fd-condensed-fibre-linear-operations-comparisons). -/
structure WeilCompatibility (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    [IsAlgClosed D.k] {T : Scheme.{u}} (g : T ≅ T) (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower g.hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) (c : Comparisons l D g z) : Prop where
  tensor_frobenius : ∀ (F L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) hF hL hLis
      (v : fibre l D (F.carrier ⊗ L.carrier) z),
    c.tensor F L hF hL hLis
      ((operator l D g.hom (F.carrier ⊗ L.carrier)
        (tensorWeil l g F L).str z n h).hom v) =
      TensorProduct.map (operator l D g.hom F.carrier F.str z n h).hom
        (operator l D g.hom L.carrier L.str z n h).hom
        (c.tensor F L hF hL hLis v)
  dual_frobenius : ∀ (L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) hL hLis
      (f : fibre l D ((ihom L.carrier).obj (𝟙_ (Modules l T))) z)
      (v : fibre l D L.carrier z),
    c.dual L hL hLis
      ((operator l D g.hom ((ihom L.carrier).obj (𝟙_ (Modules l T)))
        (dualWeil l g L).str z n h).hom f) v =
      c.dual L hL hLis f
        ((transport l D g.hom L.carrier L.str z z n h).inv.hom v)
  sum_frobenius : ∀ (I : Type u) [Finite I]
      (F : I → IsoAlgebra
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)),
    (∀ i, IsConstantModelConstructible (Profinite.padicAlgClRingObj l) T (F i).carrier) →
    IsIso (piComparison
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
        pointSections l D.k) (fun i ↦ (F i).carrier)) ∧
    ∀ i : I,
      operator l D g.hom (∏ᶜ fun i ↦ (F i).carrier)
        (sumWeil l g I F).str z n h ≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          pointSections l D.k).map (Pi.π (fun j ↦ (F j).carrier) i) =
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          pointSections l D.k).map (Pi.π (fun j ↦ (F j).carrier) i) ≫
        operator l D g.hom (F i).carrier (F i).str z n h

/-- At every geometric point the normalized tensor and dual fibre
comparisons are natural; at compatible closed-point lifts they intertwine local
geometric Frobenius, including finite sums.
Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-deligne-laumon-a1/sec-purity-of-the-lisse-part-of-the-fourier-transform/
sk-p-dl-a1-some-weight/lem-fd-realified-kernel-real.proof.md, Steps 1--2
(blueprint: lem-fd-condensed-fibre-linear-operations-comparisons).

Proof (the six DAG steps):
1. Exact module inverse image pulls the finite-free local models of L to the point.
The algebraically closed field is strictly henselian and w-contractible: its maximal
ideal is zero, its residue field is separably closed, and its component space is a point.
The projectivity theorem for a w-contractible affine splits a trivializing cover of the
terminal point. Connectedness selects one member, giving a global finite-free basis.
2. Tensoring sections defines the comparison, which in that basis sends v tensor (a_j)
to (a_j v). Its inverse sends (v_j) to the sum of v_j tensor e_j. This proves invertibility
without making the comparison depend on the basis. Functoriality gives tensor naturality.
3. On each trivializing pro-etale slice, restriction commutes with internal Hom and
pullback preserves the finite products representing the dual. Evaluation therefore
identifies the two dual bases. Sections give the usual perfect pairing over Lambda,
and precomposition commutes with evaluation, giving contravariant naturality.
4. The tensor Weil datum uses the inverse tensorator. The dual datum uses the closed
comparison, coefficient-unit map and inverse input datum, hence preserves evaluation.
Internal Hom from L is locally a finite product, hence exact. Applying it to a K-injective
resolution of the unit shows its derived Hom has only the ordinary dual in degree zero.
The augmentation is a quasi-isomorphism compatible with evaluation and with these three
arrows, giving the derived-dual identification and its Weil equation.
5. Induct on the closed-point degree to tensor the iterated data. The pullback
compositors and the point return preserve tensoring sections; the unit return fixes
scalars. The tensor operator equation holds on pure tensors, which span the tensor product.
6. Iterate the evaluation identity to obtain (Bf)(Av)=f(v); replace v by A inverse v.
This is the inverse-transpose equation. Additive point pullback and sections preserve
finite biproducts and their injections and projections, and the iterates and return
commute with those maps. Thus the direct-sum comparison is invertible and intertwines
the block diagonal operators. The same formulas include rank zero and the empty sum. -/
theorem condensed_fibre_linear_operations_comparisons
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (T₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    [IsSeparated T₀.hom] :
    (letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    (∀ z : Spec (.of D.k) ⟶ pullback T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))),
      Nonempty (Comparisons l D (D.geometricFrobenius T₀) z)) ∧
    ∀ (x : {x : T₀.left // x ∈ closedPoints T₀.left})
      (ι : T₀.left.residueField x.val →+* D.k)
      (_hι : ι.comp (T₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
      (z : Spec (.of D.k) ⟶ (D.geometricFiber T₀).left)
      (_hz₁ : z ≫ pullback.fst T₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
        Spec.map (CommRingCat.ofHom ι) ≫ T₀.left.fromSpecResidueField x.val)
      (_hz₂ : z ≫ pullback.snd T₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = 𝟙 _),
      letI := (T₀.hom.residueFieldAlgebraMap x.val).toAlgebra
      let n := Module.finrank D.k₀ (T₀.left.residueField x.val) - 1
      ∃ (h : z ≫ localPositivePower (D.geometricFrobenius T₀).hom n =
          localPositivePower (frobeniusPointIso D).hom n ≫ z)
        (c : Comparisons l D (D.geometricFrobenius T₀) z),
        WeilCompatibility l D (D.geometricFrobenius T₀) z n h c) := by
  sorry

end WeilConjectures.CondensedFibreComparisons
