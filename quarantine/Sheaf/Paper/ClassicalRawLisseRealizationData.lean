/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.LisseIntegralSmallCoefficients
public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.Paper.LisseRationalRealization
public import Sheaf.Paper.RationalCoefficientCategoryComparison
public import Sheaf.Paper.ContinuousRationalDerivedRealization
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.AdicHeartIntrinsicFibres
public import Sheaf.Paper.LisseCompletedSystemData
public import WeilConjectures.AlgebraicGeometry.GeometricPointFieldExtension

import Sheaf.Paper.LisseCompletedSystemComparison
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound

/-! # Classical finite systems and normalized raw lisse realization

Source: Bhatt--Scholze, Lemma 6.8.2, Proposition 6.8.4(1),(3),(4),
Proposition 6.8.11(3), Proposition 6.8.14(2), Remark 6.8.15
(blueprint: def-zl-classical-raw-lisse-realization-data).

The source is the finite-free full subcategory of the recorded classical integral
systems, rationalized with the existing tensor-Hom scalar localization. The localized
coefficient ring is identified with E by `sfRationalCoefficientEquiv`. No idempotents
or additional objects are introduced. All comparison data below occur in the conclusion.
## Main definitions

* `Systems` and `Rational`: the recorded classical source with finite free levels.
* `IntegralComparison`, `IntegralRealization`: quotient, limit and raw functors.
* `FiniteComparison`, `PbcComparison`, `Family`: normalized realization data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option Elab.async true
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped TensorProduct
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.ClassicalRawLisse

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)

/-- Forget separation, retaining the same finite-type geometric scheme.
Source: BS 6.8 (blueprint: def-zl-classical-raw-lisse-realization-data). -/
def realizationBase (W : PerAdic.Base D.k) : LisseRealization.Base D l hl :=
  ⟨W.scheme⟩

/-- The coefficient prime is invertible, by the existing finite-field calculation.
Source: BS 6.8 (blueprint: def-zl-classical-raw-lisse-realization-data). -/
@[instance_reducible]
def baseInvertible (W : PerAdic.Base D.k) (x : W.scheme) :
    Invertible (l : W.scheme.residueField x) :=
  LisseRealization.baseInvertible D l hl (realizationBase D l hl W) x

variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (W : PerAdic.Base D.k)

/-- The existing classical integral systems, including their compatible-family morphisms.
Source: Weil II (1.1.1)b (blueprint: def-zl-classical-raw-lisse-realization-data). -/
abbrev Integral := ObjectProperty.FullSubcategory (IsLisseIntegralDiagramOfUniverses l E W.scheme)

/-- Free-modelled means finite free stalks of every finite, locally constant reduction.
This is exactly `CompletedLisse.IsFreeSystem` with the small coefficient interface.
Source: BS 6.8.4(1) (blueprint: def-zl-classical-raw-lisse-realization-data). -/
def IsFree (F : Integral D l E W) : Prop :=
  ∀ (n : ℕ) (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ W.scheme),
    ∃ r : ℕ, Nonempty
      (((pointSmallEtale x).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).obj
          (F.obj.obj (op n)) ≃ₗ[Padic.coefficientExtensionIntegers l E]
            (Fin r → Padic.coefficientExtensionRing l E (n + 1)))

/-- The full subcategory of normalized finite locally free classical systems.
Source: BS 6.8.4(1) (blueprint: def-zl-classical-raw-lisse-realization-data). -/
abbrev Systems := ObjectProperty.FullSubcategory (IsFree D l E W)

/-- Free-modelled classical E-sheaves: unchanged systems and localized compatible Homs.
The existing equivalence of the localized coefficient ring with E changes only scalars.
Source: Weil II (1.1.1)c (blueprint: def-zl-classical-raw-lisse-realization-data). -/
abbrev Rational := ScalarLocalization (Padic.coefficientExtensionIntegers l E)
  (Systems D l E W) (Padic.coefficientExtensionUniformizer l E)

/-- The actual tensor-with-one functor on classical compatible families.
Source: Weil II (1.1.1)c (blueprint: def-zl-classical-raw-lisse-realization-data). -/
abbrev rationalize := ScalarLocalization.localization (Padic.coefficientExtensionIntegers l E)
  (Systems D l E W) (Padic.coefficientExtensionUniformizer l E)

/-- Forget the two full-subcategory witnesses, retaining the literal etale tower.
Source: BS 6.8.4(1) (blueprint: def-zl-classical-raw-lisse-realization-data). -/
def etaleTower (F : Systems D l E W) :
    ℕᵒᵖ ⥤ Sheaf W.scheme.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  F.obj.obj ⋙ sheafCompose _
    (forget₂ (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) AddCommGrpCat)

/-- Actual levelwise inverse image from the etale site to the pro-etale site.
Source: BS 5.1.5, 6.8.4(1) (blueprint: def-zl-classical-raw-lisse-realization-data). -/
def proEtaleTower (F : Systems D l E W) :=
  etaleTower D l E W F ⋙
    supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} W.scheme

/-- The lisse modules over the prescribed inverse-limit coefficient ring.
Source: BS 6.8.3 (blueprint: def-zl-classical-raw-lisse-realization-data). -/
abbrev Lattices (Y : Scheme.{u}) :=
  ObjectProperty.FullSubcategory
    (fun M : scalarReductionSource l E Y ↦ M.IsFiniteLocallyFree)

/-- Forget just the coefficient action of a completed module.
Source: BS 6.8.4(1) (blueprint: def-zl-classical-raw-lisse-realization-data). -/
abbrev forgetLattice (Y : Scheme.{u}) :
    scalarReductionSource l E Y ⥤ Sheaf (ProEt.topology Y) AddCommGrpCat.{u + 1} :=
  SheafOfModules.toSheaf _

/-- Multiplication by an actual constant scalar section, on the underlying abelian sheaf.
Source: BS 6.8.2 (blueprint: def-zl-classical-raw-lisse-realization-data). -/
def scalar (Y : Scheme.{u}) (M : scalarReductionSource l E Y)
    (a : Padic.coefficientExtensionIntegers l E) :
    (forgetLattice l E Y).obj M ⟶ (forgetLattice l E Y).obj M :=
  (forgetLattice l E Y).map (((integralScalarChainAction l E Y a).app
    ((CochainComplex.singleFunctor (scalarReductionSource l E Y) (0 : ℤ)).obj M)).f 0)

/-- Quotient-normalized reduction and inverse-limit reconstruction, on the actual rings.
Every quotient is a cokernel of ordinary scalar multiplication; no derived quotient is used.
Source: BS 6.8.4(1) (blueprint: def-zl-classical-raw-lisse-realization-data). -/
structure IntegralComparison where
  equivalence : Lattices l E W.scheme ≌ Systems D l E W
  reduction (M : Lattices l E W.scheme) :
    (Functor.const ℕᵒᵖ).obj ((forgetLattice l E W.scheme).obj M.obj) ⟶
      proEtaleTower D l E W (equivalence.functor.obj M)
  quotient (M : Lattices l E W.scheme) (n : ℕ) :
    ∃ h : scalar l E W.scheme M.obj (Padic.coefficientExtensionUniformizer l E ^ (n + 1)) ≫
        (reduction M).app (op n) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ ((reduction M).app (op n)) h))
  scalar_compatibility (M : Lattices l E W.scheme) (n : ℕ)
      (a : Padic.coefficientExtensionIntegers l E) :
    scalar l E W.scheme M.obj a ≫ (reduction M).app (op n) =
      (reduction M).app (op n) ≫
        (supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} W.scheme).map
          ((sheafCompose _ (forget₂
            (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) AddCommGrpCat)).map
              (a • 𝟙 ((equivalence.functor.obj M).obj.obj.obj (op n))))
  completion (F : Systems D l E W) :
    (Functor.const ℕᵒᵖ).obj
        ((forgetLattice l E W.scheme).obj (equivalence.inverse.obj F).obj) ⟶
      proEtaleTower D l E W F
  limit (F : Systems D l E W) : IsLimit (Cone.mk _ (completion F))
  naturality {F G : Systems D l E W} (f : F ⟶ G) (n : ℕ) :
    (forgetLattice l E W.scheme).map (equivalence.inverse.map f).hom ≫
        (completion G).app (op n) = (completion F).app (op n) ≫
      (supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} W.scheme).map
        ((sheafCompose _ (forget₂
          (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) AddCommGrpCat)).map
            (f.hom.hom.app (op n)))
  unit_projection (M : Lattices l E W.scheme) (n : ℕ) :
    (forgetLattice l E W.scheme).map (equivalence.unitIso.hom.app M).hom ≫
      (completion (equivalence.functor.obj M)).app (op n) = (reduction M).app (op n)
  counit_projection (F : Systems D l E W) (n : ℕ) :
    (reduction (equivalence.inverse.obj F)).app (op n) ≫
      (supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} W.scheme).map
        ((sheafCompose _ (forget₂
          (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) AddCommGrpCat)).map
            ((equivalence.counitIso.hom.app F).hom.hom.app (op n))) =
      (completion F).app (op n)


/-- The limit followed by degree-zero inclusion and its actual constructibility witnesses.
The membership proof contains the compatible etale origins of the sf predicate.
Source: BS 6.8.11(3) (blueprint: def-zl-classical-raw-lisse-realization-data). -/
structure IntegralRealization (c : IntegralComparison D l E W) where
  constructible (M : Lattices l E W.scheme) :
    sfIntegralConstructible l E W.scheme ((DerivedCategory.singleFunctor _ 0).obj M.obj)
  integral : Systems D l E W ⥤ sfIntegralConstructibleCategory l E W.scheme
  objects (F : Systems D l E W) : (integral.obj F).obj =
    (DerivedCategory.singleFunctor _ 0).obj (c.equivalence.inverse.obj F).obj
  maps {F G : Systems D l E W} (f : F ⟶ G) :
    HEq (integral.map f).hom
      ((DerivedCategory.singleFunctor _ 0).map (c.equivalence.inverse.map f).hom)
  raw : Rational D l E W ⥤ sfRationalHeart l E W.scheme
  raw_objects (F : Rational D l E W) :
    (raw.obj F).obj = (sfRationalConstructibleLocalization l E W.scheme).obj
      (integral.obj F.obj)
  raw_maps {F G : Systems D l E W} (f : F ⟶ G)
      (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :
    HEq (raw.map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f)).hom
      (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] integral.map f)
  additive : raw.Additive
  fullyFaithful : raw.FullyFaithful

/-- The sheaf module localization of the reconstructed lattice, with no derived tensor.
Its map on fractions is prescribed by the finite-stage comparison below.
Source: BS 6.8.4(4) (blueprint: def-zl-classical-raw-lisse-realization-data). -/
abbrev moduleLocalization (a : LisseRealization.At D l hl E (realizationBase D l hl W)) :=
  pbcExtend (LisseRealization.scalar D l hl E a)

/-- Classical adic fibre: the recorded ordinary inverse limit of geometric stalks,
then the actual tensor with E. The coefficient inclusion is the valuation-ring subtype.
Source: Weil II (1.1.1)b,c (blueprint: def-zl-classical-raw-lisse-realization-data). -/
def classicalFibre (F : Systems D l E W) (x : Spec (.of D.k) ⟶ W.scheme) :=
  (ModuleCat.extendScalars.{u, u, u + 1} (Padic.coefficientExtensionIntegers l E).subtype).obj
    (adicIntegralFiberOfUniverses l E W.scheme F.obj.obj D.k x)

/-- Comparison of the actual finite-system realization with the prescribed sf module
realization. Both the object comparison and every fraction map are fixed explicitly.
Source: BS 6.8.4(4), 6.8.14(2)
(blueprint: def-zl-classical-raw-lisse-realization-data). -/
structure FiniteComparison (c : IntegralComparison D l E W)
    (r : IntegralRealization D l E W c)
    (a : LisseRealization.At D l hl E (realizationBase D l hl W)) where
  modules : Rational D l E W ⥤ LisseRealization.Modules D l hl E (realizationBase D l hl W)
  objects (F : Rational D l E W) : modules.obj F ≅
    (moduleLocalization D l hl E W a).obj (c.equivalence.inverse.obj F.obj).obj
  map_fraction (F G : Rational D l E W) (f : F.obj ⟶ G.obj)
      (b : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :
    modules.map (b ⊗ₜ[Padic.coefficientExtensionIntegers l E] f) ≫ (objects G).hom =
      (objects F).hom ≫
        (sfRationalCoefficientEquiv l E b •
          (moduleLocalization D l hl E W a).map (c.equivalence.inverse.map f).hom)
  additive : modules.Additive
  comparison : r.raw ⋙ (sfRationalHeartProperty l E W.scheme).ι ⋙
    a.sheaf D l hl E ≅ modules
  lisse (F : Rational D l E W) :
    LisseRealization.Lisse D l hl E (realizationBase D l hl W) (r.raw.obj F).obj
  fibre (x : Spec (.of D.k) ⟶ W.scheme) (F : Rational D l E W) :
    (sfAdicRationalFiber l E W.scheme x).obj (r.raw.obj F).obj ≅
      classicalFibre D l E W F.obj x
  fibre_natural (x : Spec (.of D.k) ⟶ W.scheme) {F G : Systems D l E W} (f : F ⟶ G) :
    (sfAdicRationalFiber l E W.scheme x).map
        (r.raw.map ((rationalize D l E W).map f)).hom ≫
      (fibre x ((rationalize D l E W).obj G)).hom =
    (fibre x ((rationalize D l E W).obj F)).hom ≫
      (ModuleCat.extendScalars.{u, u, u + 1} (Padic.coefficientExtensionIntegers l E).subtype).map
        (limMap
          (Functor.whiskerRight f.hom.hom
          ((pointSmallEtale x).ulift.{u + 1}.sheafFiber
            (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)))))
  fibre_fraction (x : Spec (.of D.k) ⟶ W.scheme) (F G : Rational D l E W)
      (f : F.obj ⟶ G.obj) (z : Localization.Away
        (Padic.coefficientExtensionUniformizer l E)) :
    (sfAdicRationalFiber l E W.scheme x).map
        (r.raw.map (z ⊗ₜ[Padic.coefficientExtensionIntegers l E] f)).hom ≫
      (fibre x G).hom =
    (fibre x F).hom ≫ (sfRationalCoefficientEquiv l E z •
      (ModuleCat.extendScalars.{u, u, u + 1} (Padic.coefficientExtensionIntegers l E).subtype).map
        (limMap (Functor.whiskerRight f.hom.hom
          ((pointSmallEtale x).ulift.{u + 1}.sheafFiber
            (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))))))


/-- The continuous realization base, with dimension and prime-unit proofs inherited
from the geometric finite-field hypotheses; these are not extra assumptions.
Source: BS 6.8.14 (blueprint: def-zl-classical-raw-lisse-realization-data). -/
def continuousBase : ContinuousRational.Base.{u} l where
  scheme := W.scheme
  dimension := (PerAdic.base_geometric_properties W).2
  prime_unit x := by
    simpa only [map_natCast] using
      (frobeniusPointPrimeUnit D l hl ((W.scheme ↘ Spec (.of D.k)) x)).map
        ((W.scheme ↘ Spec (.of D.k)).stalkMap x).hom

/-- Field-independent form of the recorded identity-induced sf/PBC comparison.
Both integral objects and every fraction are fixed by the normalized coefficient transport.
Source: BS 6.8.11(3), 6.8.14(2); coefficient-comparison node, steps 1--2
(blueprint: def-zl-classical-raw-lisse-realization-data). -/
structure PbcComparison (c : IntegralComparison D l E W)
    (r : IntegralRealization D l E W c)
    (a : LisseRealization.At D l hl E (realizationBase D l hl W))
    (b : ContinuousRational.At l E (continuousBase D l hl W))
    (f : FiniteComparison D l hl E W c r a) where
  integral : sfIntegralConstructibleCategory l E W.scheme ≌
    PbcBoundedConstructibleComplete W.scheme (pbcIntegralDatum l E)
  integral_identity : integral.functor ⋙
      ObjectProperty.ι (PbcIsBoundedConstructibleComplete W.scheme (pbcIntegralDatum l E)) =
    (sfIntegralConstructible l E W.scheme).ι ⋙ integralDetailedTransport W.scheme l E
  rational : sfRationalConstructibleCategory l E W.scheme ≌
    PbcRationalCategory W.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)
  rational_objects (K : sfRationalConstructibleCategory l E W.scheme) :
    rational.functor.obj K = ⟨integral.functor.obj K.obj⟩
  rational_fractions (K H : sfIntegralConstructibleCategory l E W.scheme)
      (z : Localization.Away (Padic.coefficientExtensionUniformizer l E)) (g : K ⟶ H) :
    HEq (rational.functor.map (z ⊗ₜ[Padic.coefficientExtensionIntegers l E] g))
      (fdRawTensor (pbcUniformizer l E)
        ((pbcRationalCoefficientEquiv l E).symm (sfRationalCoefficientEquiv l E z))
        (integral.functor.map g))
  comparison : r.raw ⋙ (sfRationalHeartProperty l E W.scheme).ι ⋙
    rational.functor ⋙ b.J ≅ f.modules ⋙ DerivedCategory.singleFunctor _ 0
  lift (F : Rational D l E W) (N : sfRationalHeart l E W.scheme)
      (e : (rational.functor ⋙ b.J).obj N.obj ≅
        (DerivedCategory.singleFunctor _ 0).obj (f.modules.obj F)) :
    ∃ i : r.raw.obj F ≅ N,
      (rational.functor ⋙ b.J).map i.hom.hom =
        (comparison.hom.app F) ≫ e.inv
  fibre (x : Spec (.of D.k) ⟶ W.scheme) :
    (sfRationalHeartProperty l E W.scheme).ι ⋙ rational.functor ⋙
      PerAdic.fiber l E W.scheme x ≅
    (sfRationalHeartProperty l E W.scheme).ι ⋙ sfAdicRationalFiber l E W.scheme x
  fibre_normalization (x : Spec (.of D.k) ⟶ W.scheme)
      (K : sfIntegralConstructibleCategory l E W.scheme)
      (hK : sfRationalHeartProperty l E W.scheme
        ((sfRationalConstructibleLocalization l E W.scheme).obj K)) :
    HEq ((fibre x).hom.app
      ⟨(sfRationalConstructibleLocalization l E W.scheme).obj K, hK⟩)
      (𝟙 ((sfAdicIntegralFiber l E W.scheme x).obj K))

/-- A single compatible finite-stage choice of all normalized classical realizations.
Source: BS 6.8.4, 6.8.14 (blueprint: def-zl-classical-raw-lisse-realization-data). -/
structure Family (a : LisseRealization.Family D l hl) (b : ContinuousRational.Family.{u} l) where
  integral : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    (X : PerAdic.Base D.k), IntegralComparison D l A X
  raw : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    (X : PerAdic.Base D.k), IntegralRealization D l A X (integral A X)
  finite : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    (X : PerAdic.Base D.k), FiniteComparison D l hl A X (integral A X) (raw A X)
      (a.realization A (realizationBase D l hl X))
  pbc : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    (X : PerAdic.Base D.k), PbcComparison D l hl A X (integral A X) (raw A X)
      (a.realization A (realizationBase D l hl X))
      (b.realization A (continuousBase D l hl X)) (finite A X)

end WeilConjectures.ClassicalRawLisse
