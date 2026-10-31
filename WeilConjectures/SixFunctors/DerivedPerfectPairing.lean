/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.Algebra.Homology.DerivedInternalHomMixedUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
public import WeilConjectures.SixFunctors.ExactSectionsDerivedCup
public import WeilConjectures.AlgebraicGeometry.CondensedSmoothTrace
public import WeilConjectures.SixFunctors.CondensedDerivedTensorShifts
public import WeilConjectures.SixFunctors.ExactScalarPointCup
public import WeilConjectures.AlgebraicGeometry.CondensedSmoothTraceUnit
public import WeilConjectures.AlgebraicGeometry.SitePerfectComplex
public import WeilConjectures.AlgebraicGeometry.InternalSignedTateTwist
public import WeilConjectures.AlgebraicGeometry.AdmissibleCondensedCoefficients
public import Mathlib.Data.ZMod.Basic
import WeilConjectures.SecSmoothPurity.TransportFiniteLineDerived
import WeilConjectures.SecSmoothPurity.TransportFiniteSupport
import WeilConjectures.AlgebraicGeometry.GeoP1Cohomology
import WeilConjectures.AlgebraicGeometry.SpDirectImageEtaleMate
import all WeilConjectures.AlgebraicGeometry.ProjectiveLineTateCoefficientGenerator
import all WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerSupplement
import all WeilConjectures.AlgebraicGeometry.ProjectiveLineConstantCoefficientGenerator
import all WeilConjectures.AlgebraicGeometry.Curve.AffineLineKummer
import all WeilConjectures.AlgebraicGeometry.ProjectiveLineGenusZero
import all WeilConjectures.AlgebraicGeometry.Curve
import all WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import all WeilConjectures.Topology.RingedSpaceModuleCohomology
import all WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
import all WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import all WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
import all WeilConjectures.AlgebraicGeometry.Curve.Estimate
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import all WeilConjectures.AlgebraicGeometry.Sites.Kummer
import all Mathlib.Algebra.Module.ZMod
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import all WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import all WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import all WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import all WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClassGenerator
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
import all WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import all WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import all WeilConjectures.CategoryTheory.SheafTensor
import all WeilConjectures.CategoryTheory.SheafTensorStructure
import all Mathlib.CategoryTheory.Abelian.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Sheafification
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory

public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift

/-! # Derived perfect pairings and the Poincare pairing

Source: latest blueprint, sec-six-functors/sk-def-pairing/_section.md,
first paragraph and complement (blueprint: sk-def-pairing).

## Main definitions

* `pairingSheafCup`: the canonical projection/counit mixed-support cup.
* `pairingTwistedEvaluation`: the native twisted evaluation.
* `pairingScalarCup` and `pairingScalarTrace`: exact point-sections arrows.
* `derivedPoincarePairing`: their displayed cup/evaluation/trace composite.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

-- Use the published site-size specialization, avoiding an unassigned max universe.
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local instance 10000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- The mixed-support cup before taking scalar sections. It is projection, the inverse
open projection comparison, composition of pullbacks, and the pull/direct counit.
Source: latest blueprint, complement, mixed-support cup (blueprint: sk-def-pairing). -/
def pairingSheafCup (c : Compactification f)
    (K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (rightDerivedLowerShriekOfCompactification Λ c).obj K ⊗
      (lowerStar Λ f).rightDerivedFunctor.obj L ⟶
        (rightDerivedLowerShriekOfCompactification Λ c).obj (K ⊗ L) :=
  moduleObjectProjectionMap Λ c.g ((openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj K)
      ((lowerStar Λ f).rightDerivedFunctor.obj L) ≫
    (lowerStar Λ c.g).rightDerivedFunctor.map
      (inv (((openImmersionProjectionComparison' Λ c.i).app K).app
          ((upperStar Λ c.g).leftDerivedFunctor.obj
            ((lowerStar Λ f).rightDerivedFunctor.obj L))) ≫
        (openImmersionLowerShriek Λ c.i).mapDerivedCategory.map
          (K ◁ ((leftDerivedUpperStarComp Λ c.i c.g).inv.app
              ((lowerStar Λ f).rightDerivedFunctor.obj L) ≫
            (Functor.leftDerivedFunctorNatIso _ (upperStarCongr Λ c.comm.symm)).hom.app
              ((lowerStar Λ f).rightDerivedFunctor.obj L) ≫
            (derivedUpperStarLowerStarAdjunction Λ f).counit.app L)))

/-- Twisted evaluation for the native relative closed tensor. The inverse associator
is followed by evaluation tensor identity and the left unitor.
Source: latest blueprint, ev_K(d) (blueprint: sk-def-pairing). -/
def pairingTwistedEvaluation
    (K T : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    K ⊗ ((ihom K).obj (𝟙_ _) ⊗ T) ⟶ T :=
  (α_ K _ T).inv ≫ ((ihom.ev K).app (𝟙_ _) ▷ T) ≫ (λ_ T).hom

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing
open PurityTransport

/-- Exact scalar sections applied after compact-support direct image.
Source: latest blueprint, RΓc formula (blueprint: sk-def-pairing). -/
abbrev pairingCompactSections (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} {a : X ⟶ Spec (.of k)} (cf : Compactification a) :=
  rightDerivedLowerShriekOfCompactification Λ cf ⋙
    (CohomologyTransport.sections Λ (Spec (.of k))).mapDerivedCategory

/-- Exact scalar sections applied after ordinary derived direct image.
Source: latest blueprint, RΓ formula (blueprint: sk-def-pairing). -/
abbrev pairingOrdinarySections (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) :=
  (lowerStar Λ a).rightDerivedFunctor ⋙
    (CohomologyTransport.sections Λ (Spec (.of k))).mapDerivedCategory

/-- Mixed-support cup: the exact sections tensorator precedes the image of the
canonical sheaf cup. The cohomological shift is moved using the native tensor shift.
Source: latest blueprint, displayed cup map (blueprint: sk-def-pairing). -/
def pairingScalarCup (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} {a : X ⟶ Spec (.of k)} (cf : Compactification a)
    (K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) (n : ℤ) :
    (pairingCompactSections Λ k cf).obj K ⊗
        ((pairingOrdinarySections Λ k a).obj L) ⟦n⟧ ⟶
      ((pairingCompactSections Λ k cf).obj (K ⊗ L)) ⟦n⟧ :=
  ((tensorLeft ((pairingCompactSections Λ k cf).obj K)).commShiftIso n).hom.app
      ((pairingOrdinarySections Λ k a).obj L) ≫
    (shiftFunctor _ n).map
      ((pairingExactScalarPointCup Λ k).derived.μ
          ((rightDerivedLowerShriekOfCompactification Λ cf).obj K)
          ((lowerStar Λ a).rightDerivedFunctor.obj L) ≫
        (CohomologyTransport.sections Λ (Spec (.of k))).mapDerivedCategory.map
          (pairingSheafCup Λ cf K L))

private theorem pairingIdentityFinite (S : Scheme.{u}) : LocallyOfFiniteType (𝟙 S) := by
  have : IsIso (𝟙 S) := IsIso.id S
  have : IsOpenImmersion (𝟙 S) := IsOpenImmersion.of_isIso (𝟙 S)
  exact locallyOfFiniteType_of_isOpenImmersion (𝟙 S)

attribute [local instance 10000] pairingIdentityFinite in
/-- The structural smooth datum of an arbitrary smooth separated finite-type
k-scheme, including disconnected and empty schemes. No descent is required.
Source: latest blueprint, geometric hypotheses (blueprint: sk-def-pairing). -/
abbrev pairingSmoothDatum (D : WeilConjectures.FiniteFieldDatum.{u})
    (X : Over (Spec (.of D.k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (cf : Compactification X.hom) : SmoothDatum D where
  X := X
  Y := Over.mk (𝟙 (Spec (.of D.k)))
  yFinite := inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k))))
  yQuasiCompact := inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k))))
  ySeparated := inferInstanceAs (IsSeparated (𝟙 (Spec (.of D.k))))
  map := X.hom
  isOver := ⟨Category.comp_id X.hom⟩
  dim := d
  compactification := cf

/-- Smooth trace after exact point sections. The shift comparison goes from the
shift of sections to sections of the shifted object; the inverse normalized unit
then identifies sections of the coefficient unit with Lambda(*).
Source: latest blueprint, Tr_X (blueprint: sk-def-pairing). -/
def pairingScalarTrace (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (Λ : ScalarSixRing.{u}) (c : Coefficient ell) (e : c.bundled.{u} ell ≅ Λ)
    (X : Over (Spec (.of D.k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (cf : Compactification X.hom) :
    letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    ((pairingCompactSections Λ.X D.k cf).obj
      (smoothTraceCoefficientLine ell Λ c e X.left d)) ⟦2 * (d : ℤ)⟧ ⟶ 𝟙_ _ :=
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  ((pairingCompactSections Λ.X D.k cf).commShiftIso (2 * (d : ℤ))).inv.app
      (smoothTraceCoefficientLine ell Λ c e X.left d) ≫
    (CohomologyTransport.sections Λ.X (Spec (.of D.k))).mapDerivedCategory.map
      (smoothTraceUnitOfCoefficientIso ell Λ c e D hEll (pairingSmoothDatum D X d cf)) ≫
    (pairingExactScalarPointCup_unitIso Λ.X D.k).inv

/-- The derived Poincare pairing in the original condensed coefficient ring. A
presentation is a ring isomorphism to one of the admissible rings, not a change
of coefficient theory. In particular arbitrary admissible Lambda and arbitrary
smooth X over the algebraic closure are allowed. The three arrows are cup,
compact-support twisted evaluation shifted by 2d, and normalized smooth trace.
Source: latest blueprint, beta_K (blueprint: sk-def-pairing). -/
def derivedPoincarePairing (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (Λ : ScalarSixRing.{u}) (c : Coefficient ell) (e : c.bundled.{u} ell ≅ Λ)
    (X : Over (Spec (.of D.k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (cf : Compactification X.hom)
    (K : ConstantModelConstructibleFiniteTor Λ.X X.left)
    (_hK : IsPerfectOnCoefficientSite Λ.X X.left K.obj) :
    letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    (pairingCompactSections Λ.X D.k cf).obj K.obj ⊗
      ((pairingOrdinarySections Λ.X D.k X.hom).obj
        ((ihom K.obj).obj (𝟙_ _) ⊗ smoothTraceCoefficientLine ell Λ c e X.left d))
          ⟦2 * (d : ℤ)⟧ ⟶ 𝟙_ (DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ.X))) :=
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  pairingScalarCup Λ.X D.k cf K.obj
      ((ihom K.obj).obj (𝟙_ _) ⊗ smoothTraceCoefficientLine ell Λ c e X.left d)
      (2 * (d : ℤ)) ≫
    (shiftFunctor _ (2 * (d : ℤ))).map
      ((pairingCompactSections Λ.X D.k cf).map
        (pairingTwistedEvaluation Λ.X K.obj (smoothTraceCoefficientLine ell Λ c e X.left d))) ≫
    pairingScalarTrace ell D hEll Λ c e X d cf

private def pairingTensorPower {C : Type*} [Category C] [MonoidalCategory C]
    (L : C) : ℕ → C
  | 0 => 𝟙_ C
  | n + 1 => pairingTensorPower L n ⊗ L

set_option maxHeartbeats 800000 in
-- Matching the two concrete sheaf-tensor constructions exceeds the default limit.
@[irreducible] private def pairingSectionPowerIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ∀ n, (InternalAbelianSheafModule.sectionModuleEquivalence
      (Scheme.ProEt.topology X) (condensedRingObj Λ X)).functor.obj
        (pairingTensorPower L n) ≅
      AlgebraicGeometry.ProEtale.spSignedTwist X (condensedRingObj Λ X) L (n : ℤ) := by
  let E := InternalAbelianSheafModule.sectionModuleFunctor.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)
  intro n
  change E.obj (pairingTensorPower L n) ≅ SheafOfModules.scalarTensorPower
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) (condensedRingObj Λ X)) (E.obj L) n
  induction n with
  | zero =>
      exact InternalAbelianSheafModule.comparison_unitIso
        (Scheme.ProEt.topology X) (condensedRingObj Λ X)
  | succ n ih =>
      rw [pairingTensorPower]
      cases n with
      | zero => exact E.mapIso (λ_ L)
      | succ n =>
          let T := SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
            (A := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
              (Scheme.ProEt.topology X) (condensedRingObj Λ X)) (E.obj L)
          let t : E.obj (pairingTensorPower L (n + 1) ⊗ L) ≅
              T.obj (E.obj (pairingTensorPower L (n + 1))) :=
            (InternalAbelianSheafModule.sheafTensorIso.{u + 1, u + 1, u}
              (Scheme.ProEt.topology X) (condensedRingObj Λ X)
                (pairingTensorPower L (n + 1)) L).symm
          exact t ≪≫ T.mapIso ih

/-- The line used in the pairing is the recorded native signed twist at d≥0,
with the root-tower first line transported along the same ring isomorphism.
Source: latest blueprint, native Tate twists (blueprint: sk-def-pairing).
Proof: scalar extension along an isomorphism is exact and strong monoidal. Its
single-complex comparison identifies extension of a degree-zero line with the
degree-zero extension. At zero, use its regular-unit comparison; at a successor,
use its tensor comparison and the preceding comparison. The section-module
equivalence is strong monoidal and its inverse identifies these tensor powers
with spInternalSignedTwist at the nonnegative integer d. This proves the claimed
isomorphism without choosing roots or an orientation. -/
theorem pairingTateLine_native (ell : ℕ) [Fact ell.Prime]
    (Λ : ScalarSixRing.{u}) (c : Coefficient ell) (e : c.bundled.{u} ell ≅ Λ)
    (X : Scheme.{u}) (d : ℕ) :
    Nonempty (smoothTraceCoefficientLine ell Λ c e X d ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (AlgebraicGeometry.ProEtale.spInternalSignedTwist X (condensedRingObj Λ.X X)
          ((Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := Λ.X)
            e.hom.hom.hom X)).obj
            (c.firstLine ell X)) (d : ℤ))) := by
  let a := coefficientMap (Λ := c.obj ell) (Λ' := Λ.X) e.hom.hom.hom X
  have : IsIso a := by dsimp [a, coefficientMap]; infer_instance
  have : PreservesFiniteLimits (Mod.extendScalars a) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv a).symm
  let := Mod.extendScalarsMonoidal a
  let F := Mod.extendScalars a
  let L := F.obj (c.firstLine ell X)
  have h : ∀ n, F.obj (c.line ell X n) ≅ pairingTensorPower L n := by
    intro n
    induction n with
    | zero => exact (Functor.Monoidal.εIso F).symm
    | succ n ih =>
        exact (Functor.Monoidal.μIso F (c.line ell X n) (c.firstLine ell X)).symm ≪≫
          tensorIso ih (Iso.refl _)
  let E := InternalAbelianSheafModule.sectionModuleEquivalence
    (Scheme.ProEt.topology X) (condensedRingObj Λ.X X)
  refine ⟨(F.singleFunctorCompLeftDerivedFunctorIso.app (c.line ell X d)) ≪≫
    (DerivedCategory.singleFunctor
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X))
      0).mapIso ?_⟩
  exact h d ≪≫ E.unitIso.app _ ≪≫ E.inverse.mapIso (pairingSectionPowerIso Λ.X X L d)

/-- The presentation parameters in the definition cover precisely admissible rings.
In the finite case exponent zero means the zero ring, which also has a positive
annihilating exponent. A Mon isomorphism between commutative objects is exactly
an isomorphism in CommMon; no coefficient action or structure is lost.
Source: latest blueprint, admissibility hypothesis (blueprint: sk-def-pairing).
Proof: unfold IsAdmissibleCoefficient. Choose its prime. In each of its six
branches use the corresponding Coefficient constructor and reverse the ring iso.
For a finite ring, replace the annihilating exponent n by n+1 using multiplication
by ell. Conversely each constructor supplies exactly the corresponding admissible
branch, and the given ring iso transports it. This includes finite zero rings. -/
theorem pairingAdmissiblePresentation_iff (Λ : ScalarSixRing.{u}) :
    IsAdmissibleCoefficient Λ.X ↔
      ∃ (ell : ℕ) (_hEll : Fact ell.Prime) (c : Coefficient ell),
        Nonempty (c.bundled.{u} ell ≅ Λ) := by
  constructor
  · rintro ⟨ell, hEll, h⟩
    let := hEll
    rcases h with h | h | h | h | h | h
    · rcases h with ⟨A, hA, hfin, htop, hd, hr, ⟨n, hn⟩, ⟨e⟩⟩
      let := hA
      let := hfin
      have ht : htop = ⊥ := @DiscreteTopology.eq_bot A htop hd
      subst htop
      have hn' : (ell ^ (n + 1) : A) = 0 := by rw [pow_succ, hn, zero_mul]
      refine ⟨ell, hEll, .finite (.of A) hfin n hn', ?_⟩
      exact ⟨(CommMon.fullyFaithfulForget₂Mon _).preimageIso e.symm⟩
    · rcases h with ⟨e⟩
      exact ⟨ell, hEll, .integers,
        ⟨(CommMon.fullyFaithfulForget₂Mon _).preimageIso e.symm⟩⟩
    · rcases h with ⟨e⟩
      exact ⟨ell, hEll, .rationals,
        ⟨(CommMon.fullyFaithfulForget₂Mon _).preimageIso e.symm⟩⟩
    · rcases h with ⟨E, ⟨e⟩⟩
      exact ⟨ell, hEll, .integral E,
        ⟨(CommMon.fullyFaithfulForget₂Mon _).preimageIso e.symm⟩⟩
    · rcases h with ⟨E, ⟨e⟩⟩
      exact ⟨ell, hEll, .rational E,
        ⟨(CommMon.fullyFaithfulForget₂Mon _).preimageIso e.symm⟩⟩
    · rcases h with ⟨e⟩
      exact ⟨ell, hEll, .closure,
        ⟨(CommMon.fullyFaithfulForget₂Mon _).preimageIso e.symm⟩⟩
  · rintro ⟨ell, hEll, c, ⟨e⟩⟩
    let := hEll
    have h : Nonempty (Mon.mk Λ.X ≅ Mon.mk (c.obj ell)) :=
      ⟨((CommMon.forget₂Mon _).mapIso e).symm⟩
    refine ⟨ell, hEll, ?_⟩
    cases c with
    | finite A fin n hn =>
        let := fin
        let : TopologicalSpace A := ⊥
        let : DiscreteTopology A := discreteTopology_bot A
        exact Or.inl ⟨A, inferInstance, fin, ⊥, inferInstance, inferInstance,
          ⟨n + 1, hn⟩, h⟩
    | integers => exact Or.inr (Or.inl h)
    | rationals => exact Or.inr (Or.inr (Or.inl h))
    | integral E => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, h⟩)))
    | rational E => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, h⟩))))
    | closure => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

private theorem pairingFiniteLineCoordinates (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (Y : Over (Spec (.of D.k))) [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (A : CommRingCat.{0}) [fin : Finite A] (n : ℕ)
    (hA : (ell ^ (n + 1) : A) = 0) :
    ∃ hY : IsUnit ((ell ^ (n + 1) : ℕ) : Γ(Y.left, ⊤)),
      Nonempty (FiniteLineCoordinates ell A fin n hA Y.left hY) := by
  obtain ⟨a, ⟨_, _, _, _, ha⟩, _⟩ :=
    WeilConjectures.PurityWeil.Condensed.existsUniqueNormalizedFamily ell D hEll
  exact (ha A fin n hA Y).elim fun hY h ↦
    h.elim fun _ h ↦ h.elim fun pY _ ↦ ⟨hY, ⟨pY⟩⟩

set_option maxHeartbeats 2000000 in
-- The finite coefficient and compact-support comparisons require a long isomorphism chain.
/-- The projective-line qualification in derived form. The two summands are the
trivialized positive line shifted by two and the coefficient unit in degree zero.
Source: latest blueprint, final P1 qualification (blueprint: sk-def-pairing).
Proof: the affine normalization clause of existsUniqueNormalizedFamily supplies the
finite line coordinates on the point and on the projective line; finiteDerivedLine and
finiteDerivedUnit identify the native positive line and unit, through the exact finite
encoding equivalence, with comparison pullback of the ordinary etale finite Tate line
and constant module. finiteEncodingSupport and compactSupportSiteComparison carry the
native compact-support object to comparison pullback of the etale one. On the etale
side, compare cf with the chosen compactification; the structural map is proper
(ProjectiveSpace.instIsProper), so lower shriek is the derived pushforward, and
spDirectImageComparisonIso returns to the pro-etale direct image. Apply the inverse
of the decomposition of geoP1Cohomology at exponent n+1, trivialize the line on the
point by a primitive root (kummer_line_as_constant), and reflect the isomorphism along
the finite encoding equivalence. Finally apply exact point sections, its shift and
biproduct comparisons and the scalar unit identification. Here n+1 runs through
every positive exponent of ell, including exponent one. -/
theorem pairingProjectiveLine_decomposition (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p) (n : ℕ)
    (cf : Compactification
      (AlgebraicGeometry.ProjectiveLine (Spec (.of D.k)) ↘ Spec (.of D.k))) :
    letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    let c : Coefficient ell := .finite (.of (ZMod (ell ^ (n + 1))))
      inferInstance n ((Nat.cast_pow ell (n + 1)).symm.trans (ZMod.natCast_self (ell ^ (n + 1))))
    Nonempty (((pairingCompactSections (c.obj ell) D.k cf).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (c.line ell (AlgebraicGeometry.ProjectiveLine (Spec (.of D.k))) 1))) ⟦(2 : ℤ)⟧ ≅
      (𝟙_ _) ⟦(2 : ℤ)⟧ ⊞ 𝟙_ _) := by
  have hsheaf :
      let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
      let c : Coefficient ell := .finite (.of (ZMod (ell ^ (n + 1))))
        inferInstance n ((Nat.cast_pow ell (n + 1)).symm.trans (ZMod.natCast_self (ell ^ (n + 1))))
      Nonempty (((rightDerivedLowerShriekOfCompactification (c.obj ell) cf).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (c.line ell (AlgebraicGeometry.ProjectiveLine (Spec (.of D.k))) 1))) ⟦(2 : ℤ)⟧ ≅
        ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)) ⟦(2 : ℤ)⟧ ⊞
          (DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)) := by
    dsimp only
    let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    let A := CommRingCat.of (ZMod (ell ^ (n + 1)))
    have hA : (ell ^ (n + 1) : A) = 0 :=
      (Nat.cast_pow ell (n + 1)).symm.trans (ZMod.natCast_self _)
    let c := Coefficient.finite A inferInstance n hA
    let T := Spec (.of D.k)
    let P := AlgebraicGeometry.ProjectiveLine T
    let q := P ↘ T
    let : TopologicalSpace A := ⊥
    let : DiscreteTopology A := discreteTopology_bot A
    let Y : Over (Spec (.of D.k)) := Over.mk (𝟙 T)
    have : LocallyOfFiniteType Y.hom := pairingIdentityFinite T
    have : IsIso (𝟙 T) := IsIso.id T
    have : QuasiCompact Y.hom := quasiCompact_of_isIso (𝟙 T)
    have : IsSeparated Y.hom := inferInstanceAs (IsSeparated (𝟙 T))
    let Z : Over (Spec (.of D.k)) := Over.mk q
    have : LocallyOfFiniteType Z.hom := inferInstanceAs (LocallyOfFiniteType q)
    have : QuasiCompact Z.hom := inferInstanceAs (QuasiCompact q)
    have : IsSeparated Z.hom := inferInstanceAs (IsSeparated q)
    obtain ⟨hT, ⟨pT⟩⟩ := pairingFiniteLineCoordinates ell D hEll Y A n hA
    obtain ⟨hP, ⟨pP⟩⟩ := pairingFiniteLineCoordinates ell D hEll Z A n hA
    let B := ULift.{u + 1} A
    have hB := finiteLiftAnnihilator ell A n hA
    let ET := (finiteEncodingDerived A T).inverse
    have : ET.CommShift ℤ := by
      change (finiteEncoding A T).inverse.mapDerivedCategory.CommShift ℤ
      infer_instance
    have : ET.Additive := by
      change (finiteEncoding A T).inverse.mapDerivedCategory.Additive
      infer_instance
    let V := (comparisonUpperStar (ModuleCat.{u + 1} B) T).mapDerivedCategory
    let L := (Etale.ordinaryFiniteLine B (ell ^ (n + 1)) hB P) ⟦(2 : ℤ)⟧
    let R := rightDerivedLowerShriekOfCompactification (c.obj ell) cf
    let K := c.derivedLine ell P 1
    let eL := finiteDerivedLine ell A n hA P hP pP
    let eU := finiteDerivedUnit ell A n hA T hT pT
    obtain ⟨b, _, _⟩ := geoP1Cohomology ell Fact.out (n + 1) (by omega) B hB
    have hL : DerivedCategory.TStructure.t.plus L := by
      refine ⟨-2, ?_⟩
      exact DerivedCategory.TStructure.t.isGE_shift _ 0 2 (-2) (by decide)
    have hNk : ((ell ^ (n + 1) : ℕ) : D.k) ≠ 0 := by
      have h := hT.map (Scheme.ΓSpecIso (.of D.k)).hom.hom
      simpa only [map_natCast] using h.ne_zero
    obtain ⟨t⟩ := Etale.kummer_line_as_constant (ell ^ (n + 1)) B hB D.k (𝟙 T) hNk
    let tD := (DerivedCategory.singleFunctor _ 0).mapIso t
    let eD := (Etale.rightDerivedLowerShriekOfCompactificationIso
      B cf (HasCompactification.compactification q)).app L ≪≫
      (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} B) q).app L
    let eC := (finiteEncodingSupport A cf).app K ≪≫
      (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) cf).mapIso eL ≪≫
      (compactSupportSiteComparison B cf).app ⟨L, hL⟩
    let U := unit ell c T
    let v : V.obj ((Etale.ordinaryFiniteUnit B T) ⟦(2 : ℤ)⟧) ≅ ET.obj (U ⟦(2 : ℤ)⟧) :=
      (V.commShiftIso (2 : ℤ)).app _ ≪≫ (shiftFunctor _ (2 : ℤ)).mapIso eU.symm ≪≫
        ((ET.commShiftIso (2 : ℤ)).app _).symm
    have : PreservesBinaryBiproducts ET := preservesBinaryBiproducts_of_preservesBiproducts ET
    let e := eC ≪≫ V.mapIso eD ≪≫ spDirectImageComparisonIso B q L hL ≪≫
      (b T hT).symm ≪≫
      biprod.mapIso (V.mapIso ((shiftFunctor _ (2 : ℤ)).mapIso tD) ≪≫ v) eU.symm ≪≫
      (ET.mapBiprod _ _).symm
    exact ⟨((R.commShiftIso (2 : ℤ)).app _).symm ≪≫ ET.preimageIso e⟩
  dsimp only
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let c : Coefficient ell := .finite (.of (ZMod (ell ^ (n + 1))))
    inferInstance n ((Nat.cast_pow ell (n + 1)).symm.trans (ZMod.natCast_self _))
  let P := AlgebraicGeometry.ProjectiveLine (Spec (.of D.k))
  let R := rightDerivedLowerShriekOfCompactification (c.obj ell) cf
  let S := (CohomologyTransport.sections (c.obj ell) (Spec (.of D.k))).mapDerivedCategory
  obtain ⟨e⟩ := hsheaf
  have : PreservesBinaryBiproducts S := preservesBinaryBiproducts_of_preservesBiproducts S
  let u := S.mapIso (DerivedCategory.singleFunctorObjUnitIso _) ≪≫
    (pairingExactScalarPointCup_unitIso (c.obj ell) D.k).symm
  let u2 := (S.commShiftIso (2 : ℤ)).app
    ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)) ≪≫
      (shiftFunctor _ (2 : ℤ)).mapIso u
  refine ⟨((S.commShiftIso (2 : ℤ)).app (R.obj ((DerivedCategory.singleFunctor _ 0).obj
    (c.line ell P 1)))).symm ≪≫ S.mapIso e ≪≫ S.mapBiprod _ _ ≪≫
    biprod.mapIso u2 u⟩

private theorem pairingUnit_cohomology (R : Type (u + 1)) [CommRing R] [Nontrivial R]
    (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i).obj (𝟙_ _)) ↔
      i ≠ 0 := by
  let C := ModuleCat.{u + 1} R
  let U : C := 𝟙_ C
  let S := (DerivedCategory.singleFunctor C 0).obj U
  let e := (DerivedCategory.homologyFunctor C i).mapIso
    (DerivedCategory.singleFunctorObjUnitIso C).symm
  rw [e.isZero_iff]
  by_cases hi : i = 0
  · subst i
    change IsZero ((DerivedCategory.singleFunctor C 0 ⋙
      DerivedCategory.homologyFunctor C 0).obj U) ↔ (0 : ℤ) ≠ 0
    rw [((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app U).isZero_iff]
    constructor
    · intro h
      have : Subsingleton R := ModuleCat.subsingleton_of_isZero h
      exact False.elim (zero_ne_one (Subsingleton.elim (0 : R) 1))
    · exact fun h ↦ False.elim (h rfl)
  · refine ⟨fun _ ↦ hi, fun _ ↦ ?_⟩
    rcases lt_or_gt_of_ne hi with hi | hi
    · exact DerivedCategory.isZero_of_isGE S 0 i hi
    · exact DerivedCategory.isZero_of_isLE S 0 i hi

/-- Both indicated cohomology groups are nonzero and every other group is zero.
This is the precise meaning of 'in degrees -2 and 0', with positive finite exponent.
Source: latest blueprint, final P1 qualification (blueprint: sk-def-pairing).
Proof: use pairingProjectiveLine_decomposition and homology of biproducts. The
coefficient unit in degree zero has no other cohomology; its shift by two is in
degree -2. ZMod(ell^(n+1)) is nonzero because ell is prime and n+1 is positive.
Thus each of the two indicated homology objects is nonzero and all the rest vanish. -/
theorem pairingProjectiveLine_cohomology (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p) (n : ℕ)
    (cf : Compactification
      (AlgebraicGeometry.ProjectiveLine (Spec (.of D.k)) ↘ Spec (.of D.k))) :
    letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    let c : Coefficient ell := .finite (.of (ZMod (ell ^ (n + 1))))
      inferInstance n ((Nat.cast_pow ell (n + 1)).symm.trans (ZMod.natCast_self (ell ^ (n + 1))))
    ∀ i : ℤ, IsZero ((DerivedCategory.homologyFunctor _ i).obj
      (((pairingCompactSections (c.obj ell) D.k cf).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (c.line ell (AlgebraicGeometry.ProjectiveLine (Spec (.of D.k))) 1))) ⟦(2 : ℤ)⟧)) ↔
        i ≠ -2 ∧ i ≠ 0 := by
  dsimp only
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let c : Coefficient ell := .finite (.of (ZMod (ell ^ (n + 1))))
    inferInstance n ((Nat.cast_pow ell (n + 1)).symm.trans (ZMod.natCast_self _))
  let R := condensedScalarRing (c.obj ell)
  have : Fact (1 < ell ^ (n + 1)) :=
    ⟨one_lt_pow₀ (Fact.out : ell.Prime).one_lt (by omega)⟩
  have : Nontrivial R := by
    change Nontrivial (ULift.{u + 1} C((⊤_ Profinite.{u}), ZMod (ell ^ (n + 1))))
    let : Nonempty (⊤_ Profinite.{u}) :=
      ⟨(terminal.from (Profinite.of PUnit.{u + 1})) PUnit.unit⟩
    infer_instance
  obtain ⟨e⟩ := pairingProjectiveLine_decomposition ell D hEll n cf
  intro i
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i
  have := preservesBinaryBiproducts_of_preservesBiproducts H
  let b : H.obj ((𝟙_ _) ⟦(2 : ℤ)⟧ ⊞ 𝟙_ _) ≅
      H.obj ((𝟙_ _) ⟦(2 : ℤ)⟧) ⊞ H.obj (𝟙_ _) := H.mapBiprod _ _
  rw [(H.mapIso e).isZero_iff, b.isZero_iff, biprod_isZero_iff _ _]
  let t : H.obj ((𝟙_ _) ⟦(2 : ℤ)⟧) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) (i + 2)).obj (𝟙_ _) := by
    simpa only [Functor.comp_obj, DerivedCategory.shift_homologyFunctor] using
      (((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) 0).shiftIso
        2 i (i + 2) (by omega)).app (𝟙_ _))
  rw [t.isZero_iff, pairingUnit_cohomology R (i + 2), pairingUnit_cohomology R i]
  omega

end AlgebraicGeometry.ProEtale.CondensedRing
