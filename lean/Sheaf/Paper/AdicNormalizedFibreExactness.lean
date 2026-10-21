/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.Paper.ContinuousRationalDerivedRealization
public import Sheaf.Paper.LisseIntegralSmallCoefficients
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientPullback
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import Sheaf.Paper.PbcRationalCategory
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Paper.CoefficientHeartClosure
import Sheaf.Paper.CoefficientHeartCommonStratification
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.Paper.LisseCompletedSystemComparison
import Sheaf.NumberTheory.Padics.AdicLimitFiniteModules
import Sheaf.Paper.EtaleLocalMonodromyRealization
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal
import Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
import Sheaf.Paper.PointProEtaleSectionsExact
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-! # Normalized geometric fibres of the rational heart

Source: Bhatt--Scholze, Proposition 6.8.4(1),(4),(6), Corollary 6.8.5 and Lemma 6.8.7
(blueprint: lem-per-adic-normalized-fibre-exactness).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.ProEtale
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.ContinuousRational.NormalizedFibre

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The continuous coefficient map, defined by adjunction from precomposition of functions.
Source: BS 6.8.1--6.8.2 (blueprint: lem-per-adic-normalized-fibre-exactness). -/
def coefficient {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (adicTowerInverseImage f).obj (rationalCoefficientSheaf l Y E) ⟶
      rationalCoefficientSheaf l X E := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientPullback (ULift.{u + 1, u} E) f

/-- Constant field sections at the final object of the geometric point.
Source: BS 6.8.1 (blueprint: lem-per-adic-normalized-fibre-exactness). -/
def pointConstants (κ : Type u) [Field κ] : E →+*
    (rationalCoefficientSheaf l (Spec (.of κ)) E).obj.obj
      (op (ProEt.mk (𝟙 (Spec (.of κ))))) where
  toFun a := (scalarSections l E (Spec (.of κ)) a).val
    (op (ProEt.mk (𝟙 (Spec (.of κ)))))
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Intrinsic fibre: module inverse image, final-object sections, and constant E-action.
No stratification, lattice, or exchange of a stalk with a limit enters this construction.
Source: BS 6.8.4--6.8.7 (blueprint: lem-per-adic-normalized-fibre-exactness). -/
def ambient {X : Scheme.{u}} (κ : Type u) [Field κ] (x : Spec (.of κ) ⟶ X) :
    pbcModules X (rationalCoefficientSheaf l X E) ⥤ ModuleCat.{u + 1} E :=
  modulePull x (coefficient l E x) ⋙
    SheafOfModules.evaluation _ (op (ProEt.mk (𝟙 (Spec (.of κ))))) ⋙
      ModuleCat.restrictScalars (pointConstants l E κ)

/-- The localized heart, with its already recorded raw category and standard t-structure.
Source: BS 6.8.14 (blueprint: lem-per-adic-normalized-fibre-exactness). -/
abbrev Heart (X : Base.{u} l) := (localizedT l E X).heart.FullSubcategory

/-- Degree-zero sheaf realization of the raw rational heart.
Source: BS 6.8.14 (blueprint: lem-per-adic-normalized-fibre-exactness). -/
def realize (X : Base.{u} l) (a : At l E X) :
    Heart l E X ⥤ pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E) :=
  (localizedT l E X).heart.ι ⋙ a.J ⋙ DerivedCategory.homologyFunctor _ 0

/-- The sheaf realization inherits additivity from the inclusion, J, and H⁰.
Source: BS 6.8.14 (blueprint: lem-per-adic-normalized-fibre-exactness). -/
instance realizeAdditive (X : Base.{u} l) (a : At l E X) :
    (realize l E X a).Additive := by
  unfold realize
  infer_instance

/-- The desired fibre on the heart, obtained from the intrinsic sheaf fibre.
Source: BS 6.8.4--6.8.7 (blueprint: lem-per-adic-normalized-fibre-exactness). -/
def omega (X : Base.{u} l) (a : At l E X) (κ : Type u) [Field κ]
    (x : Spec (.of κ) ⟶ X.scheme) : Heart l E X ⥤ ModuleCat.{u + 1} E :=
  realize l E X a ⋙ ambient l E κ x

/-- Multiplication by a constant integer on an integral continuous module.
Source: BS 6.8.2 (blueprint: lem-per-adic-normalized-fibre-exactness). -/
def integerScalar (T : Scheme.{u})
    (M : pbcModules T (integralCoefficientSheaf l T E))
    (a : Padic.coefficientExtensionIntegers l E) : M ⟶ M := by
  letI := coefficientExtensionNormedField l E
  refine ⟨{ app := ?_, naturality := ?_ }⟩
  · intro U
    exact ModuleCat.ofHom
      { toFun := fun m ↦ ContinuousMap.const U.unop.left (ULift.up a) • m
        map_add' := smul_add _
        map_smul' := fun r m ↦ by
          change _ • (r • m) = r • (_ • m)
          rw [smul_smul, smul_smul, mul_comm] }
  · intro U V f
    ext m
    exact (M.val.map_smul f (ContinuousMap.const U.unop.left (ULift.up a)) m).symm

/-- Forget only the integral coefficient action.
Source: BS 6.8.4(1) (blueprint: lem-per-adic-normalized-fibre-exactness). -/
abbrev forgetIntegral (T : Scheme.{u}) :=
  SheafOfModules.toSheaf.{u + 1} ((adicLisseForget T).obj (integralCoefficientSheaf l T E))

/-- The normalized etale system on the pro-etale site, with its underlying additive groups.
Source: BS 5.1.5 and 6.8.4(1) (blueprint: lem-per-adic-normalized-fibre-exactness). -/
def proSystem (T : Scheme.{u}) (N : AdicIntegralDiagramOfUniverses l E T) :=
  N ⋙ sheafCompose _
    (forget₂ (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) AddCommGrpCat) ⋙
      supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} T

/-- A local lattice and its normalized finite free etale reductions. The limit and quotient
universal properties retain the actual lattice; scalar compatibility fixes its integral action.
This is local chart data, and is never assumed to exist globally on a lisse stratum.
Source: BS 6.8.4(1) (blueprint: lem-per-adic-normalized-fibre-exactness). -/
structure Lattice (T : Scheme.{u}) where
  integral : pbcModules T (integralCoefficientSheaf l T E)
  locallyFree : integral.IsFiniteLocallyFree
  system : AdicIntegralDiagramOfUniverses l E T
  lisse : IsLisseIntegralDiagramOfUniverses l E T system
  finiteFree : ∀ (κ : Type u) [Field κ] [IsAlgClosed κ]
      (x : Spec (.of κ) ⟶ T) (n : ℕ), ∃ r : ℕ, Nonempty
        ((((pointSmallEtale x).ulift.{u + 1}.sheafFiber
          (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).obj
          (system.obj (op n))) ≃ₗ[Padic.coefficientExtensionIntegers l E]
            (Fin r → Padic.coefficientExtensionRing l E (n + 1)))
  reduction : (Functor.const ℕᵒᵖ).obj ((forgetIntegral l E T).obj integral) ⟶
    proSystem l E T system
  complete : IsLimit (Cone.mk _ reduction)
  quotient : ∀ n : ℕ, ∃ h :
      (forgetIntegral l E T).map (integerScalar l E T integral
        (Padic.coefficientExtensionUniformizer l E ^ (n + 1))) ≫ reduction.app (op n) = 0,
    Nonempty (IsColimit (CokernelCofork.ofπ (reduction.app (op n)) h))
  scalar : ∀ (a : Padic.coefficientExtensionIntegers l E) (n : ℕ),
    (forgetIntegral l E T).map (integerScalar l E T integral a) ≫ reduction.app (op n) =
      reduction.app (op n) ≫
        (supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} T).map
          ((sheafCompose _
            (forget₂ (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
              AddCommGrpCat)).map (a • 𝟙 (system.obj (op n))))

/-- Rationalize this actual lattice by the actual continuous coefficient inclusion.
Source: BS 6.8.4(4) (blueprint: lem-per-adic-normalized-fibre-exactness). -/
def Lattice.rational {T : Scheme.{u}} (N : Lattice l E T) :=
  (pbcExtend (integralRationalCoefficientMap l E T)).obj N.integral

/-- The integral fibre is the recorded inverse limit of etale stalks.
Source: Weil II (1.1.1)b), BS 6.8.4(1)
(blueprint: lem-per-adic-normalized-fibre-exactness). -/
def Lattice.fiber {T : Scheme.{u}} (N : Lattice l E T)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ T) :=
  adicIntegralFiberOfUniverses l E T N.system κ x

/-- Its rational fibre uses balanced scalar extension, so it is E tensor_A lim N_n,x.
Source: Weil II (1.1.1)c), BS 6.8.4(4)
(blueprint: lem-per-adic-normalized-fibre-exactness). -/
def Lattice.rationalFiber {T : Scheme.{u}} (N : Lattice l E T)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ T) :=
  (ModuleCat.extendScalars (Padic.coefficientExtensionIntegers l E).subtype).obj
    (N.fiber l E κ x)

/-- A geometric chart on a stratum; the affine chart is etale, rather than pro-etale.
Source: BS 6.8.4(6) and 6.8.6 (blueprint: lem-per-adic-normalized-fibre-exactness). -/
structure Chart (X : Base.{u} l) where
  strata : FiniteLocallyClosedStratification X.scheme
  index : Fin strata.n
  scheme : Scheme.{u}
  [affine : IsAffine scheme]
  etale : scheme ⟶ strata.domain index
  [isEtale : Etale etale]

attribute [instance] Chart.affine Chart.isEtale

/-- The chart's actual map to X.
Source: BS 6.8.6 (blueprint: lem-per-adic-normalized-fibre-exactness). -/
def Chart.map {X : Base.{u} l} (C : Chart l X) := C.etale ≫ C.strata.immersion C.index

/-- An adapted stratification means precisely lissity on every stratum.
Source: BS 6.8.6 (blueprint: lem-per-adic-normalized-fibre-exactness). -/
def Chart.Adapted {X : Base.{u} l} (a : At l E X) (C : Chart l X)
    (F : Heart l E X) : Prop :=
  ∀ i : Fin C.strata.n,
    ((modulePull (C.strata.immersion i) (coefficient l E (C.strata.immersion i))).obj
      ((realize l E X a).obj F)).IsFiniteLocallyFree

/-- Restriction to the chart uses the canonical continuous coefficient map.
Source: BS 6.8.2 (blueprint: lem-per-adic-normalized-fibre-exactness). -/
def Chart.restrict {X : Base.{u} l} (a : At l E X) (C : Chart l X) :=
  realize l E X a ⋙ modulePull C.map (coefficient l E C.map)

/-- A system map induces its actual inverse-limit stalk map followed by balanced localization.
Source: BS 6.8.4(1),(4) (blueprint: lem-per-adic-normalized-fibre-exactness). -/
def rationalLimitMap {T : Scheme.{u}} (N M : Lattice l E T)
    (uN : N.system ⟶ M.system) (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ T) : N.rationalFiber l E κ x ⟶ M.rationalFiber l E κ x :=
  (ModuleCat.extendScalars (Padic.coefficientExtensionIntegers l E).subtype).map
    (limMap (Functor.whiskerRight uN ((pointSmallEtale x).ulift.{u + 1}.sheafFiber
      (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)))))

/-- An integral map represents a specified compatible map of normalized systems.
Source: BS 6.8.4(1) (blueprint: lem-per-adic-normalized-fibre-exactness). -/
def Represents {T : Scheme.{u}} (N M : Lattice l E T)
    (f : N.integral ⟶ M.integral) (uN : N.system ⟶ M.system) : Prop :=
  ∀ n : ℕ, (forgetIntegral l E T).map f ≫ M.reduction.app (op n) =
    N.reduction.app (op n) ≫
      (supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} T).map
        ((sheafCompose _
          (forget₂ (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
            AddCommGrpCat)).map (uN.app (op n)))

/-- A finite-dimensional E-linear fibre, naturally identified with the intrinsic construction.
The exact structure is measured after the specified realization into all continuous modules.
Source: BS 6.8.4--6.8.7 (blueprint: lem-per-adic-normalized-fibre-exactness). -/
structure Point (X : Base.{u} l) (a : At l E X) (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ X.scheme) where
  functor : Heart l E X ⥤ ModuleCat.{u + 1} E
  [additive : functor.Additive]
  [linear : functor.Linear E]
  intrinsic : functor ≅ omega l E X a κ x
  finite : ∀ F, FiniteDimensional E (functor.obj F)
  exact : ∀ S : ShortComplex (Heart l E X),
    (S.map (realize l E X a)).ShortExact → (S.map functor).ShortExact

attribute [instance] Point.additive Point.linear

/-- All normalized local lattice comparisons and joint detection assertions, for one E-stage.
The chart and presentation are universally quantified, so the same fibre is used for every
choice of stratification, etale chart, lattice and fractional representative.
Source: BS 6.8.4(1),(4),(6), 6.8.5 and 6.8.7
(blueprint: lem-per-adic-normalized-fibre-exactness). -/
structure Assertions (X : Base.{u} l) (a : At l E X) where
  point : ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
    Point l E X a κ x
  local_chart : ∀ (F : Heart l E X) (κ : Type u) [Field κ] [IsAlgClosed κ]
      (x : Spec (.of κ) ⟶ X.scheme),
    ∃ (C : Chart l X) (t : Spec (.of κ) ⟶ C.scheme) (N : Lattice l E C.scheme),
      t ≫ C.map = x ∧ C.Adapted l E a F ∧
        Nonempty ((C.restrict l E a).obj F ≅ N.rational l E)
  integral_finite_free : ∀ (C : Chart l X) (N : Lattice l E C.scheme)
      (κ : Type u) [Field κ] [IsAlgClosed κ] (t : Spec (.of κ) ⟶ C.scheme),
    Module.Finite (Padic.coefficientExtensionIntegers l E) (N.fiber l E κ t) ∧
      Module.Free (Padic.coefficientExtensionIntegers l E) (N.fiber l E κ t)
  normalization : ∀ (C : Chart l X) (F : Heart l E X) (_hF : C.Adapted l E a F)
      (N : Lattice l E C.scheme) (_φ : (C.restrict l E a).obj F ≅ N.rational l E)
      (κ : Type u) [Field κ] [IsAlgClosed κ] (t : Spec (.of κ) ⟶ C.scheme),
    (point κ (t ≫ C.map)).functor.obj F ≅ N.rationalFiber l E κ t
  fractions : ∀ (C : Chart l X) (F G : Heart l E X)
      (hF : C.Adapted l E a F) (hG : C.Adapted l E a G)
      (N M : Lattice l E C.scheme)
      (φ : (C.restrict l E a).obj F ≅ N.rational l E)
      (ψ : (C.restrict l E a).obj G ≅ M.rational l E)
      (f : F ⟶ G) (u : N.integral ⟶ M.integral) (uN : N.system ⟶ M.system)
      (_hu : Represents l E N M u uN) (b : ℕ)
      (_hf : (C.restrict l E a).map f ≫ ψ.hom = φ.hom ≫
        (((Padic.coefficientExtensionUniformizer l E : E) ^ b)⁻¹ •
          (pbcExtend (integralRationalCoefficientMap l E C.scheme)).map u))
      (κ : Type u) [Field κ] [IsAlgClosed κ] (t : Spec (.of κ) ⟶ C.scheme),
    (point κ (t ≫ C.map)).functor.map f ≫ (normalization C G hG M ψ κ t).hom =
      (normalization C F hF N φ κ t).hom ≫
        (((Padic.coefficientExtensionUniformizer l E : E) ^ b)⁻¹ •
          rationalLimitMap l E N M uN κ t)
  detects_zero : ∀ F : Heart l E X,
    (∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
      IsZero ((point κ x).functor.obj F)) → IsZero F
  detects_iso : ∀ (F G : Heart l E X) (f : F ⟶ G),
    (∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
      IsIso ((point κ x).functor.map f)) → IsIso f
  detects_zero_map : ∀ (F G : Heart l E X) (f : F ⟶ G),
    (∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
      (point κ x).functor.map f = 0) → f = 0
  detects_exact : ∀ S : ShortComplex (Heart l E X),
    (S.map (realize l E X a)).Exact ↔
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
        (S.map (point κ x).functor).Exact
  detects_short_exact : ∀ S : ShortComplex (Heart l E X),
    (S.map (realize l E X a)).ShortExact ↔
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
        (S.map (point κ x).functor).ShortExact

/-- Normalized geometric fibres of the constructible rational heart, including exactness
and simultaneous detection of zero objects, isomorphisms, zero maps and (short) exactness.
The Base data are the noetherianity, dimension and invertibility consequences already
needed to name the recorded category; the finite-type hypotheses below are retained.

Source: Bhatt--Scholze, Proposition 6.8.4(1),(4),(6), Corollary 6.8.5 and Lemma 6.8.7
(blueprint: lem-per-adic-normalized-fibre-exactness).

Proof plan:
1. Finite type over a field implies noetherianity and finite dimension. Use the continuous
rational realization J_X, and define the fibre intrinsically as sections at Spec κ after
ordinary module inverse image and the continuous-function coefficient map. The balanced
composition comparisons send b tensor (c tensor m) to bc tensor m; hence restriction to a
stratum and then a chart gives the same intrinsic fibre.
2. Choose an adapted finite stratification and an affine etale lattice chart through the
point, using etale-local lattice existence. The completed-system comparison identifies the
lattice with the inverse limit of its normalized etale reductions. Pull each reduction to
the algebraically closed point first. The etale stalk comparison identifies these with
constant sheaves with values (N_n)_x. Rationalization and point sections therefore give
E tensor_A lim (N_n)_x; no commutation of arbitrary stalks with limits is used.
3. The normalized finite-free stalk tower has finite A-module limit by the adic finite-module
limit theorem, with the prescribed quotients. If ϖm=0, its (n+1)-component is divisible by
ϖ^n, hence has zero n-component for every n. Thus the limit is torsion-free. Over the DVR A,
a finite torsion-free module is finite free, including rank zero.
4. An integral reduction-system map induces its inverse-limit map, and dividing by ϖ^b
multiplies the rational fibre map by ϖ^(-b). The raw localization relation annihilates the
difference of equal fractions by a power of ϖ, proving independence of representatives.
All local identifications are with the single intrinsic fibre. Comparing choices by their
composite through that fibre gives natural comparisons satisfying the cocycle. Etale fibre
products and common refinements compare charts and adapted stratifications.
5. For a short exact constructible continuous-module sequence, choose a common lisse
stratification. Its restriction is exact. A pro-etale cover makes the quotient finite free;
the local splitting lemma splits the epimorphism on a further cover. Additive module
inverse image preserves split sequences. Pulling this cover to Spec κ gives local exactness,
and exact point sections give the claimed short exact fibre sequence.
6. For zero detection use local monodromy presentations on connected qcqs noetherian charts.
Pass to an affine neighbourhood of the geometric base point before using the separated
completed-system comparison. The normalized representation lattice has stalk quotients
B/ϖ^nB, limit B, and rational fibre its representation space V. Zero fibres force V=0.
Cover restriction reflects isomorphisms, and stratum restrictions jointly detect vanishing.
Full faithfulness of J_X then gives F=0. For the empty scheme use the empty covering and
stratification; its module category has only zero objects.
7. Constructible continuous modules are closed under ambient kernels, cokernels and
extensions. Exact fibres compute the kernel, cokernel and image fibres of every morphism.
Zero detection thus detects isomorphisms and zero maps. For a short complex, apply the same
argument to its middle homology, and, for short exactness, also to the first kernel and last
cokernel. Their vanishing proves the two asserted exactness equivalences. -/
theorem adic_normalized_fibre_exactness (X : Base.{u} l)
    (k : Type u) [Field k] [X.scheme.Over (Spec (.of k))]
    [LocallyOfFiniteType (X.scheme ↘ Spec (.of k))]
    [QuasiCompact (X.scheme ↘ Spec (.of k))]
    [IsSeparated (X.scheme ↘ Spec (.of k))] (_hl : IsUnit (l : k))
    (R : Family.{u} l) : Nonempty (Assertions l E X (R.realization E X)) := by
  sorry

end AlgebraicGeometry.Scheme.ContinuousRational.NormalizedFibre
