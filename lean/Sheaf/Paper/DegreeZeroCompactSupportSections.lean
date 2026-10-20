/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import Sheaf.Paper.CommonStageLisse
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.LisseIntegralCompletedRealization
public import Sheaf.Paper.LisseAdicFiberFunctors
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheaves
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.AlgebraicGeometry.ProperSupportSheafComposition
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import WeilConjectures.CategoryTheory.Triangulated.MilnorSequence
import Sheaf.Paper.CoefficientCohomologyModules
import Sheaf.Paper.FiniteCoefficientPoint
import Sheaf.Paper.GaloisLisseRepresentations
import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
import Sheaf.Paper.IntegralCompactSupportPrescribedReductions
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.LisseCompletedSystemComparison
import Sheaf.Paper.LisseIntegralSmallCoefficients
import Sheaf.Paper.PointProEtaleSectionsExact
import Sheaf.Paper.PointSectionsScalarExtension
import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.Paper.SfCommonStageDirectImage
import Sheaf.Paper.SmoothLisseIntegralLattice
import Sheaf.Paper.TraceCompactificationCohomology
import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.Topology.NoetherianSpace


/-! # Degree-zero compact support as ordinary adic sections

Source: Milne, Lectures on Etale Cohomology, Definition 18.1 and Remark 29.7;
Bhatt--Scholze, Propositions 6.8.4 and 6.8.14
(blueprint: lem-a1-degree-zero-compact-support-sections).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

/-- Geometric base change retains finite type and separatedness and is Noetherian.
Source: Milne, Definition 18.1; Stacks 01T6
(blueprint: lem-a1-degree-zero-compact-support-sections).
Proof: finite type and separatedness are stable under base change. A field is
Noetherian, so a finite-type scheme over it is Noetherian, including the empty scheme. -/
theorem a1DegreeZero_geometricProperties :
    LocallyOfFiniteType (D.geometricFiber X₀).hom ∧
      QuasiCompact (D.geometricFiber X₀).hom ∧
      IsSeparated (D.geometricFiber X₀).hom ∧
      IsNoetherian (D.geometricFiber X₀).left ∧
      (D.geometricFiber X₀).left.IsSeparated := by
  sorry

/-- The inherited finite-type structure on the geometric fibre.
Source: Stacks 01T6 (blueprint: lem-a1-degree-zero-compact-support-sections). -/
instance a1DegreeZero_finiteType : LocallyOfFiniteType (D.geometricFiber X₀).hom :=
  (a1DegreeZero_geometricProperties D X₀).1

/-- The inherited quasi-compact structure on the geometric fibre.
Source: Stacks 01T6 (blueprint: lem-a1-degree-zero-compact-support-sections). -/
instance a1DegreeZero_quasiCompact : QuasiCompact (D.geometricFiber X₀).hom :=
  (a1DegreeZero_geometricProperties D X₀).2.1

/-- The inherited separated structure on the geometric structure morphism.
Source: Stacks 01L4 (blueprint: lem-a1-degree-zero-compact-support-sections). -/
instance a1DegreeZero_separated : IsSeparated (D.geometricFiber X₀).hom :=
  (a1DegreeZero_geometricProperties D X₀).2.2.1

/-- Noetherianness required by the recorded inverse-system category.
Source: Stacks 01T6 (blueprint: lem-a1-degree-zero-compact-support-sections). -/
instance a1DegreeZero_noetherian : IsNoetherian (D.geometricFiber X₀).left :=
  (a1DegreeZero_geometricProperties D X₀).2.2.2.1

/-- Absolute separatedness required by the recorded inverse-system category.
Source: Stacks 01L4 (blueprint: lem-a1-degree-zero-compact-support-sections). -/
instance a1DegreeZero_absoluteSeparated : (D.geometricFiber X₀).left.IsSeparated :=
  (a1DegreeZero_geometricProperties D X₀).2.2.2.2

/-- Finite type for the bundled structure morphism notation used by cohomology.
Source: Stacks 01T6 (blueprint: lem-a1-degree-zero-compact-support-sections). -/
instance a1DegreeZero_structFiniteType :
    LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
  a1DegreeZero_finiteType D X₀

/-- Quasi-compactness for the same bundled structure morphism.
Source: Stacks 01T6 (blueprint: lem-a1-degree-zero-compact-support-sections). -/
instance a1DegreeZero_structQuasiCompact :
    QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
  a1DegreeZero_quasiCompact D X₀

/-- Separatedness for the same bundled structure morphism.
Source: Stacks 01L4 (blueprint: lem-a1-degree-zero-compact-support-sections). -/
instance a1DegreeZero_structSeparated :
    IsSeparated ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
  a1DegreeZero_separated D X₀

variable (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The inherited residue-field inverse needed by every recorded lisse functor.
Source: blueprint finite-field coefficient datum
(blueprint: lem-a1-degree-zero-compact-support-sections). -/
@[instance_reducible] def a1DegreeZero_primeInvertible (x : (D.geometricFiber X₀).left) :
    Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
  sfWeilPrimeInvertible D l hl X₀ x

/-- The recorded lisse category on the actual geometric fibre. Invertibility of l
is derived from the global datum, rather than imposed as another assumption.
Source: Weil II (1.1.1) (blueprint: lem-a1-degree-zero-compact-support-sections). -/
abbrev A1DegreeZeroLisse :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  LisseAlgebraicSheaf l (D.geometricFiber X₀).left Ω

/-- The literal finite-stage pair of a lisse object, without choosing a lattice.
Source: Weil II (1.1.1) d) (blueprint: lem-a1-degree-zero-compact-support-sections). -/
def a1DegreeZeroPair (L : A1DegreeZeroLisse D l hl X₀ Ω) :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  lisseAlgebraicPair l (D.geometricFiber X₀).left Ω L

/-- The actual inverse-limit, completed coefficient realization, at the literal
finite coefficient pair of the lisse object.
Source: BS 6.8.4 (blueprint: lem-a1-degree-zero-compact-support-sections). -/
def a1DegreeZeroRealization (L : A1DegreeZeroLisse D l hl X₀ Ω) :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  (lisseIntegralCompletedRealization l Ω (D.geometricFiber X₀).left
    (a1DegreeZeroPair D l hl X₀ Ω L).base).obj
      (lisseCoefficientPairModel l (D.geometricFiber X₀).left Ω
        (a1DegreeZeroPair D l hl X₀ Ω L)).integral

/-- Realizing means an isomorphism with the rationalized actual inverse-limit object
in the current common-stage category.
Source: BS 6.8.4, 6.8.14 (blueprint: lem-a1-degree-zero-compact-support-sections). -/
def A1DegreeZeroRealizes (L : A1DegreeZeroLisse D l hl X₀ Ω)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left) :
    Prop :=
  ∃ h : sfIntegralConstructible l
      (pbcFiniteField.{u} l Ω (a1DegreeZeroPair D l hl X₀ Ω L).base)
      (D.geometricFiber X₀).left (a1DegreeZeroRealization D l hl X₀ Ω L),
    Nonempty (K ≅ lisseIntegralCommonStage l Ω (D.geometricFiber X₀).left
      (a1DegreeZeroPair D l hl X₀ Ω L).base
        ⟨a1DegreeZeroRealization D l hl X₀ Ω L, h⟩)

/-- Ordinary sections are maps from the recorded constant unit, with Weil structure
forgotten. Source: Weil II (1.1.1) (blueprint: lem-a1-degree-zero-compact-support-sections). -/
abbrev A1DegreeZeroSections (L : A1DegreeZeroLisse D l hl X₀ Ω) :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  lisseAlgebraicUnit l (D.geometricFiber X₀).left Ω ⟶ L

/-- Geometric fibre maps use exactly inverse limit, rationalization and final scalar
extension from the recorded fibre functor.
Source: Weil II (1.1.1) (blueprint: lem-a1-degree-zero-compact-support-sections). -/
def a1DegreeZeroSectionFiber {κ : Type u} [Field κ] [IsAlgClosed κ]
    (y : Spec (.of κ) ⟶ (D.geometricFiber X₀).left)
    {L : A1DegreeZeroLisse D l hl X₀ Ω} (s : A1DegreeZeroSections D l hl X₀ Ω L) :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  ((lisseAlgebraicFiberFunctor l (D.geometricFiber X₀).left y Ω).map s).hom

/-- Degree-zero ordinary cohomology is ordinary adic sections; the canonical
compact-support restriction is injective and its image sections have closed proper support.
Linearity of the section comparison is expressed on every geometric fibre; these fibres
are jointly faithful, so these are precisely the ordinary Hom-vector-space operations.
No Weil-equivariance is imposed on a section.
Source: Milne, Definition 18.1 and Remark 29.7; BS 6.8.4, 6.8.14, 6.8.15
(blueprint: lem-a1-degree-zero-compact-support-sections).

Proof:
1. Finite type and separatedness survive base change; X is Noetherian and finite
 dimensional. Realize the lisse heart object at a finite coefficient field, choose
 the smooth lisse integral lattice (lem-a1-smooth-lisse-integral-lattice), and apply
 lem-per-lisse-completed-system-comparison to obtain its normalized finite reductions.
 Full faithfulness of lem-tw-lisse-rational-realization identifies its rationalization
 with the underlying object of F.
2. The lattice in degree zero is integral constructible by the stratified-perfect
 characterization. Choose a Nagata compactification j followed by p.
3. At every finite quotient, compactification cohomology and pro-etale/etale comparison
 identify H_c^0 with Γ(Xbar,j_!M_n), and H^0 with Γ(X,M_n). Negative degrees vanish.
4. Proper-support composition identifies restriction with the injection of sections
 having proper support. Its identity-on-sections definition commutes with reductions
 and restriction of scalars.
5. Exact sections on the algebraically closed point and the direct-image/limit
 comparison identify the integral groups with inverse limits. The Milnor left term
 is zero because H^(-1)=0. Coordinatewise restriction remains injective.
6. Maps from the unit system are compatible sections. Flat rationalization and final
 scalar extension commute with cohomology and retain injectivity.
7. Full faithfulness makes the comparisons independent of the lattice and natural
 for lisse morphisms. The compact-support and point scalar-extension comparisons,
 and the integral compact-support Tor bound [0,0], give coefficient-stage independence.
8. The finite-level nonzero-fibre loci are unions of the finitely many clopen
 components of X by the Galois lisse correspondence. They increase and stabilize,
 so their union is closed and proper. Finite free fibres retain nonzeroness under
 rationalization and scalar extension.
9. Clear the finitely many scalar denominators of any rational class after a common
 finite extension. Multiplication by a nonzero scalar preserves its nonzero-fibre
 locus. The zero class has empty support. Thus every class has the asserted support.
-/
theorem a1DegreeZeroCompactSupportSections [Smooth X₀.hom]
    (F : sfCommonStageWeilSheaf D l hl X₀ Ω)
    (_hF : HasCommonStageLisseLattice l Ω (D.geometricFiber X₀).left
      ((sfCommonStageWeilForget D l hl X₀ Ω).obj F.obj))
    (c : Compactification (D.geometricFiber X₀).hom) :
    ∃ (L : A1DegreeZeroLisse D l hl X₀ Ω),
      A1DegreeZeroRealizes D l hl X₀ Ω L
        ((sfCommonStageWeilForget D l hl X₀ Ω).obj F.obj) ∧
      ∃ (e : adicOrdinaryCohomology D l hl (D.geometricFiber X₀).left Ω
            ((sfCommonStageWeilForget D l hl X₀ Ω).obj F.obj) 0 ≃
          A1DegreeZeroSections D l hl X₀ Ω L)
        (a : adicCompactCohomology D l hl (D.geometricFiber X₀).left Ω c
            ((sfCommonStageWeilForget D l hl X₀ Ω).obj F.obj) 0 →ₗ[Ω]
          adicOrdinaryCohomology D l hl (D.geometricFiber X₀).left Ω
            ((sfCommonStageWeilForget D l hl X₀ Ω).obj F.obj) 0),
        Function.Injective a ∧
        (∀ (κ : Type u) [Field κ] [IsAlgClosed κ]
          (y : Spec (.of κ) ⟶ (D.geometricFiber X₀).left),
          a1DegreeZeroSectionFiber D l hl X₀ Ω y (e 0) = 0 ∧
          ∀ (b : Ω) (s t : adicOrdinaryCohomology D l hl (D.geometricFiber X₀).left Ω
              ((sfCommonStageWeilForget D l hl X₀ Ω).obj F.obj) 0),
            a1DegreeZeroSectionFiber D l hl X₀ Ω y (e (b • s + t)) =
              b • a1DegreeZeroSectionFiber D l hl X₀ Ω y (e s) +
                a1DegreeZeroSectionFiber D l hl X₀ Ω y (e t)) ∧
        ∀ z : adicCompactCohomology D l hl (D.geometricFiber X₀).left Ω c
            ((sfCommonStageWeilForget D l hl X₀ Ω).obj F.obj) 0,
          ∃ Z : TopologicalSpace.Closeds (D.geometricFiber X₀).left,
            IsClosedSubsetProperOver (D.geometricFiber X₀).hom Z ∧
            ∀ (κ : Type u) [Field κ] [IsAlgClosed κ]
              (y : Spec (.of κ) ⟶ (D.geometricFiber X₀).left)
              (t : Spec (.of κ)),
              y.base t ∈ Z ↔ a1DegreeZeroSectionFiber D l hl X₀ Ω y (e (a z)) ≠ 0 := by
  sorry


/-- Integral models in the recorded category, with the derived coefficient inverse.
Source: Weil II (1.1.1) (blueprint: lem-a1-degree-zero-compact-support-sections). -/
abbrev A1DegreeZeroIntegral (E : Padic.FiniteCoefficientFields l Ω) :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  LisseIntegralSheaf l E.val (D.geometricFiber X₀).left

/-- The unit in the same recorded lisse category.
Source: Weil II (1.1.1) (blueprint: lem-a1-degree-zero-compact-support-sections). -/
def a1DegreeZeroUnit : A1DegreeZeroLisse D l hl X₀ Ω :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  lisseAlgebraicUnit l (D.geometricFiber X₀).left Ω

/-- Include the rationalization of the displayed integral model at its actual field.
Source: Weil II (1.1.1) (blueprint: lem-a1-degree-zero-compact-support-sections). -/
def a1DegreeZeroOfModel (E : Padic.FiniteCoefficientFields l Ω)
    (M : A1DegreeZeroIntegral D l hl X₀ Ω E) : A1DegreeZeroLisse D l hl X₀ Ω :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  lisseAlgebraicOfModel l (D.geometricFiber X₀).left Ω E ⟨M⟩

/-- The displayed integral arrow tensored with one in the coefficient localization.
Source: Weil II (1.1.1) (blueprint: lem-a1-degree-zero-compact-support-sections). -/
def a1DegreeZeroModelMap (E : Padic.FiniteCoefficientFields l Ω)
    {M N : A1DegreeZeroIntegral D l hl X₀ Ω E} (f : M ⟶ N) :
    a1DegreeZeroOfModel D l hl X₀ Ω E M ⟶ a1DegreeZeroOfModel D l hl X₀ Ω E N :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  lisseAlgebraicModelMap l (D.geometricFiber X₀).left Ω E
    (F := ⟨M⟩) (H := ⟨N⟩) (TensorProduct.tmul _ 1 f)

/-- Inverse-limit realization on integral morphisms as well as objects. All operations
are the existing coefficient transport, inverse limit and degree-zero embedding.
Source: BS 6.8.4 (blueprint: lem-a1-degree-zero-compact-support-sections). -/
def a1DegreeZeroIntegralRealization (E : Padic.FiniteCoefficientFields l Ω) :
    A1DegreeZeroIntegral D l hl X₀ Ω E ⥤
      DerivedCategory (scalarReductionSource l (pbcFiniteField.{u} l Ω E)
        (D.geometricFiber X₀).left) :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  lisseIntegralCompletedRealization l Ω (D.geometricFiber X₀).left E

/-- The canonical realization of a normalized lisse integral system is constructible.
Source: BS 6.8.4 and 6.6.11
(blueprint: lem-a1-degree-zero-compact-support-sections).
Proof: the finite locally constant quotients have uniformly finite module models over
the coefficient DVR. Their normalized inverse limit is locally the completed finite
module, so is derived complete. Its derived reductions are constructible with a
common interval (possible integral torsion contributes degree -1). This is precisely
the three defining clauses of sfIntegralConstructible. -/
theorem a1DegreeZeroIntegralRealization_mem (E : Padic.FiniteCoefficientFields l Ω)
    (M : A1DegreeZeroIntegral D l hl X₀ Ω E) :
    sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) (D.geometricFiber X₀).left
      ((a1DegreeZeroIntegralRealization D l hl X₀ Ω E).obj M) := by
  sorry

/-- Restriction to the constructible category retains every object and arrow.
Source: BS 6.8.4 (blueprint: lem-a1-degree-zero-compact-support-sections). -/
def a1DegreeZeroIntegralModel (E : Padic.FiniteCoefficientFields l Ω) :=
  ObjectProperty.lift _ (a1DegreeZeroIntegralRealization D l hl X₀ Ω E)
    (a1DegreeZeroIntegralRealization_mem D l hl X₀ Ω E)

/-- Canonical scalar extension from the small integral coefficient model to Ω.
Source: Weil II (1.1.1) (blueprint: lem-a1-degree-zero-compact-support-sections). -/
def a1DegreeZeroScalar (E : Padic.FiniteCoefficientFields l Ω) :
    Padic.coefficientExtensionIntegers l (pbcFiniteField.{u} l Ω E) →+* Ω :=
  E.val.subtype.comp ((Shrink.algEquiv ℚ_[l] E.val).toRingHom.comp
    (Padic.coefficientExtensionIntegers l (pbcFiniteField.{u} l Ω E)).subtype)

/-- The canonical ordinary cohomology functor on integral lisse models, followed by
rationalization and final scalar extension. Its maps are actual derived direct-image
and point-section maps, rather than a transported arbitrary action on vector spaces.
Source: Milne, Definition 18.1; BS 6.5
(blueprint: lem-a1-degree-zero-compact-support-sections). -/
def a1DegreeZeroOrdinaryFunctor (E : Padic.FiniteCoefficientFields l Ω) :=
  a1DegreeZeroIntegralRealization D l hl X₀ Ω E ⋙
    sfCompletedDerivedDirectImage l (pbcFiniteField.{u} l Ω E) (D.geometricFiber X₀).hom ⋙
    lisseIntegralPointCohomology l Ω D E 0 ⋙
    ModuleCat.extendScalars (a1DegreeZeroScalar l Ω E)

/-- The canonical compact cohomology functor on the same models. The finite-action
functor retains the chosen reduction tower and its projection normalization.
Source: Milne, Definition 18.1; BS 6.7.6
(blueprint: lem-a1-degree-zero-compact-support-sections). -/
def a1DegreeZeroCompactFunctor (E : Padic.FiniteCoefficientFields l Ω)
    (c : Compactification (D.geometricFiber X₀).hom) :
    A1DegreeZeroIntegral D l hl X₀ Ω E ⥤ ModuleCat.{u + 1} Ω := by
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (D.geometricFiber X₀).hom.IsOver (Spec (.of D.k)) :=
    (inferInstance : ((D.geometricFiber X₀).left ↘ Spec (.of D.k)).IsOver
      (Spec (.of D.k)))
  exact a1DegreeZeroIntegralModel D l hl X₀ Ω E ⋙
    sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl) c
      (pbcFiniteField.{u} l Ω E) ⋙ ObjectProperty.ι _ ⋙
    lisseIntegralPointCohomology l Ω D E 0 ⋙
    ModuleCat.extendScalars (a1DegreeZeroScalar l Ω E)

/-- Integral morphisms map to their tensor with 1 in the actual coefficient localization.
The specified object values and integral-map formula uniquely determine this functor.
Source: Weil II (1.1.1) b)--d)
(blueprint: lem-a1-degree-zero-compact-support-sections).
Proof: send M to (E,M tensor E) and f to its coefficient-localized class 1 tensor f.
The tensor composition formula gives identities and composition. The object equality
and map formula prescribe every value, so functor extensionality gives uniqueness. -/
theorem a1DegreeZeroLisseInclusion_existsUnique (E : Padic.FiniteCoefficientFields l Ω) :
    ∃! I : A1DegreeZeroIntegral D l hl X₀ Ω E ⥤
        A1DegreeZeroLisse D l hl X₀ Ω,
      ∃ h : ∀ M, I.obj M = a1DegreeZeroOfModel D l hl X₀ Ω E M,
        ∀ (M N : A1DegreeZeroIntegral D l hl X₀ Ω E) (f : M ⟶ N),
          I.map f = eqToHom (h M) ≫
            a1DegreeZeroModelMap D l hl X₀ Ω E f ≫
                eqToHom (h N).symm := by
  sorry

/-- The functor uniquely determined by the preceding explicit object and arrow formulas.
Source: Weil II (1.1.1) (blueprint: lem-a1-degree-zero-compact-support-sections). -/
def a1DegreeZeroLisseInclusion (E : Padic.FiniteCoefficientFields l Ω) :=
  (a1DegreeZeroLisseInclusion_existsUnique D l hl X₀ Ω E).exists.choose

/-- Natural comparisons on the entire algebraic-coefficient lisse category. The
finite-stage natural isomorphisms identify the arrow actions with the actual completed
cohomology functors at every finite field, including after coefficient enlargement.
Source: BS 6.8.4, 6.8.14 and Remark 6.8.15; Milne Definition 18.1
(blueprint: lem-a1-degree-zero-compact-support-sections). -/
structure A1DegreeZeroNaturalComparison
    (c : Compactification (D.geometricFiber X₀).hom) where
  /-- Ordinary cohomology after descent from the actual integral-model functors. -/
  ordinaryCohomology : A1DegreeZeroLisse D l hl X₀ Ω ⥤ ModuleCat.{u + 1} Ω
  /-- Compact cohomology after the same coefficient descent. -/
  compactCohomology : A1DegreeZeroLisse D l hl X₀ Ω ⥤ ModuleCat.{u + 1} Ω
  /-- At every finite field its ordinary action is the specified derived action. -/
  ordinaryIntegral : ∀ E : Padic.FiniteCoefficientFields l Ω,
    a1DegreeZeroLisseInclusion D l hl X₀ Ω E ⋙ ordinaryCohomology ≅
      a1DegreeZeroOrdinaryFunctor D l hl X₀ Ω E
  /-- At every finite field its compact action is the specified compact action. -/
  compactIntegral : ∀ E : Padic.FiniteCoefficientFields l Ω,
    a1DegreeZeroLisseInclusion D l hl X₀ Ω E ⋙ compactCohomology ≅
      a1DegreeZeroCompactFunctor D l hl X₀ Ω E c
  /-- The ordinary comparison is natural for all algebraic-coefficient arrows. -/
  ordinary : ordinaryCohomology ⋙ forget (ModuleCat.{u + 1} Ω) ⋙
      uliftFunctor.{u + 2, u + 1} ≅
    coyoneda.obj (Opposite.op (a1DegreeZeroUnit D l hl X₀ Ω))
  /-- The compact restriction is natural for all algebraic-coefficient arrows. -/
  compact : compactCohomology ⟶ ordinaryCohomology
  /-- The compact restriction is injective at every object. -/
  injective : ∀ L, Function.Injective (compact.app L)
  /-- Ω-linearity of the Hom comparison, tested on the canonical adic fibres. -/
  linear : ∀ L (κ : Type u) [Field κ] [IsAlgClosed κ]
    (y : Spec (.of κ) ⟶ (D.geometricFiber X₀).left),
    a1DegreeZeroSectionFiber D l hl X₀ Ω y (ordinary.hom.app L (ULift.up 0)) = 0 ∧
    ∀ (b : Ω) (s t : ordinaryCohomology.obj L),
      a1DegreeZeroSectionFiber D l hl X₀ Ω y
          (ordinary.hom.app L (ULift.up (b • s + t))) =
        b • a1DegreeZeroSectionFiber D l hl X₀ Ω y (ordinary.hom.app L (ULift.up s)) +
          a1DegreeZeroSectionFiber D l hl X₀ Ω y (ordinary.hom.app L (ULift.up t))
  /-- Exactly the nonzero-geometric-fibre locus is closed with proper reduced structure. -/
  support : ∀ L (z : compactCohomology.obj L),
    ∃ Z : TopologicalSpace.Closeds (D.geometricFiber X₀).left,
      IsClosedSubsetProperOver (D.geometricFiber X₀).hom Z ∧
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ]
        (y : Spec (.of κ) ⟶ (D.geometricFiber X₀).left) (t : Spec (.of κ)),
        y.base t ∈ Z ↔ a1DegreeZeroSectionFiber D l hl X₀ Ω y
          (ordinary.hom.app L (ULift.up (compact.app L z))) ≠ 0

/-- The natural comparison on all algebraic-coefficient arrows realizes the stated groups.
The resulting maps are ordinary.hom.app L after the displayed cohomology comparisons,
and ordinary.hom.app L composed with compact.app L for compact support.
Source: Milne, Definition 18.1 and Remark 29.7; BS 6.8.4 and 6.8.14
(blueprint: lem-a1-degree-zero-compact-support-sections).
Proof: carry out the nine steps of a1DegreeZeroCompactSupportSections simultaneously
on integral models and their maps. Finite restriction, inverse limit, right-derived
image, point sections and flat scalar extension are functorial. Their comparison
maps commute with integral morphisms and scalar multiplication, so the ordinary
comparisons form a natural isomorphism and the compact restrictions form a natural
transformation. The same denominator-clearing argument gives naturality for all
rational arrows. At a common finite coefficient field these are exactly the given
algebraic-coefficient arrows; the integral-compact and point coefficient comparisons
satisfy the identity and tower laws, so the construction descends independently of
that field. The selected smooth lisse lattice realizes For(F); the canonical
point-fibre and derived-limit comparisons identify the two displayed groups with
the values of the actual functors. Injectivity, linearity and proper support are
those of steps 4--9 of the preceding proof, applied to every object simultaneously. -/
theorem a1DegreeZeroCompactSupportSections_natural [Smooth X₀.hom]
    (F : sfCommonStageWeilSheaf D l hl X₀ Ω)
    (_hF : HasCommonStageLisseLattice l Ω (D.geometricFiber X₀).left
      ((sfCommonStageWeilForget D l hl X₀ Ω).obj F.obj))
    (c : Compactification (D.geometricFiber X₀).hom) :
    ∃ (N : A1DegreeZeroNaturalComparison D l hl X₀ Ω c)
      (L : A1DegreeZeroLisse D l hl X₀ Ω),
      A1DegreeZeroRealizes D l hl X₀ Ω L
        ((sfCommonStageWeilForget D l hl X₀ Ω).obj F.obj) ∧
      Nonempty (adicOrdinaryCohomology D l hl (D.geometricFiber X₀).left Ω
          ((sfCommonStageWeilForget D l hl X₀ Ω).obj F.obj) 0 ≃ₗ[Ω]
        N.ordinaryCohomology.obj L) ∧
      Nonempty (adicCompactCohomology D l hl (D.geometricFiber X₀).left Ω c
          ((sfCommonStageWeilForget D l hl X₀ Ω).obj F.obj) 0 ≃ₗ[Ω]
        N.compactCohomology.obj L) := by
  sorry

end WeilConjectures
