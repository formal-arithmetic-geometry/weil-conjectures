/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CurvePerverseHeartStatement.CurvePerverseHeartStatement
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import Mathlib.CategoryTheory.Simple
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCommonStratification
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCurveLisseDescent
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartGeneralStatement
public import WeilConjectures.AlgebraicGeometry.Compactification.GeometricallyConnectedAlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.CondensedCurvePerverse.CondensedCurvePerverseStatement
public import WeilConjectures.AlgebraicGeometry.CondensedWeilDenseLisseOpen
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.DenseOpenNormal
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
public import WeilConjectures.AlgebraicGeometry.ProEtaleOpenRestriction.ProEtaleOpenRestrictionCounit
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.AlgebraicGeometry.SixFunctors.StratificationGenericNeighborhood
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp
public import WeilConjectures.CategoryTheory.Triangulated.TStructure.CohomologyComparisonPasting
public import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
public import WeilConjectures.ConstructibleSheaf.DenseOpenUnitNormal
public import WeilConjectures.ConstructibleSheaf.NormalOpenLowerStar
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Construction
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.EndoFunctor
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.RingTheory.ProperBaseChange.NormalRingFieldExtensionDescent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CurveSupportHeart
public import WeilConjectures.WeilSheaf.DenseOpen
public import WeilConjectures.WeilSheaf.RealSheaves.Setup.RealSheavesSetup
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.AffineLineConventions.AffineLineConventions
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstructibleTruncations
public import WeilConjectures.AlgebraicGeometry.CondensedCurvePerverseStatement.CurveGeometricMiddleSimpleCase
public import WeilConjectures.AlgebraicGeometry.CondensedCurvePerverseStatement.CurveGeometricPunctualSimpleCase
public import WeilConjectures.AlgebraicGeometry.CondensedCurvePerverseStatement.CurveWeilMiddleSimpleCase
public import WeilConjectures.AlgebraicGeometry.CondensedCurvePerverseStatement.CurveWeilPunctualSimpleCase
public import WeilConjectures.AlgebraicGeometry.CurvePunctual.CurvePunctualSupport
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.SimpleShortExactDichotomy
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPerverseSupport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations

/-!
# Simple perverse sheaves on a smooth curve

Source: latest blueprint, `prop-a1-curve-perverse-simples`, entire statement.
The alternatives are stated in the bounded-constructible heart classes supplied by
`thm-a1-curve-perverse-heart`, and in the corresponding Weil heart. Punctual objects
are degree-zero direct images from closed points; middle extensions are shifted
ordinary direct images from dense opens. Irreducibility is simplicity in the relevant
constructible or lisse full subcategory.
(blueprint: prop-a1-curve-perverse-simples).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedCurvePerverseStatement

variable (ell : ℕ) [Fact ell.Prime]

/-- The perverse heart Perv(C): the full subcategory of the intersection of the
support and cosupport classes of `thm-a1-curve-perverse-heart`, clause (2), inside the
bounded constructible complexes, with its inherited morphisms.
Source: latest blueprint, `prop-a1-curve-perverse-simples.md`, "the abelian category
Perv(C)" (blueprint: prop-a1-curve-perverse-simples). -/
abbrev GeometricPerv_legacy {k : Type u} [Field k]
    (hk : (Finite k ∨ IsAlgClosed k) ∧ ∀ x : k, x ≠ 0 → IsOfFinOrder x)
    (C : Over (Spec (.of k))) [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom] :=
  (CondensedRing.CondensedPerverseLEZero ell hk C ⊓
    CondensedRing.CondensedPerverseGEZero ell hk C).FullSubcategory

/-- A degree-zero punctual simple: an irreducible constructible sheaf on a closed point,
transported to the curve by the ordinary direct image.
Source: latest blueprint, `prop-a1-curve-perverse-simples.md`, punctual bullet
(blueprint: prop-a1-curve-perverse-simples). -/
def IsPunctualSimple_legacy {k : Type u} [Field k]
    (hk : (Finite k ∨ IsAlgClosed k) ∧ ∀ x : k, x ≠ 0 → IsOfFinOrder x)
    (C : Over (Spec (.of k))) [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    (P : GeometricPerv_legacy ell hk C) : Prop :=
  ∃ (x : C.left), IsClosed ({x} : Set C.left) ∧
    ∃ (E : CurvePerverseHeartStatement.Modules ell
        (Spec (C.left.residueField x)))
      (hE : IsConstructibleModuleObject
        (condensedRingObj (Profinite.padicAlgClRingObj ell)
          (Spec (C.left.residueField x))) E),
      Simple (⟨E, hE⟩ : ObjectProperty.FullSubcategory
        (IsConstructibleModuleObject
          (condensedRingObj (Profinite.padicAlgClRingObj ell)
            (Spec (C.left.residueField x)))) ) ∧
      Nonempty (P.obj.obj ≅
        (DerivedCategory.singleFunctor _ 0).obj
          ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ell)
            (C.left.fromSpecResidueField x)).obj E))

/-- A shifted middle extension of a nonzero simple lisse sheaf on a dense open.
Source: latest blueprint, `prop-a1-curve-perverse-simples.md`, middle-extension bullet
and irreducibility sentence (blueprint: prop-a1-curve-perverse-simples). -/
def IsMiddleSimple_legacy {k : Type u} [Field k]
    (hk : (Finite k ∨ IsAlgClosed k) ∧ ∀ x : k, x ≠ 0 → IsOfFinOrder x)
    (C : Over (Spec (.of k))) [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    (P : GeometricPerv_legacy ell hk C) : Prop :=
  ∃ (U : Scheme.{u}) (j : U ⟶ C.left), IsOpenImmersion j ∧ DenseRange j ∧
    ∃ (N : CurvePerverseHeartStatement.Modules ell U)
      (hN : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) N),
      ¬ IsZero N ∧
      Simple (⟨N, hN⟩ : ObjectProperty.FullSubcategory
        (IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell))) ∧
      Nonempty (P.obj.obj ≅
        ((DerivedCategory.singleFunctor _ 0).obj
          ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ell) j).obj N))⟦(1 : ℤ)⟧)

/-- The two geometric alternatives in the classification of simple perverse objects.
Source: latest blueprint, `prop-a1-curve-perverse-simples.md`, both bullets
(blueprint: prop-a1-curve-perverse-simples). -/
def SimplePerverseKinds_legacy {k : Type u} [Field k]
    (hk : (Finite k ∨ IsAlgClosed k) ∧ ∀ x : k, x ≠ 0 → IsOfFinOrder x)
    (C : Over (Spec (.of k))) [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    (P : GeometricPerv_legacy ell hk C) : Prop :=
  IsPunctualSimple_legacy ell hk C P ∨ IsMiddleSimple_legacy ell hk C P

/-- Every simple geometric perverse object is exactly one of the punctual or
middle-extension alternatives, and each listed alternative is simple.
Source: latest blueprint, `prop-a1-curve-perverse-simples.md`, final paragraph.
Proof: (1) Work with H^a = ℋ^a and heart clauses (1)-(5). The coefficient heart gives
common dense lisse opens and constructible kernels and cokernels; dense opens of the
curve have finite complements; j^*j_* = 1 by open base change and G = i_*i^*G when
j^*G = 0 by localization; sheaf exact sequences give triangles.
(2) For F lisse on U put F_p = ker(F → j_*j^*F): it is the largest punctual subsheaf
and F/F_p has none; j_*N and lisse sheaves have no punctual subsheaf.
(3) Punctual objects are simple: for 0 → Q → i_{x*}E → R → 0, clause (5) gives
H⁻¹Q = 0 and H⁻¹R ⊂ H⁰Q punctual, hence zero; H⁰Q is a submodule of E, so Q = 0
or R = 0.
(4) Middle extensions are simple: for 0 → Q → (j_*N)[1] → R → 0 restrict
0 → H⁻¹Q → j_*N → H⁻¹R → H⁰Q → 0 to a dense U' ⊂ U where N stays irreducible
(dense-open surjectivity of π₁). If H⁻¹Q vanishes on U' then the injective unit
H⁻¹R → j'_*j'^*H⁻¹R shows j_*N ≅ H⁻¹R, so Q = 0; otherwise H⁻¹R is punctual, R = 0.
(5) A simple P has H⁻¹P = 0 or H⁰P = 0. If H⁻¹P = 0, then P = G[0] with G punctual,
G = ⊕ i_{x*}E_x, and subsheaf sequences are perverse, so P = i_{x*}E, E irreducible.
(6) If H⁰P = 0, then P = F[1]; with N = j^*F lisse, F → j_*N is monic with punctual
cokernel T, and 0 → T[0] → P → (j_*N)[1] → 0 is exact in the heart, so T = 0.
(7) If 0 ≠ N' ⊊ N is lisse, saturate the cokernel C of j_*N' → j_*N by its punctual
radical; 0 → F' → j_*N → C/C_p → 0 gives a nontrivial perverse sequence, contradiction.
(blueprint: prop-a1-curve-perverse-simples). -/
theorem curve_perverse_simples_statement_legacy
    {k : Type u} [Field k] [PerfectField k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hk : (Finite k ∨ IsAlgClosed k) ∧ ∀ x : k, x ≠ 0 → IsOfFinOrder x)
    (C : Over (Spec (.of k))) [LocallyOfFiniteType C.hom] [QuasiCompact C.hom]
    [IsSeparated C.hom] [Smooth C.hom] (_hPure : Scheme.IsPureDimension C.left 1) :
    ∀ P : GeometricPerv_legacy ell hk C,
      Simple P ↔ SimplePerverseKinds_legacy ell hk C P := by
  sorry

/-- The Weil perverse heart: the full subcategory of derived Weil complexes whose
underlying geometric complexes lie in the support and cosupport classes of
`thm-a1-curve-perverse-heart`, Weil convention.
Source: latest blueprint, `prop-a1-curve-perverse-simples.md`, Perv(C) in the Weil case
(blueprint: prop-a1-curve-perverse-simples). -/
abbrev WeilPerv_legacy (D : WeilConjectures.FiniteFieldDatum.{u})
    (C₀ : Over (Spec (.of D.k₀))) [Invertible (ell : D.k)]
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] [IsSeparated C₀.hom] :=
  (CurvePerverseHeartStatement.WeilLEZero D ell C₀ ⊓
    CurvePerverseHeartStatement.WeilGEZero D ell C₀).FullSubcategory

/-- The punctual Weil alternative, with an irreducible constructible Weil module at a
closed point and its canonical degree-zero middle image.
Source: latest blueprint, `prop-a1-curve-perverse-simples.md`, punctual bullet and
the Weil convention in `thm-a1-curve-perverse-heart`
(blueprint: prop-a1-curve-perverse-simples). -/
def IsWeilPunctualSimple_legacy (D : WeilConjectures.FiniteFieldDatum.{u})
    (C₀ : Over (Spec (.of D.k₀))) [Invertible (ell : D.k)]
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] [IsSeparated C₀.hom]
    (P : WeilPerv_legacy ell D C₀) : Prop :=
  ∃ (x : C₀.left) (hx : IsClosed ({x} : Set C₀.left)),
    letI : IsClosedImmersion (C₀.left.fromSpecResidueField x) :=
      (AlgebraicGeometry.isClosed_singleton_iff_isClosedImmersion).mp hx
    let Z₀ := Over.mk (C₀.left.fromSpecResidueField x ≫ C₀.hom)
    letI : LocallyOfFiniteType Z₀.hom := inferInstanceAs
      (LocallyOfFiniteType (C₀.left.fromSpecResidueField x ≫ C₀.hom))
    letI : QuasiCompact Z₀.hom := inferInstanceAs
      (QuasiCompact (C₀.left.fromSpecResidueField x ≫ C₀.hom))
    let i₀ : Z₀ ⟶ C₀ := Over.homMk (C₀.left.fromSpecResidueField x)
    ∃ (E : WeilConjectures.NativeL2.WeilModule D ell Z₀)
      (hE : IsConstructibleModuleObject
        (condensedRingObj (Profinite.padicAlgClRingObj ell)
          (D.geometricFiber Z₀).left) E.carrier),
      Simple (⟨E, hE⟩ : WeilConjectures.condensedConstructibleWeilSheaves
        (Profinite.padicAlgClRingObj ell) (D.geometricFrobenius Z₀).hom) ∧
      Nonempty (P.obj.obj ≅
        (DerivedCategory.singleFunctor _ 0).obj
          (WeilConjectures.NativeL2.middleWeilImage D ell i₀ E))

/-- A shifted middle extension of a nonzero simple lisse Weil sheaf on a dense open.
Source: latest blueprint, `prop-a1-curve-perverse-simples.md`, middle-extension bullet
and the Weil convention in `thm-a1-curve-perverse-heart`
(blueprint: prop-a1-curve-perverse-simples). -/
def IsWeilMiddleSimple_legacy (D : WeilConjectures.FiniteFieldDatum.{u})
    (C₀ : Over (Spec (.of D.k₀))) [Invertible (ell : D.k)]
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] [IsSeparated C₀.hom]
    (P : WeilPerv_legacy ell D C₀) : Prop :=
  ∃ U₀ : Over (Spec (.of D.k₀)),
    Exists fun [_hft : LocallyOfFiniteType U₀.hom] ↦
      Exists fun [_hqc : QuasiCompact U₀.hom] ↦
        ∃ (j₀ : U₀ ⟶ C₀), IsOpenImmersion j₀.left ∧ DenseRange j₀.left ∧
          ∃ (M : WeilConjectures.NativeL2.WeilModule D ell U₀)
            (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) M.carrier),
            ¬ IsZero M ∧
            Simple (⟨M, hM⟩ : ObjectProperty.FullSubcategory
              (fun N : WeilConjectures.NativeL2.WeilModule D ell U₀ ↦
                IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) N.carrier)) ∧
            Nonempty (P.obj.obj ≅
              ((DerivedCategory.singleFunctor _ 0).obj
                (WeilConjectures.NativeL2.middleWeilImage D ell j₀ M))⟦(1 : ℤ)⟧)

/-- The two Weil alternatives in the classification.
Source: latest blueprint, `prop-a1-curve-perverse-simples.md`, both bullets
(blueprint: prop-a1-curve-perverse-simples). -/
def WeilSimpleKinds_legacy (D : WeilConjectures.FiniteFieldDatum.{u})
    (C₀ : Over (Spec (.of D.k₀))) [Invertible (ell : D.k)]
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] [IsSeparated C₀.hom]
    (P : WeilPerv_legacy ell D C₀) : Prop :=
  IsWeilPunctualSimple_legacy ell D C₀ P ∨ IsWeilMiddleSimple_legacy ell D C₀ P

/-- The same classification for the perverse Weil heart.
Source: latest blueprint, `prop-a1-curve-perverse-simples.md`, final paragraph and
the Weil convention of `thm-a1-curve-perverse-heart`.
Proof: run steps (1)-(7) of the geometric statement on Weil modules. Kernels and
cokernels of fixed pairs are computed on the underlying sheaves and carry their
canonical Weil structures, so the punctual radical, the restriction units, the
sequences and the saturation are Weil morphisms; heart clauses (1)-(5) hold verbatim in
the Weil case. Irreducibility is taken among Weil-stable lisse (resp. constructible)
subsheaves, so the dense-open step uses surjectivity on Weil groups.
(blueprint: prop-a1-curve-perverse-simples). -/
theorem curve_perverse_weil_simples_statement_legacy
    (D : WeilConjectures.FiniteFieldDatum.{u}) [Invertible (ell : D.k)]
    (C₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType C₀.hom]
    [QuasiCompact C₀.hom] [IsSeparated C₀.hom] [Smooth C₀.hom]
    (_hPure : Scheme.IsPureDimension C₀.left 1) :
    ∀ P : WeilPerv_legacy ell D C₀,
      Simple P ↔ WeilSimpleKinds_legacy ell D C₀ P := by
  sorry

/-- The perverse heart Perv(C): the full subcategory of the intersection of the
support and cosupport classes of `thm-a1-curve-perverse-heart`, clause (2), inside the
bounded constructible complexes, with its inherited morphisms.
Source: latest blueprint, `prop-a1-curve-perverse-simples.md`, "the abelian category
Perv(C)" (blueprint: prop-a1-curve-perverse-simples). -/
abbrev GeometricPerv {k : Type u} [Field k]
    (hk : Finite k ∨ IsAlgClosed k)
    (C : Over (Spec (.of k))) [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom] :=
  (CondensedRing.FiniteOrClosedPerverseLEZero ell hk C ⊓
    CondensedRing.FiniteOrClosedPerverseGEZero ell hk C).FullSubcategory

/-- A degree-zero punctual simple: an irreducible constructible sheaf on a closed point,
transported to the curve by the ordinary direct image.
Source: latest blueprint, `prop-a1-curve-perverse-simples.md`, punctual bullet
(blueprint: prop-a1-curve-perverse-simples). -/
def IsPunctualSimple {k : Type u} [Field k]
    (hk : Finite k ∨ IsAlgClosed k)
    (C : Over (Spec (.of k))) [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    (P : GeometricPerv ell hk C) : Prop :=
  ∃ (x : C.left), IsClosed ({x} : Set C.left) ∧
    ∃ (E : CondensedCurvePerverse.Modules (Profinite.padicAlgClRingObj ell)
        (Spec (C.left.residueField x)))
      (hE : IsConstructibleModuleObject
        (condensedRingObj (Profinite.padicAlgClRingObj ell)
          (Spec (C.left.residueField x))) E),
      Simple (⟨E, hE⟩ : ObjectProperty.FullSubcategory
        (IsConstructibleModuleObject
          (condensedRingObj (Profinite.padicAlgClRingObj ell)
            (Spec (C.left.residueField x)))) ) ∧
      Nonempty (P.obj.obj ≅
        (DerivedCategory.singleFunctor _ 0).obj
          ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ell)
            (C.left.fromSpecResidueField x)).obj E))

/-- A shifted middle extension of a nonzero simple lisse sheaf on a dense open.
Source: latest blueprint, `prop-a1-curve-perverse-simples.md`, middle-extension bullet
and irreducibility sentence (blueprint: prop-a1-curve-perverse-simples). -/
def IsMiddleSimple {k : Type u} [Field k]
    (hk : Finite k ∨ IsAlgClosed k)
    (C : Over (Spec (.of k))) [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    (P : GeometricPerv ell hk C) : Prop :=
  ∃ (U : Scheme.{u}) (j : U ⟶ C.left), IsOpenImmersion j ∧ DenseRange j ∧
    ∃ (N : CondensedCurvePerverse.Modules (Profinite.padicAlgClRingObj ell) U)
      (hN : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) N),
      ¬ IsZero N ∧
      Simple (⟨N, hN⟩ : ObjectProperty.FullSubcategory
        (IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell))) ∧
      Nonempty (P.obj.obj ≅
        ((DerivedCategory.singleFunctor _ 0).obj
          ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ell) j).obj N))⟦(1 : ℤ)⟧)

/-- The two geometric alternatives in the classification of simple perverse objects.
Source: latest blueprint, `prop-a1-curve-perverse-simples.md`, both bullets
(blueprint: prop-a1-curve-perverse-simples). -/
def SimplePerverseKinds {k : Type u} [Field k]
    (hk : Finite k ∨ IsAlgClosed k)
    (C : Over (Spec (.of k))) [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    (P : GeometricPerv ell hk C) : Prop :=
  IsPunctualSimple ell hk C P ∨ IsMiddleSimple ell hk C P

/-- The canonical heart truncation sequence of a simple object has a zero endpoint. -/
private theorem simple_cohomology_dichotomy
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (Q : ObjectProperty (DerivedCategory A))
    (leZero geZero : ObjectProperty Q.FullSubcategory)
    (P : (leZero ⊓ geZero).FullSubcategory) [Simple P]
    (S : ShortComplex (leZero ⊓ geZero).FullSubcategory)
    (hmid : S.X₂ = P) (hS : S.ShortExact)
    (hB : Nonempty (S.X₁.obj.obj ≅
      ((DerivedCategory.singleFunctor A 0).obj
        ((DerivedCategory.homologyFunctor A (-1)).obj P.obj.obj))⟦(1 : ℤ)⟧))
    (hC : Nonempty (S.X₃.obj.obj ≅ (DerivedCategory.singleFunctor A 0).obj
      ((DerivedCategory.homologyFunctor A 0).obj P.obj.obj))) :
    IsZero ((DerivedCategory.homologyFunctor A (-1)).obj P.obj.obj) ∨
      IsZero ((DerivedCategory.homologyFunctor A 0).obj P.obj.obj) := by
  obtain ⟨eB⟩ := hB
  obtain ⟨eC⟩ := hC
  have : Simple S.X₂ := hmid.symm ▸ inferInstance
  let I := ObjectProperty.ι (leZero ⊓ geZero) ⋙ ObjectProperty.ι Q
  obtain hB | hC := hS.isZero_left_or_right
  · left
    have hB' := (I.map_isZero hB).of_iso eB.symm
    have hsingle := IsZero.of_full_of_faithful_of_isZero
      (shiftFunctor (DerivedCategory A) (1 : ℤ)) _ hB'
    exact IsZero.of_full_of_faithful_of_isZero (DerivedCategory.singleFunctor A 0) _ hsingle
  · right
    exact IsZero.of_full_of_faithful_of_isZero (DerivedCategory.singleFunctor A 0) _
      ((I.map_isZero hC).of_iso eC.symm)

/-- A punctual presentation has no ordinary cohomology in degree -1. -/
private theorem punctual_homology_neg_one_zero
    {k : Type u} [Field k]
    (hk : Finite k ∨ IsAlgClosed k)
    (C : Over (Spec (.of k))) [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    (P : GeometricPerv ell hk C) (hP : IsPunctualSimple ell hk C P) :
    IsZero ((DerivedCategory.homologyFunctor _ (-1)).obj P.obj.obj) := by
  obtain ⟨x, hx, E, hE, hsimple, ⟨e⟩⟩ := hP
  exact ((DerivedCategory.isGE_iff _ 0).mp inferInstance (-1) (by decide)).of_iso
    ((DerivedCategory.homologyFunctor _ (-1)).mapIso e)

/-- A shifted ordinary middle-image presentation has no ordinary degree-zero cohomology. -/
private theorem middle_homology_zero_zero
    {k : Type u} [Field k]
    (hk : Finite k ∨ IsAlgClosed k)
    (C : Over (Spec (.of k))) [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    (P : GeometricPerv ell hk C) (hP : IsMiddleSimple ell hk C P) :
    IsZero ((DerivedCategory.homologyFunctor _ 0).obj P.obj.obj) := by
  obtain ⟨U, j, hj, hdense, N, hN, hnz, hsimple, ⟨e⟩⟩ := hP
  let F := (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ell) j).obj N
  have : ((DerivedCategory.singleFunctor _ 0).obj F)⟦(1 : ℤ)⟧ |>.IsLE (-1) :=
    DerivedCategory.TStructure.t.isLE_shift _ 0 1 (-1) (by decide)
  exact ((DerivedCategory.isLE_iff _ (-1)).mp this 0 (by decide)).of_iso
    ((DerivedCategory.homologyFunctor _ 0).mapIso e)

/-- The ordinary cohomology of a simple support-defined heart object is pure. -/
private theorem geometric_simple_cohomology_dichotomy
    {k : Type u} [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ell)]
    (hk : Finite k ∨ IsAlgClosed k)
    (C : Over (Spec (.of k))) [LocallyOfFiniteType C.hom] [QuasiCompact C.hom]
    [IsSeparated C.hom] [Smooth C.hom] (hPure : Scheme.IsPureDimension C.left 1)
    (P : GeometricPerv ell hk C) [Simple P] :
    IsZero ((DerivedCategory.homologyFunctor _ (-1)).obj P.obj.obj) ∨
      IsZero ((DerivedCategory.homologyFunctor _ 0).obj P.obj.obj) := by
  have h := CondensedRing.curveSupportHeart ell hk C hPure
  obtain ⟨A, B, S, hA, hP, hB, hS, e₁, e₂, h₁, h₂, hmaps⟩ := h.2.2.2.1 P
  apply simple_cohomology_dichotomy _ _ _ P S hP hS
  · simpa only [hA] using h₁
  · simpa only [hB] using h₂

/-- Every simple geometric perverse object is exactly one of the punctual or
middle-extension alternatives, and each listed alternative is simple.
Source: latest blueprint, `prop-a1-curve-perverse-simples.md`, final paragraph.
Proof: Use heart clauses (1)-(5). Punctual simplicity follows from the six-term
sequence: H⁻¹Q is zero and H⁻¹R embeds into punctual H⁰Q, hence is zero; the remaining
subsheaf corresponds to a submodule at x. For a middle extension, restrict the six-term
sequence to a dense lisse open. The irreducibility dichotomy in
lem-wf-dense-open-pi1-surjective (4) says the restricted subobject is zero or full.
In case (a) the restriction unit and its lisse-unit comparison from (3) force Q = 0;
in case (b) the quotient is punctual and punctual-free, hence R = 0.
For classification, the canonical truncation sequence forces H⁻¹P = 0 or H⁰P = 0.
In the first case the finite-support direct sum has exactly one simple summand.
In the second case the injective unit F → j_*N has punctual cokernel T. Its rotated
triangle is short exact in the heart by lem-weil-heart-short-exact-triangles (4),
so simplicity kills T. Finally saturating a proposed nontrivial lisse subobject
by the maximal punctual subsheaf of its cokernel gives a forbidden short exact
heart sequence, proving N irreducible. The case lemmas retain precisely these steps.
(blueprint: prop-a1-curve-perverse-simples). -/
theorem curve_perverse_simples_statement
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hk : Finite k ∨ IsAlgClosed k)
    (C : Over (Spec (.of k))) [LocallyOfFiniteType C.hom] [QuasiCompact C.hom]
    [IsSeparated C.hom] [Smooth C.hom] (_hPure : Scheme.IsPureDimension C.left 1) :
    ∀ P : GeometricPerv ell hk C,
      Simple P ↔ SimplePerverseKinds ell hk C P := by
  intro P
  constructor
  · intro hP
    have := hP
    obtain h | h := geometric_simple_cohomology_dichotomy ell hk C _hPure P
    · exact Or.inl ((geometric_punctual_simple_case ell hk C _hPure P h).mp hP)
    · exact Or.inr ((geometric_middle_simple_case ell hk C _hPure P h).mp hP)
  · rintro (hP | hP)
    · exact (geometric_punctual_simple_case ell hk C _hPure P
        (punctual_homology_neg_one_zero ell hk C P hP)).mpr hP
    · exact (geometric_middle_simple_case ell hk C _hPure P
        (middle_homology_zero_zero ell hk C P hP)).mpr hP

/-- The Weil perverse heart: the full subcategory of derived Weil complexes whose
underlying geometric complexes lie in the support and cosupport classes of
`thm-a1-curve-perverse-heart`, Weil convention.
Source: latest blueprint, `prop-a1-curve-perverse-simples.md`, Perv(C) in the Weil case
(blueprint: prop-a1-curve-perverse-simples). -/
abbrev WeilPerv (D : WeilConjectures.FiniteFieldDatum.{u})
    (C₀ : Over (Spec (.of D.k₀))) [Fact (ringChar D.k).Prime]
    [Fact (ringChar D.k ≠ ell)]
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] [IsSeparated C₀.hom] [Smooth C₀.hom] :=
  (CondensedRing.CurveWeil.upperZero D ell C₀ ⊓
    CondensedRing.CurveWeil.lowerZero D ell C₀).FullSubcategory

/-- The punctual Weil alternative, with an irreducible constructible Weil module at a
closed point and its canonical degree-zero middle image.
Source: latest blueprint, `prop-a1-curve-perverse-simples.md`, punctual bullet and
the Weil convention in `thm-a1-curve-perverse-heart`
(blueprint: prop-a1-curve-perverse-simples). -/
def IsWeilPunctualSimple (D : WeilConjectures.FiniteFieldDatum.{u})
    (C₀ : Over (Spec (.of D.k₀))) [Fact (ringChar D.k).Prime]
    [Fact (ringChar D.k ≠ ell)]
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] [IsSeparated C₀.hom] [Smooth C₀.hom]
    (P : WeilPerv ell D C₀) : Prop :=
  ∃ (x : C₀.left) (hx : IsClosed ({x} : Set C₀.left)),
    letI : IsClosedImmersion (C₀.left.fromSpecResidueField x) :=
      (AlgebraicGeometry.isClosed_singleton_iff_isClosedImmersion).mp hx
    let Z₀ := Over.mk (C₀.left.fromSpecResidueField x ≫ C₀.hom)
    letI : LocallyOfFiniteType Z₀.hom := inferInstanceAs
      (LocallyOfFiniteType (C₀.left.fromSpecResidueField x ≫ C₀.hom))
    letI : QuasiCompact Z₀.hom := inferInstanceAs
      (QuasiCompact (C₀.left.fromSpecResidueField x ≫ C₀.hom))
    let i₀ : Z₀ ⟶ C₀ := Over.homMk (C₀.left.fromSpecResidueField x)
    ∃ (E : WeilConjectures.NativeL2.WeilModule D ell Z₀)
      (hE : IsConstructibleModuleObject
        (condensedRingObj (Profinite.padicAlgClRingObj ell)
          (D.geometricFiber Z₀).left) E.carrier),
      Simple (⟨E, hE⟩ : WeilConjectures.condensedConstructibleWeilSheaves
        (Profinite.padicAlgClRingObj ell) (D.geometricFrobenius Z₀).hom) ∧
      Nonempty (P.obj.obj ≅
        (DerivedCategory.singleFunctor _ 0).obj
          (WeilConjectures.NativeL2.middleWeilImage D ell i₀ E))

/-- A shifted middle extension of a nonzero simple lisse Weil sheaf on a dense open.
Source: latest blueprint, `prop-a1-curve-perverse-simples.md`, middle-extension bullet
and the Weil convention in `thm-a1-curve-perverse-heart`
(blueprint: prop-a1-curve-perverse-simples). -/
def IsWeilMiddleSimple (D : WeilConjectures.FiniteFieldDatum.{u})
    (C₀ : Over (Spec (.of D.k₀))) [Fact (ringChar D.k).Prime]
    [Fact (ringChar D.k ≠ ell)]
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] [IsSeparated C₀.hom] [Smooth C₀.hom]
    (P : WeilPerv ell D C₀) : Prop :=
  ∃ U₀ : Over (Spec (.of D.k₀)),
    Exists fun [_hft : LocallyOfFiniteType U₀.hom] ↦
      Exists fun [_hqc : QuasiCompact U₀.hom] ↦
        ∃ (j₀ : U₀ ⟶ C₀), IsOpenImmersion j₀.left ∧ DenseRange j₀.left ∧
          ∃ (M : WeilConjectures.NativeL2.WeilModule D ell U₀)
            (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) M.carrier),
            ¬ IsZero M ∧
            Simple (⟨M, hM⟩ : ObjectProperty.FullSubcategory
              (fun N : WeilConjectures.NativeL2.WeilModule D ell U₀ ↦
                IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) N.carrier)) ∧
            Nonempty (P.obj.obj ≅
              ((DerivedCategory.singleFunctor _ 0).obj
                (WeilConjectures.NativeL2.middleWeilImage D ell j₀ M))⟦(1 : ℤ)⟧)

/-- The two Weil alternatives in the classification.
Source: latest blueprint, `prop-a1-curve-perverse-simples.md`, both bullets
(blueprint: prop-a1-curve-perverse-simples). -/
def WeilSimpleKinds (D : WeilConjectures.FiniteFieldDatum.{u})
    (C₀ : Over (Spec (.of D.k₀))) [Fact (ringChar D.k).Prime]
    [Fact (ringChar D.k ≠ ell)]
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] [IsSeparated C₀.hom] [Smooth C₀.hom]
    (P : WeilPerv ell D C₀) : Prop :=
  IsWeilPunctualSimple ell D C₀ P ∨ IsWeilMiddleSimple ell D C₀ P

/-- A punctual Weil presentation is concentrated in ordinary degree zero. -/
private theorem weil_punctual_homology_neg_one_zero
    (D : WeilConjectures.FiniteFieldDatum.{u}) [Fact (ringChar D.k).Prime]
    [Fact (ringChar D.k ≠ ell)]
    (C₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType C₀.hom]
    [QuasiCompact C₀.hom] [IsSeparated C₀.hom] [Smooth C₀.hom]
    (P : WeilPerv ell D C₀) (hP : IsWeilPunctualSimple ell D C₀ P) :
    IsZero ((DerivedCategory.homologyFunctor _ (-1)).obj P.obj.obj) := by
  obtain ⟨x, hx, E, hE, hsimple, ⟨e⟩⟩ := hP
  exact ((DerivedCategory.isGE_iff _ 0).mp inferInstance (-1) (by decide)).of_iso
    ((DerivedCategory.homologyFunctor _ (-1)).mapIso e)

/-- A shifted ordinary Weil middle image has no degree-zero ordinary cohomology. -/
private theorem weil_middle_homology_zero_zero
    (D : WeilConjectures.FiniteFieldDatum.{u}) [Fact (ringChar D.k).Prime]
    [Fact (ringChar D.k ≠ ell)]
    (C₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType C₀.hom]
    [QuasiCompact C₀.hom] [IsSeparated C₀.hom] [Smooth C₀.hom]
    (P : WeilPerv ell D C₀) (hP : IsWeilMiddleSimple ell D C₀ P) :
    IsZero ((DerivedCategory.homologyFunctor _ 0).obj P.obj.obj) := by
  obtain ⟨U₀, hft, hqc, j₀, hj, hdense, M, hM, hnz, hsimple, ⟨e⟩⟩ := hP
  let F := WeilConjectures.NativeL2.middleWeilImage D ell j₀ M
  have : ((DerivedCategory.singleFunctor _ 0).obj F)⟦(1 : ℤ)⟧ |>.IsLE (-1) :=
    DerivedCategory.TStructure.t.isLE_shift _ 0 1 (-1) (by decide)
  exact ((DerivedCategory.isLE_iff _ (-1)).mp this 0 (by decide)).of_iso
    ((DerivedCategory.homologyFunctor _ 0).mapIso e)

/-- The canonical truncation sequence also gives purity before forgetting Weil structure. -/
private theorem weil_simple_cohomology_dichotomy
    (D : WeilConjectures.FiniteFieldDatum.{u}) [Fact (ringChar D.k).Prime]
    [Fact (ringChar D.k ≠ ell)]
    (C₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType C₀.hom]
    [QuasiCompact C₀.hom] [IsSeparated C₀.hom] [Smooth C₀.hom]
    (hPure : Scheme.IsPureDimension C₀.left 1)
    (P : WeilPerv ell D C₀) [Simple P] :
    IsZero ((DerivedCategory.homologyFunctor _ (-1)).obj P.obj.obj) ∨
      IsZero ((DerivedCategory.homologyFunctor _ 0).obj P.obj.obj) := by
  have h := CondensedRing.CurveWeil.curveSupportWeilHeart D ell C₀ hPure
  obtain ⟨A, B, S, hA, hP, hB, hS, e₁, e₂, h₁, h₂, hmaps⟩ := h.2.2.2.1 P
  apply simple_cohomology_dichotomy _ _ _ P S hP hS
  · simpa only [hA] using h₁
  · simpa only [hB] using h₂

/-- The same classification for the perverse Weil heart.
Source: latest blueprint, `prop-a1-curve-perverse-simples.md`, final paragraph and
the Weil convention of `thm-a1-curve-perverse-heart`.
Proof: run steps (1)-(7) of the geometric statement on Weil modules. Kernels and
cokernels of Weil modules carry their canonical Weil structures, so the punctual
radical, the restriction units, the
sequences and saturation are Weil morphisms; heart clauses (1)-(5) hold verbatim in
the Weil case. Irreducibility is taken among Weil-stable lisse (resp. constructible)
subsheaves, so the dense-open step uses surjectivity on Weil groups.
(blueprint: prop-a1-curve-perverse-simples). -/
theorem curve_perverse_weil_simples_statement
    (D : WeilConjectures.FiniteFieldDatum.{u}) [Fact (ringChar D.k).Prime]
    [Fact (ringChar D.k ≠ ell)]
    (C₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType C₀.hom]
    [QuasiCompact C₀.hom] [IsSeparated C₀.hom] [Smooth C₀.hom]
    (_hPure : Scheme.IsPureDimension C₀.left 1) :
    ∀ P : WeilPerv ell D C₀,
      Simple P ↔ WeilSimpleKinds ell D C₀ P := by
  intro P
  constructor
  · intro hP
    have := hP
    obtain h | h := weil_simple_cohomology_dichotomy ell D C₀ _hPure P
    · exact Or.inl ((weil_punctual_simple_case ell D C₀ _hPure P h).mp hP)
    · exact Or.inr ((weil_middle_simple_case ell D C₀ _hPure P h).mp hP)
  · rintro (hP | hP)
    · exact (weil_punctual_simple_case ell D C₀ _hPure P
        (weil_punctual_homology_neg_one_zero ell D C₀ P hP)).mpr hP
    · exact (weil_middle_simple_case ell D C₀ _hPure P
        (weil_middle_homology_zero_zero ell D C₀ P hP)).mpr hP

end AlgebraicGeometry.ProEtale.CondensedCurvePerverseStatement
