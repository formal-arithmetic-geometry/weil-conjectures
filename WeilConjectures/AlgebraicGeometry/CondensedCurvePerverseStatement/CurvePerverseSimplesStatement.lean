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
def IsMiddleSimple {k : Type u} [Field k]
    (hk : Finite k ∨ IsAlgClosed k)
    (C : Over (Spec (.of k))) [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    (P : GeometricPerv ell hk C) : Prop :=
  CondensedCurvePerverse.IsGeometricSimpleMiddle
    (Profinite.padicAlgClRingObj ell) C.left P.obj.obj

/-- The two geometric alternatives in the classification of simple perverse objects.
Source: latest blueprint, `prop-a1-curve-perverse-simples.md`, both bullets
(blueprint: prop-a1-curve-perverse-simples). -/
def SimplePerverseKinds {k : Type u} [Field k]
    (hk : Finite k ∨ IsAlgClosed k)
    (C : Over (Spec (.of k))) [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    (P : GeometricPerv ell hk C) : Prop :=
  IsPunctualSimple ell hk C P ∨ IsMiddleSimple ell hk C P

/-- Every simple geometric perverse object is punctual or a shifted ordinary middle extension,
and every listed object is simple.
Source: latest blueprint, prop-a1-curve-perverse-simples.md, both bullets and final sentence;
field scope: thm-a1-curve-perverse-heart, Wei Yang #1441 item 36.
Proof: Use heart clauses (1)--(5). For a perverse subobject of i_*E, the six-term sequence
makes H^-1(Q) and H^-1(R) zero; supported subsheaves correspond to submodules of E.
For P=(j_*N)[1], restrict the six-term sequence to a dense lisse open U' avoiding H^0(Q).
Dense-open surjectivity preserves irreducibility. In case (a), H^-1(Q)|U'=0, so H^-1(Q)=0.
The unit H^-1(R) -> j'_*j'^*H^-1(R) is injective since its kernel is punctual. Its
composite with j_*N is j_* of the lisse unit isomorphism. Thus H^0(Q)=0 and Q=0.
In case (b), H^-1(Q)|U'=N|U', so H^-1(R) is punctual and zero, giving R=0.
Conversely, the canonical perverse truncation sequence makes a simple P either G[0]
with G punctual, or F[1] with F punctual-free. Decomposition of G over its finite
closed support leaves one irreducible summand. In the other case F -> j_*j^*F is
monic with punctual cokernel T. Rotation gives 0 -> T[0] -> P -> (j_*N)[1] -> 0,
so T=0. For a proper nonzero lisse N' in N, form C=coker(j_*N' -> j_*N), remove
its largest punctual subsheaf C_p, and set F'=ker(j_*N -> C/C_p). The shifted
sequence has nonzero endpoints restricting to N' and N/N', contradicting simplicity.
(blueprint: prop-a1-curve-perverse-simples). -/
theorem curve_perverse_simples_statement
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hk : Finite k ∨ IsAlgClosed k)
    (C : Over (Spec (.of k))) [LocallyOfFiniteType C.hom] [QuasiCompact C.hom]
    [IsSeparated C.hom] [Smooth C.hom] (_hPure : Scheme.IsPureDimension C.left 1) :
    ∀ P : GeometricPerv ell hk C,
      Simple P ↔ SimplePerverseKinds ell hk C P := by
  sorry

/-- The Weil perverse heart: the full subcategory of Frobenius pairs whose
underlying geometric complexes lie in the support and cosupport classes of
`thm-a1-curve-perverse-heart`, Weil convention.
Source: latest blueprint, `prop-a1-curve-perverse-simples.md`, Perv(C) in the Weil case
(blueprint: prop-a1-curve-perverse-simples). -/
abbrev WeilPerv (D : WeilConjectures.FiniteFieldDatum.{u})
    (C₀ : Over (Spec (.of D.k₀))) [Invertible (ell : D.k)]
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] [IsSeparated C₀.hom] :=
  ObjectProperty.FullSubcategory
    (fun K : Endofunctor.IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ell)
        (D.geometricFrobenius C₀).hom).mapDerivedCategory ↦
      ∃ hK : boundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj ell)
          (D.geometricFiber C₀).left) K.carrier,
        CondensedRing.FiniteOrClosedPerverseHeart ell
          (CurvePerverseHeartStatement.closure_baseField D).1
          (D.geometricFiber C₀) ⟨K.carrier, hK⟩)

/-- The punctual Weil alternative, with an irreducible constructible Weil module at a
closed point and its canonical degree-zero direct image.
Source: latest blueprint, `prop-a1-curve-perverse-simples.md`, punctual bullet and
the Weil convention in `thm-a1-curve-perverse-heart`
(blueprint: prop-a1-curve-perverse-simples). -/
def IsWeilPunctualSimple (D : WeilConjectures.FiniteFieldDatum.{u})
    (C₀ : Over (Spec (.of D.k₀))) [Invertible (ell : D.k)]
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] [IsSeparated C₀.hom]
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
      Nonempty (P.obj ≅
        (CondensedCurvePerverse.weilPlaced (Profinite.padicAlgClRingObj ell)
          (D.geometricFrobenius C₀) 0).obj
            (WeilConjectures.NativeL2.middleWeilImage D ell i₀ E))

/-- A shifted middle extension of a nonzero simple lisse Weil sheaf on a dense open.
Source: latest blueprint, `prop-a1-curve-perverse-simples.md`, middle-extension bullet
and the Weil convention in `thm-a1-curve-perverse-heart`
(blueprint: prop-a1-curve-perverse-simples). -/
def IsWeilMiddleSimple (D : WeilConjectures.FiniteFieldDatum.{u})
    (C₀ : Over (Spec (.of D.k₀))) [Invertible (ell : D.k)]
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] [IsSeparated C₀.hom]
    (P : WeilPerv ell D C₀) : Prop :=
  CondensedCurvePerverse.IsWeilSimpleMiddle D ell C₀ P.obj

/-- The two Weil alternatives in the classification.
Source: latest blueprint, `prop-a1-curve-perverse-simples.md`, both bullets
(blueprint: prop-a1-curve-perverse-simples). -/
def WeilSimpleKinds (D : WeilConjectures.FiniteFieldDatum.{u})
    (C₀ : Over (Spec (.of D.k₀))) [Invertible (ell : D.k)]
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] [IsSeparated C₀.hom]
    (P : WeilPerv ell D C₀) : Prop :=
  IsWeilPunctualSimple ell D C₀ P ∨ IsWeilMiddleSimple ell D C₀ P

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
theorem curve_perverse_weil_simples_statement
    (D : WeilConjectures.FiniteFieldDatum.{u}) [Invertible (ell : D.k)]
    (C₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType C₀.hom]
    [QuasiCompact C₀.hom] [IsSeparated C₀.hom] [Smooth C₀.hom]
    (_hPure : Scheme.IsPureDimension C₀.left 1) :
    ∀ P : WeilPerv ell D C₀,
      Simple P ↔ WeilSimpleKinds ell D C₀ P := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedCurvePerverseStatement
