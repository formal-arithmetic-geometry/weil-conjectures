/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportCoefficientChange
public import WeilConjectures.AlgebraicGeometry.FiniteCompactCoefficients.FiniteCoefficientCompactSupportCompatibility
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.FiniteCompactificationTranspose.FiniteRingCompactificationTransposeComparison
public import WeilConjectures.SixFunctors.Etale.Derived.PointUnit
public import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientOrdinary.FiniteCoefficientOrdinaryDirectImage
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedMorphismSheafComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMateData
public import WeilConjectures.AlgebraicGeometry.Support.SupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedOriginScalarComparisons
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.AlgebraicGeometry.OpenScalarOperations.OpenScalarOperations

/-!
# General-field finite dualizing coefficient change

This file states the finite coefficient-change package for ordinary etale and finite
pro-etale compact support. The source is
`literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
lem-coef-finite-dualizing.proof.md`, in the finite foundational sub-step of
`lem-coef-integral-finite-extension.proof.md`, paragraphs 3--4, together with
`lem-coef-finite-dualizing.proof.md`, paragraphs 1--3, and
`lem-coef-finite-free-extension.proof.md`, paragraphs 1 and 3.

The postponed proof has six steps. (1) It forms the ordinary compact-support scalar
comparison from the proper counit mate and open balancing, including composition and
unit normalization. (2) It transposes the scalar-extended ordinary counit, checks the
affine and closed-support charts, and obtains the ordinary dualizing isomorphism and
counit equation. (3) It transports this mate through the exact site comparison, the
canonical tensor comparison δ, and the finite-ring compactification transpose,
obtaining the pro-etale mate, its invertibility, and the mixed scalar square. (4) It
proves scheme naturality and compactification independence by normalized refinement and
tower equations. (5) It proves composition, identity, and commutative-square
compatibility by injectivity of the same exceptional Hom bijection. (6) It applies the
preceding construction to the finite quotient levels `Aₙ = R/tⁿ` and `Bₙ = S/tⁿS`,
using the finite-free integral basis and canonical derived tensor identifications to
obtain the reduction square and its transitivity.

(blueprint: lem-sf-general-field-finite-dualizing-coefficient-change)
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The canonical coefficient map on the etale dualizing complexes.
Source: `lem-coef-finite-dualizing.proof.md`, the ordinary counit mate
(blueprint: lem-sf-general-field-finite-dualizing-coefficient-change). -/
def generalFieldFiniteDualizingMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X S : Scheme.{u}} (a : X ⟶ S) [HasCompactification a] :
    (scalarExtension φ X).obj (dualizingComplex A a) ⟶ dualizingComplex B a :=
  ExceptionalCoefficients.dualizingScalarMap φ a

/-- The counit mate constructed using the supplied compactification's compact-support
functor, scalar comparison, and adjunction. The unique adjunction-compatible right-adjoint
isomorphisms transport its source and target to the canonical dualizing complexes.
Source: the finite dualizing coefficient-change proof, compactification-independence
paragraph (blueprint: lem-sf-general-field-finite-dualizing-coefficient-change). -/
noncomputable def generalFieldFiniteEtaleDualizingMapAt
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X S : Scheme.{u}} (a : X ⟶ S) [HasCompactification a]
    [QuasiCompact a]
    (c : Compactification a) :
    (scalarExtension φ X).obj (dualizingComplex A a) ⟶ dualizingComplex B a :=
  let adjA := rightDerivedUpperShriekOfCompactificationAdjunction A c
  let adjB := rightDerivedUpperShriekOfCompactificationAdjunction B c
  let eA := (rightDerivedUpperShriekAdjunction A a).rightAdjointUniq
    (adjA.ofNatIsoLeft (rightDerivedLowerShriekIso A c))
  let eB := (rightDerivedUpperShriekAdjunction B a).rightAdjointUniq
    (adjB.ofNatIsoLeft (rightDerivedLowerShriekIso B c))
  let ωA := (rightDerivedUpperShriekOfCompactification A c).obj
    (𝟙_ (DerivedCategoryModule A S))
  let uC := adjB.homEquiv _ _
    (ExceptionalCoefficients.comparisonInverse φ c ωA ≫
      (scalarExtension φ S).map (adjA.counit.app (𝟙_ (DerivedCategoryModule A S))))
  (scalarExtension φ X).map (eA.hom.app (𝟙_ (DerivedCategoryModule A S))) ≫
      uC ≫ (rightDerivedUpperShriekOfCompactification B c).map
        (ExceptionalCoefficients.unitIso φ S).hom ≫
      eB.inv.app (𝟙_ (DerivedCategoryModule B S))

/-- The pro-etale map is the mate of the ordinary coefficient map under the
canonical comparison between the two site restrictions.  The comparison is
the adjunction mate of the normalized tensor comparison (whose representative
normalization is `Scheme.proEtaleCanonicalTensorComparison`), so this definition
does not use a witness-specific scalar extension. -/
def generalFieldFiniteProDualizingMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X S : Scheme.{u}} (a : X ⟶ S) [HasCompactification a] :
    (@Sheaf.fixedCoefficientDerivedScalarExtension.{u} X.ProEt inferInstance
      (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X) A B
      inferInstance inferInstance φ).obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
          (dualizingComplex A a)) ⟶
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.obj
        (dualizingComplex B a) := by
  letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let eA := @FiniteCoefficientOrdinary.scalarAdjunction.{u} X.Etale inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) X.smallEtaleTopology A B inferInstance
    inferInstance φ
  let eP := @FiniteCoefficientOrdinary.scalarAdjunction.{u} X.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X) A B inferInstance
    inferInstance φ
  let C_A := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  let C_B := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory
  let h : dualizingComplex A a ⟶
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj
        (dualizingComplex B a) := eA.homEquiv _ _ (generalFieldFiniteDualizingMap φ a)
  exact (eP.homEquiv _ _).symm
    (C_A.map h ≫ (Scheme.comparisonRestrictScalarsIso X A φ).hom.app
      (dualizingComplex B a))

/-- The finite pro-etale transport of the counit mate constructed at the supplied
compactification, using the canonical tensor comparison δ and the exact site comparison.
Source: the finite dualizing coefficient-change proof, compactification-independence
paragraph (blueprint: lem-sf-general-field-finite-dualizing-coefficient-change). -/
noncomputable def generalFieldFiniteProDualizingMapAt
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X S : Scheme.{u}} (a : X ⟶ S) [HasCompactification a]
    [QuasiCompact a]
    (c : Compactification a) :
    (@Sheaf.fixedCoefficientDerivedScalarExtension.{u} X.ProEt inferInstance
      (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X) A B
      inferInstance inferInstance φ).obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
          (dualizingComplex A a)) ⟶
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.obj
        (dualizingComplex B a) := by
  letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  exact (ProEtale.OrdinaryScalarSite.delta φ X).hom.app (dualizingComplex A a) ≫
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.map
      (generalFieldFiniteEtaleDualizingMapAt φ a c)

/-- The scalar/pullback comparison for the fixed derived scalar extension.  It is
the mate of the published pro-etale pullback/restriction square, so its source
and target use `Sheaf.fixedCoefficientDerivedScalarExtension` itself. -/
noncomputable def generalFieldFiniteProScalarPullbackReverse
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    (ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory ⋙
        @Sheaf.fixedCoefficientDerivedScalarExtension.{u} Y.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology Y) A B
          inferInstance inferInstance φ ⟶
      @Sheaf.fixedCoefficientDerivedScalarExtension.{u} Z.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology Z) A B
          inferInstance inferInstance φ ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory := by
  let sY : EssentiallySmall.{u + 1} Y.ProEt :=
    essentiallySmallSelf.{0, u, u + 1} _
  let sZ : EssentiallySmall.{u + 1} Z.ProEt :=
    essentiallySmallSelf.{0, u, u + 1} _
  let eZ := @FiniteCoefficientOrdinary.scalarAdjunction.{u} Z.ProEt inferInstance
    sZ (Scheme.ProEt.topology Z) A B inferInstance inferInstance φ
  let eY := @FiniteCoefficientOrdinary.scalarAdjunction.{u} Y.ProEt inferInstance
    sY (Scheme.ProEt.topology Y) A B inferInstance inferInstance φ
  let h := ((mateEquiv
    eZ eY).symm
    (TwoSquare.mk _ _ _ _
      (ProEtale.leftDerivedUpperStarRestrictScalarsIso φ f).hom)).natTrans
  let iA := ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} A) f
  let iB := ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} B) f
  exact (Functor.isoWhiskerRight iA.symm
      (@Sheaf.fixedCoefficientDerivedScalarExtension.{u} Y.ProEt inferInstance sY
        (Scheme.ProEt.topology Y) A B inferInstance inferInstance φ)).hom ≫
    h ≫
    (Functor.isoWhiskerLeft
      (@Sheaf.fixedCoefficientDerivedScalarExtension.{u} Z.ProEt inferInstance sZ
        (Scheme.ProEt.topology Z) A B inferInstance inferInstance φ) iB).hom

/- The two compact-support arrows used below are the published proper/open mates.
They are named here so every pro-etale clause refers to the intrinsic map, rather
than to a witness-specific extension or an arbitrary isomorphism. -/
/-- The intrinsic ordinary finite-coefficient compact-support comparison c^e: the
proper scalar counit mate followed by proper image of the open scalar balancing,
i.e. `compactScalarMap` of lem-pur-etale-compact-scalar-coherence. Its components are
`ExceptionalCoefficients.compactSupportMap`, whose inverse defines the dualizing map.
Source: Stacks 07A4 (blueprint: lem-pur-etale-compact-scalar-coherence). -/
abbrev generalFieldFiniteEtaleCompactMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :=
  compactScalarMap φ c

/-- The intrinsic pro-etale finite-coefficient compact-support comparison.
Source: Stacks 07A4 (blueprint: lem-pur-finite-ring-compactification-transpose-comparison). -/
abbrev generalFieldFiniteProCompactMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :=
  ProEtale.FiniteCompactCoefficients.b φ c

/-- The site-comparison component used by the finite transpose.
Source: Stacks 07A4 (blueprint: lem-pur-finite-ring-compactification-transpose-comparison). -/
abbrev generalFieldFiniteSiteComparison
    (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  ProEtale.FiniteCompactCoefficients.site R c

/-- The quotient transition map used at the finite DVR levels.
Source: Stacks 09B1 (blueprint: lem-sf-general-field-finite-dualizing-coefficient-change). -/
def generalFieldFiniteQuotientTransition
    {R : Type (u + 1)} [CommRing R] (t : R) {m n : ℕ} (h : n ≤ m) :
    (R ⧸ Ideal.span ({t ^ m} : Set R)) →+*
      (R ⧸ Ideal.span ({t ^ n} : Set R)) := by
  apply Ideal.Quotient.lift (Ideal.span ({t ^ m} : Set R))
    (Ideal.Quotient.mk (Ideal.span ({t ^ n} : Set R)))
  intro x hx
  rw [Ideal.Quotient.eq_zero_iff_mem]
  have hI : Ideal.span ({t ^ m} : Set R) ≤ Ideal.span ({t ^ n} : Set R) := by
    apply Ideal.span_le.2
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    have hp : t ^ m = t ^ n * t ^ (m - n) := by
      rw [← pow_add, Nat.add_sub_of_le h]
    rw [hp]
    exact Ideal.mul_mem_right _ (Ideal.span ({t ^ n} : Set R))
      (Ideal.subset_span (show t ^ n ∈ ({t ^ n} : Set R) from Set.mem_singleton _))
  exact hI hx

/-- The canonical coefficient inclusion at a quotient level.
Source: Stacks 09B1 (blueprint: lem-sf-general-field-finite-dualizing-coefficient-change). -/
def generalFieldFiniteQuotientInclusion
    {R S : Type (u + 1)} [CommRing R] [CommRing S] [Algebra R S]
    (t : R) (n : ℕ) :
    (R ⧸ Ideal.span ({t ^ n} : Set R)) →+*
      (S ⧸ Ideal.span ({(algebraMap R S t) ^ n} : Set S)) := by
  apply Ideal.Quotient.lift (Ideal.span ({t ^ n} : Set R))
    ((Ideal.Quotient.mk (Ideal.span ({(algebraMap R S t) ^ n} : Set S))).comp
      (algebraMap R S))
  intro x hx
  simp only [RingHom.comp_apply]
  rw [Ideal.Quotient.eq_zero_iff_mem]
  have hI : Ideal.map (algebraMap R S) (Ideal.span ({t ^ n} : Set R)) ≤
      Ideal.span ({(algebraMap R S t) ^ n} : Set S) := by
    rw [Ideal.map_span]
    apply Ideal.span_mono
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    rcases hz with rfl
    rw [map_pow]
    exact show (algebraMap R S t) ^ n ∈
      ({(algebraMap R S t) ^ n} : Set S) from Set.mem_singleton _
  exact hI (Ideal.mem_map_of_mem (algebraMap R S) hx)

/-- The bounded-below unit representative used by the finite transpose.
Source: Stacks 06YY (blueprint: lem-pur-finite-ring-compactification-transpose-comparison). -/
noncomputable def generalFieldFiniteEtaleUnitPlus
    (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u}) :
    ProEtale.FiniteCompactificationTranspose.EPlus A Y :=
  ⟨𝟙_ (DerivedCategoryModule A Y), by
    exact ⟨0, inferInstance⟩⟩

/-- The pro-etale counit obtained by the restricted finite transpose at the
dualizing representative.
Source: Stacks 07A4 (blueprint: lem-pur-finite-ring-compactification-transpose-comparison). -/
noncomputable def generalFieldFiniteProEpsilon
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {X S : Scheme.{u}} (a : X ⟶ S) [HasCompactification a] [CompactSpace S] :
    (ProEtale.FiniteCompactCoefficients.pro A
      (HasCompactification.compactification a)).obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
          (dualizingComplex A a)) ⟶
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj
        (𝟙_ (DerivedCategoryModule A S)) := by
  let c := HasCompactification.compactification a
  let G := Etale.rightDerivedUpperShriek A a
  let adj := Etale.rightDerivedUpperShriekAdjunction A a
  let H := generalFieldFiniteEtaleUnitPlus A S
  let hUnit := H.property
  let hG : DerivedCategory.TStructure.t.plus (dualizingComplex A a) := by
    simpa [dualizingComplex] using
      (Etale.plus_rightDerivedUpperShriek_obj (Λ := A) a
        (𝟙_ (DerivedCategoryModule A S)) hUnit)
  exact ProEtale.FiniteCompactificationTranspose.counit A c G adj H hG

/-- The full six-clause statement package for finite coefficient change.
The parameter `l` is the single coefficient prime from the theorem; all composition,
reduction, and quotient-level clauses use this same prime.
Source: the finite dualizing coefficient-change statement in
`lem-coef-finite-dualizing.proof.md` (blueprint:
lem-sf-general-field-finite-dualizing-coefficient-change). -/
structure GeneralFieldFiniteDualizingCoefficientChange
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (l : ℕ) (φ : A →+* B) {X S : Scheme.{u}} (a : X ⟶ S)
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] [HasCompactification a]
    [CompactSpace S] : Prop where
  etale_isIso : IsIso (generalFieldFiniteDualizingMap φ a)
  etale_counit :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) a).map
        (generalFieldFiniteDualizingMap φ a) ≫
      (rightDerivedUpperShriekAdjunction B a).counit.app
        (𝟙_ (DerivedCategoryModule B S)) =
    ExceptionalCoefficients.comparisonInverse φ (HasCompactification.compactification a)
        (dualizingComplex A a) ≫
      (scalarExtension φ S).map
        ((rightDerivedUpperShriekAdjunction A a).counit.app
          (𝟙_ (DerivedCategoryModule A S))) ≫
      (ExceptionalCoefficients.unitIso φ S).hom
  canonical_delta_isIso :
    letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
    IsIso ((ProEtale.OrdinaryScalarSite.delta φ X).hom.app
      (dualizingComplex A a))
  pro_isIso : IsIso (generalFieldFiniteProDualizingMap φ a)
  natural_under_isomorphism :
    ∀ {X' S' : Scheme.{u}} (eX : X ≅ X') (eS : S ≅ S')
      (a' : X' ⟶ S') [IsSeparated a'] [LocallyOfFiniteType a'] [QuasiCompact a']
      [HasCompactification a']
      (sq : IsPullback eX.inv a' a eS.inv),
      eX.hom ≫ a' = a ≫ eS.hom →
      ((scalarExtension φ X').map (dualizingComplexBaseChangeMap A sq) ≫
          generalFieldFiniteDualizingMap φ a' =
        (scalarPullbackIso φ eX.inv).inv.app (dualizingComplex A a) ≫
          (upperStar (ModuleCat.{u + 1} B) eX.inv).leftDerivedFunctor.map
            (generalFieldFiniteDualizingMap φ a) ≫
          dualizingComplexBaseChangeMap B sq) ∧
      (letI : EssentiallySmall.{u + 1} X'.ProEt := essentiallySmallSelf.{0, u, u + 1} _
       let C_A :=
         (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
       let C_A' :=
         (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X').mapDerivedCategory
       let C_B' :=
         (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X').mapDerivedCategory
       let κA := ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso
         (ModuleCat.{u + 1} A) eX.inv
       let κB := ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso
         (ModuleCat.{u + 1} B) eX.inv
       let eA := leftDerivedUpperStarIsoMapDerivedCategory
         (ModuleCat.{u + 1} A) eX.inv
       let eB := leftDerivedUpperStarIsoMapDerivedCategory
         (ModuleCat.{u + 1} B) eX.inv
       let T_X' := @Sheaf.fixedCoefficientDerivedScalarExtension.{u} X'.ProEt
         inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
         (Scheme.ProEt.topology X') A B inferInstance inferInstance φ
       let s := generalFieldFiniteProScalarPullbackReverse φ eX.inv
       T_X'.map (κA.hom.app (dualizingComplex A a)) ≫
           T_X'.map (C_A'.map
             (eA.inv.app (dualizingComplex A a) ≫
               dualizingComplexBaseChangeMap A sq)) ≫
         generalFieldFiniteProDualizingMap φ a' =
       s.app (C_A.obj (dualizingComplex A a)) ≫
           (ProEtale.upperStar (ModuleCat.{u + 1} B) eX.inv).mapDerivedCategory.map
             (generalFieldFiniteProDualizingMap φ a) ≫
         κB.hom.app (dualizingComplex B a) ≫
           C_B'.map
             (eB.inv.app (dualizingComplex B a) ≫
               dualizingComplexBaseChangeMap B sq))
  compactification_independent :
    ∀ (c d : Compactification a),
      generalFieldFiniteEtaleDualizingMapAt φ a c =
          generalFieldFiniteEtaleDualizingMapAt φ a d ∧
        generalFieldFiniteEtaleDualizingMapAt φ a c = generalFieldFiniteDualizingMap φ a
  composition :
    ∀ {C : Type (u + 1)} [CommRing C] [Finite C]
      (_hAell : ∃ n : ℕ, ∀ x : A, (l ^ n : A) * x = 0)
      (_hBell : ∃ n : ℕ, ∀ x : B, (l ^ n : B) * x = 0)
      (_hCell : ∃ n : ℕ, ∀ x : C, (l ^ n : C) * x = 0)
      (ψ : B →+* C),
      (FiniteCoefficientOrdinary.scalarComposition X.smallEtaleTopology φ ψ).hom.app
          (dualizingComplex A a) ≫
        generalFieldFiniteDualizingMap (ψ.comp φ) a =
      (scalarExtension ψ X).map (generalFieldFiniteDualizingMap φ a) ≫
        generalFieldFiniteDualizingMap ψ a
  identity :
    generalFieldFiniteDualizingMap (RingHom.id A) a =
      (ProEtale.normalizedOriginScalarUnit X.smallEtaleTopology
        (RingHom.id A) rfl).hom.app (dualizingComplex A a) ∧
    (letI : EssentiallySmall.{u + 1} X.ProEt :=
        essentiallySmallSelf.{0, u, u + 1} _
     generalFieldFiniteProDualizingMap (RingHom.id A) a =
      (ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology X)
        (RingHom.id A) rfl).hom.app
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
          (dualizingComplex A a)))
  reduction_square :
    ∀ (R S₀ : Type (u + 1)) [CommRing R] [CommRing S₀] [Algebra R S₀]
      [Module.Free R S₀] [Module.Finite R S₀]
      (t : R) (v : S₀) (e m n : ℕ) (hmn : n ≤ m)
      (_hram : Ideal.span ({algebraMap R S₀ t} : Set S₀) =
        Ideal.span ({v ^ e} : Set S₀))
      [Finite (R ⧸ Ideal.span ({t ^ m} : Set R))]
      [Finite (R ⧸ Ideal.span ({t ^ n} : Set R))]
      [Finite (S₀ ⧸ Ideal.span ({(algebraMap R S₀ t) ^ m} : Set S₀))]
      [Finite (S₀ ⧸ Ideal.span ({(algebraMap R S₀ t) ^ n} : Set S₀))]
      (_hRmell : ∃ r : ℕ, ∀ x : R ⧸ Ideal.span ({t ^ m} : Set R),
        (l ^ r : R ⧸ Ideal.span ({t ^ m} : Set R)) * x = 0)
      (_hRnell : ∃ r : ℕ, ∀ x : R ⧸ Ideal.span ({t ^ n} : Set R),
        (l ^ r : R ⧸ Ideal.span ({t ^ n} : Set R)) * x = 0)
      (_hSmell : ∃ r : ℕ, ∀ x : S₀ ⧸ Ideal.span ({(algebraMap R S₀ t) ^ m} : Set S₀),
        (l ^ r : S₀ ⧸ Ideal.span ({(algebraMap R S₀ t) ^ m} : Set S₀)) * x = 0)
      (_hSnell : ∃ r : ℕ, ∀ x : S₀ ⧸ Ideal.span ({(algebraMap R S₀ t) ^ n} : Set S₀),
        (l ^ r : S₀ ⧸ Ideal.span ({(algebraMap R S₀ t) ^ n} : Set S₀)) * x = 0),
      letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
      let Aₘ := R ⧸ Ideal.span ({t ^ m} : Set R)
      let _Aₙ := R ⧸ Ideal.span ({t ^ n} : Set R)
      let _Bₘ := S₀ ⧸ Ideal.span ({(algebraMap R S₀ t) ^ m} : Set S₀)
      let _Bₙ := S₀ ⧸ Ideal.span ({(algebraMap R S₀ t) ^ n} : Set S₀)
      let qA := generalFieldFiniteQuotientTransition t hmn
      let qB := generalFieldFiniteQuotientTransition (algebraMap R S₀ t) hmn
      let iₘ := generalFieldFiniteQuotientInclusion t m
      let iₙ := generalFieldFiniteQuotientInclusion t n
      ∃ hcomp : qB.comp iₘ = iₙ.comp qA,
      Ideal.span ({(algebraMap R S₀ t) ^ m} : Set S₀) =
          Ideal.span ({v ^ (e * m)} : Set S₀) ∧
      Ideal.span ({(algebraMap R S₀ t) ^ n} : Set S₀) =
          Ideal.span ({v ^ (e * n)} : Set S₀) ∧
      (let hcomp := hcomp
       let τe :=
         (FiniteCoefficientOrdinary.scalarComposition X.smallEtaleTopology iₘ qB).hom.app
             (dualizingComplex Aₘ a) ≫
           eqToHom (by rw [hcomp]) ≫
         (FiniteCoefficientOrdinary.scalarComposition X.smallEtaleTopology qA iₙ).inv.app
             (dualizingComplex Aₘ a)
       (scalarExtension qB X).map (generalFieldFiniteDualizingMap iₘ a) ≫
           generalFieldFiniteDualizingMap qB a =
         τe ≫ ((scalarExtension iₙ X).map (generalFieldFiniteDualizingMap qA a) ≫
           generalFieldFiniteDualizingMap iₙ a)) ∧
      (let hcomp := hcomp
       let τp :=
         (FiniteCoefficientOrdinary.scalarComposition (Scheme.ProEt.topology X) iₘ qB).hom.app
             ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Aₘ) X).mapDerivedCategory.obj
               (dualizingComplex Aₘ a)) ≫
           eqToHom (by rw [hcomp]) ≫
         (FiniteCoefficientOrdinary.scalarComposition (Scheme.ProEt.topology X) qA iₙ).inv.app
             ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Aₘ) X).mapDerivedCategory.obj
               (dualizingComplex Aₘ a))
       (@Sheaf.fixedCoefficientDerivedScalarExtension.{u} X.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X) _ _
          inferInstance inferInstance qB).map (generalFieldFiniteProDualizingMap iₘ a) ≫
          generalFieldFiniteProDualizingMap qB a =
         τp ≫
           ((@Sheaf.fixedCoefficientDerivedScalarExtension.{u} X.ProEt inferInstance
             (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X) _ _
             inferInstance inferInstance iₙ).map (generalFieldFiniteProDualizingMap qA a) ≫
             generalFieldFiniteProDualizingMap iₙ a)) ∧
      ((FiniteCoefficientOrdinary.scalarComposition X.smallEtaleTopology iₘ qB).hom.app
          (dualizingComplex Aₘ a) ≫
        generalFieldFiniteDualizingMap (qB.comp iₘ) a =
        (scalarExtension qB X).map (generalFieldFiniteDualizingMap iₘ a) ≫
          generalFieldFiniteDualizingMap qB a) ∧
      ((FiniteCoefficientOrdinary.scalarComposition X.smallEtaleTopology qA iₙ).hom.app
          (dualizingComplex Aₘ a) ≫
        generalFieldFiniteDualizingMap (iₙ.comp qA) a =
        (scalarExtension iₙ X).map (generalFieldFiniteDualizingMap qA a) ≫
          generalFieldFiniteDualizingMap iₙ a) ∧
      ((FiniteCoefficientOrdinary.scalarComposition (Scheme.ProEt.topology X) iₘ qB).hom.app
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Aₘ) X).mapDerivedCategory.obj
            (dualizingComplex Aₘ a)) ≫
        generalFieldFiniteProDualizingMap (qB.comp iₘ) a =
        (@Sheaf.fixedCoefficientDerivedScalarExtension.{u} X.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X) _ _
          inferInstance inferInstance qB).map
            (generalFieldFiniteProDualizingMap iₘ a) ≫
          generalFieldFiniteProDualizingMap qB a)
      ∧
      ((FiniteCoefficientOrdinary.scalarComposition (Scheme.ProEt.topology X) qA iₙ).hom.app
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Aₘ) X).mapDerivedCategory.obj
            (dualizingComplex Aₘ a)) ≫
        generalFieldFiniteProDualizingMap (iₙ.comp qA) a =
        (@Sheaf.fixedCoefficientDerivedScalarExtension.{u} X.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X) _ _
          inferInstance inferInstance iₙ).map
            (generalFieldFiniteProDualizingMap qA a) ≫
          generalFieldFiniteProDualizingMap iₙ a)
  pro_b_Q_and_epsilon :
    let c := HasCompactification.compactification a
    let adj := Etale.rightDerivedUpperShriekAdjunction A a
    let H := generalFieldFiniteEtaleUnitPlus A S
    let hUnit := H.property
    let hG : DerivedCategory.TStructure.t.plus (dualizingComplex A a) := by
      simpa [dualizingComplex] using
        (Etale.plus_rightDerivedUpperShriek_obj (Λ := A) a
          (𝟙_ (DerivedCategoryModule A S)) hUnit)
    let J : ProEtale.FiniteCompactificationTranspose.EPlus A X :=
      ⟨dualizingComplex A a, hG⟩
    let bQ := ProEtale.FiniteCompactificationTranspose.B A c J
    let εQ := generalFieldFiniteProEpsilon a
    bQ.hom = (generalFieldFiniteSiteComparison A c).app (dualizingComplex A a) ∧
      bQ.hom ≫ εQ =
        (ProEtale.FiniteCompactificationTranspose.C A S).map (adj.counit.app H.obj)
  pro_b_Q_isIso :
    ∀ (J : ProEtale.FiniteCompactificationTranspose.EPlus A X),
      (ProEtale.FiniteCompactificationTranspose.B A
        (HasCompactification.compactification a) J).hom =
      (generalFieldFiniteSiteComparison A
        (HasCompactification.compactification a)).app J.obj ∧
      IsIso ((generalFieldFiniteSiteComparison A
        (HasCompactification.compactification a)).app J.obj)
  pro_epsilon_p :
    let c := HasCompactification.compactification a
    let adj := Etale.rightDerivedUpperShriekAdjunction A a
    let H := generalFieldFiniteEtaleUnitPlus A S
    let hUnit := H.property
    let hG : DerivedCategory.TStructure.t.plus (dualizingComplex A a) := by
      simpa [dualizingComplex] using
        (Etale.plus_rightDerivedUpperShriek_obj (Λ := A) a
          (𝟙_ (DerivedCategoryModule A S)) hUnit)
    let J : ProEtale.FiniteCompactificationTranspose.EPlus A X :=
      ⟨dualizingComplex A a, hG⟩
    let bQ := ProEtale.FiniteCompactificationTranspose.B A c J
    let εQ := generalFieldFiniteProEpsilon a
    εQ = bQ.inv ≫
      (ProEtale.FiniteCompactificationTranspose.C A S).map (adj.counit.app H.obj)
  pro_c_p_isIso :
    ∀ (c : Compactification a) (K : DerivedCategoryModule A X),
      ProEtale.FiniteCompactCoefficients.Input A X K →
      IsIso ((generalFieldFiniteProCompactMap φ c).app
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K))
  pro_mixed_square :
    letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
    letI : EssentiallySmall.{u + 1} S.ProEt := essentiallySmallSelf.{0, u, u + 1} _
    ∀ (c : Compactification a) (K : DerivedCategoryModule A X)
      (_hK : ProEtale.FiniteCompactCoefficients.Input A X K),
      let cP := (generalFieldFiniteProCompactMap φ c).app
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K)
      IsIso cP ∧
      (Sheaf.fixedCoefficientDerivedScalarExtension (Scheme.ProEt.topology S) φ).map
          ((generalFieldFiniteSiteComparison A c).app K) ≫
        cP ≫
        (ProEtale.FiniteCompactCoefficients.pro B
          c).map
          ((ProEtale.OrdinaryScalarSite.delta φ X).hom.app K) =
      (ProEtale.OrdinaryScalarSite.delta φ S).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) c).obj K) ≫
        (ProEtale.FiniteCompactCoefficients.nu B S).map
          ((generalFieldFiniteEtaleCompactMap φ c).app K) ≫
        (generalFieldFiniteSiteComparison B c).app
          ((scalarExtension φ X).obj K)
  pro_mate_characterization :
    letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
    generalFieldFiniteProDualizingMap φ a =
      (ProEtale.OrdinaryScalarSite.delta φ X).hom.app (dualizingComplex A a) ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.map
          (generalFieldFiniteDualizingMap φ a)
  pro_counit_equation :
    letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
    letI : EssentiallySmall.{u + 1} S.ProEt := essentiallySmallSelf.{0, u, u + 1} _
    let c := HasCompactification.compactification a
    let cP := (generalFieldFiniteProCompactMap φ c).app
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
        (dualizingComplex A a))
    let F_B := ProEtale.FiniteCompactCoefficients.pro B c
    cP ≫ F_B.map ((ProEtale.OrdinaryScalarSite.delta φ X).hom.app
      (dualizingComplex A a)) ≫
      F_B.map
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.map
          (generalFieldFiniteDualizingMap φ a)) ≫
      generalFieldFiniteProEpsilon (A := B) a =
    (ProEtale.OrdinaryScalarSite.scalar (Scheme.ProEt.topology S) φ).map
      (generalFieldFiniteProEpsilon a) ≫
      (ProEtale.OrdinaryScalarSite.delta φ S).hom.app
        (𝟙_ (DerivedCategoryModule A S)) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) S).mapDerivedCategory.map
        (ExceptionalCoefficients.unitIso φ S).hom
  transitivity :
    ∀ {C D : Type (u + 1)} [CommRing C] [CommRing D] [Finite C] [Finite D]
      (_hAell : ∃ n : ℕ, ∀ x : A, (l ^ n : A) * x = 0)
      (_hBell : ∃ n : ℕ, ∀ x : B, (l ^ n : B) * x = 0)
      (_hCell : ∃ n : ℕ, ∀ x : C, (l ^ n : C) * x = 0)
      (_hDell : ∃ n : ℕ, ∀ x : D, (l ^ n : D) * x = 0)
      (ψ : B →+* C) (χ : C →+* D),
      ((scalarExtension χ X).map
          ((FiniteCoefficientOrdinary.scalarComposition X.smallEtaleTopology φ ψ).hom.app
            (dualizingComplex A a)) ≫
        (FiniteCoefficientOrdinary.scalarComposition X.smallEtaleTopology (ψ.comp φ) χ).hom.app
          (dualizingComplex A a) ≫
        generalFieldFiniteDualizingMap (χ.comp (ψ.comp φ)) a =
      (scalarExtension χ X).map
          ((FiniteCoefficientOrdinary.scalarComposition X.smallEtaleTopology φ ψ).hom.app
            (dualizingComplex A a) ≫
            generalFieldFiniteDualizingMap (ψ.comp φ) a) ≫
        generalFieldFiniteDualizingMap χ a) ∧
      (letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
       (FiniteCoefficientOrdinary.scalarComposition (Scheme.ProEt.topology X)
          (ψ.comp φ) χ).hom.app
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
            (dualizingComplex A a)) ≫
        generalFieldFiniteProDualizingMap (χ.comp (ψ.comp φ)) a =
        (@Sheaf.fixedCoefficientDerivedScalarExtension.{u} X.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X) C D
          inferInstance inferInstance χ).map
          (generalFieldFiniteProDualizingMap (ψ.comp φ) a) ≫
        generalFieldFiniteProDualizingMap χ a)
  pro_site_composition :
    letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
    ∀ {C : Type (u + 1)} [CommRing C] [Finite C]
      (_hAell : ∃ n : ℕ, ∀ x : A, (l ^ n : A) * x = 0)
      (_hBell : ∃ n : ℕ, ∀ x : B, (l ^ n : B) * x = 0)
      (_hCell : ∃ n : ℕ, ∀ x : C, (l ^ n : C) * x = 0)
      (ψ : B →+* C),
      (FiniteCoefficientOrdinary.scalarComposition (Scheme.ProEt.topology X) φ ψ).hom.app
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
            (dualizingComplex A a)) ≫
        generalFieldFiniteProDualizingMap (ψ.comp φ) a =
      (@Sheaf.fixedCoefficientDerivedScalarExtension.{u} X.ProEt inferInstance
        (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X) B C
        inferInstance inferInstance ψ).map
          (generalFieldFiniteProDualizingMap φ a) ≫
        generalFieldFiniteProDualizingMap ψ a
  commutative_square :
    ∀ {C D : Type (u + 1)} [CommRing C] [CommRing D]
      [Finite C] [Finite D] (ψ : B →+* C) (χ : B →+* D)
      (_hBell : ∃ n : ℕ, ∀ x : B, (l ^ n : B) * x = 0)
      (_hCell : ∃ n : ℕ, ∀ x : C, (l ^ n : C) * x = 0)
      (_hDell : ∃ n : ℕ, ∀ x : D, (l ^ n : D) * x = 0)
      (r : C →+* D) (h : r.comp ψ = χ),
      (FiniteCoefficientOrdinary.scalarComposition X.smallEtaleTopology ψ r).hom.app
          (dualizingComplex B a) ≫ (h ▸ generalFieldFiniteDualizingMap χ a) =
        (scalarExtension r X).map (generalFieldFiniteDualizingMap ψ a) ≫
          generalFieldFiniteDualizingMap r a
  compactification_independent_pro :
    letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
    letI : EssentiallySmall.{u + 1} S.ProEt := essentiallySmallSelf.{0, u, u + 1} _
    ∀ (c d : Compactification a)
      , let u_c := generalFieldFiniteProDualizingMapAt φ a c
        let u_d := generalFieldFiniteProDualizingMapAt φ a d
        u_c = u_d ∧ u_c = generalFieldFiniteProDualizingMap φ a
  quotient_level_transitivity :
    ∀ {R S₀ U : Type (u + 1)} [CommRing R] [CommRing S₀] [CommRing U]
      [Algebra R S₀] [Algebra S₀ U] [Algebra R U]
      (t : R) (n : ℕ)
      [Finite (R ⧸ Ideal.span ({t ^ n} : Set R))]
      [Finite (S₀ ⧸ Ideal.span ({(algebraMap R S₀ t) ^ n} : Set S₀))]
      [Finite (U ⧸ Ideal.span ({(algebraMap R U t) ^ n} : Set U))]
      [Finite (U ⧸ Ideal.span
        ({(algebraMap S₀ U (algebraMap R S₀ t)) ^ n} : Set U))]
      (_hRell : ∃ r : ℕ, ∀ x : R ⧸ Ideal.span ({t ^ n} : Set R),
        (l ^ r : R ⧸ Ideal.span ({t ^ n} : Set R)) * x = 0)
      (_hSell : ∃ r : ℕ, ∀ x : S₀ ⧸ Ideal.span ({(algebraMap R S₀ t) ^ n} : Set S₀),
        (l ^ r : S₀ ⧸ Ideal.span ({(algebraMap R S₀ t) ^ n} : Set S₀)) * x = 0)
      (_hUell : ∃ r : ℕ, ∀ x : U ⧸ Ideal.span ({(algebraMap R U t) ^ n} : Set U),
        (l ^ r : U ⧸ Ideal.span ({(algebraMap R U t) ^ n} : Set U)) * x = 0)
      (_hUell' : ∃ r : ℕ, ∀ x : U ⧸ Ideal.span
        ({(algebraMap S₀ U (algebraMap R S₀ t)) ^ n} : Set U),
        (l ^ r : U ⧸ Ideal.span
          ({(algebraMap S₀ U (algebraMap R S₀ t)) ^ n} : Set U)) * x = 0)
      (hRU : algebraMap R U = (algebraMap S₀ U).comp (algebraMap R S₀)),
      let iRS := generalFieldFiniteQuotientInclusion t n
      let iSU := generalFieldFiniteQuotientInclusion (algebraMap R S₀ t) n
      iSU.comp iRS = hRU ▸ generalFieldFiniteQuotientInclusion t n ∧
      (let u_iRU := generalFieldFiniteDualizingMap (iSU.comp iRS) a
       (FiniteCoefficientOrdinary.scalarComposition X.smallEtaleTopology iRS iSU).hom.app
            (dualizingComplex (R ⧸ Ideal.span ({t ^ n} : Set R)) a) ≫
        u_iRU =
        (scalarExtension iSU X).map (generalFieldFiniteDualizingMap iRS a) ≫
          generalFieldFiniteDualizingMap iSU a) ∧
      (letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
       (FiniteCoefficientOrdinary.scalarComposition (Scheme.ProEt.topology X) iRS iSU).hom.app
            ((ProEtale.comparisonUpperStar
              (ModuleCat.{u + 1} (R ⧸ Ideal.span ({t ^ n} : Set R))) X).mapDerivedCategory.obj
              (dualizingComplex (R ⧸ Ideal.span ({t ^ n} : Set R)) a)) ≫
        generalFieldFiniteProDualizingMap (iSU.comp iRS) a =
        (@Sheaf.fixedCoefficientDerivedScalarExtension.{u} X.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X) _ _
          inferInstance inferInstance iSU).map
            (generalFieldFiniteProDualizingMap iRS a) ≫
          generalFieldFiniteProDualizingMap iSU a)

/-- Finite dualizing coefficient change over a finite or algebraically closed field,
with normalized ordinary and pro-etale counit mates, coherence, composition, identity,
and the finite-level reduction square.

The proof follows six steps: (1) form the ordinary compact-support scalar mate and
its cocycle; (2) transpose the ordinary counit and prove the etale dualizing
isomorphism; (3) transport the mate through the site comparison, canonical tensor
comparison, and finite compactification transpose; (4) prove scheme-isomorphism
naturality and compactification independence; (5) prove composition, the tensor-unit
identity, and commutative-square compatibility; (6) apply the construction to the
quotient levels `Aₙ = R/tⁿ` and `Bₙ = S/tⁿS`, including their reduction square and
transitivity.

Source: `lem-coef-finite-dualizing.proof.md` (blueprint:
lem-sf-general-field-finite-dualizing-coefficient-change). -/
theorem generalFieldFiniteDualizingCoefficientChange
    (k : Type u) [Field k] (p l : ℕ) (_hp : p.Prime) (_hlp : ringChar k = p)
    (_hk : Finite k ∨ IsAlgClosed k) (_hl : l.Prime) (_hlp' : l ≠ p)
    {X : Scheme.{u}} {a : X ⟶ Spec (CommRingCat.of k)}
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] [HasCompactification a]
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (l ^ n : A) * x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (l ^ n : B) * x = 0)
    (φ : A →+* B) :
    GeneralFieldFiniteDualizingCoefficientChange l φ a := by
  sorry

end AlgebraicGeometry.Etale
