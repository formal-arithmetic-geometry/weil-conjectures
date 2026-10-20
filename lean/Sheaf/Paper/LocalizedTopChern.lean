/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import Sheaf.Paper.SupportedCohomologyHom
public import Sheaf.Paper.SupportedCup
public import Sheaf.Paper.SupportedCupFunctoriality
public import Sheaf.Paper.PurityRegularSection
public import Sheaf.Paper.PurityChernClasses
public import Sheaf.Paper.PurityDivisorClass
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Sheaf.AlgebraicGeometry.CompleteFlagBundle
import Sheaf.Paper.FlagPullbackInjective
import Sheaf.Paper.PurityFrameIndependence
import Sheaf.Paper.RelativeSupportBottomDescent
import Sheaf.AlgebraicGeometry.SupportedBottomGluing
import Sheaf.Paper.ChernFlagFormula
import Mathlib.RingTheory.KrullDimension.Regular
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Localized top Chern classes of regular sections

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
thm-pur-localized-top-chern, properties (L1)--(L4)
(blueprint: thm-pur-localized-top-chern).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u c d v v₂ w w₂
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The degree reindexing in the canonical tensor-shift comparison.
Source: blueprint localized-top-Chern, Tate degrees (blueprint: thm-pur-localized-top-chern).
Proof: expand the successor cast and distribute multiplication by two. -/
theorem localizedChernDegree_succ (r : ℕ) :
    2 * (r : ℤ) + 2 = 2 * ((r + 1 : ℕ) : ℤ) := by
  omega

/-- Assemble the ordered tensor-shift comparison in an abstract abelian category.
Keeping the category abstract prevents repeated normalization of the concrete
sheaf tensor and localization instances in the kernel.
Source: blueprint localized-top-Chern (L4), tensor and shift comparisons
(blueprint: thm-pur-localized-top-chern). -/
def localizedChernTensorPowerMap {C : Type c} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] [HasColimitsOfSize.{0, 0} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [MonoidalCategory (DerivedCategory C)] [(DerivedCategory.Q (C := C)).LaxMonoidal]
    [∀ K : DerivedCategory C, ((curriedTensor (DerivedCategory C)).obj K).CommShift ℤ]
    [∀ K : DerivedCategory C, ((curriedTensor (DerivedCategory C)).flip.obj K).CommShift ℤ]
    (L : ℤ → C) (B : ℕ → DerivedCategory C)
    (z : B 0 ⟶ (DerivedCategory.singleFunctor C 0).obj (L 0))
    (step : ∀ r : ℕ, B (r + 1) ⟶
      B r ⊗ ((DerivedCategory.singleFunctor C 0).obj (L 1))⟦(2 : ℤ)⟧)
    (mul : ∀ r : ℕ, L r ⊗ L 1 ⟶ L ((r + 1 : ℕ) : ℤ)) :
    (r : ℕ) → B r ⟶ ((DerivedCategory.singleFunctor C 0).obj (L r))⟦2 * (r : ℤ)⟧
  | 0 => z ≫ (shiftFunctorZero _ ℤ).inv.app _
  | r + 1 =>
      step r ≫
      (localizedChernTensorPowerMap L B z step mul r ▷
        ((DerivedCategory.singleFunctor C 0).obj (L 1))⟦(2 : ℤ)⟧) ≫
      (ProEtale.cupTensorShiftIso
        ((DerivedCategory.singleFunctor C 0).obj (L r))
        ((DerivedCategory.singleFunctor C 0).obj (L 1)) (2 * (r : ℤ)) 2).hom ≫
      (ProEtale.cupSingleTensorMap (L r) (L 1) ≫
        (DerivedCategory.singleFunctor C 0).map (mul r))⟦2 * (r : ℤ) + 2⟧' ≫
      eqToHom (congrArg (fun n : ℤ ↦
        ((DerivedCategory.singleFunctor C 0).obj (L ((r + 1 : ℕ) : ℤ)))⟦n⟧)
        (localizedChernDegree_succ r))

/-- Characterize the ordered comparison using the actual zero, successor and
multiplication maps, allowing only transport between equal Hom presentations.
The heterogeneous equations fix all three inputs and the resulting comparison.
Source: blueprint localized-top-Chern, the canonical tensor comparison in (L4)
(blueprint: thm-pur-localized-top-chern). -/
def localizedChernTensorPowerCharacterization
    {C : Type c} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] [HasColimitsOfSize.{0, 0} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [MonoidalCategory (DerivedCategory C)] [(DerivedCategory.Q (C := C)).LaxMonoidal]
    [∀ K : DerivedCategory C, ((curriedTensor (DerivedCategory C)).obj K).CommShift ℤ]
    [∀ K : DerivedCategory C, ((curriedTensor (DerivedCategory C)).flip.obj K).CommShift ℤ]
    {L₀ : Type c} (line : L₀) {B₀ : Type (max c v)} (powers : B₀)
    {Z : Type w} (zeroMap : Z) {S : Type w} (stepMap : S)
    {M : Type v} (productMap : M) {H : Type w} (γ : H) (r : ℕ) : Prop :=
  ∃ (L : ℤ → C) (B : ℕ → DerivedCategory C)
    (z : B 0 ⟶ (DerivedCategory.singleFunctor C 0).obj (L 0))
    (step : ∀ j : ℕ, B (j + 1) ⟶
      B j ⊗ ((DerivedCategory.singleFunctor C 0).obj (L 1))⟦(2 : ℤ)⟧)
    (mul : ∀ j : ℕ, L j ⊗ L 1 ⟶ L ((j + 1 : ℕ) : ℤ)),
    HEq L line ∧ HEq B powers ∧ HEq z zeroMap ∧ HEq step stepMap ∧
      HEq mul productMap ∧ HEq γ (localizedChernTensorPowerMap L B z step mul r)

/-- The published ordered-power successor is the same tensor object as that used
by the abstract assembler. Naming this equality avoids repeatedly normalizing the
concrete monoidal dictionary in data definitions.
Source: blueprint localized-top-Chern (L4), ordered positive Tate powers
(blueprint: thm-pur-localized-top-chern).
Proof: unfold affineLinearBaseCoefficient at the successor, then derivedTensorRight
and derivedTensor. Both sides are the curried tensor of the preceding power and
ordinaryFiniteLine[2]. The signed Tate sheaf at 1 is finiteEtaleTateLine. -/
theorem localizedChernTwistSucc_eq (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) (T : Scheme.{u}) (r : ℕ) :
    Etale.affineLinearBaseCoefficient A m hA T (r + 1) =
      Etale.affineLinearBaseCoefficient A m hA T r ⊗
        ((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateSheaf A m T hA 1))⟦(2 : ℤ)⟧ := by
  sorry

/-- The degree-zero comparison in the ordered Tate presentation.
Source: blueprint localized-top-Chern (L4) (blueprint: thm-pur-localized-top-chern). -/
def localizedChernTwistZero (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) (T : Scheme.{u}) :
    Etale.affineLinearBaseCoefficient A m hA T 0 ⟶
      (DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateSheaf A m T hA 0) :=
  𝟙 _

/-- The canonical successor comparison, as transport through the named equality.
Source: blueprint localized-top-Chern (L4) (blueprint: thm-pur-localized-top-chern). -/
def localizedChernTwistStep (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) (T : Scheme.{u}) (r : ℕ) :
    Etale.affineLinearBaseCoefficient A m hA T (r + 1) ⟶
      Etale.affineLinearBaseCoefficient A m hA T r ⊗
        ((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateSheaf A m T hA 1))⟦(2 : ℤ)⟧ :=
  eqToHom (localizedChernTwistSucc_eq A m hA T r)

/-- The existing normalized product with its integer index reexpressed as a successor.
Source: blueprint localized-top-Chern (L4) (blueprint: thm-pur-localized-top-chern). -/
def localizedChernTwistProduct (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (m : Γ(T, ⊤))) (r : ℕ) :
    Scheme.finiteEtaleTateSheaf A m T hA r ⊗ Scheme.finiteEtaleTateSheaf A m T hA 1 ⟶
      Scheme.finiteEtaleTateSheaf A m T hA (r + 1 : ℕ) :=
  (functorialCupTwistProductGeneral A m hm hA T hT r 1).hom ≫
    eqToHom (congrArg (Scheme.finiteEtaleTateSheaf A m T hA)
      (Int.natCast_succ r).symm)

/-- Canonical comparison from ordered shifted root powers to the single signed
Tate sheaf shifted by twice its weight. The abstract assembler uses the actual
localization tensor map, right-shift-first comparison, and normalized product.
Source: blueprint localized-top-Chern (L4) and coefficient-twist conventions
(blueprint: thm-pur-localized-top-chern). -/
def localizedChernTwistMapEtaleRawCharacterization (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (m : Γ(T, ⊤))) (r : ℕ)
    (γ : Etale.affineLinearBaseCoefficient A m hA T r ⟶
      ((DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateSheaf A m T hA r))⟦2 * (r : ℤ)⟧) : Prop :=
  localizedChernTensorPowerCharacterization
    (C := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (Scheme.finiteEtaleTateSheaf A m T hA)
    (Etale.affineLinearBaseCoefficient A m hA T)
    (localizedChernTwistZero A m hA T) (localizedChernTwistStep A m hA T)
    (localizedChernTwistProduct A m hm hA T hT) γ r

/-- The explicit canonical map has exactly one realization in these coordinates.
Source: blueprint localized-top-Chern (L4) (blueprint: thm-pur-localized-top-chern).
Proof: unfold the named characterization. The two Hom types agree by unfolding
singleFunctor and the existing Tate/constant definitions. Transport the displayed
map through that equality; heterogeneous equality gives uniqueness. -/
theorem localizedChernTwistMapEtaleRaw_realization (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (m : Γ(T, ⊤))) (r : ℕ) :
    ∃! γ : Etale.affineLinearBaseCoefficient A m hA T r ⟶
      ((DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateSheaf A m T hA r))⟦2 * (r : ℤ)⟧,
      localizedChernTwistMapEtaleRawCharacterization A m hm hA T hT r γ := by
  sorry

/-- The uniquely specified explicit comparison in the published coordinates.
Source: blueprint localized-top-Chern (L4) (blueprint: thm-pur-localized-top-chern). -/
def localizedChernTwistMapEtaleRaw (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (m : Γ(T, ⊤))) (r : ℕ) :
    Etale.affineLinearBaseCoefficient A m hA T r ⟶
      ((DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateSheaf A m T hA r))⟦2 * (r : ℤ)⟧ :=
  (localizedChernTwistMapEtaleRaw_realization A m hm hA T hT r).choose

/-- The same canonical tensor-shift comparison at the chapter's fixed coefficients.
Source: blueprint localized-top-Chern (L4) (blueprint: thm-pur-localized-top-chern). -/
def localizedChernTwistMapEtale (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (a : T ⟶ Spec (.of P.field.k)) (r : ℕ) : P.diagonalTwistEtale T r ⟶
      ((P.functorialCupSingle false T).obj (P.functorialCupTwist false T r))⟦2 * (r : ℤ)⟧ :=
  localizedChernTwistMapEtaleRaw P.Coefficient P.diagonalExponent
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos P.level)
    P.diagonalExponent_annihilates T (P.diagonalExponent_isUnit a) r

/-- Transport a class through an exact functor and a specified target comparison,
using only its canonical single-object and shift isomorphisms.
Source: blueprint localized-top-Chern (L4), etale-to-pro-etale comparison
(blueprint: thm-pur-localized-top-chern). -/
def localizedChernClassTransport {C : Type c} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] {D : Type d} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{w₂} D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (U L : C) (K : DerivedCategory C) (n : ℤ)
    (α : F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor C 0).obj U) ⟶
      F.mapDerivedCategory.obj K)
    (τ : K ⟶ ((DerivedCategory.singleFunctor C 0).obj L)⟦n⟧) :
    (DerivedCategory.singleFunctor D 0).obj (F.obj U) ⟶
      ((DerivedCategory.singleFunctor D 0).obj (F.obj L))⟦n⟧ :=
  (F.mapDerivedCategorySingleFunctor 0).inv.app U ≫ α ≫
    F.mapDerivedCategory.map τ ≫
    (F.mapDerivedCategory.commShiftIso n).hom.app
      ((DerivedCategory.singleFunctor C 0).obj L) ≫
    ((F.mapDerivedCategorySingleFunctor 0).hom.app L)⟦n⟧'

/-- The ordinary Chern class in the identical supported-cup target coordinates.
The source single-comparison and target shift-comparison are the canonical exact
comparison inverse image, not a chosen cohomology equivalence.
Source: blueprint localized-top-Chern (L4) (blueprint: thm-pur-localized-top-chern). -/
def localizedChernOrdinaryCharacterization (P : PurityFiniteSetting.{u}) {T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) [IsSeparated a] [LocallyOfFiniteType a]
    [QuasiCompact a] (F : T.Modules) (r : ℕ) [F.IsFiniteLocallyFreeOfRank r]
    (γ : P.FunctorialCupOrdinaryH true T (2 * (r : ℤ)) r) : Prop :=
  @HEq _ γ _ (localizedChernClassTransport (P.functorialCupComparisonFunctor T)
    (P.constantEtale T) (P.functorialCupTwist false T r) (P.diagonalTwistEtale T r)
    (2 * (r : ℤ)) (P.ordinaryFiniteChernClass a F r r)
    (P.localizedChernTwistMapEtale T a r))

/-- The explicit canonical map has exactly one realization in these coordinates.
Source: blueprint localized-top-Chern (L4) (blueprint: thm-pur-localized-top-chern).
Proof: unfold the named characterization. The two Hom types agree by unfolding
singleFunctor and the existing Tate/constant definitions. Transport the displayed
map through that equality; heterogeneous equality gives uniqueness. -/
theorem localizedChernOrdinary_realization (P : PurityFiniteSetting.{u}) {T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) [IsSeparated a] [LocallyOfFiniteType a]
    [QuasiCompact a] (F : T.Modules) (r : ℕ) [F.IsFiniteLocallyFreeOfRank r] :
    ∃! γ : P.FunctorialCupOrdinaryH true T (2 * (r : ℤ)) r,
      localizedChernOrdinaryCharacterization P a F r γ := by
  sorry

/-- The uniquely specified explicit comparison in the published coordinates.
Source: blueprint localized-top-Chern (L4) (blueprint: thm-pur-localized-top-chern). -/
def localizedChernOrdinary (P : PurityFiniteSetting.{u}) {T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) [IsSeparated a] [LocallyOfFiniteType a]
    [QuasiCompact a] (F : T.Modules) (r : ℕ) [F.IsFiniteLocallyFreeOfRank r] :
    P.FunctorialCupOrdinaryH true T (2 * (r : ℤ)) r :=
  (localizedChernOrdinary_realization P a F r).choose

/-- A family of supported morphisms for the regular sections in the statement.
Source: blueprint localized-top-Chern, displayed arrow
(blueprint: thm-pur-localized-top-chern). -/
abbrev LocalizedTopChernClasses (P : PurityFiniteSetting.{u}) :=
  ∀ {T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k)) [IsSeparated a]
    [LocallyOfFiniteType a] [QuasiCompact a] (F : T.Modules) (r : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] (s : F.sections),
    IsRegularSection P T a F r s →
      P.FunctorialCupH true (regularSectionZeroProjection P T a F r s) (2 * (r : ℤ)) r

/-- The zero scheme is closed, and forgetting support gives the existing ordinary
top Chern class. Source: blueprint (L4) (blueprint: thm-pur-localized-top-chern). -/
def LocalizedTopChernForgetSupport (P : PurityFiniteSetting.{u})
    (c : P.LocalizedTopChernClasses) : Prop :=
  ∀ {T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k)) [IsSeparated a]
    [LocallyOfFiniteType a] [QuasiCompact a] (F : T.Modules) (r : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] (s : F.sections) (hs : IsRegularSection P T a F r s),
  ∃ hc : IsClosedImmersion (regularSectionZeroProjection P T a F r s),
    @functorialCupForget P true _ _ (regularSectionZeroProjection P T a F r s)
      hc (2 * (r : ℤ)) r (c a F r s hs) = P.localizedChernOrdinary a F r

/-- In rank one the class is the normalized relative-torsor Cartier class of s.
Source: blueprint (L1) (blueprint: thm-pur-localized-top-chern). -/
def LocalizedTopChernLine (P : PurityFiniteSetting.{u})
    (c : P.LocalizedTopChernClasses) : Prop :=
  ∀ {T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k)) [IsSeparated a]
    [LocallyOfFiniteType a] [QuasiCompact a] (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank 1] (s : F.sections) (hs : IsRegularSection P T a F 1 s),
  ∃ (hc : IsClosedImmersion (regularSectionZeroProjection P T a F 1 s))
    (hI : (regularSectionZeroProjection P T a F 1 s).ker.IsInvertible)
    (D : P.DivisorEtaleClasses T),
    P.DivisorEtaleNormalized T a D ∧
      c a F 1 s hs = @divisorProEtale P _ _
        (regularSectionZeroProjection P T a F 1 s) hc
        (@DivisorEtaleClasses.homClassOf P T D _
          (regularSectionZeroProjection P T a F 1 s) hc hI)

/-- Arbitrary base change when the pulled-back section remains regular. The
canonical Cartesian square is a conclusion, not an additional assumption.
Source: blueprint (L2) (blueprint: thm-pur-localized-top-chern). -/
def LocalizedTopChernBaseChange (P : PurityFiniteSetting.{u})
    (c : P.LocalizedTopChernClasses) : Prop :=
  ∀ {T T' : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k)) [IsSeparated a]
    [LocallyOfFiniteType a] [QuasiCompact a] (g : T' ⟶ T)
    [IsSeparated (g ≫ a)] [LocallyOfFiniteType (g ≫ a)] [QuasiCompact (g ≫ a)]
    (F : T.Modules) (r : ℕ) [F.IsFiniteLocallyFreeOfRank r]
    (s : F.sections) (hs : IsRegularSection P T a F r s)
    (F' : T'.Modules) [F'.IsFiniteLocallyFreeOfRank r]
    (e : (Scheme.Modules.tensorPullback g).obj F ≅ F') (s' : F'.sections)
    (_he : ∀ U : T.Opens,
      e.hom.val.app (op (g ⁻¹ᵁ U))
          (Scheme.Modules.tensorPullbackSection g F U (s.val (op U))) =
        s'.val (op (g ⁻¹ᵁ U)))
    (hs' : IsRegularSection P T' (g ≫ a) F' r s'),
  ∃ (hc : IsClosedImmersion (regularSectionZeroProjection P T a F r s))
    (hc' : IsClosedImmersion (regularSectionZeroProjection P T' (g ≫ a) F' r s'))
    (gZ : regularSectionZeroScheme P T' (g ≫ a) F' r s' ⟶
      regularSectionZeroScheme P T a F r s)
    (sq : ChosenCartesianSquare gZ (regularSectionZeroProjection P T' (g ≫ a) F' r s')
      (regularSectionZeroProjection P T a F r s) g),
    @functorialCupPullback P true _ _ _ _
      (regularSectionZeroProjection P T a F r s)
      (regularSectionZeroProjection P T' (g ≫ a) F' r s') hc hc' g gZ sq a
      (2 * (r : ℤ)) r (c a F r s hs) = c (g ≫ a) F' r s' hs'

/-- The internal cup product on the scheme-theoretic intersection, identified
with the zero scheme of the actual direct sum section. Source: blueprint (L3)
(blueprint: thm-pur-localized-top-chern). -/
def LocalizedTopChernDirectSum (P : PurityFiniteSetting.{u})
    (c : P.LocalizedTopChernClasses) : Prop :=
  ∀ {T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k)) [IsSeparated a]
    [LocallyOfFiniteType a] [QuasiCompact a] (F G : T.Modules) (r e : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank e]
    (s : F.sections) (t : G.sections) (hs : IsRegularSection P T a F r s)
    (ht : IsRegularSection P T a G e t) (_htr : IsTransverseDirectSum P T a F G r e s t),
  ∃ (hFG : (F ⨯ G).IsFiniteLocallyFreeOfRank (r + e))
    (hst : @IsRegularSection P T a _ _ _ (F ⨯ G) (r + e) hFG
      (regularSectionSum F G s t))
    (hc : IsClosedImmersion (regularSectionZeroProjection P T a F r s))
    (hd : IsClosedImmersion (regularSectionZeroProjection P T a G e t))
    (hi : IsClosedImmersion (regularSectionIntersectionProjection P T a F G r e s t))
    (hj : IsClosedImmersion (regularSectionSumZeroProjection P T a F G r e s t))
    (hproj : (regularSectionSumZeroComparison P T a F G r e s t).hom ≫
        regularSectionIntersectionProjection P T a F G r e s t =
      regularSectionSumZeroProjection P T a F G r e s t),
    HEq (@functorialCupChangeSupport P true _ _ _
      (regularSectionIntersectionProjection P T a F G r e s t)
      (regularSectionSumZeroProjection P T a F G r e s t) hi hj
      (regularSectionSumZeroComparison P T a F G r e s t).hom hproj
      (2 * ((r + e : ℕ) : ℤ)) (r + e : ℕ)
      (@c T a _ _ _ (F ⨯ G) (r + e) hFG (regularSectionSum F G s t) hst))
    (@functorialCup P true _ _ _ a
      (regularSectionZeroProjection P T a F r s)
      (regularSectionZeroProjection P T a G e t) hc hd
      (2 * (r : ℤ)) (2 * (e : ℤ)) r e (c a F r s hs) (c a G e t ht))

/-- Exactly the four properties of the localized class, factored as named predicates
so the kernel checks each geometric law once.
Source: blueprint localized-top-Chern, (L1)--(L4)
(blueprint: thm-pur-localized-top-chern). -/
def LocalizedTopChernLaws (P : PurityFiniteSetting.{u})
    (c : P.LocalizedTopChernClasses) : Prop :=
  P.LocalizedTopChernForgetSupport c ∧ P.LocalizedTopChernLine c ∧
    P.LocalizedTopChernBaseChange c ∧ P.LocalizedTopChernDirectSum c

/-- The forget_support clause of the four localized Chern laws.
Source: blueprint localized-top-Chern, (L1)--(L4)
(blueprint: thm-pur-localized-top-chern).
Proof: project the corresponding conjunct of LocalizedTopChernLaws. -/
theorem LocalizedTopChernLaws.forget_support (P : PurityFiniteSetting.{u})
    {c : P.LocalizedTopChernClasses} (h : P.LocalizedTopChernLaws c) :
    P.LocalizedTopChernForgetSupport c := by
  exact h.1

/-- The line clause of the four localized Chern laws.
Source: blueprint localized-top-Chern, (L1)--(L4)
(blueprint: thm-pur-localized-top-chern).
Proof: project the corresponding conjunct of LocalizedTopChernLaws. -/
theorem LocalizedTopChernLaws.line (P : PurityFiniteSetting.{u})
    {c : P.LocalizedTopChernClasses} (h : P.LocalizedTopChernLaws c) :
    P.LocalizedTopChernLine c := by
  exact h.2.1

/-- The base_change clause of the four localized Chern laws.
Source: blueprint localized-top-Chern, (L1)--(L4)
(blueprint: thm-pur-localized-top-chern).
Proof: project the corresponding conjunct of LocalizedTopChernLaws. -/
theorem LocalizedTopChernLaws.base_change (P : PurityFiniteSetting.{u})
    {c : P.LocalizedTopChernClasses} (h : P.LocalizedTopChernLaws c) :
    P.LocalizedTopChernBaseChange c := by
  exact h.2.2.1

/-- The direct_sum clause of the four localized Chern laws.
Source: blueprint localized-top-Chern, (L1)--(L4)
(blueprint: thm-pur-localized-top-chern).
Proof: project the corresponding conjunct of LocalizedTopChernLaws. -/
theorem LocalizedTopChernLaws.direct_sum (P : PurityFiniteSetting.{u})
    {c : P.LocalizedTopChernClasses} (h : P.LocalizedTopChernLaws c) :
    P.LocalizedTopChernDirectSum c := by
  exact h.2.2.2

/-- There is a canonical localized top Chern family, with precisely (L1)--(L4).
Source: blueprint main-20261015, thm-pur-localized-top-chern, statement and the
repaired DAG proof (blueprint: thm-pur-localized-top-chern).

Proof following all eleven DAG steps:
1. In rank zero use the coefficient identity; its support-forgetting image is c_0=1.
   For positive rank use lem-pur-supported-hom to write supported classes as arrows.
   The complete flag bundle and lem-pur-flag-pullback-injective detect equality.
2. On the total space E(F), the zero section has coordinate ideal (x_1,...,x_r).
   Variables are a regular sequence over any ring. Affine-space smoothness and the
   nonzerodivisor dimension-drop lemma give the required relative smooth pair.
   Lem-pur-relative-support-bottom-descent gives vanishing below degree 2r.
3. Lem-pur-supported-bottom-gluing identifies this lowest supported group with
   sections of its local-cohomology sheaf. Lem-pur-frame-independence identifies
   the coordinate classes on overlaps. Glue the universal class u_F there.
   In the recorded Yoneda convention each coordinate divisor contributes minus
   the frame boundary, as specified by lem-pur-divisor-class; use their product.
4. Coordinate boundaries commute with pullback, so uniqueness in bottom-degree
   gluing gives h*u_F=u_(g*F) on the new total space, including singular bases.
5. Define the class by s*u_F, whose support is the recorded fibre-product Z(s).
   This is one global supported pullback, not descent on an arbitrary zero scheme.
6. In rank one the zero-section Cartier class has these same local values.
   Lem-pur-cartier-class-agreement identifies its regular pullback with cl(Z(s)),
   the relative-torsor Kummer class in (L1), with the corrected divisor sign.
7. Composition of supported pullbacks gives (L2). For tautological sections every
   base change still has polynomial-variable components, hence is regular.
8. On E(F direct-sum G), the internal product of the two universal orientations
   has the same coordinate values as u_(F direct-sum G). Bottom-degree gluing
   identifies them; pull back along (s,t). Transversality puts all sections in
   the statement and the canonical zero-scheme comparison gives (L3).
9. On the complete flag bundle use its actual tautological filtration. The
   nested Cartier composite of lem-pur-flag-localized-product has the same local
   coordinate product by lem-pur-flag-local-comparison. Bottom gluing identifies
   it with the universal orientation; no intermediate arbitrary zero locus is used.
10. Forget supports and apply the projection formula to that nested composite.
    Pullback along the section gives the product of the Chern roots on the flag.
11. The projective-bundle relation makes ordinary Chern classes natural, and
    lem-pur-chern-flag-formula identifies their top class with that same product.
    Full-support flag injectivity proves (L4). The explicit tensor-shift maps in
    this module only identify the two existing Tate presentations. All construction
    uses ordinary supported cohomology and the projective-bundle formula. -/
theorem localized_top_chern (P : PurityFiniteSetting.{u}) :
    ∃ c : P.LocalizedTopChernClasses, P.LocalizedTopChernLaws c := by
  sorry

end WeilConjectures.PurityFiniteSetting
