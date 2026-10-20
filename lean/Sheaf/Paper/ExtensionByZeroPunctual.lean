/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72
-/
module

public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.AdicHeartIntrinsicFibres
public import Sheaf.Paper.AdicPunctualWeights
public import Sheaf.Paper.WeilCompactSupportCohomology
import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import Sheaf.Paper.SfIntegralCompactSupportConstructible
import Sheaf.Paper.SfConstructibleHeart
import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
import Sheaf.Paper.CompletedOpenExchangeTransport
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Sheaf.AlgebraicGeometry.FrobeniusOpenSquare
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Paper.DlConstructibleFibresExact
import Sheaf.Paper.LocalFrobeniusTrace
import Sheaf.Paper.SfWeilSheafComplex
import Sheaf.SixFunctors.IntegralOpenReductionComparison

/-! # Exact extension by zero and punctual weights

Source: blueprint main-20261015, sec-deligne-laumon-general,
sk-l-dl-general-quasifinite/lem-zl-quasi-finite.proof.md, parts (1) and (2)
(blueprint: lem-zl-extension-by-zero-punctual).

The canonical open extension is the left adjoint of the recorded Weil pullback.
The theorem identifies its underlying object with the actual completed-tower compact
support value and supplies the natural coefficient-fibre and local-Frobenius formulas.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar] [IsAlgClosure (Padic l) Qbar]
  {U₀ X₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] [hUsep : IsSeparated U₀.hom]
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [hXsep : IsSeparated X₀.hom]
  (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left]


/-- Noetherianity makes this open immersion quasi-compact; this is a consequence,
not an extra hypothesis on the open immersion.
Source: Stacks 01T6 and 01OZ (blueprint: lem-zl-extension-by-zero-punctual).
Proof: a finite-type scheme over a field is Noetherian. Every open subset of a
Noetherian space is quasi-compact. Apply this to inverse images of affine opens. -/
@[instance]
theorem zlOpen_quasiCompact : QuasiCompact j₀.left := by
  sorry

/-- The prescribed geometric-fibre map is an open immersion.
Source: blueprint geometric base change of open immersions
(blueprint: lem-zl-extension-by-zero-punctual).
Proof: zlFiberMap is the map of Over.pullback along Spec(k) → Spec(k₀).
Its square with j₀ is Cartesian by the pullback universal property. Open immersions
are stable under this base change. -/
@[instance]
theorem zlOpenFiber_isOpenImmersion : IsOpenImmersion (zlFiberMap D j₀) := by
  sorry

include hUsep hXsep

/-- Open extension preserves constructibility, so the Weil-heart pullback has its
canonical left adjoint within the constructible heart.
Source: blueprint proof (1); Stacks 03DJ and 03S5
(blueprint: lem-zl-extension-by-zero-punctual).
Proof: at finite torsion coefficients use extension by zero left adjoint to restriction.
The completed open-reduction comparison identifies its strict reduction tower and
its total limit with completed ringed-site extension. This is constructible and
exact. Rationalize and pass to common stages, preserving the units and counits.
The Frobenius Cartesian square induces the Weil action by its canonical mate;
the adjunction equation is equivariant, hence restricts to the Weil heart. -/
theorem zlOpenWeilPull_isRightAdjoint :
    (zlWeilPull D l hl Qbar j₀).IsRightAdjoint := by
  sorry

/-- The canonical extension by zero, characterized by the open restriction adjunction.
Choosing an adjoint determines the functor up to its unique adjunction isomorphism.
Source: blueprint proof (1) (blueprint: lem-zl-extension-by-zero-punctual). -/
def zlOpenWeilShriek :
    sfCommonStageWeilSheaf D l hl U₀ Qbar ⥤ sfCommonStageWeilSheaf D l hl X₀ Qbar :=
  letI := zlOpenWeilPull_isRightAdjoint D l hl Qbar j₀
  (zlWeilPull D l hl Qbar j₀).leftAdjoint

omit hUsep hXsep

/-- Forget the heart and Weil structures, retaining the literal common-stage carrier.
Source: blueprint proof (1) (blueprint: lem-zl-extension-by-zero-punctual). -/
def zlWeilHeartCarrier (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] :
    sfCommonStageWeilSheaf D l hl Y₀ Qbar ⥤
      generalAlgebraicallyClosedConstructibleCategory l Qbar (D.geometricFiber Y₀).left :=
  ObjectProperty.ι _ ⋙ sfCommonStageWeilForget D l hl Y₀ Qbar

/-- Finite-stage heart carrier, for the normalized rational compact-support comparison.
Source: blueprint proof (1) (blueprint: lem-zl-extension-by-zero-punctual). -/
def zlFiniteWeilHeartCarrier (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] :
    sfWeilSheaf D l hl Y₀ E ⥤ sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left :=
  ObjectProperty.ι _ ⋙ sfWeilForget D l hl Y₀ E

/-- Naturality of the existing finite-stage Frobenius comparison.
Source: blueprint common-stage passage in proof (1)
(blueprint: lem-zl-extension-by-zero-punctual).
Proof: the common-stage pullback is defined on common-stage representatives by the
finite pullback and its scalar comparisons. Apply its prescribed map formula to a
same-stage arrow. Both sides are its finite pullback, with the identical inclusion
associators. Naturality of the equality comparisons gives the displayed identity. -/
theorem zlWeilStageSquare_naturality (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (L : Padic.FiniteCoefficientFields l Qbar)
    (K M : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) (D.geometricFiber Y₀).left)
    (f : K ⟶ M) :
    (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Qbar).map
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).map f) ≫
      (sfWeilStagePullbackIdentification D l hl Y₀ Qbar L M).hom =
    (sfWeilStagePullbackIdentification D l hl Y₀ Qbar L K).hom ≫
      (GeneralAlgebraicallyClosedCoefficients.inclusion L).map
        ((sfWeilFrobeniusPullback D l hl Y₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L)).map f) := by
  sorry

/-- The existing stage comparison, bundled naturally for the fixed-pair transport.
Source: blueprint common-stage passage in proof (1)
(blueprint: lem-zl-extension-by-zero-punctual). -/
def zlWeilStageSquare (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (L : Padic.FiniteCoefficientFields l Qbar) :
    GeneralAlgebraicallyClosedCoefficients.inclusion L ⋙
        sfCommonStageWeilFrobeniusPullback D l hl Y₀ Qbar ≅
      sfWeilFrobeniusPullback D l hl Y₀
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) ⋙
          GeneralAlgebraicallyClosedCoefficients.inclusion L :=
  NatIso.ofComponents (sfWeilStagePullbackIdentification D l hl Y₀ Qbar L)
    (fun {K M} f ↦ zlWeilStageSquare_naturality D l hl Qbar Y₀ L K M f)

/-- A finite-stage heart object is in the common-stage heart under the recorded
fixed-pair inclusion.
Source: blueprint common-stage passage in proof (1)
(blueprint: lem-zl-extension-by-zero-punctual).
Proof: each of the two standard rational classes represents the corresponding
common-stage class at its given field. Their intersection is the heart. The
fixed-pair transport has exactly that same included carrier. -/
theorem zlWeilHeartStage_mem (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (L : Padic.FiniteCoefficientFields l Qbar)
    (K : sfWeilSheaf D l hl Y₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L)) :
    sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Qbar
      ((CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
        (zlWeilStageSquare D l hl Qbar Y₀ L)).obj K.obj).carrier := by
  sorry

/-- The literal finite-stage Weil inclusion, restricted to the two constructible
hearts. This extends the existing sfWeilStageObject action to all arrows.
Source: blueprint common-stage passage in proof (1)
(blueprint: lem-zl-extension-by-zero-punctual). -/
def zlWeilHeartStage (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (L : Padic.FiniteCoefficientFields l Qbar) :
    sfWeilSheaf D l hl Y₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) ⥤
      sfCommonStageWeilSheaf D l hl Y₀ Qbar :=
  ((sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Qbar).inverseImage
    (sfCommonStageWeilForget D l hl Y₀ Qbar)).lift
      (ObjectProperty.ι _ ⋙ CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
        (zlWeilStageSquare D l hl Qbar Y₀ L))
      (zlWeilHeartStage_mem D l hl Qbar Y₀ L)

/-- H⁰ of the actual finite-coefficient derived point fibre, natural in Weil sheaves.
The operator on its value is localClosedFrobeniusCohomology in degree zero.
Source: blueprint proof (2) (blueprint: lem-zl-extension-by-zero-punctual). -/
def zlClosedCoefficientFiber (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) :
    sfWeilSheaf D l hl Y₀ E ⥤ ModuleCat.{u} E :=
  zlFiniteWeilHeartCarrier D l hl E Y₀ ⋙
    @rationalDerivedPullback l _ E _ _ _ _ _ (localClosedPoint D Y₀ y ι hι)
      (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl Y₀) ⋙
    pointRationalFibre D l hl E ⋙ DerivedCategory.coefficientFdCohomology E 0

/-- Punctual upper eigenvalue bound, without a mixed-filtration hypothesis.
Source: blueprint proof (2) (blueprint: lem-zl-extension-by-zero-punctual). -/
def ZlPunctualUpperBound (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (iota : Qbar ≃+* ℂ)
    (F : sfCommonStageWeilSheaf D l hl Y₀ Qbar) (w : ℝ) : Prop :=
  ∀ (y : {y : Y₀.left // y ∈ closedPoints Y₀.left}) (α : Qbar),
    SfPunctualEigenvalue D l hl Qbar Y₀ F y α →
      ‖iota α‖ ≤ (Nat.card (Y₀.left.residueField y.val) : ℝ) ^ (w / 2)

include hUsep hXsep

/-- Extension by zero is exact on constructible common-stage Weil sheaves, is the
recorded compact-support functor, and has the natural adic fibre formula at every
geometric point. At closed points of the open, its natural finite-stage fibre
comparison intertwines the specified local geometric Frobenius. Consequently it
preserves punctual upper bounds and punctual purity, for every real weight.

Source: blueprint main-20261015, proof of lem-zl-quasi-finite, (1) and (2)
(blueprint: lem-zl-extension-by-zero-punctual).

Proof, in the order of the DAG node:
1. Separated finite type survives geometric base change. Finite type over the field
   gives Noetherianity, hence quasi-compactness of j, and a closed complement exists
   (lem-pod-separated-finite-type-base-change, lem-weil-pbc-finite-type-over-noetherian,
   lem-weil-pbc-noetherian-open-subscheme-noetherian,
   lem-weil-pbc-closed-subset-closed-subscheme).
2. Use the compactification (j,id). lem-sf-integral-open-reduction-comparison identifies
   its completed strict-tower limit with ringed-site extension by zero. The latter is
   exact by lem-pur-site-restriction-module-adjunction-exact, and its limit is integral
   constructible by lem-sf-integral-compact-support-constructible.
3. Rationalization and common-stage descent preserve both standard classes: represent
   an object in the corresponding integral class, apply step 2, then transport its
   representing isomorphism. Use def-weil-constructible-standard-tstructure and
   prop-functor-package for the coefficient comparisons. Thus the heart is preserved.
4. lem-cbc-completed-extension-zero-comparison identifies restriction to the open with
   the identity and to its closed complement with zero, as at finite coefficients by
   lem-cbc-proetale-extension-zero. Apply lem-per-adic-heart-pullback-fibres at every
   geometric point. All comparisons are natural in the input and descend through
   rationalization and common stages.
5. lem-trf-frobenius-open-square and prop-functor-package give the canonical Frobenius
   exchange. Define the output action as j!theta after that exchange. It restricts to
   theta on the open. The same identity for all Frobenius powers, followed by the
   return and point-transport comparisons of def-weil-local-frobenius-trace, gives
   precisely the intertwining equation below, including finite scalar extension.
6. At each geometric point, a short exact sequence extends to its original sequence
   on the open and to the zero sequence outside. Exactness detection in
   lem-dl-a1-constructible-fibres-exact proves exactness, retaining Weil structures.
7. Open immersion does not change the residue field of a closed point. The operators
   in step 5 have identical eigenvalues, hence the same inequalities and equalities.
   Outside the open the zero space has no eigenvalues. This proves both weight clauses,
   including the zero sheaf, empty open, identity immersion, and arbitrary real w. -/
theorem extensionByZero_punctual (iota : Qbar ≃+* ℂ) :
    (zlOpenWeilShriek D l hl Qbar j₀).Additive ∧
    PreservesFiniteLimits (zlOpenWeilShriek D l hl Qbar j₀) ∧
    PreservesFiniteColimits (zlOpenWeilShriek D l hl Qbar j₀) ∧
    (∀ (F : sfCommonStageWeilSheaf D l hl U₀ Qbar)
      (L : Padic.FiniteCoefficientFields l Qbar)
      (K : sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) (D.geometricFiber U₀).left),
      Nonempty (F.obj.carrier ≅ (GeneralAlgebraicallyClosedCoefficients.inclusion L).obj
        ((sfRationalConstructibleLocalization l _ (D.geometricFiber U₀).left).obj K)) →
      Nonempty (((zlOpenWeilShriek D l hl Qbar j₀).obj F).obj.carrier ≅
        sfQbarCompactSupportValue l (X := (D.geometricFiber U₀).left)
          (Y := (D.geometricFiber X₀).left) (f := zlFiberMap D j₀)
          D.k (zlClosurePrimeUnit D l hl) Qbar
          (Compactification.ofIsOpenImmersion (zlFiberMap D j₀)) L K)) ∧
    (∃
      (FU : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω],
        (Spec (.of Ω) ⟶ (D.geometricFiber U₀).left) →
          (generalAlgebraicallyClosedConstructibleCategory l Qbar (D.geometricFiber U₀).left ⥤
            ModuleCat.{max (u + 1) v} Qbar))
      (FX : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω],
        (Spec (.of Ω) ⟶ (D.geometricFiber X₀).left) →
          (generalAlgebraicallyClosedConstructibleCategory l Qbar (D.geometricFiber X₀).left ⥤
            ModuleCat.{max (u + 1) v} Qbar)),
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (x : Spec (.of Ω) ⟶ (D.geometricFiber U₀).left),
        SfAdicCommonFiberSpec l (D.geometricFiber U₀).left x Qbar (FU Ω x)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (x : Spec (.of Ω) ⟶ (D.geometricFiber X₀).left),
        SfAdicCommonFiberSpec l (D.geometricFiber X₀).left x Qbar (FX Ω x)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (x : Spec (.of Ω) ⟶ (D.geometricFiber U₀).left),
        Nonempty (zlOpenWeilShriek D l hl Qbar j₀ ⋙ zlWeilHeartCarrier D l hl Qbar X₀ ⋙
          FX Ω (x ≫ zlFiberMap D j₀) ≅ zlWeilHeartCarrier D l hl Qbar U₀ ⋙ FU Ω x)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (x : Spec (.of Ω) ⟶ (D.geometricFiber X₀).left),
        Set.range x.base ⊆ (Set.range (zlFiberMap D j₀).base)ᶜ →
        ∀ F : sfCommonStageWeilSheaf D l hl U₀ Qbar,
          IsZero ((FX Ω x).obj (((zlOpenWeilShriek D l hl Qbar j₀).obj F).obj.carrier)))) ∧
    (∀ L : Padic.FiniteCoefficientFields l Qbar,
      ∃ J : sfWeilSheaf D l hl U₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) ⥤
          sfWeilSheaf D l hl X₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L),
      Nonempty (J ⋙ zlFiniteWeilHeartCarrier D l hl _ X₀ ≅
        zlFiniteWeilHeartCarrier D l hl _ U₀ ⋙
          sfCompactSupportFiniteFunctor l (X := (D.geometricFiber U₀).left)
            (Y := (D.geometricFiber X₀).left) (f := zlFiberMap D j₀)
            D.k (zlClosurePrimeUnit D l hl)
            (Compactification.ofIsOpenImmersion (zlFiberMap D j₀))
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L)) ∧
      Nonempty (zlWeilHeartStage D l hl Qbar U₀ L ⋙ zlOpenWeilShriek D l hl Qbar j₀ ≅
        J ⋙ zlWeilHeartStage D l hl Qbar X₀ L) ∧
      ∀ (u : {u : U₀.left // u ∈ closedPoints U₀.left})
        (x : {x : X₀.left // x ∈ closedPoints X₀.left})
        (ιU : U₀.left.residueField u.val →+* D.k)
        (hU : ιU.comp (U₀.hom.residueFieldAlgebraMap u.val) = algebraMap D.k₀ D.k)
        (ιX : X₀.left.residueField x.val →+* D.k)
        (hX : ιX.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k),
        j₀.left.base u.val = x.val →
        localClosedPoint D U₀ u ιU hU ≫ zlFiberMap D j₀ =
          localClosedPoint D X₀ x ιX hX →
        ∃ e : J ⋙ zlClosedCoefficientFiber D l hl _ X₀ x ιX hX ≅
            zlClosedCoefficientFiber D l hl _ U₀ u ιU hU,
          ∀ K : sfWeilSheaf D l hl U₀
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L),
            localClosedFrobeniusCohomology l _ D hl X₀ (J.obj K).obj x ιX hX 0 ≫
                e.hom.app K =
              e.hom.app K ≫ localClosedFrobeniusCohomology l _ D hl U₀ K.obj u ιU hU 0) ∧
    (∀ (w : ℝ) (F : sfCommonStageWeilSheaf D l hl U₀ Qbar),
      (ZlPunctualUpperBound D l hl Qbar U₀ iota F w →
        ZlPunctualUpperBound D l hl Qbar X₀ iota
          ((zlOpenWeilShriek D l hl Qbar j₀).obj F) w) ∧
      (SfIsPunctuallyPureOfWeight D l hl Qbar U₀ iota F w →
        SfIsPunctuallyPureOfWeight D l hl Qbar X₀ iota
          ((zlOpenWeilShriek D l hl Qbar j₀).obj F) w)) := by
  sorry

end WeilConjectures
