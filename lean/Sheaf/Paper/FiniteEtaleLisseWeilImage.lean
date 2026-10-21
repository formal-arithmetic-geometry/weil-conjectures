/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.Paper.CommonStageWeilShriek
public import Sheaf.Paper.CommonStageLisse
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.Paper.SfIntegralReductionTower
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.Paper.LisseIntegralSmallCoefficients
import WeilConjectures.Mathlib.Topology.NoetherianSpace
import Sheaf.Paper.GaloisLisseRepresentations
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.RepresentationTheory.Rep.Basic
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import Sheaf.Paper.LisseAdicFiberFunctors
import Sheaf.Paper.LisseModuleSheaves
import Sheaf.Paper.LisseTensorScalarExtension
import Sheaf.RepresentationTheory.LAdic
import Sheaf.RepresentationTheory.ProfiniteStableLattice
import Sheaf.Paper.ProEtaleLisseOrigin
import Sheaf.SixFunctors.IntegralLisseReductionEquivalence
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import WeilConjectures.AlgebraicGeometry.FiniteEtalePushforwardLocallyConstant
import WeilConjectures.SixFunctors.Finite.BaseChange
import Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.SfCommonStageDirectImage
import Sheaf.Paper.SfConstructibleHeart
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.Paper.SfWeilSheafComplex
import WeilConjectures.WeilSheaf.FourierInversion.OtherSections

/-! # Lissity of finite etale direct image on the actual Weil fixed pairs

Source: blueprint main-20261015, sec-deligne-laumon-a1, sk-thm-dl-a1-upper,
lem-a1-reduction-lisse-pure.proof.md, opening sentence
(blueprint: lem-a1-finite-map-lisse).

The proper direct image and its Frobenius mate are the recorded common-stage operations.
The integral certificate explicitly identifies the finite-level derived-limit definition
with the underived completed-module direct image, before rationalization. It also identifies
that rationalization with the underlying object of the equivariant proper image.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [hXsep : IsSeparated X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [hYsep : IsSeparated Y₀.hom]
  (g₀ : Y₀ ⟶ X₀) [IsFinite g₀.left] [het : Etale g₀.left]

/-- The finite direct image on the recorded category of Weil fixed pairs. Its structure
is the prescribed Frobenius exchange followed by the direct image of theta, with no
condition on an arithmetic Galois action and no choice of a Frobenius-stable lattice.
Source: blueprint opening sentence and Stanford L19, Definition 1.1.7
(blueprint: lem-a1-finite-map-lisse). -/
def a1FiniteEtaleWeilImage :
    sfCommonStageWeilComplex D l hl Y₀ Ω ⥤ sfCommonStageWeilComplex D l hl X₀ Ω :=
  IsoAlgebra.mapOfNatIso (zlProperFrobenius D l hl Ω g₀)

/-- A finite-stage witness for the equality of the ordinary and derived images of
the displayed lisse sheaf. The input is realized by a finite locally free completed
module N. The output is realized by the actual underived g_*N, and the recorded
Roos-triangle derived image of the input is isomorphic to that same degree-zero object.
All categories, scalar localizations, site maps and Frobenius comparisons are the
recorded ones; none are arbitrary input maps.
Source: blueprint opening sentence; BS Proposition 6.8.4; Stacks 095B
(blueprint: lem-a1-finite-map-lisse). -/
structure A1FiniteEtaleImageRealization (F : sfCommonStageWeilSheaf D l hl Y₀ Ω) where
  stage : AlgebraicallyClosedCoefficients.Index l Ω
  input : sfIntegralConstructibleCategory l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω stage) (D.geometricFiber Y₀).left
  lattice : scalarReductionSource l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω stage) (D.geometricFiber Y₀).left
  finiteFree : SheafOfModules.IsFiniteLocallyFree.{u + 1, u, u + 1} lattice
  inputDegreeZero : Nonempty (input.obj ≅ (DerivedCategory.singleFunctor _ 0).obj lattice)
  inputRealization : Nonempty (F.obj.carrier ≅
    (GeneralAlgebraicallyClosedCoefficients.inclusion stage).obj
      ((sfRationalConstructibleLocalization l _ (D.geometricFiber Y₀).left).obj input))
  output : sfIntegralConstructibleCategory l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω stage) (D.geometricFiber X₀).left
  outputDegreeZero : Nonempty (output.obj ≅ (DerivedCategory.singleFunctor _ 0).obj
    ((sfCompletedModuleDirectImage l _ (zlFiberMap D g₀)).obj lattice))
  outputRealization : Nonempty (((a1FiniteEtaleWeilImage D l hl Ω g₀).obj F.obj).carrier ≅
    (GeneralAlgebraicallyClosedCoefficients.inclusion stage).obj
      ((sfRationalConstructibleLocalization l _ (D.geometricFiber X₀).left).obj output))
  product : HasProduct (sfDirectImageTerm l _ (zlFiberMap D g₀) input.obj)
  derivedImage : @SfIntegralDirectImage l _
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω stage) _ _ _ _ _
      (zlFiberMap D g₀) input.obj product
  derivedEqualsUnderived : Nonempty (derivedImage.obj ≅ output.obj)

include hXsep hYsep het in
/-- A finite etale direct image of a lisse Weil sheaf is a lisse Weil sheaf, and is
also its derived image. This uses fixed pairs over the constructible derived category,
not a derived category of Weil sheaves.
Source: blueprint main-20261015, lem-a1-reduction-lisse-pure.proof.md, opening sentence
(blueprint: lem-a1-finite-map-lisse).

Proof:
1. Choose a finite field of coefficients representing the underlying lisse sheaf.
   The geometric source is Noetherian with finitely many clopen connected components
   (lem-sfb-noetherian-connected-components-open). On each component use the Galois
   correspondence (cor-galois-lisse-representations) and a stable integral lattice
   (lem-pod-profinite-stable-lattice). Transfer the finite levels to the pro-etale
   site (lem-sf-proetale-locally-constant-origin) and realize their inverse limit
   (lem-sfb-integral-lisse-reduction-equivalence). Only a geometric lattice is used.
2. Finiteness and etaleness survive base change. Apply the finite-etale local splitting
   theorem (lem-weil-pbc-finite-etale-etale-local-split) separately on covering members;
   the finite sheet set may be empty and its size need not be globally constant.
3. The sectionwise direct-image formula and the sheaf axiom give the finite product of
   sheet restrictions. Those restrictions are exact by pro-etale localization and
   lem-weil-pbc-proetale-restriction-injectives. Finite products are exact by local
   lifting of finitely many coordinates and a common refinement. Thus g_* is exact.
4. Use lem-weil-pbc-exact-functor-derived-functor at each quotient coefficient ring.
   The etale finite-pushforward theorem and finite-exchange comparison identify its
   image with a locally finite free sheaf N_n. Sheetwise computation identifies its
   actual quotient transitions, including all their composition compatibilities.
5. Integral lisse reconstruction gives N = lim N_n, locally finite free. Epimorphic
   transitions and det-pe-milnor-epimorphic compute the derived limits. The defining
   formula of def-weil-derived-direct-image gives Rg_*M = N[0], while the sectionwise
   formula gives g_*M = N. The two-term uniformizer resolution identifies ordinary
   and derived reductions, and the Roos triangle proves derived completeness.
   The single-stratum reductions give integral constructibility with amplitude [0,0].
6. Rationalize and pass to common stages. Finite sheet sums commute with scalar
   extension, coherently on transitions and field extensions. Thus the output is
   lisse, in the constructible heart, and has the displayed underived realization.
   Rank zero, empty schemes or fibres, and varying degree and rank are included.
7. Apply the canonical proper Frobenius exchange and then the image of theta, as in
   prop-weil-operations. The map is over k₀, so its geometric fibre commutes with
   Frobenius. The fixed pair has the underlying object from steps 5-6 and therefore
   is a constructible lisse Weil sheaf (def-weil-weil-sheaf-complex). -/
theorem a1FiniteEtaleWeilImage_lisse
    (F : sfCommonStageWeilSheaf D l hl Y₀ Ω)
    (_hF : HasCommonStageLisseLattice l Ω (D.geometricFiber Y₀).left F.obj.carrier) :
    sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω
        (((a1FiniteEtaleWeilImage D l hl Ω g₀).obj F.obj).carrier) ∧
      HasCommonStageLisseLattice l Ω (D.geometricFiber X₀).left
        (((a1FiniteEtaleWeilImage D l hl Ω g₀).obj F.obj).carrier) ∧
      Nonempty (A1FiniteEtaleImageRealization D l hl Ω g₀ F) := by
  sorry

end WeilConjectures
