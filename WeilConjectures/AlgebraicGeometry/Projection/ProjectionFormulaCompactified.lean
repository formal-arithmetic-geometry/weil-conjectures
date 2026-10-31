/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.ProperBaseChange.OpenImmersionTensorPiece
public import WeilConjectures.AlgebraicGeometry.Projection.ProjectionCompactification
public import WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionFormulaArrows
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalPullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
public import WeilConjectures.AlgebraicGeometry.Ringed.RingedProjectionRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat
import WeilConjectures.CategoryTheory.Monoidal.Dualizable

/-!
# The compactified projection formula for locally perfect coefficients

Source: Weil blueprint, proper base change, lemma 1271
(blueprint: lemma-weil-pbc-projection-formula-compactified).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme
section Open

variable {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
  (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R ≅ S)

/-- The derived open adjunction is the localization of the termwise ordinary adjunction.
Source: Stacks, Tags 03DI and 015F
(blueprint: lemma-weil-pbc-projection-formula-compactified). -/
def proEtaleRingDerivedOpenAdjunction :
    proEtaleRingDerivedOpenExtension j R S c ⊣ proEtaleRingDerivedPullback j R S c :=
  letI : CatCommSq
      ((proEtaleRingOpenExtension j R S c).mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (proEtaleRingDerivedOpenExtension j R S c) :=
    ⟨(proEtaleRingOpenExtension j R S c).mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq
      ((proEtaleRingModulePullback j R S c).mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (proEtaleRingDerivedPullback j R S c) :=
    ⟨(proEtaleRingModulePullback j R S c).mapDerivedCategoryFactors.symm⟩
  let am : proEtaleRingOpenExtension j R S c ⊣ proEtaleRingModulePullback j R S c :=
    Adjunction.ofIsRightAdjoint _
  (am.mapHomologicalComplex (ComplexShape.up ℤ)).localization
      DerivedCategory.Q (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
      DerivedCategory.Q (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
      (proEtaleRingDerivedOpenExtension j R S c) (proEtaleRingDerivedPullback j R S c)

/-- The adjunction projection is exactly the transpose of unit tensor identity.
Source: Stacks, Tags 03DI and 07A4
(blueprint: lemma-weil-pbc-projection-formula-compactified). -/
def proEtaleOpenProjection
    (a : ProEtaleTensorModel Z R) (b : ProEtaleTensorModel X S)
    (E : DerivedCategory (proEtaleRingModules X S))
    (M : DerivedCategory (proEtaleRingModules Z R)) :
    (proEtaleRingDerivedOpenExtension j R S c).obj
        (b.tensor.obj (E, (proEtaleRingDerivedPullback j R S c).obj M)) ⟶
      a.tensor.obj ((proEtaleRingDerivedOpenExtension j R S c).obj E, M) :=
  ((proEtaleRingDerivedOpenAdjunction j R S c).homEquiv _ _).symm
    (b.tensor.map (Prod.mkHom ((proEtaleRingDerivedOpenAdjunction j R S c).unit.app E)
      (𝟙 _)) ≫ (proEtaleCanonicalTensorComparison j R S c a b).inv.app
        ((proEtaleRingDerivedOpenExtension j R S c).obj E, M))

end Open
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.ProjectionRestriction

variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
  {J : GrothendieckTopology C} {H : GrothendieckTopology D}
  {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf H CommRingCat.{u + 1}}
  {F : C ⥤ D} (o : Operation F R S) (t : o.OrdinaryTensor)

end AlgebraicGeometry.Scheme.ProjectionRestriction

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (d : Compactification f) [QuasiCompact d.i]
  (RY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (RZ : Sheaf (ProEt.topology d.Z) CommRingCat.{u + 1})
  (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (cp : (proEtaleSheafInverseImage d.g CommRingCat.{u + 1}).obj RY ≅ RZ)
  (cj : (proEtaleSheafInverseImage d.i CommRingCat.{u + 1}).obj RZ ≅ RX)
  (a : ProEtaleTensorModel Y RY) (b : ProEtaleTensorModel d.Z RZ)
  (c : ProEtaleTensorModel X RX)
  (E : DerivedCategory (proEtaleRingModules X RX))
  (Q : DerivedCategory (proEtaleRingModules Y RY))

/-- The first arrow is the adjoint of counit tensor identity for p and j_!E.
Source: Weil blueprint, lemma 1271
(blueprint: lemma-weil-pbc-projection-formula-compactified). -/
def compactifiedProjectionPi :=
  derivedProjectionFormulaMate (proEtaleRingDerivedPullback d.g RY RZ cp)
    (proEtaleRingDerivedDirectImage d.g RY RZ cp)
    (proEtaleRingDerivedAdjunction d.g RY RZ cp) a.tensor b.tensor
    (proEtaleCanonicalTensorComparison d.g RY RZ cp a b)
    ((proEtaleRingDerivedOpenExtension d.i RZ RX cj).obj E) Q

/-- Theta is alpha inverse followed by extension of identity tensor c inverse.
The factorization identifies f with d.i followed by d.g; its coefficient identification
is exactly the composite identification, with no independent third choice.
Source: Weil blueprint, lemma 1271
(blueprint: lemma-weil-pbc-projection-formula-compactified). -/
def compactifiedProjectionTheta
    (hα : IsIso (proEtaleOpenProjection d.i RZ RX cj b c E
      ((proEtaleRingDerivedPullback d.g RY RZ cp).obj Q))) :
    b.tensor.obj ((proEtaleRingDerivedOpenExtension d.i RZ RX cj).obj E,
        (proEtaleRingDerivedPullback d.g RY RZ cp).obj Q) ≅
      (proEtaleRingDerivedOpenExtension d.i RZ RX cj).obj
        (c.tensor.obj (E, (proEtaleRingDerivedPullback (d.i ≫ d.g) RY RX
          (proEtaleRingCompositeCoefficients d.i d.g RY RZ RX cp cj)).obj Q)) :=
  (@asIso _ _ _ _ (proEtaleOpenProjection d.i RZ RX cj b c E
    ((proEtaleRingDerivedPullback d.g RY RZ cp).obj Q)) hα).symm ≪≫
      (proEtaleRingDerivedOpenExtension d.i RZ RX cj).mapIso
        (c.tensor.mapIso (Iso.prod (Iso.refl E)
          ((proEtaleCanonicalPullbackComposition d.i d.g RY RZ RX cp cj).app Q).symm))

/-- The ordered forward map pi followed by Rp_* theta.
Source: Weil blueprint, lemma 1271
(blueprint: lemma-weil-pbc-projection-formula-compactified). -/
def compactifiedProjectionForward
    (hα : IsIso (proEtaleOpenProjection d.i RZ RX cj b c E
      ((proEtaleRingDerivedPullback d.g RY RZ cp).obj Q))) :=
  compactifiedProjectionPi d RY RZ RX cp cj a b E Q ≫
    (proEtaleRingDerivedDirectImage d.g RY RZ cp).map
      (compactifiedProjectionTheta d RY RZ RX cp cj b c E Q hα).hom

/-- The reverse ordered map Rp_* theta inverse followed by rho = pi inverse.
Source: Weil blueprint, lemma 1271
(blueprint: lemma-weil-pbc-projection-formula-compactified). -/
def compactifiedProjectionReverse
    (hα : IsIso (proEtaleOpenProjection d.i RZ RX cj b c E
      ((proEtaleRingDerivedPullback d.g RY RZ cp).obj Q)))
    (hπ : IsIso (compactifiedProjectionPi d RY RZ RX cp cj a b E Q)) :=
  (proEtaleRingDerivedDirectImage d.g RY RZ cp).map
      (compactifiedProjectionTheta d RY RZ RX cp cj b c E Q hα).inv ≫
    @inv _ _ _ _ (compactifiedProjectionPi d RY RZ RX cp cj a b E Q) hπ

/-- The compactified perfect projection formula with its exact ordered inverse.
The local strict-perfect normalization of rho is recorded below on canonical slice
operations. No uniform bound, completion, constructibility or boundedness of E occurs.
Source: Weil blueprint, proper base change, lemma 1271
(blueprint: lemma-weil-pbc-projection-formula-compactified).
Proof: (1) The exact open adjunction defines alpha for arbitrary coefficients by the
unit transpose. (2) Localize at each site object. The Hom adjunction chain, using the
counit-compatible direct-image restriction comparison, identifies restriction of j_!
with local extension and carries its unit to the local unit. Tensor and pullback
restriction comparisons therefore carry alpha to exactly the local transpose.
(3) Cover each object by strict-perfect representatives of Q. Signed totalization
proves that the local pi is inverse to the specified finite-total rho. Naturality
transports this pair along each representative isomorphism. Local detection of
isomorphisms proves global pi invertible; restriction of its inverse is the specified
local inverse by uniqueness. (4) Pull the cover back to the intermediate site. Exact
coefficient-identified pullback preserves finite-free splittings and boundedness on
each cover member. The open-piece theorem makes each local alpha invertible; local
detection makes global alpha invertible. (5) The canonical composition comparison is
invertible, so theta is invertible with inverse alpha followed by j_!(1 tensor c).
(6) Rp_* preserves the two inverse equations. Associativity cancels theta against its
inverse and pi against rho in both orders. The endpoints are Rp_*j_! by definition,
including for unbounded E and locally varying bounds. -/
theorem proEtaleProjectionFormula_compactified
    (hQ : IsProEtaleSitePerfect Y RY Q) :
    ∃ hα : IsIso (proEtaleOpenProjection d.i RZ RX cj b c E
        ((proEtaleRingDerivedPullback d.g RY RZ cp).obj Q)),
    ∃ hπ : IsIso (compactifiedProjectionPi d RY RZ RX cp cj a b E Q),
      IsIso (compactifiedProjectionForward d RY RZ RX cp cj a b c E Q hα) ∧
      compactifiedProjectionForward d RY RZ RX cp cj a b c E Q hα ≫
        compactifiedProjectionReverse d RY RZ RX cp cj a b c E Q hα hπ = 𝟙 _ ∧
      compactifiedProjectionReverse d RY RZ RX cp cj a b c E Q hα hπ ≫
        compactifiedProjectionForward d RY RZ RX cp cj a b c E Q hα = 𝟙 _ := sorry

end AlgebraicGeometry.Scheme
