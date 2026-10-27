module

public import Sheaf.AlgebraicGeometry.SpaceRelativeDerivedProjection
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport
public import Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
import Sheaf.AlgebraicGeometry.ElementaryEtaleShriekExact
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.RingedProjectionTensorComposition

/-! # Proper-support derived projection formula without quasi-compactness

Source: Stacks Project, spaces-perfect.tex, Tag 08IS, support reduction and the two
successive tensor identifications; Tag 08IN; sites-cohomology.tex, Tag 08I6
(blueprint: lem-sfb-space-proper-support-derived-projection-formula).

The assertion is invertibility of the actual bifunctorial projection comparison,
followed by the balanced scalar-restriction identification. Its right side retains
the structure-module action through E. Neither f nor the tensor object is required
to be quasi-compact or bounded, respectively.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

attribute [local irreducible] derivedDualityModel derivedTensorPullback
  spaceRelativeDerivedTensor spaceRelativeProjectionComparison

/-- The canonical proper-support derived projection comparison is invertible.
Coherence is the existing finite-presentation predicate on the original étale module
sheaf, equivalent on locally Noetherian charts to quasi-coherent finite generation.
Support is the existing nonzero-geometric-stalk locus, with its reduced closed structure.
Source: Stacks, spaces-perfect.tex, Tags 08IS and 08IN; sites-cohomology.tex, Tag 08I6
(blueprint: lem-sfb-space-proper-support-derived-projection-formula).

Proof plan:
1. Choose a finite cohomology interval. By lem-sfb-space-proper-support-closed-operations
its finite union T of supports is proper over Y and hence quasi-compact. Affine charts
have quasi-compact open images (lem-a1-space-etale-open-image); finitely many cover T.
Their union U is a quasi-compact open containing T, empty if T is empty. The hypotheses
make X quasi-separated (lem-sfb-space-qcqs-source-products). Its open U is also so, and
lem-sfb-space-qcqs-permanence makes g:U → Y quasi-compact and quasi-separated.
2. E vanishes on W=X\T, detected by geometric stalks
(lem-sfb-space-etale-conservative-geometric-points). The exact open-cover sequence
lem-sfb-space-elementary-shriek-exact gives j_!(E|U) ≅ E. Supported excision
lem-sfb-space-supported-etale-excision identifies this with Rj_*(E|U). Its transpose
is the identity, so the resulting E → Rj_*(E|U) is the unit. Composition in
lem-sfb-space-derived-etale-chart-calculus gives Rf_*E ≅ Rg_*(E|U).
3. Put K=F[0] and M=E tensor Lf*K. Exact restriction and tensor pullback
(lem-weil-pbc-ringed-topoi-derived-tensor-pullback and
lem-sfb-space-derived-etale-chart-calculus) make M vanish on W as well. The same
support argument identifies Rf_*M with Rg_*((E|U) tensor Lg*K), without boundedness of M.
4. Coherent cohomology is quasi-coherent; restriction preserves it. Apply
lem-sfb-space-qcqs-derived-projection-formula to g and K. Together with steps 2 and 3
this gives an invertible comparison with the required ordinary projection endpoints.
5. Identify that map with the canonical projection mate for f: use naturality along
the unit E → Rj_*j*E and the composition identity of
lem-sfb-ringed-projection-tensor-composition. Transposing the remaining identity
under j* ⊣ Rj_* gives the tensor comparison itself on both sides, by naturality and
the triangular identity. Thus the chosen U disappears from the resulting canonical map.
6. Finally apply lem-sfb-ringed-topos-relative-tensor-pullback (08I6), the balanced
identification e tensor (a tensor g) ↦ ae tensor g, with the first-factor action.
This is spaceRelativeTensorComparison. Its image under Rf_* is invertible, so its
composite with the projection mate is the displayed relative projection isomorphism.
Bifunctoriality is spaceRelativeProjectionComparison_naturality. No relative Tor,
flatness or quasi-compactness hypothesis on f enters any step. -/
theorem spaceProperSupportDerivedProjectionFormula
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    (hYln : ∀ T : Y.EtaleSite, IsLocallyNoetherian (Y.etaleForget.obj T))
    (hYqc : CompactSpace (Point Y.obj.obj)) (hYqs : IsAbsolutelyQuasiSeparated Y)
    (hflft : MapIsLocally (@LocallyOfFiniteType) f)
    (hfqs : MapIsQuasiCompact (Limits.pullback.diagonal f.hom.hom))
    (E : X.DerivedModules)
    (hEcoh : ∀ n : ℤ, SheafOfModules.IsFinitePresentation
      (X.smallModuleEquivalence.inverse.obj
        ((DerivedCategory.homologyFunctor X.SmallModules n).obj E)))
    (hEb : ∃ a b : ℤ, a ≤ b ∧ ∀ n : ℤ, n < a ∨ b < n →
      IsZero ((DerivedCategory.homologyFunctor X.SmallModules n).obj E))
    (hEsupp : ∀ n : ℤ, ∃ C : ClosedSubspace X,
      IsReduced (C.val : AlgebraicSpace S) ∧
      pointImage C.val.arrow.hom.hom = moduleSupport
        (X.smallModuleEquivalence.inverse.obj
          ((DerivedCategory.homologyFunctor X.SmallModules n).obj E)) ∧
      MapIsProper (C.val.arrow ≫ f))
    (F : Y.QCoh) :
    IsIso (spaceRelativeProjectionComparison f E
      ((DerivedCategory.singleFunctor Y.SmallModules 0).obj
        (Y.smallModuleRestriction.obj F.obj))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
