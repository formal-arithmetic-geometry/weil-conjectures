/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import WeilConjectures.AlgebraicGeometry.ProperCurveModuli
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePointClasses
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePointTopology
public import WeilConjectures.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Connected.Basic
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists
import WeilConjectures.AlgebraicGeometry.FieldExtensionFpqcCover
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFlatLfpUniversallyOpen
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity

/-! # Properness from connected proper geometric fibres

Source: Deligne, Le lemme de Gabber, Section 1.1, printed pp. 131--132;
EGA IV-3, Corollaire 15.7.10 and Proposition 15.7.9, printed pp. 245--247;
Stacks Project, Tags 0CWI and 042S
(blueprint: lem-sfb-connected-proper-fibres-proper).

The source is an algebraic space, and fibres are sheaf fibre products. Finite presentation
is written as quasi-compactness, quasi-compact diagonal and chartwise local finite presentation.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The actual Yoneda map of a field-valued point to the base, regarded as a map of spaces.
Source: Stacks Project, Tag 025Y, representable sheaves and their morphisms
(blueprint: lem-sfb-connected-proper-fibres-proper). -/
def geometricPointSpaceMap {S : Scheme.{u}} {Ω : Type u} [Field Ω]
    (barS : Spec (.of Ω) ⟶ S) :
    schemeSpace (Over.mk barS) ⟶ schemeSpace (Over.mk (𝟙 S)) :=
  ObjectProperty.homMk ((Scheme.fppfTopology.over S).yoneda.map (Over.homMk barS))

/-- A separated flat finitely presented algebraic space over a locally Noetherian scheme
is proper if all its geometric fibres are nonempty, connected and proper.
Source: Deligne, Le lemme de Gabber, Section 1.1, final paragraph, printed pp. 131--132;
EGA IV-3, Corollaire 15.7.10 with Proposition 15.7.9, printed pp. 245--247;
Stacks Project, Tags 0CWI and 042S
(blueprint: lem-sfb-connected-proper-fibres-proper).

Proof:
1. By [lem-sfb-space-proper-strict-local-test], test after each strict localization
   T = Spec A of S. The ring A is strictly henselian local by
   [lem-weil-pbc-strict-henselization-functoriality]. Base-change permanence
   [lem-sfb-space-flat-proper-fp-locality] preserves flatness and finite presentation;
   the closed diagonal also pulls back. Fibre-product associativity
   [lem-trf-space-fibre-products-etale-covers] identifies geometric fibres with those
   of the original family, so they remain nonempty, connected and proper.
2. For k the residue field of A, choose an algebraic closure Ω of k. The field spectrum
   map is fpqc by [lem-pc-field-extension-fpqc-cover]. Properness of the geometric
   closed fibre descends to the entire closed fibre X_k by
   [lem-sfb-space-proper-fpqc-descent]. This fibre is nonempty as well.
3. The pair (A, maximalIdeal A) is henselian by [def-weil-pbc-henselian-terminology].
   The family is separated and of finite type. Apply
   [lem-sfb-space-henselian-proper-clopen-lift] to the whole proper closed fibre:
   it lifts to a clopen W in X, proper over T, with closed fibre X_k.
4. By [lem-sfb-flat-lfp-space-universally-open], the image of W is open in T and
   contains its closed point, hence is all of the local spectrum. Every geometric
   fibre of W is nonempty: a point in W over the image of the geometric point acquires
   a common field extension with that point. This uses the field-valued point convention
   [def-trf-algebraic-space-jointly-surjective-family] and the fibre-product universal
   property [lem-trf-space-fibre-products-etale-covers]. Being nonempty and clopen in
   a connected geometric fibre of X, it is that entire fibre.
5. A point of X outside W would, after algebraic closure of its representative field,
   give a point outside W in a geometric fibre, contradicting step 4. Thus W = X,
   including the restricted structure sheaf, so X is proper over T. The strict-local
   test gives properness over S. For empty S there are no geometric points and the
   same test gives the assertion directly. -/
theorem proper_of_flat_of_connected_proper_geometricFibres
    {S : Scheme.{u}} [IsLocallyNoetherian S] (Y : AlgebraicSpace S)
    (h : Y ⟶ schemeSpace (Over.mk (𝟙 S)))
    (hsep : MapIsSeparated h) (hflat : MapIsFlat h)
    (hqc : MapIsQuasiCompact h.hom.hom)
    (hqs : MapIsQuasiCompact (pullback.diagonal h.hom.hom))
    (hlfp : MapIsLocallyOfFinitePresentation h)
    (hfibres : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (barS : Spec (.of Ω) ⟶ S),
      ConnectedSpace (Point (enlargedFibreProduct (geometricPointSpaceMap barS) h).obj.obj) ∧
        MapIsProper (enlargedFibreProductFst (geometricPointSpaceMap barS) h)) :
    MapIsProper h := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
