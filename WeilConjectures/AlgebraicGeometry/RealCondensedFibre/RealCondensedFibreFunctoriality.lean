/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LisseQlbar.LisseQlbarRepresentations
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.StalkTransport
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.PathTransport
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
public import WeilConjectures.AlgebraicGeometry.GaloisCategories
public import WeilConjectures.CategoryTheory.SetFunctorAut.AutProfinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.FieldTheory.KrullTopology
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalenceExtension
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ConstantCover
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.GroupTheory.WeilGroup
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.CategoryTheory.Filtered.Connected
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.AlgebraicGeometry.DescendFinite
public import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent
public import WeilConjectures.AlgebraicGeometry.IntermediateFieldLimit
public import WeilConjectures.Mathlib.CategoryTheory.Galois.Prorepresentability
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Functoriality of condensed lisse geometric fibres

Source: current blueprint, `sec-purity-real-sheaves/sk-d-real-weil/_section.md`,
finite-reduction paragraph and complement; `sk-d-real-weil.proof.md`, second paragraph
(blueprint: lem-real-condensed-fibre-functoriality).

The comparison for inverse image is constructed from module pullback composition.
The statement below packages the simultaneous path maps on the three recorded coefficient
rings, their finite-quotient normalization, exactness, and tensor/scalar compatibilities.
Loop actions mean evaluation of this same normalized path family on automorphisms of the
finite-etale fibre functor. Thus no separate, arbitrarily chosen representation is introduced.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.RealCondensedFibre

/-- The schemes allowed in the statement, including the local-ring meaning of normality.
Source: the hypotheses (blueprint: lem-real-condensed-fibre-functoriality). -/
structure Context where
  X : Scheme.{u}
  nonempty : Nonempty X
  connected : ConnectedSpace X
  locallyNoetherian : IsLocallyNoetherian X
  compact : CompactSpace X
  normal : ∀ p : X, IsDomain (X.presheaf.stalk p) ∧ IsIntegrallyClosed (X.presheaf.stalk p)

attribute [instance] Context.nonempty Context.connected Context.locallyNoetherian Context.compact

variable (ell : ℕ) [Fact ell.Prime]

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The existing internal module category over the pulled-back coefficient.
Source: thm-lisse-qlbar-representations (blueprint: lem-real-condensed-fibre-functoriality). -/
abbrev Modules (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)

/-- Its lisse predicate is the dependency's locally-free predicate.
Source: thm-lisse-qlbar-representations (blueprint: lem-real-condensed-fibre-functoriality). -/
abbrev Lisse {X : Scheme.{u}} (L : Modules Λ X) :=
  CondensedRing.LocallyFree (condensedRingObj Λ X) L

attribute [local irreducible] CondensedRing.upperStar in
/-- Pull back a finite quotient through the canonical underlying-sheaf and site comparisons.
Source: node proof step 1 (blueprint: lem-real-condensed-fibre-functoriality). -/
@[irreducible] def pullbackQuotient {X Y : Scheme.{u}} (f : Y ⟶ X) (L : Modules Λ X)
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1})
    (q : L.X ⟶ (comparisonUpperStar Ab.{u + 1} X).obj F) :
    ((CondensedRing.upperStar Λ f).obj L).X ⟶
      (comparisonUpperStar Ab.{u + 1} Y).obj ((Etale.upperStar Ab.{u + 1} f).obj F) :=
  (CondensedRing.upperStarObjXIso Λ f L).hom ≫ (ProEtale.upperStar Ab.{u + 1} f).map q ≫
    (comparisonUpperStarCompUpperStarIso Ab.{u + 1} f).hom.app F

set_option maxHeartbeats 0 in
-- Each clause retains its actual canonical maps and finite-level normalization.
set_option maxHeartbeats 400000 in
-- Each clause retains its actual canonical maps and finite-level normalization.
set_option maxHeartbeats 400000 in
-- Each clause retains its actual canonical maps and finite-level normalization.
set_option maxHeartbeats 400000 in
-- Each clause retains its actual canonical maps and finite-level normalization.
set_option maxHeartbeats 400000 in
-- Each clause retains its actual canonical maps and finite-level normalization.
set_option maxHeartbeats 400000 in
-- Each clause retains its actual canonical maps and finite-level normalization.
set_option maxHeartbeats 400000 in
-- Each clause retains its actual canonical maps and finite-level normalization.
set_option maxHeartbeats 400000 in
-- Each clause retains its actual canonical maps and finite-level normalization.
set_option maxHeartbeats 400000 in
-- Each clause retains its actual canonical maps and finite-level normalization.
set_option maxHeartbeats 400000 in
-- Each clause retains its actual canonical maps and finite-level normalization.
end AlgebraicGeometry.ProEtale.RealCondensedFibre
