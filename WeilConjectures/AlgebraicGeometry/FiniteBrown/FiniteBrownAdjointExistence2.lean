/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.AlgebraicGeometry.EtaleProEtaleExceptionalTransport
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedOpenCounitSiteTransport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift
public import WeilConjectures.Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import WeilConjectures.SixFunctors.Etale.Derived.Supports
public import Mathlib.Algebra.FiveLemma
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenCoverShriekTriangle
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
public import WeilConjectures.AlgebraicGeometry.Affine.AffineDualizingCoefficient
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Stalk
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
public import WeilConjectures.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization.OrdinaryAffineCounitTensorMaps
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryAffineCounitTensorNormalization
public import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceTopTrace

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteBrown

/-- Finite Brown restriction, local computation, normalized chart counits, overlaps,
signed Mayer--Vietoris descent, and representing-pair uniqueness.
Source: literature/blueprint/latest/blueprint/part-six-operations/sec-coefficients-constructible/
sec-n-brown/sk-thm-existence/sk-lem-sp-finite-existence/_section.md and its proof file
sk-lem-sp-finite-existence.proof.md; SGA 4 XVIII, 3.2.5; Stacks Tag 0GKK
(blueprint: sk-lem-sp-finite-existence).

Proof: (1) Restrict the Brown adjunction using compact-support and exceptional
finite-ctf preservation. (2) All chart opens are Noetherian; their etale maps to affine
space are separated finite type by the diagonal argument. (3) Compose exact etale
sum/evaluation with the ordered affine projection adjunction. Its counit is the sum
followed by integration; the ordinary affine tensor normalization identifies the
latter with inverse projection formula followed by tensor of the coefficient trace.
The affine top-trace theorem makes that trace invertible. Transport through the finite
site equivalence, retaining the specified compact-support and open counits. (4) Unique
counit-preserving right-adjoint comparisons identify overlaps and give their cocycle
law. (5) The degreewise signed open-cover short exact sequence gives the displayed
triangle; finite site and open-counit comparison retain its actual arrows. (6) Apply
finiteRingCounit_localRepresentability to the two-open cover, including its intersection
and all shifted tests. (7) The two representing Hom bijections give unique inverse maps
between a glued pair and the Brown pair, since their composites preserve the counits.
-/
theorem finiteBrownAdjointExistence
    (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (c : Compactification f)
    (d : ℕ) [SmoothOfRelativeDimension d f] (_hcd : BaseFieldFiniteCD ell k) :
    letI : Smooth f := SmoothOfRelativeDimension.smooth d f
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
    letI : IsNoetherian X := ⟨⟩
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
    letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
    letI : IsNoetherian Y := ⟨⟩
    Nonempty (ExistenceData ell n hn k f c d) := by
  classical
  letI : Smooth f := SmoothOfRelativeDimension.smooth d f
  letI : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  letI : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  letI : IsNoetherian X := ⟨⟩
  letI : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  letI : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  letI : IsNoetherian Y := ⟨⟩
  obtain ⟨B⟩ := finiteBrownAdjointExistence_brownCore ell n hn k f c _hcd
  obtain ⟨C⟩ := finiteBrownAdjointExistence_chartCore ell n hn k f c d _hcd B
  obtain ⟨LU⟩ := finiteBrownAdjointExistence_localUnique ell n hn k f c d _hcd B
  obtain ⟨MV⟩ := finiteBrownAdjointExistence_mayerVietoris ell n hn k f c d _hcd B
  obtain ⟨G⟩ := finiteBrownAdjointExistence_gluing ell n hn k f c d _hcd B C
  let E : ExistenceData ell n hn k f c d :=
    { brown := B
      support_preserves := C.support_preserves
      comparison_preserves := C.comparison_preserves
      comparison_equivalence := C.comparison_equivalence
      twistTransport := C.twistTransport
      lineData := C.lineData
      exponent_unit := C.exponent_unit
      integration_isIso := C.integration_isIso
      projection_normalization := C.projection_normalization
      chart := C.chart
      localRepresents := C.localRepresents
      openTerm_ctf := C.openTerm_ctf
      localUnique := LU.localUnique
      mayerVietoris := MV.mayerVietoris
      gluing := G.gluing }
  exact ⟨E⟩

end AlgebraicGeometry.ProEtale.FiniteBrown
