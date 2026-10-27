/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q139
-/
module

public import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.SpaceAffineHomComparison
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport
public import Sheaf.AlgebraicGeometry.AffineEtaleDerivedModuleRealization
public import Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence
import Sheaf.AlgebraicGeometry.AffineKoszulLowLocalization
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Supported Koszul tests and low open localization

Source: Stacks Project, spaces-perfect.tex, Tag 0GFI,
proposition-detecting-bounded-below, the distinguished-square Koszul paragraph;
Tags 08HK and 08GG; perfect.tex, Tag 0GEK
(blueprint: lem-sfb-space-supported-koszul-low-localization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The associated small étale Koszul object on the represented affine scheme.
The existing scalar pullback sheafifies the modules O(W) tensor_A M on charts;
on this affine it is exactly the associated étale module functor of
lem-sfb-affine-etale-derived-module-realization. Extension along embeddingDownNat
places K_q in cochain degree -q, with zero terms in positive degrees.
Source: Stacks, spaces-perfect.tex, Tag 0GFI; more-algebra.tex, Tag 0623
(blueprint: lem-sfb-space-supported-koszul-low-localization). -/
def spaceAffineEtaleKoszul {S : Scheme.{u}} (A : Type u) [CommRing A]
    (s : Spec (.of A) ⟶ S) (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w} (schemeSpace (Over.mk s)).SmallModules] :
    (schemeSpace (Over.mk s)).DerivedModules :=
  DerivedCategory.Q.obj
    (((affineScalarPullback A (Over.mk s) (Iso.refl _) (schemeSpace (Over.mk s))
      (𝟙 _)).mapHomologicalComplex (.up ℤ)).obj
        ((ExteriorAlgebra.koszulComplex A r f).extend ComplexShape.embeddingDownNat))

/-- In an elementary distinguished square with affine chart, principal-open generators
of the overlap exist. Every such Koszul list gives a perfect supported pushforward,
and eventual negative Hom vanishing forces the canonical open unit to be an
isomorphism after a sufficiently low standard truncation.

Source: Stacks, spaces-perfect.tex, Tag 0GFI,
proposition-detecting-bounded-below, distinguished-square paragraph; Tags 08HK and
08GG; perfect.tex, Tag 0GEK
(blueprint: lem-sfb-space-supported-koszul-low-localization).

Proof:
1. Absolute quasi-separatedness makes the overlap of U with the affine V quasi-compact
   (lem-sfb-qcqs-space-fibre-product and lem-weil-pbc-affine-scheme-qcqs).
   Refine by principal opens (lem-weil-pbc-spec-localization-away-basic-open) and take
   a finite subcover, permitting the empty list when the overlap is empty.
2. The actual Koszul representative is bounded in [-r,0] with finite free terms
   (def-weil-pbc-koszul-complex and lem-sfb-affine-etale-derived-module-realization).
   The contraction by f_k inverse times e_k makes it contractible on D(f_k).
3. Supported étale excision (lem-sfb-space-supported-etale-excision) identifies its
   restrictions with B on V and zero on U. Local strict-perfect models, using
   lem-sfb-ringed-site-strict-perfect-local-actual, prove Rp_*B perfect. Excision's
   Hom bijection transfers the negative vanishing to B against E restricted to V.
4. Use lem-sfb-derived-etale-zariski-equivalence and the affine realization to pass
   to Zariski D_QCoh. Choose b with all Hom groups zero in degrees at most b.
   lem-sfb-affine-koszul-low-localization makes the canonical local unit invertible
   after truncation at b-1. Its comparison respects the adjunction unit.
5. Set a=b-1. The unit restricts to this map on V and the identity on U by
   lem-sfb-space-derived-etale-chart-calculus. Exact restriction commutes with
   standard truncation (def-sbc-standard-tstructure-derived-category). Its cone's
   cohomology restricts to zero on the covering U together with V, hence is zero
   by sheaf descent. Thus the truncated canonical unit is an isomorphism.

The inverse image appearing below is the underlying open of T=U times_X V.
The reduced closed subspace is parametrized with its defining support equality;
its existence and uniqueness are lem-sfb-space-reduced-closed-support. -/
theorem space_supported_koszul_low_localization
    {S : Scheme.{u}} (X U : AlgebraicSpace S) (i : U ⟶ X)
    (hi : IsRepresentableWith (fun _ _ q ↦ IsOpenImmersion q.left) i.hom.hom)
    (hXqc : CompactSpace (Point X.obj.obj)) (hXqs : IsAbsolutelyQuasiSeparated X)
    (hUqc : CompactSpace (Point U.obj.obj))
    (A : Type u) [CommRing A] (s : Spec (.of A) ⟶ S)
    (p : schemeSpace (Over.mk s) ⟶ X) (hp : IsEtale p.hom.hom)
    (Z : ClosedSubspace X) (hZred : IsReduced (Z.val : AlgebraicSpace S))
    (hZ : pointImage Z.val.arrow.hom.hom = (pointImage i.hom.hom)ᶜ)
    (hZp : IsIso (pullback.snd p.hom Z.val.arrow.hom))
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} U.SmallModules]
    [HasDerivedCategory.{w} (schemeSpace (Over.mk s)).SmallModules] :
    (∃ (r : ℕ) (f : Fin r → A),
      schemePointMap p.hom.hom ⁻¹' pointImage i.hom.hom =
        ⋃ k : Fin r, (PrimeSpectrum.basicOpen (f k) : Set (PrimeSpectrum A))) ∧
    ∀ (r : ℕ) (f : Fin r → A),
      schemePointMap p.hom.hom ⁻¹' pointImage i.hom.hom =
        ⋃ k : Fin r, (PrimeSpectrum.basicOpen (f k) : Set (PrimeSpectrum A)) →
      SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
        X.smallStructureSheaf ((derivedDirectImage p).obj (spaceAffineEtaleKoszul A s r f)) ∧
      ∀ E : X.DerivedModules, X.derivedQCohProperty E →
        (∃ b : ℤ, ∀ j : ℤ, j ≤ b →
          Subsingleton (((derivedDirectImage p).obj (spaceAffineEtaleKoszul A s r f)) ⟶
            (E⟦j⟧))) →
        ∃ a : ℤ, IsIso ((DerivedCategory.TStructure.t.truncLE a).map
          ((spaceDerivedAdjunction i).unit.app E)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
