module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace
public import Sheaf.AlgebraicGeometry.ReducedAlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.SpaceAffineHomComparison
public import Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AffineEtaleDerivedModuleRealization
public import Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence
import Sheaf.AlgebraicGeometry.AffineKoszulUpperLocalization
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Supported Koszul tests and high open localization

Source: Stacks Project, spaces-perfect.tex, Tag 0GFH, distinguished-square proof;
Tags 08HK and 08GG; perfect.tex, Tag 0GEJ
(blueprint: lem-sfb-space-supported-koszul-high-localization).

The affine associated complex is constructed termwise using the canonical scalar
pullback. The overlap is specified on ordinary points of Spec A by its inverse image
under the chart map. The conclusion concerns the canonical adjunction unit itself.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The associated étale Koszul object on the represented affine scheme. Extending the
chain complex along `embeddingDownNat` places K_n in cohomological degree -n; the
canonical scalar pullback sheafifies O(W) tensor_A K_n on affine étale charts W.
This is the associated module realization, expressed on the equivalent small model.
Source: Stacks Project, spaces-perfect.tex, Tag 0GFH, construction of K;
Tags 0622 and 071Q (blueprint: lem-sfb-space-supported-koszul-high-localization). -/
def affineSpaceKoszul {S : Scheme.{u}} (A : Type u) [CommRing A]
    (v : Spec (.of A) ⟶ S)
    [HasDerivedCategory.{w} (schemeSpace (Over.mk v)).SmallModules]
    (r : ℕ) (f : Fin r → A) : (schemeSpace (Over.mk v)).DerivedModules :=
  DerivedCategory.Q.obj
    (((affineScalarPullback A (Over.mk v) (Iso.refl _) (schemeSpace (Over.mk v))
      (𝟙 _)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((ExteriorAlgebra.koszulComplex A r f).extend ComplexShape.embeddingDownNat))

/-- A distinguished square has a finite principal-open overlap. For every such list,
the pushforward of its associated Koszul object is perfect and detects the upper
truncation of the canonical open-localization unit by eventual shifted Hom vanishing.
The open inclusion is identified with an existing open subfunctor; the closed subspace
is its reduced complement. Its actual base-change projection is required to be invertible.
Source: Stacks Project, spaces-perfect.tex, Tag 0GFH, supported Koszul and high-truncation
paragraphs; Tags 08HK and 08GG; perfect.tex, Tag 0GEJ
(blueprint: lem-sfb-space-supported-koszul-high-localization).

Proof:
1. The absolute diagonal of U is a base change of that of X, so U is quasi-separated.
The affine V is qcqs (lem-weil-pbc-affine-scheme-qcqs). Thus U times_X V is quasi-compact
by lem-sfb-qcqs-space-fibre-product. Refine by principal opens and take a finite subcover
using lem-weil-pbc-spec-localization-away-basic-open. The empty overlap permits r = 0.
2. Fix any such list. The exterior-power bases in def-weil-pbc-koszul-complex make its
associated complex bounded finite free, using lem-sfb-affine-etale-derived-module-realization.
On D(f_k), wedge with f_k inverse times e_k contracts it, since d(e_k wedge x) equals
f_k x minus e_k wedge d(x). Thus B restricts to zero on the overlap. For r = 0,
B is the structure module in degree zero and the restriction assertion is vacuous.
3. Apply lem-sfb-space-supported-etale-excision: p* Rp* B is B, i* Rp* B is zero,
and Hom(Rp* B,E[j]) is Hom(B,p*E[j]). The cover U together with V is jointly surjective
étale. The bounded finite free model on V and the zero model on U prove perfection
of Rp* B using def-weil-pbc-strict-perfect-coefficient-package and
lem-sfb-ringed-site-strict-perfect-local-actual to realize local derived maps by chain maps.
4. Étale chart calculus preserves quasi-coherent cohomology. Transfer Hom vanishing to V.
The exact derived étale/Zariski equivalence (lem-sfb-derived-etale-zariski-equivalence)
sends B to the Zariski associated Koszul object. Apply lem-sfb-affine-koszul-upper-localization
there, using Hom(B,E[n]) = Hom(B[-n],E). Exact topology comparison commutes with truncation.
Its direct-image comparison applies to the quasi-compact separated open overlap and
identifies the units by their identity transposes. This gives the truncated unit on V.
5. The unit-compatible étale base change of lem-sfb-space-derived-etale-chart-calculus
identifies the restriction of the stated unit to V with the preceding unit, and its
restriction to U with the identity. Exact restriction commutes with standard truncation
(def-sbc-standard-tstructure-derived-category). The cone has zero cohomology on this
cover, hence everywhere by the sheaf axiom. It is acyclic, so localization at
quasi-isomorphisms (def-weil-abstract-derived-category) makes the displayed map invertible. -/
theorem space_supported_koszul_high_localization {S : Scheme.{u}}
    (X U : AlgebraicSpace S) (i : U ⟶ X)
    (hXqc : CompactSpace (Point X.obj.obj)) (hXqs : IsAbsolutelyQuasiSeparated X)
    (hUqc : CompactSpace (Point U.obj.obj))
    (hi : ∃ O : OpenSubspace X, ∃ e : U.obj.obj ≅ O.val.toFunctor,
      e.hom ≫ O.val.ι = i.hom.hom)
    (A : Type u) [CommRing A] (v : Spec (.of A) ⟶ S)
    (p : schemeSpace (Over.mk v) ⟶ X) (hp : IsEtale p.hom.hom)
    (Z : ClosedSubspace X) (hZred : IsReduced (Z.val : AlgebraicSpace S))
    (hZsupport : pointImage Z.val.arrow.hom.hom = (pointImage i.hom.hom)ᶜ)
    (hdist : IsIso (Limits.pullback.snd p.hom Z.val.arrow.hom))
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} U.SmallModules]
    [HasDerivedCategory.{w} (schemeSpace (Over.mk v)).SmallModules] :
    (∃ (r : ℕ) (f : Fin r → A),
      schemePointMap p.hom.hom ⁻¹' pointImage i.hom.hom =
        ⋃ k : Fin r, (PrimeSpectrum.basicOpen (f k) : Set (PrimeSpectrum A))) ∧
    ∀ (r : ℕ) (f : Fin r → A),
      schemePointMap p.hom.hom ⁻¹' pointImage i.hom.hom =
        (⋃ k : Fin r, (PrimeSpectrum.basicOpen (f k) : Set (PrimeSpectrum A))) →
      SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u}
        X.smallStructureSheaf ((derivedDirectImage p).obj (affineSpaceKoszul A v r f)) ∧
      ∀ E : X.DerivedQCoh,
        (∃ N : ℤ, ∀ j : ℤ, N ≤ j →
          Subsingleton ((derivedDirectImage p).obj (affineSpaceKoszul A v r f) ⟶ E.obj⟦j⟧)) →
        ∃ a : ℤ, IsIso ((DerivedCategory.TStructure.t.truncGE a).map
          ((spaceDerivedAdjunction i).unit.app E.obj)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
