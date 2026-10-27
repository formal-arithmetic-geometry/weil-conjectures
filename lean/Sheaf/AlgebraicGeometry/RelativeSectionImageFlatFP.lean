module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.AlgebraicGeometry.SchemeAmpleCanonicalProjCriterion
public import Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
public import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
import WeilConjectures.AlgebraicGeometry.AffinePseudoCoherentCriterion
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import WeilConjectures.AlgebraicGeometry.LerayDegenerateSections
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Semicontinuity
import WeilConjectures.AlgebraicGeometry.PerfectPseudoCoherentLocallyFiniteTor
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectBaseChange
import WeilConjectures.AlgebraicGeometry.InvertSCOhomology
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.LerayNatural
import Sheaf.AlgebraicGeometry.MixedGlobalSectionsDirectImageIso
import Sheaf.AlgebraicGeometry.ProjInvertibleMapTwistIso
import Sheaf.TraceFormula.ProjectiveBundleProper
import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
import Sheaf.TraceFormula.SpaceLineModuleProjMap
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.Algebra.Category.ModuleCat.FilteredColimitFlat
import Mathlib.RingTheory.FiniteStability
import WeilConjectures.AlgebraicGeometry.FinitePresentationKernelSurjectionFiniteType
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Flat finitely presented images of relative section algebras

Source: Stacks Project, Tags 068A, 0B6G, 0A1H, 0B91, 01O4 and 01O9;
Knudsen II, Section 2, Proposition 2.1, relative-image spreading consequence
(blueprint: lem-sfb-relative-section-image-flat-fp).

The section algebra and its chart-normalized evaluation use the existing interfaces.
The auxiliary predicates only unpack this statement's canonical maps and compatibilities.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The degree-one direct image, retaining the zeroth tensor factor in M^1.
Source: Stacks 01O4 (blueprint: lem-sfb-relative-section-image-flat-fp). -/
abbrev relativeImageDegreeOne {Y S : Scheme.{u}} (f : Y ⟶ S) (M : Y.Modules) : S.Modules :=
  (pushforward f).obj (M.tensorPow 1)

/-- Evaluation is the counit of the section-normalized tensor adjunction.
Source: Stacks 01O9 (blueprint: lem-sfb-relative-section-image-flat-fp). -/
def relativeImageEvaluation {Y S : Scheme.{u}} (f : Y ⟶ S) (M : Y.Modules) :
    (tensorPullback f).obj (relativeImageDegreeOne f M) ⟶ M.tensorPow 1 :=
  (tensorPullbackSectionAdjunction f).counit.app (M.tensorPow 1)

/-- The canonical symmetric algebra of A_1. Finite local freeness supplies quasi-coherence.
Source: Stacks 01OB (blueprint: lem-sfb-relative-section-image-flat-fp). -/
def relativeImageSymmetric {Y S : Scheme.{u}} (f : Y ⟶ S) (M : Y.Modules)
    [(relativeImageDegreeOne f M).IsFiniteLocallyFree] : S.GradedAlgebraData :=
  SymmetricAlgebraSheaf.gradedAlgebraData (relativeImageDegreeOne f M)

/-- The symmetric quotient is fixed on each degree-one generator by its actual section.
Since it is a graded O_S-algebra map, this fixes all section-multiplication maps.
Source: Stacks 01O4 (blueprint: lem-sfb-relative-section-image-flat-fp). -/
def RelativeImageIsSectionQuotient {Y S : Scheme.{u}} {f : Y ⟶ S} {M : Y.Modules}
    [(relativeImageDegreeOne f M).IsFiniteLocallyFree] (A : RelativeSectionAlgebra f M)
    (phi : relativeImageSymmetric f M ⟶ A.data) : Prop :=
  ∀ (V : S.affineOpens) (s : Γ(M.tensorPow 1, f ⁻¹ᵁ V.1)),
    phi.app V (SymmetricAlgebra.ι Γ(S, V.1)
      ((relativeImageDegreeOne f M).val.obj (op V.1)) s) =
        ((A.sectionEquiv V 1).symm s).val

/-- Base change of a morphism over S, with its actual two pullback projections.
Source: Stacks 01JX (blueprint: lem-sfb-relative-section-image-flat-fp). -/
def relativeImageFibreMap {Y X S T : Scheme.{u}} (f : Y ⟶ S) (p : X ⟶ S)
    (q : Y ⟶ X) (w : q ≫ p = f) (g : T ⟶ S) :
    Limits.pullback (C := Scheme.{u}) f g ⟶ Limits.pullback (C := Scheme.{u}) p g :=
  pullback.map f g p g q (𝟙 T) (𝟙 S)
    (by simpa only [Category.comp_id] using w.symm) (by simp)

/-- Actual section pullback and the tensor-power comparison on an affine base-change chart.
Source: Stacks 0A1H, 01O9 (blueprint: lem-sfb-relative-section-image-flat-fp). -/
def relativeImagePullbackSection {Y S T : Scheme.{u}} (f : Y ⟶ S) (g : T ⟶ S)
    (M : Y.Modules) (V : S.affineOpens) (W : T.affineOpens)
    (h : W.1 ≤ g ⁻¹ᵁ V.1) (n : ℕ) (s : Γ(M.tensorPow n, f ⁻¹ᵁ V.1)) :
    Γ(((tensorPullback (pullback.fst f g)).obj M).tensorPow n,
      pullback.snd f g ⁻¹ᵁ W.1) :=
  (((tensorPullback (pullback.fst f g)).obj M).tensorPow n).presheaf.map
    (homOfLE (by
      intro x hx
      change f (pullback.fst f g x) ∈ V.1
      rw [← Scheme.Hom.comp_apply, pullback.condition]
      exact h hx)).op
    ((boundaryPullbackPowIso (pullback.fst f g) M n).hom.app
      (pullback.fst f g ⁻¹ᵁ (f ⁻¹ᵁ V.1))
      (tensorPullbackSection (pullback.fst f g) (M.tensorPow n) (f ⁻¹ᵁ V.1) s))

/-- The canonical graded coefficient comparison, in every degree including zero.
Source: Stacks 0A1H, 01O9 (blueprint: lem-sfb-relative-section-image-flat-fp). -/
def RelativeImageBaseChangeSections {Y S T : Scheme.{u}} (f : Y ⟶ S) (g : T ⟶ S)
    (M : Y.Modules) (A : RelativeSectionAlgebra f M)
    (B : RelativeSectionAlgebra (pullback.snd f g)
      ((tensorPullback (pullback.fst f g)).obj M))
    (b : Scheme.GradedAlgebraData.PullbackData g A.data B.data) : Prop :=
  ∀ (V : S.affineOpens) (W : T.affineOpens) (h : W.1 ≤ g ⁻¹ᵁ V.1)
    (n : ℕ) (s : A.data.grading V n),
    B.sectionEquiv W n ⟨b.map h s, (b.map h).map_mem s.property⟩ =
      relativeImagePullbackSection f g M V W h n (A.sectionEquiv V n s)

/-- The affine chart meaning of h_*O_Y = O_image(h), canonically. The image is Mathlib's
kernel-defined closed subscheme. Bijectivity on every image open is exactly the
structure-sheaf isomorphism; pushing along its closed immersion gives the stated equality
of modules on the projective space.
Source: Stacks 01R8, Knudsen II 2.1
(blueprint: lem-sfb-relative-section-image-flat-fp). -/
def RelativeImageStructureComparison {Y P : Scheme.{u}} (h : Y ⟶ P) : Prop :=
  ∀ U : h.image.Opens, Function.Bijective (h.toImage.app U)

/-- The desired image geometry for a fixed canonical symmetric quotient and evaluation.
The relative degree-one twist is the restriction of the normalized projective-bundle
O(1); its pullback by q is M. The classification equation fixes this comparison on
all evaluated generators, so it also fixes its pullbacks.
Source: Stacks 01O4, 01O9 and Knudsen II 2.1
(blueprint: lem-sfb-relative-section-image-flat-fp). -/
def RelativeImageGeometry {Y S : Scheme.{u}} (f : Y ⟶ S) (M : Y.Modules)
    [(relativeImageDegreeOne f M).IsFiniteLocallyFree] (A : RelativeSectionAlgebra f M)
    (phi : relativeImageSymmetric f M ⟶ A.data)
    (hsurj : ∀ V : S.affineOpens, Function.Surjective (phi.app V))
    (h : Y ⟶ (relativeImageSymmetric f M).relProj) (q : Y ⟶ A.data.relProj) : Prop :=
  Flat A.data.relProjHom ∧ LocallyOfFinitePresentation A.data.relProjHom ∧
    QuasiCompact A.data.relProjHom ∧ QuasiSeparated A.data.relProjHom ∧
    IsClosedImmersion (Scheme.GradedAlgebraData.relProjMap phi
      (Scheme.GradedAlgebraData.irrelevantLE_of_surjective phi hsurj)) ∧
    A.IsCanonicalMap q ∧ IsProper q ∧ Surjective q ∧
    q ≫ Scheme.GradedAlgebraData.relProjMap phi
      (Scheme.GradedAlgebraData.irrelevantLE_of_surjective phi hsurj) = h ∧
    ∃ D : ProjectiveBundleQuotientGeometry.TautologicalQuotient (relativeImageDegreeOne f M),
      ProjectiveBundleQuotientGeometry.Classifies D f (M.tensorPow 1)
        (relativeImageEvaluation f M) h ∧
      Nonempty ((tensorPullback q).obj
        ((tensorPullback (Scheme.GradedAlgebraData.relProjMap phi
          (Scheme.GradedAlgebraData.irrelevantLE_of_surjective phi hsurj))).obj D.line) ≅ M)

/-- The geometric-fibre comparison as a closed subscheme, including the factor map.
Source: Knudsen II 2.1, Stacks 01O4, 01R8
(blueprint: lem-sfb-relative-section-image-flat-fp). -/
def RelativeImageGeometricFibres {Y S : Scheme.{u}} (f : Y ⟶ S) (M : Y.Modules)
    [(relativeImageDegreeOne f M).IsFiniteLocallyFree] (A : RelativeSectionAlgebra f M)
    (phi : relativeImageSymmetric f M ⟶ A.data)
    (hsurj : ∀ V : S.affineOpens, Function.Surjective (phi.app V))
    (h : Y ⟶ (relativeImageSymmetric f M).relProj)
    (wh : h ≫ (relativeImageSymmetric f M).relProjHom = f)
    (q : Y ⟶ A.data.relProj) (wq : q ≫ A.data.relProjHom = f) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S),
    ∃ e : Limits.pullback (C := Scheme.{u}) A.data.relProjHom t ≅
        (relativeImageFibreMap f (relativeImageSymmetric f M).relProjHom h wh t).image,
      e.hom ≫ (relativeImageFibreMap f
        (relativeImageSymmetric f M).relProjHom h wh t).imageι =
        relativeImageFibreMap A.data.relProjHom (relativeImageSymmetric f M).relProjHom
          (Scheme.GradedAlgebraData.relProjMap phi
            (Scheme.GradedAlgebraData.irrelevantLE_of_surjective phi hsurj))
          (Scheme.GradedAlgebraData.relProjMap_relProjHom phi
            (Scheme.GradedAlgebraData.irrelevantLE_of_surjective phi hsurj)) t ∧
      relativeImageFibreMap f A.data.relProjHom q wq t ≫ e.hom =
        (relativeImageFibreMap f (relativeImageSymmetric f M).relProjHom h wh t).toImage

/-- Naturality under arbitrary base change. The algebra comparison is fixed on actual
sections, the symmetric comparison commutes with the quotient, and the evaluation square
commutes. All image and twist comparisons are the normalized ones in RelativeImageGeometry.
Source: Stacks 0A1H, 01O4, 01O9
(blueprint: lem-sfb-relative-section-image-flat-fp). -/
def RelativeImageArbitraryBaseChange {Y S : Scheme.{u}} (f : Y ⟶ S) (M : Y.Modules)
    [(relativeImageDegreeOne f M).IsFiniteLocallyFree] (A : RelativeSectionAlgebra f M)
    (phi : relativeImageSymmetric f M ⟶ A.data)
    (hsurj : ∀ V : S.affineOpens, Function.Surjective (phi.app V))
    (h : Y ⟶ (relativeImageSymmetric f M).relProj) (q : Y ⟶ A.data.relProj) : Prop :=
  ∀ (T : Scheme.{u}) (g : T ⟶ S),
    ∃ (hfinite : (relativeImageDegreeOne (pullback.snd f g)
        ((tensorPullback (pullback.fst f g)).obj M)).IsFiniteLocallyFree)
      (B : RelativeSectionAlgebra (pullback.snd f g)
        ((tensorPullback (pullback.fst f g)).obj M))
      (b : Scheme.GradedAlgebraData.PullbackData g A.data B.data)
      (psi : @relativeImageSymmetric _ _ (pullback.snd f g)
          ((tensorPullback (pullback.fst f g)).obj M) hfinite ⟶ B.data)
      (hpsi : ∀ V, Function.Surjective (psi.app V))
      (c : Scheme.GradedAlgebraData.PullbackData g (relativeImageSymmetric f M)
        (@relativeImageSymmetric _ _ (pullback.snd f g)
          ((tensorPullback (pullback.fst f g)).obj M) hfinite))
      (h' : Limits.pullback (C := Scheme.{u}) f g ⟶ (@relativeImageSymmetric _ _ (pullback.snd f g)
        ((tensorPullback (pullback.fst f g)).obj M) hfinite).relProj)
      (q' : Limits.pullback (C := Scheme.{u}) f g ⟶ B.data.relProj),
      @RelativeImageIsSectionQuotient _ _ _ _ hfinite B psi ∧
      RelativeImageBaseChangeSections f g M A B b ∧
      (∀ (V : S.affineOpens) (W : T.affineOpens) (hv : W.1 ≤ g ⁻¹ᵁ V.1)
        (a : (relativeImageSymmetric f M).obj V),
        psi.app W (c.map hv a) = b.map hv (phi.app V a)) ∧
      @RelativeImageGeometry _ _ _ _ hfinite B psi hpsi h' q' ∧
      q' ≫ b.relProjComparison = pullback.fst f g ≫ q ∧
      h' ≫ c.relProjComparison = pullback.fst f g ≫ h ∧
      Scheme.GradedAlgebraData.relProjMap psi
        (Scheme.GradedAlgebraData.irrelevantLE_of_surjective psi hpsi) ≫
          c.relProjComparison = b.relProjComparison ≫
            Scheme.GradedAlgebraData.relProjMap phi
              (Scheme.GradedAlgebraData.irrelevantLE_of_surjective phi hsurj)

/-- Naturality under isomorphisms of the pair. The section formula includes an arbitrary
isomorphism from the pulled-back line to M', not merely equality of the two lines.
Source: Knudsen II 2.1, Stacks 01O9
(blueprint: lem-sfb-relative-section-image-flat-fp). -/
def RelativeImagePairIsomorphisms {Y S : Scheme.{u}} (f : Y ⟶ S) (M : Y.Modules)
    [(relativeImageDegreeOne f M).IsFiniteLocallyFree] (A : RelativeSectionAlgebra f M)
    (phi : relativeImageSymmetric f M ⟶ A.data)
    (hsurj : ∀ V : S.affineOpens, Function.Surjective (phi.app V))
    (h : Y ⟶ (relativeImageSymmetric f M).relProj) (q : Y ⟶ A.data.relProj) : Prop :=
  ∀ (Y' : Scheme.{u}) (f' : Y' ⟶ S) (M' : Y'.Modules)
    (e : Y' ≅ Y) (we : e.hom ≫ f = f')
    (l : (tensorPullback e.hom).obj M ≅ M'),
    ∃ (hfinite : (relativeImageDegreeOne f' M').IsFiniteLocallyFree)
      (B : RelativeSectionAlgebra f' M') (b : A.data ≅ B.data)
      (psi : @relativeImageSymmetric _ _ f' M' hfinite ⟶ B.data)
      (hpsi : ∀ V, Function.Surjective (psi.app V))
      (c : relativeImageSymmetric f M ≅ @relativeImageSymmetric _ _ f' M' hfinite)
      (h' : Y' ⟶ (@relativeImageSymmetric _ _ f' M' hfinite).relProj)
      (q' : Y' ⟶ B.data.relProj),
      @RelativeImageIsSectionQuotient _ _ _ _ hfinite B psi ∧
      @RelativeImageGeometry _ _ _ _ hfinite B psi hpsi h' q' ∧
      c.hom ≫ psi = phi ≫ b.hom ∧
      q' ≫ (Scheme.GradedAlgebraData.relProjIsoOfIso b).hom = e.hom ≫ q ∧
      h' ≫ (Scheme.GradedAlgebraData.relProjIsoOfIso c).hom = e.hom ≫ h ∧
      Scheme.GradedAlgebraData.relProjMap psi
        (Scheme.GradedAlgebraData.irrelevantLE_of_surjective psi hpsi) ≫
          (Scheme.GradedAlgebraData.relProjIsoOfIso c).hom =
        (Scheme.GradedAlgebraData.relProjIsoOfIso b).hom ≫
          Scheme.GradedAlgebraData.relProjMap phi
            (Scheme.GradedAlgebraData.irrelevantLE_of_surjective phi hsurj) ∧
      ∀ (V : S.affineOpens) (n : ℕ) (s : A.data.grading V n),
        (M'.tensorPow n).presheaf.map
          (eqToHom (congrArg (fun k : Y' ⟶ S ↦ k ⁻¹ᵁ V.1) we)).op
          (B.sectionEquiv V n ⟨b.hom.app V s, (b.hom.app V).map_mem s.property⟩) =
        (boundaryTensorPowIso l n).hom.app (e.hom ⁻¹ᵁ (f ⁻¹ᵁ V.1))
          ((boundaryPullbackPowIso e.hom M n).hom.app (e.hom ⁻¹ᵁ (f ⁻¹ᵁ V.1))
            (tensorPullbackSection e.hom (M.tensorPow n) (f ⁻¹ᵁ V.1)
              (A.sectionEquiv V n s)))

/-- Flat finitely presented relative image of an acyclic section algebra.

Source: Stacks 068A, 0B6G, 0A1H, 0B91, 01O4; Knudsen II 2.1, relative-image
spreading consequence (blueprint: lem-sfb-relative-section-image-flat-fp).

Proof, following the ten steps of the node:
1. On an affine base where A_1 is free of rank r, the section quotient gives the closed
immersion Proj A into P^(r-1); nonempty fibres and evaluation give r>0 on a nonempty base.
Uses: prop-nagata-relative-proj-functoriality, lem-trf-projective-bundle-quotient-geometry,
lem-trf-projective-bundle-proper.

2. The adjunction evaluations in all degrees define the canonical Proj map q. Degree-one
surjectivity makes its domain all Y. The twist comparison sends tautological sections to
actual evaluations, identifies q^*O(1) with M and identifies the composite with h. Since
Y/S is proper and Proj A/S is separated, q is proper.
Uses: lem-trf-space-line-module-proj-map, lem-trf-proj-invertible-map-twist-iso,
lem-trf-projective-bundle-quotient-geometry, lem-weil-pbc-proper-over-separated.

3. Section localization at s identifies Gamma(Y_s,O) with C_(s), including C_0=R, by
sending a/s^n to its evaluated fraction. Quasi-coherence and the affine tilde/Gamma
adjunction give O_ProjA = q_*O_Y on each standard chart. The proper-image theorem then
identifies Proj A with the scheme-theoretic image and makes q surjective.
Uses: lem-sc-invert-s-cohomology, lem-weil-pbc-proj-structure-sheaf-standard-sections,
prop-nagata-proj-standard-open, pqf-lem-image-proper, lem-pc-derived-direct-image-preserves-qcoh,
lem-weil-pbc-affine-tilde-gamma-adjunction.

4. Each C_(s) is the sequential colimit of the finite projective C_n under multiplication
by s. Filtered colimits of flat modules are flat, so the chart flatness criterion applies.
Uses: lem-pc-finite-flat-affine-sections-projective, lem-weil-pbc-projective-module-flat,
lem-weil-pbc-filtered-colimit-flat-modules, lem-weil-pbc-flat-ring-map-iff-flat-affine,
prop-nagata-proj-standard-open.

5. Perfect proper base change makes Rf_*M^j perfect. Fibrewise vanishing and degree-zero
base change put it in the degree-zero perfect locus, hence identify it with A_j[0].
Affine Cech vanishing and degenerate Leray give H^p(Y_U,M^j)=0 for p>0,j>0.
Uses: lem-pc-rf-perfect-base-change, lem-pc-perfect-locus, sk-lem-picard-cech-computes,
lem-pc-leray-degenerate-sections.

6. Cohomology localization represents every higher class on Y_s with positive denominator
power, so the preceding vanishing kills it. Quasi-coherence and affine Leray yield
R^p h_*O_Y=0 for p>0 and Rh_*O_Y=i_*O_ProjA[0].
Uses: lem-sc-invert-s-cohomology, lem-pc-derived-direct-image-preserves-qcoh,
sk-lem-picard-cech-computes, lem-pc-leray-degenerate-sections,
lem-weil-pbc-affine-tilde-gamma-adjunction.

7. Projection formula and normalized derived Leray identify the finite list of projective
space twists with Rf_*M^d, for d=0,...,r-1. Proper flat finite-presentation perfect base
change makes those perfect. The affine derived equivalence and affine pseudo-coherence
criterion give pseudo-coherence in D(R), and the finite twist test implies that
Rh_*O_Y, hence i_*O_ProjA[0], is pseudo-coherent on projective space.
Uses: lem-pc-derived-direct-image-preserves-qcoh, lem-pc-projection-formula,
lem-sc-mixed-global-sections-direct-image-iso, lem-pc-rf-perfect-base-change,
def-pc-perfect-complex, lem-pc-perfect-pseudo-coherent-locally-finite-tor,
lem-sfb-projective-space-pseudocoherence-twist-test, lem-pc-affine-qcoh-derived-equivalence,
lem-pc-affine-pseudo-coherent-criterion.

8. Truncate its bounded-above finite-free model to obtain a finite module presentation.
The finite-presentation kernel theorem makes the ideal of the image finitely generated.
On distinguished projective charts the image is a finitely presented polynomial quotient.
Properness supplies quasi-compactness and quasi-separatedness, hence finite presentation.
Uses: def-pur-pseudo-coherent-complex,
lem-weil-pbc-finite-presentation-kernel-surjection-finite-type,
lem-weil-pbc-finite-presentation-base-change-composition, def-sbc-locally-finite-presentation.

9. The stipulated section base-change maps respect unit and multiplication. Relative-Proj
base change and the evaluated fraction formula give the displayed cartesian comparisons,
quotient and evaluation squares, and normalized twist comparisons under every base change.
Uses: lemma-nagata-relative-proj-base-change-arbitrary, lem-trf-space-line-module-proj-map,
lem-trf-projective-bundle-quotient-geometry, lem-trf-proj-invertible-map-twist-iso.

10. On a geometric fibre, degree-zero base change identifies its graded pieces with the
fibre section algebra. The same localization calculation identifies its Proj with the
kernel-defined image of h and q with h.toImage. Pullback and an isomorphism of lines
preserve the homogeneous fraction formulas, giving naturality under every pair isomorphism.
Uses: prop-nagata-relative-proj-functoriality, lem-trf-projective-bundle-quotient-geometry,
lem-trf-proj-invertible-map-twist-iso.
-/
theorem relative_section_image_flat_fp {Y S : Scheme.{u}} (f : Y ⟶ S)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (M : Y.Modules) [M.IsInvertible]
    [hfinite : ∀ n : ℕ, ((pushforward f).obj (M.tensorPow (n + 1))).IsFiniteLocallyFree]
    (hfibres : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S),
      Nonempty (Limits.pullback (C := Scheme.{u}) f t) ∧
        (Limits.pullback (C := Scheme.{u}) f t).IsPureDimension 1)
    (hO : ∀ (T : Scheme.{u}) (g : T ⟶ S),
      IsIso ((tensorPullbackSectionAdjunction (pullback.snd f g)).unit.app
        (SheafOfModules.unit T.ringCatSheaf)))
    (hvanish : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S)
      (j i : ℕ), 0 < j → 0 < i →
      IsZero ((RingedSpace.moduleCohomology
        (Limits.pullback (C := Scheme.{u}) f t).toRingedSpace i).obj
        (((tensorPullback (pullback.fst f t)).obj M).tensorPow j)))
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S) (j : ℕ), 0 < j →
      IsIso (moduleBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition (M.tensorPow j)))
    (heval : Epi (relativeImageEvaluation f M))
    (A : RelativeSectionAlgebra f M)
    (phi : relativeImageSymmetric f M ⟶ A.data)
    (hphi : RelativeImageIsSectionQuotient A phi)
    (hsurj : ∀ V : S.affineOpens, Function.Surjective (phi.app V))
    (h : Y ⟶ (relativeImageSymmetric f M).relProj)
    (wh : h ≫ (relativeImageSymmetric f M).relProjHom = f)
    (hcanonical : ProjectiveBundleQuotientGeometry.IsCanonicalMap f (M.tensorPow 1)
      (relativeImageEvaluation f M) h)
    (himage : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S),
      RelativeImageStructureComparison
        (relativeImageFibreMap f (relativeImageSymmetric f M).relProjHom h wh t))
    (hhigher : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S)
      (i : ℕ), 0 < i → IsZero
        (((pushforward (relativeImageFibreMap f
          (relativeImageSymmetric f M).relProjHom h wh t)).rightDerived i).obj
            (SheafOfModules.unit (Limits.pullback (C := Scheme.{u}) f t).ringCatSheaf))) :
    ∃ (q : Y ⟶ A.data.relProj) (wq : q ≫ A.data.relProjHom = f),
      RelativeImageGeometry f M A phi hsurj h q ∧
      RelativeImageGeometricFibres f M A phi hsurj h wh q wq ∧
      RelativeImageArbitraryBaseChange f M A phi hsurj h q ∧
      RelativeImagePairIsomorphisms f M A phi hsurj h q := by
  sorry

end AlgebraicGeometry.Scheme.Modules
