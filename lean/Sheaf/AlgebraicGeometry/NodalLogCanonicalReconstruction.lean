/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.AlgebraicGeometry.MarkedNodalDualizingDegrees
public import Sheaf.AlgebraicGeometry.SchemeAmpleCanonicalProjCriterion
public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
public import Sheaf.AlgebraicGeometry.NodalDualizingDatum
import WeilConjectures.RingTheory.CompleteIntersectionOverField
import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.RingTheory.RegularSequencePrincipalNeighbourhood
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.Modules.Ample
import WeilConjectures.AlgebraicGeometry.ConstantLocalDimensionComponents
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import Sheaf.AlgebraicGeometry.AmpleProjLocalChart
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import WeilConjectures.AlgebraicGeometry.Curve.ClosedPoint
import Sheaf.AlgebraicGeometry.SectionRingLocalizationBijective
import Sheaf.TraceFormula.AmpleNeighbourhood
import Sheaf.AlgebraicGeometry.AmpleIffNormalizedComponentDegreePos
import Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction
import Sheaf.AlgebraicGeometry.NodalCurveLCICriterion
import Sheaf.AlgebraicGeometry.NodalNormalizationAdjunction
import Sheaf.TraceFormula.SchemeRelativeAmpleAffineCover
import Sheaf.TraceFormula.SmoothCurveSectionCartier
import WeilConjectures.AlgebraicGeometry.DimensionAtPointFieldExtension
import WeilConjectures.RingTheory.GlobalCompleteIntersectionPrincipalLocalization
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.RingTheory.RelativeGlobalCompleteIntersectionLocalRegularSequence
import WeilConjectures.RingTheory.SyntomicAtPrimeRelativeGlobalCompleteIntersection

public import Mathlib.AlgebraicGeometry.Morphisms.Flat

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

public import Mathlib.Topology.KrullDimension

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

public import Mathlib.RingTheory.AdicCompletion.Basic

public import Mathlib.RingTheory.MvPowerSeries.Basic

public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

public import Sheaf.AlgebraicGeometry.ReducedNormalization

public import WeilConjectures.AlgebraicGeometry.Ample

public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures

public import Sheaf.TraceFormula.MultipointedCurve

public import Sheaf.AlgebraicGeometry.MultipointedCurveModification

public import Sheaf.AlgebraicGeometry.PureDimension

public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction

public import Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap

public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

import Mathlib.AlgebraicGeometry.Morphisms.Finite

import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

import Mathlib.AlgebraicGeometry.Morphisms.Separated

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import Mathlib.AlgebraicGeometry.Morphisms.Immersion

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Log dualizing polarization and reconstruction of marked nodal families

Source: Stacks Project, Moduli of Curves, Tags 0E6R and 0E74 (component argument,
with the marking twist); Varieties, Tag 0B5Y; Morphisms, Tags 01VJ and 0C6J
(blueprint: lem-sfb-nodal-log-canonical-reconstruction).

We use the existing multipointed-curve and normalized dualizing interfaces. A splitting
of the marking into finitely many copies of the base records the disjoint sections.
The log fundamental class fixes comparisons under marked-family isomorphisms; the
section formula fixes the induced graded algebra map in every degree, including zero.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- The fundamental class followed by the canonical divisor section. The latter is
literally the inclusion of the marking ideal, viewed as a section of its dual.
Source: Stacks, Moduli of Curves, Tag 0E6R, with the Cartier section twist
(blueprint: lem-sfb-nodal-log-canonical-reconstruction). -/
def nodalLogFundamental {S : Scheme.{u}} (P : MultipointedCurve S)
    (F : P.X.Modules) (D : NodalDualizingDatum P.x F) :
    P.x.relativeDifferentials ⟶ markedNodalLine P F :=
  D.fundamental ≫ (ρ_ F).inv ≫
    F ◁ (SheafOfModules.unitHomEquiv (P.i.ker.toModulesᵛ)).symm
      ((SheafOfModules.homObjSectionsEquiv P.i.ker.toModules
        (SheafOfModules.unit P.X.ringCatSheaf)).symm P.i.ker.toModulesι)

/-- Pull a section of a tensor power back by the actual `1 ⊗ s` map and then apply
the power of the specified line comparison. No section map is chosen by existence.
Source: Stacks, Morphisms, Tag 01VJ, canonical evaluation
(blueprint: lem-sfb-nodal-log-canonical-reconstruction). -/
def nodalLogPullbackSection {X Y : Scheme.{u}} (g : X ⟶ Y)
    (L : Y.Modules) (M : X.Modules)
    (e : (Scheme.Modules.tensorPullback g).obj L ≅ M)
    (n : ℕ) (U : Y.Opens) (s : Γ(L.tensorPow n, U)) : Γ(M.tensorPow n, g ⁻¹ᵁ U) :=
  (Scheme.Modules.boundaryTensorPowIso e n).hom.app (g ⁻¹ᵁ U)
    ((Scheme.Modules.boundaryPullbackPowIso g L n).hom.app (g ⁻¹ᵁ U)
      (Scheme.Modules.tensorPullbackSection g (L.tensorPow n) U s))

/-- Naturality under isomorphisms of marked families. The line comparison is normalized
by the log fundamental class, and the graded algebra isomorphism acts on every section
by its actual pullback followed by this comparison. The last equation is the evaluation
square for the existing contravariant relative-Proj functor.
Source: Stacks, Morphisms, Tags 01VJ and 0C6J, naturality of evaluation
(blueprint: lem-sfb-nodal-log-canonical-reconstruction). -/
def NodalLogReconstructionIsNatural {S : Scheme.{u}} (P : MultipointedCurve S)
    (D : MarkedNodalDualizingDegreesData P)
    (A : Scheme.Modules.RelativeSectionAlgebra P.x (markedNodalLine P D.omega))
    (r : P.X ⟶ A.data.relProj) : Prop :=
  ∀ (Q : MultipointedCurve S) (E : MarkedNodalDualizingDegreesData Q)
    (e : P.X ≅ Q.X) (d : P.D ≅ Q.D)
    (he : e.hom ≫ Q.x = P.x),
    d.hom ≫ Q.d = P.d → P.i ≫ e.hom = d.hom ≫ Q.i →
    ∃ c : (Scheme.Modules.tensorPullback e.hom).obj (markedNodalLine Q E.omega) ≅
        markedNodalLine P D.omega,
      (∀ (U : Q.X.Opens) (a : Γ(Q.X, U)),
        (((Scheme.Modules.tensorPullback e.hom).map
            (nodalLogFundamental Q E.omega E.dualizing)) ≫ c.hom).app
            (e.hom ⁻¹ᵁ U) (Q.x.relativeDifferentialsPullbackGenerator e.hom U a) =
          (nodalLogFundamental P D.omega D.dualizing).app (e.hom ⁻¹ᵁ U)
            (P.x.relativeDifferentialsDerivation.d (X := op (e.hom ⁻¹ᵁ U))
              (e.hom.app U a))) ∧
      ∀ (B : Scheme.Modules.RelativeSectionAlgebra Q.x (markedNodalLine Q E.omega))
        (s : Q.X ⟶ B.data.relProj), B.IsCanonicalMap s →
        ∃ b : B.data ≅ A.data,
          (∀ (V : S.affineOpens) (n : ℕ) (a : B.data.grading V n),
            ((markedNodalLine P D.omega).tensorPow n).presheaf.map
                (eqToHom (congrArg (fun f : P.X ⟶ S ↦ f ⁻¹ᵁ V.1) he)).op
                (A.sectionEquiv V n
                  ⟨b.hom.app V a, (b.hom.app V).map_mem a.property⟩) =
              nodalLogPullbackSection e.hom (markedNodalLine Q E.omega)
                (markedNodalLine P D.omega) c n (Q.x ⁻¹ᵁ V.1)
                (B.sectionEquiv V n a)) ∧
          r ≫ (Scheme.GradedAlgebraData.relProjIsoOfIso b).hom = e.hom ≫ s

/-- The affine-base reconstruction uses the existing direct-sum section ring with its
tensor products. The degree-zero coefficient map is fixed on every element of R by the
structure morphism. The inverse-image and fraction formulas fix the evaluation map.
Source: Stacks, Morphisms, Tag 0C6J; Properties, Tags 01PZ and 01Q1
(blueprint: lem-sfb-nodal-log-canonical-reconstruction). -/
def NodalLogAffineReconstruction {S : Scheme.{u}} (P : MultipointedCurve S)
    (L : P.X.Modules) (hL : L.IsInvertible) : Prop :=
  ∀ (R : Type u) [CommRing R] (e : S ≅ Spec (.of R)),
    ∃ (c : R →+* Scheme.Modules.sectionRingGrade L 0)
      (r : P.X ≅ Proj (Scheme.Modules.sectionRingGrade L)),
      (∀ a : R, (c a).val =
        DirectSum.of (Scheme.Modules.SectionRingComponent L) 0
          (Scheme.Modules.unitSectionsEquiv ⊤
            (((P.x ≫ e.hom).appTop).hom ((Scheme.ΓSpecIso (.of R)).inv a)))) ∧
      r.hom ≫ Proj.toSpecZero (Scheme.Modules.sectionRingGrade L) ≫
        Spec.map (CommRingCat.ofHom c) = P.x ≫ e.hom ∧
      ∀ (m : ℕ) (_hm : 0 < m) (s : Scheme.Modules.sectionRingGrade L m),
        (r.hom ⁻¹ᵁ Proj.basicOpen (Scheme.Modules.sectionRingGrade L) s.val : Set P.X) =
          Scheme.Modules.nonvanishingLocus (L.tensorPow m) (s.val m) ∧
        ∀ (n : ℕ) (a : Scheme.Modules.sectionRingGrade L (n • m)),
          (r.hom.app (Proj.basicOpen (Scheme.Modules.sectionRingGrade L) s.val)
            (Proj.awayToSection (Scheme.Modules.sectionRingGrade L) s.val
              (HomogeneousLocalization.Away.mk (Scheme.Modules.sectionRingGrade L)
                s.property n a.val a.property))) •
            (L.tensorPow (n • m)).presheaf.map (homOfLE
              (le_top : r.hom ⁻¹ᵁ
                Proj.basicOpen (Scheme.Modules.sectionRingGrade L) s.val ≤ ⊤)).op
              ((s.val ^ n) (n • m)) =
          (L.tensorPow (n • m)).presheaf.map (homOfLE
            (le_top : r.hom ⁻¹ᵁ
              Proj.basicOpen (Scheme.Modules.sectionRingGrade L) s.val ≤ ⊤)).op
            (a.val (n • m))

/-- A marked projective flat finitely presented nodal family has its canonical
base-change-compatible dualizing line. Its marking twist has normalized-component degree
`2g - 2 + r`, is relatively ample when those numbers are positive, and reconstructs the
family by canonical relative Proj, naturally under marked-family isomorphisms. The
splitting of the marking is exactly a finite list of pairwise disjoint sections; n=0
is allowed. No integral or normal base, smooth generic fibre or modification map occurs.

Source: Stacks, Moduli of Curves, Tag 0E6R and the component argument of 0E74, with the
section twist; Varieties, Tag 0B5Y; Morphisms, Tags 01VJ and 0C6J
(blueprint: lem-sfb-nodal-log-canonical-reconstruction).

Proof plan, following the node's fourteen steps:
1. Projectivity gives properness. Restrict to arbitrary affine base opens, whose rings
   are Noetherian; use affine refinements of overlaps, never affine intersections.
2. Geometric purity descends to residue-field fibres. The nodal lci criterion and
   principal localization give the required fibre complete-intersection neighbourhoods.
3. The syntomic relative presentation theorem gives relative complete intersections.
   Shrink by the regular-sequence principal-neighbourhood lemma and adjoin yh-1 to
   obtain regular curve presentations with one more variable than relations.
4. Flat-lci canonical adjunction constructs the line on each base affine. Its canonical
   comparisons glue and give arbitrary base change, including non-Noetherian new bases.
5. The lci-curve fundamental class supplies the Jacobian normalization in every regular
   presentation; its isomorphism locus is the smooth locus.
6. A section of a separated morphism is closed. Smooth curve sections are Cartier;
   their disjoint product ideal gives D, including the unit ideal when n=0.
7. Dualize the marking ideal and tensor with omega. Relative Cartier pullback and the
   tensor pullback comparison identify these constructions after every base change.
8. Nodal normalization adjunction identifies the normalized pullback with differentials
   twisted by all node branches and markings. A self-node contributes twice.
9. Riemann--Roch compares Euler degree and classical degree. Canonical degree and the
   divisor tensor-degree formula give 2g-2+r, with every rational point counted once.
10. Positive component degrees give geometric-fibre ampleness; descent gives ordinary
    fibre ampleness. Ample neighbourhoods and the affine-cover criterion give relative
    ampleness over every base affine.
11. The relative section algebra and evaluation construction give the canonical open
    immersion into relative Proj. Its affine charts are the usual section-ring charts.
12. Section-ring localization bijectivity shows that any nonempty standard Proj open
    meets the image, hence the image is dense, also in degree-zero-degenerate cases.
13. Proj is separated over each base affine, so the map from the proper curve has closed
    image. A closed dense open immersion is an isomorphism; these local inverses glue.
14. Adjunction and Cartier comparisons under a marked-family isomorphism respect the
    log fundamental class and products of sections. Relative Proj functoriality and the
    chart ratio formula give the displayed naturality square.
-/
theorem exists_nodal_log_canonical_reconstruction
    (S : Scheme.{u}) [IsLocallyNoetherian S]
    (P : MultipointedCurve S) [IsHProjective P.x]
    (n : ℕ) (marking : (∐ fun _ : Fin n ↦ S) ≅ P.D)
    (hmarking : marking.hom ≫ P.d = Sigma.desc (fun _ : Fin n ↦ 𝟙 S))
    (hsmooth : ∀ z : P.D, P.i z ∈ P.x.smoothLocus)
    (hnodal : HasNodalGeometricFibres P.x)
    (hgeometric : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S),
      IsReduced (pullback P.x t) ∧ (pullback P.x t).IsPureDimension 1) :
    ∃ D : MarkedNodalDualizingDegreesData P,
      IsIso ((Scheme.Modules.tensorPullback P.x.smoothLocus.ι).map
        D.dualizing.fundamental) ∧
      ((∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S)
          (Z : Scheme.{u}) [IsIntegral Z] (j : Z ⟶ pullback P.x t),
          IsClosedImmersion j →
          Set.range j ∈ irreducibleComponents (pullback (C := Scheme) P.x t) →
          0 < (2 * markedNodalComponentGenus Ω Z (j ≫ pullback.snd P.x t) : ℤ) - 2 +
            ((markedNodalBranches P Ω t Z j).ncard : ℤ)) →
        ∀ (V : S.Opens), IsAffineOpen V →
          ∃ h : ((Scheme.Modules.tensorPullback (P.x ⁻¹ᵁ V).ι).obj
              (markedNodalLine P D.omega)).IsInvertible,
            @Scheme.Modules.IsAmple (P.x ⁻¹ᵁ V).toScheme
              ((Scheme.Modules.tensorPullback (P.x ⁻¹ᵁ V).ι).obj
                (markedNodalLine P D.omega)) h) ∧
      ((∀ (V : S.Opens), IsAffineOpen V →
          ∃ h : ((Scheme.Modules.tensorPullback (P.x ⁻¹ᵁ V).ι).obj
              (markedNodalLine P D.omega)).IsInvertible,
            @Scheme.Modules.IsAmple (P.x ⁻¹ᵁ V).toScheme
              ((Scheme.Modules.tensorPullback (P.x ⁻¹ᵁ V).ι).obj
                (markedNodalLine P D.omega)) h) →
        (∃ (A : Scheme.Modules.RelativeSectionAlgebra P.x (markedNodalLine P D.omega))
            (r : P.X ≅ A.data.relProj),
          A.IsCanonicalMap r.hom ∧ NodalLogReconstructionIsNatural P D A r.hom) ∧
        NodalLogAffineReconstruction P (markedNodalLine P D.omega) D.marked_invertible) := by
  sorry

end AlgebraicGeometry
