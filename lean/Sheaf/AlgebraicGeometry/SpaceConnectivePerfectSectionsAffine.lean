/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.AlgebraicGeometry.RelativeDualizingTracePair
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.RingTheory.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.CategoryTheory.Yoneda
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativeSpecCorrespondence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Affine representability of sections of universally connective perfect complexes

Source: Stacks Project, quot.tex, Tag 08JX, lemma-cohomology-perfect-complex (2)
(blueprint: lem-sfb-space-connective-perfect-sections-affine).

The section groups are the existing H⁰ RΓ on the equivalent small étale ringed model.
Naturality is specified by a commuting square of derived sections O[0] → Lg* K;
this retains the canonical structure pullback and pullback composition comparisons.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The existing zeroth hypercohomology functor on the equivalent small étale model.
Source: Stacks, Tag 08JX (2), with Section 07A5
(blueprint: lem-sfb-space-connective-perfect-sections-affine). -/
abbrev connectiveSectionsH0 (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules] : X.DerivedModules ⥤ AddCommGrpCat.{u} :=
  ringedSiteZerothHypercohomologyOfUniverses.{u, u, u, w}
    X.smallEtaleModelTopology X.smallStructureSheaf

/-- The class of the constant section one in H⁰ RΓ(O[0]). It is the image of the
identity of O under the universal right-derived comparison, without choosing a class.
Source: Stacks, Sections 07A5 and 08JA; Tag 08JX (2)
(blueprint: lem-sfb-space-connective-perfect-sections-affine). -/
def connectiveSectionsOne (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules] :
    (connectiveSectionsH0 X).obj X.derivedStructure :=
  letI := HasDerivedCategory.standard AddCommGrpCat.{u}
  let G := preadditiveCoyoneda.obj (op (SheafOfModules.unit X.smallStructureRings))
  let M := SheafOfModules.unit X.smallStructureRings
  let c : (DerivedCategory.singleFunctor AddCommGrpCat.{u} 0).obj (G.obj M) ⟶
      G.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor X.SmallModules 0).obj M) :=
    (DerivedCategory.singleFunctorIsoCompQ AddCommGrpCat.{u} 0).hom.app _ ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).inv.app M) ≫
      (DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).inv.app _ ≫
      DerivedCategory.Qh.map ((G.mapHomotopyCategoryFactors (.up ℤ)).inv.app _) ≫
      G.rightDerivedFunctorUnit.app _ ≫
      G.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso X.SmallModules).hom.app _) ≫
      G.rightDerivedFunctor.map
        ((DerivedCategory.singleFunctorIsoCompQ X.SmallModules 0).inv.app M)
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map c
    (((DerivedCategory.singleFunctorCompHomologyFunctorIso AddCommGrpCat.{u} 0).inv.app
      (G.obj M)) (𝟙 M))

/-- The hypercohomology class of a derived section, by functoriality applied to one.
Source: Stacks, Tag 08JA and Tag 08JX (2)
(blueprint: lem-sfb-space-connective-perfect-sections-affine). -/
def connectiveSectionsClass (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules] {E : X.DerivedModules}
    (s : X.derivedStructure ⟶ E) : (connectiveSectionsH0 X).obj E :=
  (connectiveSectionsH0 X).map s (connectiveSectionsOne X)

/-- Universally connective perfect complexes have affine finitely presented spaces of
sections, naturally on all scheme tests.

Source: Stacks Project, quot.tex, Tag 08JX, lemma-cohomology-perfect-complex (2),
specialized to perfect K (blueprint: lem-sfb-space-connective-perfect-sections-affine).

Proof:
1. By lem-sfb-ringed-site-connective-hypercohomology, H⁰ RΓ equals sections of H⁰.
   Étale restriction is exact (lem-trf-space-etale-module-pushforward-restriction),
   so these sections form an étale sheaf, on arbitrary and empty scheme tests.
2. Use lem-sfb-space-connective-nonnegative-free-model to choose an affine étale
   cover with bounded nonnegative finite free models. They compute pullback by
   lem-pc-bounded-above-flat-kflat-site. Sections are the kernel of d⁰ on sections.
3. On Spec A, for a matrix (a_ji) of d⁰: Oⁿ → Oᵐ, take
   Spec A[x₁,...,xₙ]/(sum_i a_ji x_i). The morphism-into-affine bijection
   (lem-weil-pbc-morphism-into-affine-scheme) identifies its arbitrary test points
   with that kernel. Evaluation of variables proves the bijection and naturality;
   the finite presentation is explicit (def-weil-pbc-finitely-presented-algebra,
   def-sbc-locally-finite-presentation).
4. On overlaps Yoneda (lem-galois-yoneda-fully-faithful) gives the unique compatible
   isomorphisms, hence their cocycle. Relative Spec and fppf descent of coordinate
   algebras (lem-sfb-space-relative-spec-correspondence, lem-sfb-space-fppf-qcoh-descent,
   lem-sfb-space-fppf-covering-calculus) give a quasi-coherent algebra on B.
5. Its relative Spec is V. The local bijections glue by the two sheaf axioms, and
   their naturality glues by uniqueness. Under H⁰ RΓ, derived sections are maps
   O[0] → Lg* K; pulling these maps back gives exactly the displayed commuting square.
6. The chart criterion (lem-sfb-space-local-properties-chart-test) gives local finite
   presentation. Affineness descends (lem-sfb-space-affine-locality) and implies
   quasi-compactness and separatedness. The diagonal is quasi-compact by
   lem-pc-separated-quasi-separated on scheme tests. Thus V → B is finitely presented.
No Noetherian hypothesis, uniform bound, or nonempty-test condition is used. -/
theorem space_connective_perfect_sections_affine
    [∀ X : AlgebraicSpace S, HasDerivedCategory.{w} X.SmallModules]
    (B : AlgebraicSpace S) (K : B.DerivedModules)
    (hperfect : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
      B.smallStructureSheaf K)
    (hconnective : ∀ (T : Over S) (g : schemeSpace T ⟶ B) (i : ℤ), i < 0 →
      IsZero ((DerivedCategory.homologyFunctor (schemeSpace T).SmallModules i).obj
        ((spaceDerivedPullback g).obj K))) :
    ∃ (V : AlgebraicSpace S) (p : V ⟶ B),
      MapIsAffine p ∧ MapIsQuasiCompact p.hom.hom ∧
      MapIsQuasiCompact (pullback.diagonal p.hom.hom) ∧
      MapIsLocallyOfFinitePresentation p ∧
      ∃ e : ∀ (T : Over S) (g : schemeSpace T ⟶ B),
          { k : schemeSpace T ⟶ V // k ≫ p = g } ≃
            (connectiveSectionsH0 (schemeSpace T)).obj ((spaceDerivedPullback g).obj K),
        ∀ (T U : Over S) (g : schemeSpace T ⟶ B) (h : U ⟶ T)
          (kT : { k : schemeSpace T ⟶ V // k ≫ p = g })
          (kU : { k : schemeSpace U ⟶ V // k ≫ p = traceSchemeMap h ≫ g }),
          kU.val = traceSchemeMap h ≫ kT.val →
          ∃ (sT : (schemeSpace T).derivedStructure ⟶ (spaceDerivedPullback g).obj K)
            (sU : (schemeSpace U).derivedStructure ⟶
              (spaceDerivedPullback (traceSchemeMap h ≫ g)).obj K),
            connectiveSectionsClass (schemeSpace T) sT = e T g kT ∧
            connectiveSectionsClass (schemeSpace U) sU = e U (traceSchemeMap h ≫ g) kU ∧
            traceDerivedStructureMap (traceSchemeMap h) ≫ sU ≫
                (spaceDerivedPullbackComp g (traceSchemeMap h)).hom.app K =
              (spaceDerivedPullback (traceSchemeMap h)).map sT := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
