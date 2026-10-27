/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.AlgebraDiagramPullbackData
import Sheaf.CategoryTheory.AlgebraDiagramExactness
import Sheaf.CategoryTheory.AlgebraDiagramScalarPresentation
import Sheaf.CategoryTheory.AlgebraDiagramOrdinaryComparisons
import Sheaf.CategoryTheory.AlgebraDiagramOrdinaryUnitNaturality
import Sheaf.CategoryTheory.AlgebraDiagramDerivedComparisons
import Sheaf.CategoryTheory.AlgebraDiagramAmbientSpecialization
import Sheaf.CategoryTheory.AlgebraDiagramAmbientBalancing
import Sheaf.CategoryTheory.AlgebraDiagramExtensionUnit
import Sheaf.CategoryTheory.AlgebraDiagramThetaNaturality
import Sheaf.CategoryTheory.AlgebraDiagramScalarUnitNaturality

/-! # Derived scalar extension and pullback on algebra diagrams

Source: Stacks 03EL, 07A4 and 0G7E.
(blueprint: lem-pur-algebra-diagram-pullback-extension-coherence).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 4096
attribute [local instance 100000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize

universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.CochainPullback
attribute [local irreducible] DerivedCategory.Q Functor.mapDerivedCategory
attribute [local irreducible] Functor.mapHomologicalComplex Functor.curry
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] SheafOfModules.PullbackTensorCanonical.canonicalDerivedTensor
attribute [local irreducible] SheafOfModules.PullbackTensorCanonical.canonicalRepresentativeIso
namespace CategoryTheory.AlgebraDiagramPullback

/-- Derived scalar-extension/pullback coherence for entire strict algebra diagrams,
with normalized representatives, scalar units and compatible algebra maps.

Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 0G7E,
and sites-modules.tex, Tag 03EL; the scalar/unit refinement of steps 1--6
(blueprint: lem-pur-algebra-diagram-pullback-extension-coherence).

Proof plan:
1. Realize the diagrams on the small product sites, using
   lem-weil-pbc-diagram-site-realization. Horizontal restrictions retain the actual
   algebra transitions. Constant-left-module inverse image identifies the constant
   base rings. Geometric-inverse-image-exact and the scalar-restriction adjunction
   show exactness of the two inverse images and of both restrictions. The ordinary
   restriction comparison inserts the scalar unit; the invertible structural ring
   maps give its multiplication inverse. Localize it to obtain b.
2. Choose one flat-term K-flat resolution P on the whole diagram site, using
   lem-pc-kflat-resolution. Derived-change-of-rings computes extension on P, and
   ringed-topoi-derived-tensor-pullback preserves the resolving class. The exact
   algebra inverse image needs no further resolution of P tensor B. The existing
   cochain kappa gives c by balanced association; its inverse multiplies scalars.
3. Resolve the underlying coefficient complex B[0] by Q. Tensoring Q -> B[0]
   with P is a quasi-isomorphism by K-flat tensor invariance. The same holds after
   exact inverse image. Site-derived-tensor-descent and
   lem-pur-exact-pullback-signed-comparison identify the ambient comparison on
   (P,Q). Naturality and cancellation of the invertible resolution maps identify
   its one-sided coefficient specialization with the ordinary tensor comparison.
4. On a tensor a tensor (p tensor b), the restriction/extension composite is
   (1 tensor p) tensor (a-bar b), equal by balancing to (a tensor p) tensor b.
   Thus U(c) composed with b equals the independently normalized ambient theta.
5. The normalized derived coefficient adjunction represents its unit by
   p mapped to p tensor 1. Pullback followed by theta sends a tensor p to
   (a tensor p) tensor 1. This proves the displayed unit equality without asserting
   that scalar extension's unit is a quasi-isomorphism.
6. Check the formulas before localization on every horizontal arrow, chain map
   and compatible algebra map. Multiplicativity and preservation of one give
   identical expressions on both routes. Resolving-class descent and localization
   extend the maps and equalities naturally to all unbounded derived objects.
   The coefficient maps in CoefficientNaturality are the actual maps on B[0],
   transported through the specified tensor identifications. No flatness of B/A,
   boundedness, perfectness, completeness or quotient condition enters.
-/
theorem algebraDiagramPullbackExtensionCoherence
    (I X Y : Type u) [SmallCategory I] [SmallCategory X] [SmallCategory Y]
    (KX : GrothendieckTopology X) (KY : GrothendieckTopology Y)
    (A : Type u) [CommRing A]
    (F : Sheaf KY (Type u) ⥤ Sheaf KX (Type u))
    (G : Sheaf KX (Type u) ⥤ Sheaf KY (Type u))
    (adj : F ⊣ G) [PreservesFiniteLimits F]
    (g : RingedPullback.{u, u, u, u, u}
      (diagramConstantRing I Y KY A) (diagramConstantRing I X KX A))
    (hInv : g.uInv = ((diagramSiteSheafEquivalence I Y KY).functor ⋙
      (Functor.whiskeringRight I _ _).obj F) ⋙ (diagramSiteSheafEquivalence I X KX).inverse)
    (hDir : g.uPush = (diagramSiteSheafEquivalence I X KX).functor ⋙
      ((Functor.whiskeringRight I _ _).obj G ⋙ (diagramSiteSheafEquivalence I Y KY).inverse))
    (hAdj : HEq g.adj (((diagramSiteSheafEquivalence I Y KY).toAdjunction.comp
      (adj.whiskerRight I)).comp (diagramSiteSheafEquivalence I X KX).symm.toAdjunction))
    (hConstants : HasCanonicalConstants (diagramSiteTopology I Y KY)
      (diagramSiteTopology I X KX) A g)
    [IsIso g.coefficient]
    (kg : Comparison.{u, u, u, u, u} g)
    (d : CoefficientSquare.{u, u, u, u, u} g) [IsIso d.coefficient']
    (kd : Comparison.{u, u, u, u, u} (changed g d))
    [HasDerivedCategory.{w} (Modules.{u, u, u} (diagramConstantRing I Y KY A))]
    [HasDerivedCategory.{w} (Modules.{u, u, u} (diagramConstantRing I X KX A))]
    [HasDerivedCategory.{w} (Modules.{u, u, u} d.R')]
    [HasDerivedCategory.{w} (Modules.{u, u, u} d.S')] :
    Nonempty (Result g kg d kd) := by
  classical
  have : ExactPullback g := pullback_exact g
  have : IsIso (changed g d).coefficient := by dsimp [changed]; infer_instance
  have : ExactPullback (changed g d) := pullback_exact (changed g d)
  have : ExactRestriction d.sourceMap := restriction_exact d.sourceMap
  have : ExactRestriction d.targetMap := restriction_exact d.targetMap
  obtain ⟨s⟩ := scalar_presentation d.sourceMap
  obtain ⟨t⟩ := scalar_presentation d.targetMap
  obtain ⟨b, hb⟩ := ordinary_restriction g kg d kd
  obtain ⟨beta, hbeta⟩ := coefficient_iso g kg d kd
  have hflat := pullback_resolving g kg
  obtain ⟨e, he⟩ := extension_descent g kg d kd s t
    (fun P hp hf ↦ (hflat P hp hf).1)
  obtain ⟨a, ha⟩ := ambient_exists g kg
  let q : Coherence g kg d kd := {
    source := s
    target := t
    ordinaryRestriction := b
    restriction_generators := hb
    restriction := CategoryTheory.Functor.mapDerivedCategorySquareIso b
    restriction_model := restriction_descent g d b
    extension := e
    extension_model := he
    beta := beta
    beta_generators := hbeta
    ambient := a
    ambient_model := ha
    theta := ambientSpecialization g d s t a beta
    theta_ambient := ambientSpecialization_hom g d s t a beta
    tensor_coherence := ambient_balancing g kg d kd s t b hb e he beta hbeta a ha
    unit_coherence := by
      intro M
      rw [← ambient_balancing g kg d kd s t b hb e he beta hbeta a ha M]
      exact extension_unit g kg d kd s t b hb e he hflat M }
  refine ⟨{ comparison := q, coefficient_naturality := ?_ }⟩
  intro d' k'' _ _ _ _ _ q' psiY psiX hsource htarget hring hY hX hy hx M
  have hbeta' := coefficient_naturality g kg d d' q.beta q'.beta
    q.beta_generators q'.beta_generators psiY psiX hring hY hX hy hx
  exact ⟨theta_natural g kg d d' kd k'' q q' hY hX hbeta' M,
    scalar_unit_natural d.sourceMap d'.sourceMap q.source q'.source psiY hY hy M,
    scalar_unit_natural d.targetMap d'.targetMap q.target q'.target psiX hX hx
      (g.L.mapDerivedCategory.obj M)⟩

end CategoryTheory.AlgebraDiagramPullback
