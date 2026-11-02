/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DualizingOpenMate.DualizingOpenMate
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
public import WeilConjectures.AlgebraicGeometry.Proper.ProperFiniteCoefficientExtension
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.Ordered.OrderedAffineTraceNormalForm

/-! # Local and global finite-free dualizing mates

Source: blueprint/latest, lem-coef-finite-free-extension.proof.md, paragraph 1
(local closed-embedding computation and coefficient-linear affine counit), and paragraph 3
(equality by transposition) (blueprint: lem-coef-finite-free-dualizing-local-global-mate).

The affine space is the existing ordered coordinate tower, canonically isomorphic to affine
space. Its right functor and adjunction are the Kummer-trace-normalized ones. In particular
`orderedAffineRightIso` identifies its value at the coefficient unit with the ordinary
Tate power shifted by twice the dimension. All right adjoints below are quantified with
their adjunctions: no extra choice of a dualizing object or of its counit is made.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.FiniteFreeDualizing

/-- Closed compact support with the identity open part is ordinary derived direct image.
Source: parent proof paragraph 1, closed-embedding computation
(blueprint: lem-coef-finite-free-dualizing-local-global-mate). -/
def closedSupportIso (R : Type (u + 1)) [CommRing R]
    {V T : Scheme.{u}} (i : V ⟶ T) [IsClosedImmersion i] :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R)
        (Compactification.ofIsProper i) ≅
      (lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor :=
  Functor.isoWhiskerRight
      (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} R) V) _ ≪≫
    Functor.leftUnitor _

/-- The canonical compact-support comparison from a closed chart followed by the ordered
coordinate tower. The first factor removes the identity open part, the second uses the
existing ordered affine comparison, and the last three use compatible composition and
common refinement. Source: parent proof paragraph 1, local closed-embedding computation
(blueprint: lem-coef-finite-free-dualizing-local-global-mate). -/
def chartLeftIso (R : Type (u + 1)) [CommRing R] [Finite R]
    {V S : Scheme.{u}} [IsNoetherian V] [IsNoetherian S]
    (r : ℕ) (i : V ⟶ affineTraceTower S r) [IsClosedImmersion i]
    (c : Compactification (affineTraceProjection S r))
    (d : Compactification (i ≫ affineTraceProjection S r)) :
    (lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor ⋙ affineTraceLeft R S r ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) d :=
  let e := d.ofComp c
  Functor.isoWhiskerRight (closedSupportIso R i).symm _ ≪≫
    Functor.isoWhiskerLeft _ (ProEtale.reductionEtaleAffineLeftIso R S r c) ≪≫
    Functor.isoWhiskerRight
      (rightDerivedLowerShriekOfCompactificationIso R
        (Compactification.ofIsProper i) e.restrict) _ ≪≫
    rightDerivedLowerShriekOfCompactificationCompIso R c e ≪≫
    rightDerivedLowerShriekOfCompactificationIso R (c.comp e) d

/-- The ordinary closed-shriek scalar mate, transposed from the inverse ordinary
proper direct-image comparison followed by scalar extension of the exceptional counit.
Source: parent proof paragraph 1, closed exceptional comparison with the same counit map
(blueprint: lem-coef-finite-free-dualizing-local-global-mate). -/
def closedMate {R A : Type (u + 1)} [CommRing R] [CommRing A] [Finite R] [Finite A]
    (φ : R →+* A) {V T : Scheme.{u}} [IsNoetherian V] [IsNoetherian T]
    (i : V ⟶ T) [IsClosedImmersion i]
    (HR : DerivedCategoryModule R T ⥤ DerivedCategoryModule R V)
    (HA : DerivedCategoryModule A T ⥤ DerivedCategoryModule A V)
    (aR : (lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor ⊣ HR)
    (aA : (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor ⊣ HA)
    (M : DerivedCategoryModule R T) :
    (scalarExtension φ V).obj (HR.obj M) ⟶ HA.obj ((scalarExtension φ T).obj M) :=
  letI := (properFiniteCoefficientExtension φ i).1 (HR.obj M)
  aA.homEquiv _ _
    (inv ((scalarMate φ i).app (HR.obj M)) ≫ (scalarExtension φ T).map (aR.counit.app M))

/-- Counit-preserving restriction to a closed affine chart. The right adjoint on the chart
is the composite of the ordered normalized affine adjunction and the ordinary closed
adjunction. The unique locality isomorphism supplies its restriction comparison.
Source: parent proof paragraphs 1 and 3
(blueprint: lem-coef-finite-free-dualizing-local-global-mate). -/
def chartRestrictionIso (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hR : (N : R) = 0)
    (t : OrdinaryFiniteTwistTransport R N hR)
    (P : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum R N hR t T hT)
    {V X S : Scheme.{u}} [IsNoetherian V] [IsNoetherian X] [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (f : X ⟶ S) (v : V ⟶ X)
    [Etale v] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (r : ℕ) (i : V ⟶ affineTraceTower S r) [IsClosedImmersion i]
    (h : v ≫ f = i ≫ affineTraceProjection S r)
    (cf : Compactification f) (cq : Compactification (affineTraceProjection S r))
    (cg : Compactification (i ≫ affineTraceProjection S r))
    (Hf : DerivedCategoryModule R S ⥤ DerivedCategoryModule R X)
    (Hi : DerivedCategoryModule R (affineTraceTower S r) ⥤ DerivedCategoryModule R V)
    (af : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cf ⊣ Hf)
    (ai : (lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor ⊣ Hi) :
    Hf ⋙ (upperStar (ModuleCat.{u + 1} R) v).mapDerivedCategory ≅
      affineTraceRight R N hR S r ⋙ Hi :=
  (existsUnique_etaleAmbientAdjointLocalityIso R v f cf (cg.copy h) Hf
    (affineTraceRight R N hR S r ⋙ Hi) af
    ((ai.comp (affineTraceAdjunction R N hR t P S hS r)).ofNatIsoLeft
      (chartLeftIso R r i cq cg))).choose

/-- The affine coefficient map at the coefficient unit. The recursive scalar comparison
is ordinary Tate balancing in the ordered Kummer normal form; its last factor identifies
scalar extension of the coefficient unit with the new coefficient unit.
Source: parent proof paragraph 1, Tate and coefficient-linear affine counit sentence
(blueprint: lem-coef-finite-free-dualizing-local-global-mate). -/
def affineUnitScalarIso
    {R A : Type (u + 1)} [CommRing R] [CommRing A]
    (φ : R →+* A) (N : ℕ) (hR : (N : R) = 0) (hA : (N : A) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (r : ℕ) :
    (scalarExtension φ (affineTraceTower S r)).obj
        ((affineTraceRight R N hR S r).obj (constantComplex R S)) ≅
      (affineTraceRight A N hA S r).obj (constantComplex A S) :=
  ProEtale.reductionEtaleAffineScalarIso φ S N hR hA hS r (constantComplex R S) ≪≫
    (affineTraceRight A N hA S r).mapIso (ExceptionalCoefficients.unitIso φ S)

/-- The global finite-free counit transpose equals the closed chart mate after the unique
counit-preserving locality identifications. Quantifying over every affine etale chart
also asserts that all its chart maps are restrictions of this one global morphism;
restriction again to an overlap therefore gives the same morphism by either chart.

Source: parent lem-coef-finite-free-extension.proof.md, paragraphs 1 and 3
(blueprint: lem-coef-finite-free-dualizing-local-global-mate).

Proof: (1) finite-free proper comparison and exact open balancing make the canonical
compact-support coefficient comparison invertible on every unbounded input. For a closed
map the inverse direct-image comparison and the exceptional counit give `closedMate`.
(2) The scalar squares commute with direct-image and open composition, restriction
exchange, and graph-normalized etale sum extension. Paste these squares along the
canonical common-refinement and composition maps. (3) Transpose under etale sum extension
and the global compact-support adjunction: the restriction of the global mate is the
mate for the restricted structural morphism, with the locality counit normalization.
(4) On the ordered affine tower, root-of-unity balancing and coefficient-linearity of
the normalized affine counit identify this mate at the unit with `affineUnitScalarIso`.
(5) Compose the closed and affine adjunctions. Their scalar square is the paste of the
two constituent squares, so its mate is the closed mate followed by the closed right
adjoint applied to the affine scalar isomorphism. Its transpose is exactly that in
(3); injectivity of the adjunction Hom bijection proves the displayed equality.
(6) Pull these equalities back to any overlap: each chart map is already the restriction
of the same global map. This does not assert descent or uniqueness for arbitrary derived
morphisms from their values on a cover. -/
theorem localGlobal_mate
    {R A : Type (u + 1)} [CommRing R] [CommRing A] [Finite R] [Finite A]
    (φ : R →+* A) (hfree : @Module.Free R A _ _ (Module.compHom A φ))
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0) (hA : (N : A) = 0)
    (tR : OrdinaryFiniteTwistTransport R N hR)
    (tA : OrdinaryFiniteTwistTransport A N hA)
    (PR : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum R N hR tR T hT)
    (PA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA tA T hT)
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (f : X ⟶ S)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (cf : Compactification f)
    (HR : DerivedCategoryModule R S ⥤ DerivedCategoryModule R X)
    (HA : DerivedCategoryModule A S ⥤ DerivedCategoryModule A X)
    (aR : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cf ⊣ HR)
    (aA : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf ⊣ HA) :
    (∀ L : DerivedCategoryModule R X,
      IsIso (ExceptionalCoefficients.compactSupportMap φ cf L)) ∧
    ∀ {V : Scheme.{u}} [IsNoetherian V] [IsAffine V]
      (v : V ⟶ X) [Etale v] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
      (r : ℕ) (i : V ⟶ affineTraceTower S r) [IsClosedImmersion i]
      (h : v ≫ f = i ≫ affineTraceProjection S r)
      (cq : Compactification (affineTraceProjection S r))
      (cg : Compactification (i ≫ affineTraceProjection S r))
      (IR : DerivedCategoryModule R (affineTraceTower S r) ⥤ DerivedCategoryModule R V)
      (IA : DerivedCategoryModule A (affineTraceTower S r) ⥤ DerivedCategoryModule A V)
      (bR : (lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor ⊣ IR)
      (bA : (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor ⊣ IA),
      letI : IsNoetherian (affineTraceTower S r) := affineTraceNoetherian S r
      (scalarPullbackIso φ v).inv.app (HR.obj (constantComplex R S)) ≫
        (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.map
          (DualizingOpenMate.globalMate φ cf HR HA aR aA) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v).hom.app
          (HA.obj (constantComplex A S)) ≫
        (chartRestrictionIso A N hA tA PA hS f v r i h cf cq cg HA IA aA bA).hom.app
          (constantComplex A S) =
      (scalarExtension φ V).map
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} R) v).hom.app
              (HR.obj (constantComplex R S)) ≫
            (chartRestrictionIso R N hR tR PR hS f v r i h cf cq cg HR IR aR bR).hom.app
              (constantComplex R S)) ≫
        closedMate φ i IR IA bR bA
          ((affineTraceRight R N hR S r).obj (constantComplex R S)) ≫
        IA.map (affineUnitScalarIso φ N hR hA S hS r).hom := by
  sorry

end AlgebraicGeometry.Etale.FiniteFreeDualizing
