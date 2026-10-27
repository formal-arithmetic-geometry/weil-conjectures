/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.CategoryTheory.DerivedColimitBar
public import Sheaf.CategoryTheory.ContinuousCocontinuousDerivedShriek
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Sheaf.CategoryTheory.DerivedCategory.BoundedAboveAcyclicComputation

/-!
# Pointwise comma-category model for derived presheaf lower shriek

Source: Stacks Project, Cohomology on Sites, Tags 08PK, 08PG and 08PH
(blueprint: lem-trf-derived-shriek-comma-homology).

`StructuredArrow V u` is precisely `(V ↓ u)`, with its stated arrow direction.
The identity-cover sites have bottom Grothendieck topology; their module sheaves
are the ordinary module-presheaf categories used here. The model record asserts
existence of the canonical comparisons without selecting data from an unproved
existence theorem. Its resolution coordinates fix the chain identification on
all generators, including for nonprojective coefficient modules.
-/

@[expose] public noncomputable section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {E D : Type u} [SmallCategory E] [SmallCategory D]
  {R : Type u} [CommRing R]

/-- Precomposition is the exact inverse image on identity-cover sites.
Source: Stacks 08PH (blueprint: lem-trf-derived-shriek-comma-homology). -/
abbrev commaShriekInverse (f : E ⥤ D) :
    (Dᵒᵖ ⥤ ModuleCat.{u} R) ⥤ (Eᵒᵖ ⥤ ModuleCat.{u} R) :=
  (Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{u} R)).obj f.op

/-- Coefficients on `(V ↓ f)` are restriction along its projection to `E`.
Source: Stacks 08PK (blueprint: lem-trf-derived-shriek-comma-homology). -/
abbrev commaShriekCoefficients (f : E ⥤ D) (V : D) :
    (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ((StructuredArrow V f)ᵒᵖ ⥤ ModuleCat.{u} R) :=
  (Functor.whiskeringLeft (StructuredArrow V f)ᵒᵖ Eᵒᵖ (ModuleCat.{u} R)).obj
    (StructuredArrow.proj V f).op

/-- Evaluation at `V`, before or after descent to the derived category.
Source: Stacks 08PK (blueprint: lem-trf-derived-shriek-comma-homology). -/
abbrev commaShriekEvaluation (V : D) :
    (Dᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
  (evaluation Dᵒᵖ (ModuleCat.{u} R)).obj (op V)

/-- Restriction in `V` on derived evaluations is the unique localization of the
sectionwise restriction transformation. This is a construction, not a chosen map.
Source: Stacks 08PK (blueprint: lem-trf-derived-shriek-comma-homology). -/
def commaShriekDerivedRestriction {V W : D} (b : W ⟶ V) :
    (commaShriekEvaluation (R := R) V).mapDerivedCategory ⟶
      (commaShriekEvaluation (R := R) W).mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (Dᵒᵖ ⥤ ModuleCat.{u} R) (.up ℤ))
    ((commaShriekEvaluation (R := R) V).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    ((commaShriekEvaluation (R := R) W).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (commaShriekEvaluation (R := R) V).mapDerivedCategory
    (commaShriekEvaluation (R := R) W).mapDerivedCategory
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex
        ((evaluation Dᵒᵖ (ModuleCat.{u} R)).map b.op) (.up ℤ)) DerivedCategory.Q)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The full comma computation, including the normalized total derived adjunction,
resolution comparison, counit augmentation and both naturalities.
Source: Stacks 08PK, 08PG, 08PH, 07AC and 0DVC
(blueprint: lem-trf-derived-shriek-comma-homology).

The presheaf resolution is the sum of coefficient representables on each chain.
The coordinate isomorphisms and restriction formula specify these representables
without introducing a second definition of them. `chainFormula` fixes their image
under the ordinary left adjoint on every generator. `model_eq` then fixes the
precise canonical derived isomorphism, rather than only its homology or an arbitrary
isomorphism. All these data are asserted together by the existence theorem. -/
structure DerivedShriekCommaModel (B : CategoryColimitBarSystem.{u}) (f : E ⥤ D)
    (R : Type u) [CommRing R] where
  shriek : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ (Dᵒᵖ ⥤ ModuleCat.{u} R)
  [additive : shriek.Additive]
  adjunction : shriek ⊣ commaShriekInverse (R := R) f
  derived : DerivedCategory (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤
    DerivedCategory (Dᵒᵖ ⥤ ModuleCat.{u} R)
  comparison : DerivedCategory.Q ⋙ derived ⟶
    shriek.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  universal : derived.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (Eᵒᵖ ⥤ ModuleCat.{u} R) (.up ℤ))
  definedAt : ∀ X : HomotopyCategory (Eᵒᵖ ⥤ ModuleCat.{u} R) (.up ℤ),
    IsEssentiallyConstantProDiagram
      (MorphismProperty.Over.forget
        (HomotopyCategory.quasiIso (Eᵒᵖ ⥤ ModuleCat.{u} R) (.up ℤ)) ⊤ X ⋙
        Over.forget X ⋙ shriek.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
      (derived.obj (DerivedCategory.Qh.obj X))
  [commShift : derived.CommShift ℤ]
  triangulated : derived.IsTriangulated
  derivedAdjunction : derived ⊣ (commaShriekInverse (R := R) f).mapDerivedCategory
  normalization : ∀ (C : CochainComplex (Eᵒᵖ ⥤ ModuleCat.{u} R) ℤ)
    (N : CochainComplex (Dᵒᵖ ⥤ ModuleCat.{u} R) ℤ)
    (a : (shriek.mapHomologicalComplex (.up ℤ)).obj C ⟶ N),
    derivedAdjunction.homEquiv (DerivedCategory.Q.obj C) (DerivedCategory.Q.obj N)
      (comparison.app C ≫ DerivedCategory.Q.map a) =
      DerivedCategory.Q.map
        ((adjunction.mapHomologicalComplex (.up ℤ)).homEquiv C N a) ≫
      (commaShriekInverse (R := R) f).mapDerivedCategoryFactors.inv.app N
  resolution : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ CochainComplex (Eᵒᵖ ⥤ ModuleCat.{u} R) ℤ
  augmentation : resolution ⟶ CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R) 0
  quasiIso : ∀ F, QuasiIso (augmentation.app F)
  acyclic : ∀ F, IsIso (comparison.app (resolution.obj F))
  resolutionPositive : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (r : ℤ), 0 < r →
    IsZero ((resolution.obj F).X r)
  coordinates : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (n : ℕ) (W : E),
    ((resolution.obj F).X (-(n : ℤ))).obj (op W) ≅
      ∐ (fun c : Σ c : ComposableArrows E n, W ⟶ c.left ↦ F.obj (op c.1.right))
  resolutionRestriction : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (n : ℕ)
    (c : ComposableArrows E n) (W W' : E) (a : W ⟶ c.left) (b : W' ⟶ W)
    (x : F.obj (op c.right)),
    ((resolution.obj F).X (-(n : ℤ))).map b.op
      ((Sigma.ι _ ⟨c, a⟩ ≫ (coordinates F n W).inv) x) =
      (Sigma.ι _ ⟨c, b ≫ a⟩ ≫ (coordinates F n W').inv) x
  augmentationFormula : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (c : ComposableArrows E 0)
    (W : E) (a : W ⟶ c.left) (x : F.obj (op c.right)),
    (((augmentation.app F).f 0).app (op W) ≫
      ((HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 F 0 rfl).hom.app (op W)))
        ((Sigma.ι _ ⟨c, a⟩ ≫ (coordinates F 0 W).inv) x) =
      F.map (a ≫ c.map (homOfLE (Fin.le_last _))).op x
  chainIso : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (V : D),
    ((commaShriekEvaluation (R := R) V).mapHomologicalComplex (.up ℤ)).obj
      ((shriek.mapHomologicalComplex (.up ℤ)).obj (resolution.obj F)) ≅
        (B.models (StructuredArrow V f) R).bar.obj ((commaShriekCoefficients f V).obj F)
  chainFormula : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (V : D) (n : ℕ)
    (c : ComposableArrows (StructuredArrow V f) n)
    (x : F.obj (op c.right.right)),
    ((chainIso F V).hom.f (-(n : ℤ)))
      ((((adjunction.unit.app ((resolution.obj F).X (-(n : ℤ)))).app
        (op (c.left.right)) ≫
        (shriek.obj ((resolution.obj F).X (-(n : ℤ)))).map c.left.hom.op)
          ((Sigma.ι _ ⟨c ⋙ StructuredArrow.proj V f, 𝟙 _⟩ ≫
            (coordinates F n (c.left.right)).inv) x))) =
      (B.models (StructuredArrow V f) R).generator
        ((commaShriekCoefficients f V).obj F) n c x
  model : ∀ V : D,
    CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R) 0 ⋙ DerivedCategory.Q ⋙
      derived ⋙ (commaShriekEvaluation (R := R) V).mapDerivedCategory ≅
      commaShriekCoefficients f V ⋙ (B.models (StructuredArrow V f) R).bar ⋙
        DerivedCategory.Q
  model_eq : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (V : D),
    (model V).hom.app F =
      (commaShriekEvaluation (R := R) V).mapDerivedCategory.map
        (inv (derived.map (DerivedCategory.Q.map (augmentation.app F))) ≫
          comparison.app (resolution.obj F)) ≫
      (commaShriekEvaluation (R := R) V).mapDerivedCategoryFactors.hom.app
        ((shriek.mapHomologicalComplex (.up ℤ)).obj (resolution.obj F)) ≫
      DerivedCategory.Q.map (chainIso F V).hom
  restriction : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R) {V W : D} (_b : W ⟶ V),
    (B.models (StructuredArrow V f) R).bar.obj ((commaShriekCoefficients f V).obj F) ⟶
      (B.models (StructuredArrow W f) R).bar.obj ((commaShriekCoefficients f W).obj F)
  restrictionFormula : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R) {V W : D} (b : W ⟶ V)
    (n : ℕ) (c : ComposableArrows (StructuredArrow V f) n)
    (x : F.obj (op c.right.right)),
    ((restriction F b).f (-(n : ℤ)))
      ((B.models (StructuredArrow V f) R).generator
        ((commaShriekCoefficients f V).obj F) n c x) =
      (B.models (StructuredArrow W f) R).generator
        ((commaShriekCoefficients f W).obj F) n (c ⋙ StructuredArrow.map b) x
  restrictionNaturality : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R) {V W : D} (b : W ⟶ V),
    (commaShriekDerivedRestriction (R := R) b).app
      (derived.obj (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R) 0).obj F))) ≫
      (model W).hom.app F = (model V).hom.app F ≫ DerivedCategory.Q.map (restriction F b)
  positive : ∀ (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (V : D) (r : ℤ), 0 < r →
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) r).obj
      ((commaShriekEvaluation (R := R) V).mapDerivedCategory.obj
        (derived.obj (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R) 0).obj F)))))
  counitAugmentation : ∀ (K : Dᵒᵖ ⥤ ModuleCat.{u} R) (V : D),
    (B.models (StructuredArrow V f) R).bar.obj
      ((commaShriekCoefficients f V).obj ((commaShriekInverse f).obj K)) ⟶
        (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (K.obj (op V))
  counitFormula : ∀ (K : Dᵒᵖ ⥤ ModuleCat.{u} R) (V : D)
    (c : ComposableArrows (StructuredArrow V f) 0)
    (x : K.obj (op (f.obj c.right.right))),
    ((counitAugmentation K V).f 0 ≫
      (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 (K.obj (op V)) 0 rfl).hom)
        ((B.models (StructuredArrow V f) R).generator
          ((commaShriekCoefficients f V).obj ((commaShriekInverse f).obj K)) 0 c x) =
      K.map c.right.hom.op x
  counit_eq : ∀ (K : Dᵒᵖ ⥤ ModuleCat.{u} R) (V : D),
    (commaShriekEvaluation (R := R) V).mapDerivedCategory.map
      (derived.map (DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex
          (commaShriekInverse (R := R) f) (.up ℤ) 0).inv.app K) ≫
        (commaShriekInverse (R := R) f).mapDerivedCategoryFactors.inv.app
        ((CochainComplex.singleFunctor (Dᵒᵖ ⥤ ModuleCat.{u} R) 0).obj K)) ≫
        derivedAdjunction.counit.app (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (Dᵒᵖ ⥤ ModuleCat.{u} R) 0).obj K))) ≫
      (commaShriekEvaluation (R := R) V).mapDerivedCategoryFactors.hom.app
        ((CochainComplex.singleFunctor (Dᵒᵖ ⥤ ModuleCat.{u} R) 0).obj K) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex
          (commaShriekEvaluation (R := R) V) (.up ℤ) 0).hom.app K) =
      (model V).hom.app ((commaShriekInverse f).obj K) ≫
        DerivedCategory.Q.map (counitAugmentation K V)

  restrictionCoefficient : ∀ {F G : Eᵒᵖ ⥤ ModuleCat.{u} R} (t : F ⟶ G)
    {V W : D} (b : W ⟶ V),
    (B.models (StructuredArrow V f) R).bar.map ((commaShriekCoefficients f V).map t) ≫
      restriction G b = restriction F b ≫
        (B.models (StructuredArrow W f) R).bar.map ((commaShriekCoefficients f W).map t)
  counitRestriction : ∀ (K : Dᵒᵖ ⥤ ModuleCat.{u} R) {V W : D} (b : W ⟶ V),
    counitAugmentation K V ≫ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map
      (K.map b.op) = restriction ((commaShriekInverse f).obj K) b ≫ counitAugmentation K W
  counitCoefficient : ∀ {K L : Dᵒᵖ ⥤ ModuleCat.{u} R} (t : K ⟶ L) (V : D),
    (B.models (StructuredArrow V f) R).bar.map
      ((commaShriekCoefficients f V).map ((commaShriekInverse f).map t)) ≫
      counitAugmentation L V = counitAugmentation K V ≫
        (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map (t.app (op V))

/-- The ordinary left adjoint in the computation is the existing Mathlib left Kan
extension, with the canonical identification of left adjoints to precomposition.
Source: Stacks 08PH (blueprint: lem-trf-derived-shriek-comma-homology). -/
def DerivedShriekCommaModel.lanIso
    {B : CategoryColimitBarSystem.{u}} {f : E ⥤ D}
    (M : DerivedShriekCommaModel B f R) : M.shriek ≅ f.op.lan :=
  Adjunction.leftAdjointUniq M.adjunction (f.op.lanAdjunction (ModuleCat.{u} R))

/-- The nonpositive cohomology identifications obtained from the derived comma isomorphism.
Source: Stacks 08PK and 08PG
(blueprint: lem-trf-derived-shriek-comma-homology).

Apply the degree `-n` cohomology functor to `M.model V`, then use its standard
factorization through localization to read the right side as cohomology of the
actual bar complex. This is a construction from the derived isomorphism. -/
def DerivedShriekCommaModel.homologyIso
    {B : CategoryColimitBarSystem.{u}} {f : E ⥤ D}
    (M : DerivedShriekCommaModel B f R) (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (V : D) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-(n : ℤ))).obj
      ((commaShriekEvaluation (R := R) V).mapDerivedCategory.obj
        (M.derived.obj (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R) 0).obj F)))) ≅
    ((B.models (StructuredArrow V f) R).bar.obj
      ((commaShriekCoefficients f V).obj F)).homology (-(n : ℤ)) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-(n : ℤ))).mapIso
    ((M.model V).app F) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) (-(n : ℤ))).app _

/-- Derived left Kan extension of module presheaves is canonically computed pointwise
by the comma-category bar complex, compatibly with counits and restrictions.
Source: Stacks Project, Cohomology on Sites, Tags 08PK, 08PG and 08PH;
Tags 07AC and 0DVC for the normalized unbounded derived adjunction
(blueprint: lem-trf-derived-shriek-comma-homology).

Proof (all fourteen steps of the DAG proof):
1. Give both categories the singleton-isomorphism pretopology. Every presheaf is a
   sheaf, so kernels and cokernels are objectwise and both evaluation and
   precomposition are exact. Every functor is continuous and cocontinuous for
   these topologies. Apply lem-trf-continuous-cocontinuous-derived-shriek with the
   constant ring and identity ring map. Transport along the constant-ring module
   equivalences to obtain the ordinary left adjoint, its everywhere-defined total
   derived functor, universal comparison and normalized derived adjunction.
   The ordinary left adjoint is Lan along `f.op`, by its defining Hom bijection.
2. For an object U and module M, the presheaf L_U(M)(W) is the sum of M over
   arrows W → U. A map L_U(M) → H is determined by its identity summand at U.
   A linear map M → H(U) extends by (a,x) ↦ H(a)x; naturality proves that these
   two operations are inverse. This establishes the coefficient Yoneda adjunction.
3. Direct sums of module exact sequences are exact: lift each of the finitely many
   nonzero components of an element separately. Hence L_U is exact. If P is a
   projective module, the adjunction of step 2 lifts maps from L_U(P) across every
   objectwise epimorphism. The sum over (U,x), x ∈ H(U), of L_U(R) surjects onto H:
   at W, the identity summand belonging to (W,x) maps to x. Sums of projectives
   are projective by choosing a lift on each summand. Thus both presheaf categories
   have enough projectives, as do modules by the free-module surjection.
4. The ordinary adjunction identifies g_! L_U(M) with L_fU(M). Its map sends an
   arrow a to f(a), with unchanged coefficient, by the identity-summand formula.
   The same Hom bijection shows that g_! preserves sums and cokernels, so it is
   additive and right exact. This also fixes its generator maps explicitly.
5. For A = ∐ L_Uc(Mc), choose module projective resolutions Pc → Mc[0], all
   zero above zero, using lem-trf-bounded-above-acyclic-derived-computation.
   The sum of L_Uc(Pc) is a bounded-above projective resolution of A[0]. Its
   shriek image is the sum of L_fUc(Pc), again resolving g_! A[0], by exactness.
   The cited theorem inverts the comparison on this projective resolution.
   Naturality of the comparison and the two resolution quasi-isomorphisms then
   invert it on A[0]. No projectivity or flatness of Mc is required.
6. Form the augmented presheaf resolution whose degree -n is the sum, over
   chains Un → ... → U0, of L_Un(F(U0)). At W its coordinates are (b:W → Un,
   chain,x). The first face composes b with the next arrow, internal faces
   compose adjacent arrows, and the last face restricts x. Their alternating sum
   squares to zero, since deleting two vertices in either order agrees by
   associativity and functoriality; paired signs are opposite. The augmentation
   sends (b:W → U0,x) to F(b)x and kills the degree -1 differential.
7. At fixed W insert W at the front of each chain, with identity initial arrow;
   in augmented degree send x to (id_W,x). Deleting the inserted vertex is the
   identity; later deletions cancel the insertion after the corresponding old
   deletion. Thus ds+sd=1, including degree zero where ds+sα=1 and αs=1.
   The evaluated augmented complex is contractible, so its augmentation is an
   objectwise quasi-isomorphism. Objectwise homology makes it a presheaf
   quasi-isomorphism. No naturality of this contraction in W is asserted.
8. Every term is acyclic by step 5 and the resolution is zero above zero.
   Apply lem-trf-bounded-above-acyclic-derived-computation: the comparison on
   the resolution is invertible and the canonical identification is
   inv(Lg_! Qα) followed by that comparison. Naturality for augmented resolutions
   gives coefficient naturality of this exact map, not just a homology isomorphism.
9. The shriek image evaluated at V has generators (a:V → fUn, Un → ... → U0,x).
   Set an=a and aj-1=f(hj)aj. These are exactly chains of (V ↓ f). Conversely
   forget a0,...,an-1, which the comma equations uniquely determine. This is a
   bijection of indexing sets, with identical coefficient F(U0), hence a
   degreewise isomorphism with the specified model of lem-trf-derived-colimit-bar.
10. The first face carries an to f(hn)an, precisely the comma first face;
    internal faces compose the same arrows; the last face restricts by F(h1).
    The signs agree vertex by vertex. Hence the bijection is a chain isomorphism
    with `chainFormula`. Evaluation preserves quasi-isomorphisms and descends
    to derived categories. Applying it to step 8 gives `model_eq`.
11. Restriction along b:W → V sends (a,chain,x) to (ba,chain,x), exactly the
    functor StructuredArrow.map b with unchanged coefficient. A coefficient
    map t applies t_U0 to x, commuting with the last face by naturality and
    with the other faces directly. These formulas commute with each other.
    With step 8 they give the two naturalities of the derived identification.
12. Apply the degree -n cohomology functor to the derived isomorphism to get
    `homologyIso`. The bar complex has zero positive terms, so its positive
    cohomology and that of the derived evaluation vanish. Empty comma categories
    give empty sums in every degree, hence the zero complex as required.
13. For F=f⁻¹K, the adjoint of the resolution augmentation has degree-zero
    formula (a:V → fU,x) ↦ K(a)x, by step 2, and is zero in all other degrees.
    On a degree -1 generator its composite with the differential is
    K(f(h)a)x - K(a)K(f(h))x=0. It is therefore the specified chain augmentation.
14. The normalized derived Hom bijection sends Q(c) ε_B to Q(α).
    The defining property and naturality of the derived counit send e_K LQ(α)
    to the same Q(α). Injectivity of that bijection gives
    e_K LQ(α)=Q(c) ε_B, hence e_K=Q(c) i_F. Evaluate and use step 10 to obtain
    `counit_eq`. Functoriality K(ab)=K(b)K(a) and naturality of maps K → K'
    prove the asserted restriction and coefficient compatibility of the counit. -/
theorem derivedShriekCommaModel_exists (B : CategoryColimitBarSystem.{u})
    (f : E ⥤ D) (R : Type u) [CommRing R] :
    Nonempty (DerivedShriekCommaModel B f R) := by
  sorry

end CategoryTheory
