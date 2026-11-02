/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.ModuleRingedToposDerivedComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperPasting
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.Supporting.AdjunctConjugateOpenFactor
import WeilConjectures.CategoryTheory.SixFunctors.ResolvingDerivedAdjunction

/-! # Ringed proper/open mate normalization

Source: Stacks Project, sites-cohomology.tex, Tags 0D6G and 07A7; categories.tex,
Tag 0DV0; latest blueprint sk-thm-purity-transport, proof Step 3
(blueprint: lem-pur-condensed-ringed-proper-open-mate-normalization).

The right-derived comparison and the Hom formula below fix the actual derived adjunction.
In particular no preservation of K-injectives by direct image, and no invertibility of
an arbitrary structural ring map, is assumed.

The seven proof steps are: (1) identify the localized pro-etale sites and construct
the sectionwise restriction for the structural ring map; (2) localize it on
K-injectives; (3) check the ordinary Hom-square and its mate normalization; (4) use
flat-term K-flat representatives to identify the inverse normalized beta; (5) identify
the localized restriction with the conjugate and compute its pullback-composition
transpose; (6) apply the adjunct-conjugate factor identity with the actual open unit;
(7) transport all units, counits, compositors, the restriction, and the proper mate
through `condensed_module_ringed_derived_comparison`, `openLocalization`, and
`condensedOpenProperPasting`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
open SheafOfModules.OpenTensorNormalization

namespace SheafOfModules.ProperOpenMateNormalization

/-- Sectionwise direct image is additive, with Mathlib's existing structure.
Source: Stacks 03D7
(blueprint: lem-pur-condensed-ringed-proper-open-mate-normalization). -/
instance directAdditive {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology .ordinary Y) CommRingCat.{u + 1})
    (S : Sheaf (topology .ordinary X) CommRingCat.{u + 1})
    (c : R ⟶ ((baseChange .ordinary f).sheafPushforwardContinuous CommRingCat.{u + 1}
      (topology .ordinary Y) (topology .ordinary X)).obj S) :
    (direct .ordinary f R S c).Additive where
  map_add := by intros; rfl

/-- The K-injective direct image with its universal comparison and the derived adjunction
normalized on every cochain map. These conditions specify the canonical derived functor
and adjunction up to their unique comparison, rather than selecting an arbitrary adjunction.
Source: Stacks 070I, 07A6 and 07A7
(blueprint: lem-pur-condensed-ringed-proper-open-mate-normalization). -/
structure DirectModel
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf K CommRingCat.{u + 1}}
    {V : Mod S ⥤ Mod R} [V.Additive] (p : Pullback R S V) where
  functor : Der S ⥤ Der R
  comparison : V.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ functor
  universal : functor.IsRightDerivedFunctor comparison
    (HomologicalComplex.quasiIso (Mod S) (.up ℤ))
  injective : ∀ I : CochainComplex (Mod S) ℤ, I.IsKInjective →
    IsIso (comparison.app I)
  adjunction : p.derived ⊣ functor
  hom : ∀ (P : CochainComplex (Mod R) ℤ) (I : CochainComplex (Mod S) ℤ)
      (f : (p.ordinary.mapHomologicalComplex (.up ℤ)).obj P ⟶ I),
    adjunction.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)
        (derivedPullbackComplexComparison p.ordinary p.derived p.epsilon P ≫
          DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((p.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv P I f) ≫
        comparison.app I

/-- The specified right-adjoint conjugate of inverse beta, with the composite adjunctions
in their actual order. Source: Stacks 07A7 and 0DV0
(blueprint: lem-pur-condensed-ringed-proper-open-mate-normalization). -/
def conjugate {d : Input.{u} .ordinary} {t : SiteSquare d} {o : Operations d t}
    (a : Assertion o) (gp : DirectModel o.gPull) (gr : DirectModel o.gUPull) :
    gp.functor ⋙ o.opens.jStar ≅ o.opens.jStar' ⋙ gr.functor :=
  conjugateIsoEquiv (o.opens.adj.comp gp.adjunction)
    (gr.adjunction.comp o.opens.adj') a.beta.symm

/-- Lambda is this conjugate on extension by zero followed by the inverse actual open
unit. Source: Stacks 0D6G and 07A7
(blueprint: lem-pur-condensed-ringed-proper-open-mate-normalization). -/
def restriction {d : Input.{u} .ordinary} {t : SiteSquare d} {o : Operations d t}
    (a : Assertion o) (gp : DirectModel o.gPull) (gr : DirectModel o.gUPull) :
    (o.opens.jShriek' ⋙ gp.functor) ⋙ o.opens.jStar ≅ gr.functor :=
  let e : 𝟭 _ ≅ o.opens.jShriek' ⋙ o.opens.jStar' :=
    NatIso.ofComponents (fun M ↦ @asIso _ _ _ _ (o.opens.adj'.unit.app M) (a.unit' M))
      (fun {_ _} f ↦ o.opens.adj'.unit.naturality f)
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft o.opens.jShriek' (conjugate a gp gr) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e.symm gr.functor ≪≫
    Functor.leftUnitor _

/-- The proper-adjunction mate, before taking its open adjunct.
Source: Stacks 07A7, actual unit--beta--counit formula
(blueprint: lem-pur-condensed-ringed-proper-open-mate-normalization). -/
def gamma {d : Input.{u} .ordinary} {t : SiteSquare d} {o : Operations d t}
    (a : Assertion o) (gp : DirectModel o.gPull) (gr : DirectModel o.gUPull) :
    gr.functor ⋙ o.opens.jShriek ⟶ o.opens.jShriek' ⋙ gp.functor :=
  (mateEquiv gr.adjunction gp.adjunction
    (TwoSquare.mk _ _ _ _ a.beta.hom)).natTrans

/-- The complete normalization for arbitrary structural ring maps on the Cartesian
proper/open square, on the entire unbounded module derived categories.
Source: Stacks 0D6G, 08FI, 07A6, 07A7 and 0DV0
(blueprint: lem-pur-condensed-ringed-proper-open-mate-normalization).

Proof plan.
1. Identify the two pro-etale slice sites. The fibre-product identification gives
   o.rightSquare, linear for the restricted structural ring map, with o.rightSections.
2. Resolve the input by a K-injective I. Exact open restriction preserves K-injectives,
   so both right-derived images are computed by the two ordinary direct images of I.
   Localize o.rightSquare degreewise; homotopy classes give naturality and independence
   of the resolution. This is precisely the representative equation below.
3. The ordinary Hom-square sends postcomposition by o.rightSquare to precomposition
   by inverse open beta. Its scalar actions are the ordinary ringed module actions.
4. Resolve the left input by a flat-term K-flat P. Open extension preserves K-flatness
   and flat terms. The normalized pullback compositor and open adjunction compute
   inverse beta by that same ordinary transpose on P.
5. Use the cochain Hom formula in DirectModel.hom for both composite adjunctions.
   The ordinary Hom-square descends to the derived Hom-square. Yoneda identifies its
   right transformation with conjugate. Expanding the transpose gives theta inverse
   followed by restriction of the proper counit, as in the second equation below.
6. Apply adjunct_transport with the identity extra open factor and f the r-counit.
   Inverse beta cancels beta and the adjunction triangle gives the identity. Since
   lambda is invertible, gamma is the open adjunct of its inverse. All constructions
   are natural transformations on the full unbounded categories.
-/
theorem ringedProperOpenMateNormalization (d : Input.{u} .ordinary)
    [QuasiCompact d.j] [QuasiCompact d.j'] [IsProper d.g] [IsProper d.gU]
    (t : SiteSquare d) (o : Operations d t) (a : Assertion o) :
    ∃ (gp : DirectModel o.gPull) (gr : DirectModel o.gUPull),
      (∀ (I : CochainComplex (Mod d.S) ℤ), I.IsKInjective →
        (restrict .ordinary d.j d.R).mapDerivedCategoryFactors.inv.app
            ((direct .ordinary d.g d.R d.S d.coefficient).mapHomologicalComplex
              (.up ℤ) |>.obj I) ≫
          o.opens.jStar.map (gp.comparison.app I) ≫
          (conjugate a gp gr).hom.app (DerivedCategory.Q.obj I) ≫
          gr.functor.map ((restrict .ordinary d.j' d.S).mapDerivedCategoryFactors.hom.app I) =
        DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex o.rightSquare.hom (.up ℤ)).app I) ≫
          gr.comparison.app
            (((restrict .ordinary d.j' d.S).mapHomologicalComplex (.up ℤ)).obj I)) ∧
      (∀ N : Der d.S,
        gr.adjunction.homEquiv _ _
          (o.theta.inv.app (gp.functor.obj N) ≫
            o.opens.jStar'.map (gp.adjunction.counit.app N)) =
          (conjugate a gp gr).hom.app N) ∧
      (∀ M : Der (restrictRing .ordinary d.j' d.S),
        o.opens.adj.homEquiv _ _ ((gamma a gp gr).app M) ≫
            (restriction a gp gr).hom.app M =
          𝟙 (gr.functor.obj M) ∧
        (gamma a gp gr).app M =
          (o.opens.adj.homEquiv _ _).symm ((restriction a gp gr).inv.app M) ∧
        (gamma a gp gr).app M =
          gp.adjunction.unit.app (o.opens.jShriek.obj (gr.functor.obj M)) ≫
            gp.functor.map (a.beta.hom.app (gr.functor.obj M)) ≫
            gp.functor.map (o.opens.jShriek'.map (gr.adjunction.counit.app M))) := by
  sorry

end SheafOfModules.ProperOpenMateNormalization

namespace AlgebraicGeometry.ProEtale.CondensedRing.ProperOpenMateNormalization

open ModuleRingedComparison
open CondensedOpenProper

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ Z)]

/-- The section pullback comparison in the exact presentation of total pullback.
Its first factor is the canonical K-flat-to-termwise comparison, so this changes no
adjunction normalization. Source: Stacks 07A6; internal/section comparison theorem
(blueprint: lem-pur-condensed-ringed-proper-open-mate-normalization). -/
def exactPullComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P Λ f ⋙ (derivedEquivalence Λ X).functor ≅
      (derivedEquivalence Λ Y).functor ⋙ derivedPullback Λ f :=
  Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm _ ≪≫
    derivedPullComparison Λ f

/-- The ringed conjugate uses the independently derived section-module adjunctions,
not adjunctions transported by definition from internal modules. Source: Stacks 07A6/07A7
(blueprint: lem-pur-condensed-ringed-proper-open-mate-normalization). -/
def sectionConjugate {V W S T : Scheme.{u}} {k : V ⟶ W} {r : V ⟶ S}
    {p : W ⟶ T} {i : S ⟶ T} [IsOpenImmersion k] [IsOpenImmersion i]
    (β : derivedExtension Λ i ⋙ derivedPullback Λ p ≅
      derivedPullback Λ r ⋙ derivedExtension Λ k) :
    derivedPushforward Λ p ⋙ derivedPullback Λ i ≅
      derivedPullback Λ k ⋙ derivedPushforward Λ r :=
  conjugateIsoEquiv ((derivedOpenAdjunction Λ i).comp (derivedAdjunction Λ p))
    ((derivedAdjunction Λ r).comp (derivedOpenAdjunction Λ k)) β.symm

/-- The section proper mate is the unit--beta--counit map for the actual ringed
adjunctions. Source: Stacks 07A7
(blueprint: lem-pur-condensed-ringed-proper-open-mate-normalization). -/
def sectionGamma {V W S T : Scheme.{u}} {k : V ⟶ W} {r : V ⟶ S}
    {p : W ⟶ T} {i : S ⟶ T} [IsOpenImmersion k] [IsOpenImmersion i]
    (β : derivedExtension Λ i ⋙ derivedPullback Λ p ≅
      derivedPullback Λ r ⋙ derivedExtension Λ k) :
    derivedPushforward Λ r ⋙ derivedExtension Λ i ⟶
      derivedExtension Λ k ⋙ derivedPushforward Λ p :=
  (mateEquiv (derivedAdjunction Λ r) (derivedAdjunction Λ p)
    (TwoSquare.mk _ _ _ _ β.hom)).natTrans

/-- The internal proper-adjunction mate uses the exact presentation of total pullback.
Source: Stacks 07A7; normalized open exchange of the proper/open pasting theorem
(blueprint: lem-pur-condensed-ringed-proper-open-mate-normalization). -/
def internalGamma {V W S T : Scheme.{u}} {k : V ⟶ W} {r : V ⟶ S}
    {p : W ⟶ T} {i : S ⟶ T} [IsOpenImmersion k] [IsOpenImmersion i]
    (β : J Λ i ⋙ P Λ p ≅ P Λ r ⋙ J Λ k) :
    R Λ r ⋙ J Λ i ⟶ J Λ k ⋙ R Λ p :=
  (mateEquiv (upperStarLowerStarAdjunction Λ r).mapDerivedCategoryRightDerivedAdjunction
    (upperStarLowerStarAdjunction Λ p).mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ β.hom)).natTrans

set_option maxHeartbeats 1600000 in
-- The four independent section-equivalence comparisons retain their full coefficient data.
/-- For admissible pulled-back condensed coefficients, the same normalized conjugate
and proper mate agree with the specified internal open-restriction and pasting maps.
The first equation normalizes the inverse section beta by the actual open unit and
canonical pullback compositors, exactly as Assertion.beta_inverse. The second equation
asserts that this normalized comparison is carried to the specified internal comparison.
Source: latest blueprint sk-thm-purity-transport, Step 3; Stacks 07A6/07A7, 0D6G, 0DV0
(blueprint: lem-pur-condensed-ringed-proper-open-mate-normalization).

Proof plan.
7. Apply the internal/section comparison to all four arrows. It identifies the ordinary
   and derived adjunction Hom bijections, their units and counits, and the canonical
   pullback compositors. Its open clause also identifies extension by zero. Hence the
   first equation is the section open-unit transpose, with the canonical geometric
   compositors and the equality of the two scheme composites. The comparison preserves
   this transpose, so the normalized inverse beta agrees with the specified internal
   inverse comparison, giving the second equation.
   Conjugation commutes with these normalized adjunction comparisons. The ringed
   representative calculation and canonical pullback transpose identify the internal
   conjugate with derivedDirectImageOpenRestriction, giving the next two equations.
   The inverse-open-unit restriction of the proper/open pasting theorem is therefore
   exactly lambda. Its gamma is the open adjunct of inverse lambda. Injectivity of the
   open Hom bijection and the preceding ringed identity identify it with the proper
   mate, giving the fifth equation. The last equation transports this actual proper
   mate through the same section comparisons. Every equation holds on all unbounded
   objects, before imposing any constructibility condition.
-/
theorem condensedProperOpenMateNormalization (_hΛ : IsAdmissibleCoefficient Λ)
    (ℓ p₀ : ℕ) [Fact ℓ.Prime] (F : Type u) [Field F] [CharP F p₀]
    (_hp : 0 < p₀) (_hne : p₀ ≠ ℓ)
    {V W S T : Over (Scheme.Spec.obj (op (CommRingCat.of F)))}
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k.left] [QuasiCompact k.left]
    [IsOpenImmersion i.left] [QuasiCompact i.left]
    [IsProper p.left] [IsProper r.left]
    (sq : IsPullback k.left r.left p.left i.left) (a : Pasting Λ) :
    ∃ β : derivedExtension Λ i.left ⋙ derivedPullback Λ p.left ≅
        derivedPullback Λ r.left ⋙ derivedExtension Λ k.left,
      (∀ M : DerivedCategory (modules Λ S.left),
        (derivedOpenAdjunction Λ k.left).homEquiv _ _ (β.inv.app M) =
          (derivedPullback Λ r.left).map ((derivedOpenAdjunction Λ i.left).unit.app M) ≫
            (derivedPullbackComposition Λ r.left i.left).inv.app
              ((derivedExtension Λ i.left).obj M) ≫
            (eqToIso (congrArg
              (fun f : V.left ⟶ T.left ↦ derivedPullback Λ f) sq.toCommSq.w.symm)).hom.app
                ((derivedExtension Λ i.left).obj M) ≫
            (derivedPullbackComposition Λ k.left p.left).hom.app
              ((derivedExtension Λ i.left).obj M)) ∧
      (∀ M : D Λ S.left,
        (derivedEquivalence Λ W.left).functor.map ((a.B sq.flip).hom.app M) ≫
            (derivedExtensionComparison Λ k.left).hom.app ((P Λ r.left).obj M) ≫
            (derivedExtension Λ k.left).map ((exactPullComparison Λ r.left).hom.app M) =
          (exactPullComparison Λ p.left).hom.app ((J Λ i.left).obj M) ≫
            (derivedPullback Λ p.left).map ((derivedExtensionComparison Λ i.left).hom.app M) ≫
            β.hom.app ((derivedEquivalence Λ S.left).functor.obj M)) ∧
      (conjugateIsoEquiv
          ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i.left).comp
            (upperStarLowerStarAdjunction Λ p.left).mapDerivedCategoryRightDerivedAdjunction)
          ((upperStarLowerStarAdjunction Λ r.left).mapDerivedCategoryRightDerivedAdjunction.comp
            (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ k.left))
          (a.B sq.flip).symm).hom = derivedDirectImageOpenRestriction Λ sq.toCommSq ∧
      (∀ N : D Λ W.left,
        (derivedEquivalence Λ S.left).functor.map
            ((derivedDirectImageOpenRestriction Λ sq.toCommSq).app N) ≫
            (derivedPushComparison Λ r.left).hom.app ((P Λ k.left).obj N) ≫
            (derivedPushforward Λ r.left).map ((exactPullComparison Λ k.left).hom.app N) =
          (exactPullComparison Λ i.left).hom.app ((R Λ p.left).obj N) ≫
            (derivedPullback Λ i.left).map ((derivedPushComparison Λ p.left).hom.app N) ≫
            (sectionConjugate Λ β).hom.app ((derivedEquivalence Λ W.left).functor.obj N)) ∧
      internalGamma Λ (a.B sq.flip) = CondensedOpenProper.gamma Λ a.units sq.toCommSq ∧
      (∀ M : D Λ V.left,
        (derivedEquivalence Λ T.left).functor.map ((internalGamma Λ (a.B sq.flip)).app M) ≫
            (derivedPushComparison Λ p.left).hom.app ((J Λ k.left).obj M) ≫
            (derivedPushforward Λ p.left).map
              ((derivedExtensionComparison Λ k.left).hom.app M) =
          (derivedExtensionComparison Λ i.left).hom.app ((R Λ r.left).obj M) ≫
            (derivedExtension Λ i.left).map ((derivedPushComparison Λ r.left).hom.app M) ≫
            (sectionGamma Λ β).app ((derivedEquivalence Λ V.left).functor.obj M)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.ProperOpenMateNormalization
