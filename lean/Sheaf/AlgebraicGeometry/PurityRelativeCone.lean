/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q82
-/
module

public import Sheaf.AlgebraicGeometry.RelativeEtaleCohomology
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Sheaf.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison
import Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections
import WeilConjectures.CategoryTheory.InjectiveSheafMonoRestriction
import Sheaf.CategoryTheory.SiteCohomologyPullback
import Sheaf.CategoryTheory.SiteLerayDegenerate
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence

/-!
# Relative section cones and supported cohomology

Source: Stacks Project, Cohomology on Sites, cohomology with support; blueprint
main-20261015, sec-smooth-purity/sk-prop-an/lem-pur-divisor-class.proof.md
(blueprint: lem-pur-divisor-relative-cone).

The structures below package equations, rather than choosing comparison maps from an
existence theorem. Their kernel and right-derived normalizations fix the identifications.
Object squares express both restriction to an etale neighbourhood and enlargement of
support, on the site of the original scheme, without changing sites by an implicit bridge.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex

namespace AlgebraicGeometry
namespace Etale
namespace RelativeCone

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)

/-- Evaluation on the given site. Source: Stacks, cohomology with support
(blueprint: lem-pur-divisor-relative-cone). -/
noncomputable abbrev evaluationFunctor (V : C) : Sheaf J AddCommGrpCat.{u + 1} ⥤
    AddCommGrpCat.{u + 1} :=
  sheafToPresheaf J _ ⋙ (evaluation _ _).obj (op V)

/-- Restriction on sections. Source: Stacks, cohomology with support
(blueprint: lem-pur-divisor-relative-cone). -/
noncomputable def restriction {V W : C} (f : W ⟶ V) :
    evaluationFunctor J V ⟶ evaluationFunctor J W :=
  Functor.whiskerLeft (sheafToPresheaf J _) ((evaluation _ _).map f.op)

/-- A section complex, extended by zero. This specializes to `relativeSections`.
Source: Stacks, cohomology with support (blueprint: lem-pur-divisor-relative-cone). -/
noncomputable abbrev sections (V : C)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℕ) :=
  (((evaluationFunctor J V).mapHomologicalComplex (.up ℕ)).obj I).extend
    ComplexShape.embeddingUpNat

/-- Restriction between the extended section complexes.
Source: Stacks, cohomology with support (blueprint: lem-pur-divisor-relative-cone). -/
noncomputable def restrictionComplex {V W : C} (f : W ⟶ V)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℕ) :
    sections J V I ⟶ sections J W I :=
  extendMap ((NatTrans.mapHomologicalComplex (restriction J f) _).app I)
    ComplexShape.embeddingUpNat

/-- The signed relative cone, on either site and over any object of that site.
Source: Stacks, cohomology with support (blueprint: lem-pur-divisor-relative-cone). -/
noncomputable abbrev fiber {V W : C} (f : W ⟶ V)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℕ) :=
  (CochainComplex.mappingCone (restrictionComplex J f I))⟦(-1 : ℤ)⟧

/-- The supported-section complex, using the dependency's single support functor.
Source: Stacks, cohomology with support (blueprint: lem-pur-divisor-relative-cone). -/
noncomputable abbrev supported {V W : C} (f : W ⟶ V)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℕ) :=
  (((Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f).mapHomologicalComplex
    (.up ℕ)).obj I).extend ComplexShape.embeddingUpNat

variable [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]

/-- The canonical computation isomorphism, including the extension-by-zero transport.
Source: Stacks Tag 09XP (blueprint: lem-pur-divisor-relative-cone). -/
noncomputable def computation (G : Sheaf J AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1})
    [G.Additive] {F : Sheaf J AddCommGrpCat.{u + 1}} (I : InjectiveResolution F) (q : ℕ) :
    (G.rightDerived q).obj F ≅
      ((((G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extend
        ComplexShape.embeddingUpNat).homology (q : ℤ)) :=
  I.isoRightDerivedObj G q ≪≫
    (((G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat (by rfl)).symm

/-- Forgetting support before deriving it.
Source: Stacks, cohomology with support (blueprint: lem-pur-divisor-relative-cone). -/
noncomputable def forgetSupport {V W : C} (f : W ⟶ V) :
    Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f ⟶ evaluationFunctor J V where
  app F := kernel.ι (F.obj.map f.op)
  naturality α := by simp [Sheaf.supportedSectionsFunctor, evaluationFunctor]

/-- The map of supported-section functors belonging to an actual object square.
Source: Stacks, support restriction (blueprint: lem-pur-divisor-relative-cone). -/
noncomputable def supportRestriction {V W V' W' : C} (f : W ⟶ V) (f' : W' ⟶ V')
    (v : V' ⟶ V) (w : W' ⟶ W) (h : f' ≫ v = w ≫ f) :
    Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f ⟶
      Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f' where
  app F := kernel.map _ _ (F.obj.map v.op) (F.obj.map w.op)
    (by simpa only [← Functor.map_comp, ← op_comp] using
      (congrArg (fun g ↦ F.obj.map g.op) h).symm)
  naturality F F' α := by
    apply equalizer.hom_ext
    dsimp [Sheaf.supportedSectionsFunctor]
    simp only [Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc]
    rw [← α.hom.naturality]

/-- A coefficient-resolution map evaluated on an object.
Source: Stacks Tag 09XP (blueprint: lem-pur-divisor-relative-cone). -/
noncomputable def coefficientMap (V : C)
    {I I' : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℕ} (φ : I ⟶ I') :
    sections J V I ⟶ sections J V I' :=
  extendMap (((evaluationFunctor J V).mapHomologicalComplex (.up ℕ)).map φ)
    ComplexShape.embeddingUpNat

end RelativeCone

namespace RelativeCone

/-- The first cone projection; the etale specialization is `relativeForgetComplex`.
Source: Stacks Tag 0G71 (blueprint: lem-pur-divisor-relative-cone). -/
noncomputable def projection {A B : CochainComplex AddCommGrpCat.{u + 1} ℤ} (r : A ⟶ B) :
    (CochainComplex.mappingCone r)⟦(-1 : ℤ)⟧ ⟶ A :=
  (CategoryTheory.shiftFunctor _ (-1 : ℤ)).map
      (CochainComplex.HomComplex.Cocycle.equivHomShift.symm (CochainComplex.mappingCone.fst r)) ≫
    (shiftFunctorAdd _ (1 : ℤ) (-1 : ℤ)).inv.app _ ≫
    (shiftFunctorZero _ ℤ).hom.app _

/-- The shifted cone inclusion, corresponding to `(0,-b)` in the signed model.
Source: Stacks Tag 0G71 (blueprint: lem-pur-divisor-relative-cone). -/
noncomputable def boundary {A B : CochainComplex AddCommGrpCat.{u + 1} ℤ} (r : A ⟶ B) :
    B⟦(-1 : ℤ)⟧ ⟶ (CochainComplex.mappingCone r)⟦(-1 : ℤ)⟧ :=
  (CategoryTheory.shiftFunctor _ (-1 : ℤ)).map (CochainComplex.mappingCone.inr r)

/-- Commutation with the two arrows of the relative triangle.
Source: Stacks Tag 0G78 (blueprint: lem-pur-divisor-relative-cone). -/
def TriangleSquare {A B A' B' : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (r' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ r' = r ≫ b) : Prop :=
  relativeFiberMap r r' a b h ≫ projection r' = projection r ≫ a ∧
  (CategoryTheory.shiftFunctor _ (-1 : ℤ)).map b ≫ boundary r' =
    boundary r ≫ relativeFiberMap r r' a b h

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
variable [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]

/-- Canonically normalized realization for a support pair and a supplied resolution.
The boundary field compares with the connecting map of the kernel short exact sequence;
the forget field compares with `R^q` of the actual kernel inclusion, rather than an
unconstrained map. Source: Stacks, cohomology with support
(blueprint: lem-pur-divisor-relative-cone). -/
structure Realization {V W : C} (f : W ⟶ V)
    {F : Sheaf J AddCommGrpCat.{u + 1}} (I : InjectiveResolution F) where
  kernelIso : supported J f I.cocomplex ≅ kernel (restrictionComplex J f I.cocomplex)
  kernel_components : ∀ n : ℕ,
    kernelIso.hom.f (n : ℤ) ≫ (kernel.ι (restrictionComplex J f I.cocomplex)).f n =
      ((((Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f).mapHomologicalComplex
        (.up ℕ)).obj I.cocomplex).extendXIso
        ComplexShape.embeddingUpNat (by rfl)).hom ≫
        kernel.ι ((I.cocomplex.X n).obj.map f.op) ≫
        ((((evaluationFunctor J V).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendXIso
          ComplexShape.embeddingUpNat (by rfl)).inv
  κ : kernel (restrictionComplex J f I.cocomplex) ⟶ fiber J f I.cocomplex
  κ_quasiIso : HomologicalComplex.quasiIso AddCommGrpCat.{u + 1} (.up ℤ) κ
  κ_components : ∀ n : ℤ,
    κ.f n ≫ ((CochainComplex.mappingCone (restrictionComplex J f I.cocomplex)).shiftFunctorObjXIso
      (-1) n (n - 1) (by omega)).hom ≫
      HomologicalComplex.homotopyCofiber.sndX (restrictionComplex J f I.cocomplex) (n - 1) = 0 ∧
    κ.f n ≫ ((CochainComplex.mappingCone (restrictionComplex J f I.cocomplex)).shiftFunctorObjXIso
      (-1) n (n - 1) (by omega)).hom ≫
      HomologicalComplex.homotopyCofiber.fstX (restrictionComplex J f I.cocomplex)
        (n - 1) n (by change n - 1 + 1 = n; omega) =
      (kernel.ι (restrictionComplex J f I.cocomplex)).f n
  exact : (ShortComplex.mk (kernel.ι (restrictionComplex J f I.cocomplex))
    (restrictionComplex J f I.cocomplex) (kernel.condition _)).ShortExact
  e : ∀ q : ℕ, (fiber J f I.cocomplex).homology q ≅
    ((Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f).rightDerived q).obj F
  normalization : ∀ q : ℕ,
    homologyMap kernelIso.hom (q : ℤ) ≫ homologyMap κ (q : ℤ) ≫ (e q).hom =
      (computation J (Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f) I q).inv
  forget : ∀ q : ℕ,
    (e q).hom ≫ (NatTrans.rightDerived (forgetSupport J f) q).app F =
      homologyMap (projection (restrictionComplex J f I.cocomplex)) (q : ℤ) ≫
        (computation J (evaluationFunctor J V) I q).inv
  localization : ∀ q : ℕ,
    homologyMap (boundary (restrictionComplex J f I.cocomplex)) (q : ℤ) ≫ (e q).hom =
      (CochainComplex.ShiftSequence.shiftIso AddCommGrpCat.{u + 1} (-1) (q : ℤ)
        ((q : ℤ) - 1) (by omega)).hom.app (sections J W I.cocomplex) ≫
      exact.δ ((q : ℤ) - 1) (q : ℤ) (by change (q : ℤ) - 1 + 1 = q; omega) ≫
      homologyMap kernelIso.inv (q : ℤ) ≫
      (computation J (Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f) I q).inv

/-- A compatible family of realizations on one site. Object squares include the pullback
square of an etale neighbourhood and the square `W' ⊆ W` with identity on the ambient
object. Coefficient lifts are arbitrary lifts of the given coefficient morphism, so the
identity-coefficient case states independence of the resolution and of its comparison map.
Source: Stacks, cohomology with support (blueprint: lem-pur-divisor-relative-cone). -/
structure System (P : ∀ {V W : C}, (W ⟶ V) → Prop) where
  realization : ∀ {V W : C} (f : W ⟶ V), P f →
    ∀ {F : Sheaf J AddCommGrpCat.{u + 1}} (I : InjectiveResolution F), Realization J f I
  coefficients : ∀ {V W : C} (f : W ⟶ V) (hf : P f)
    {F F' : Sheaf J AddCommGrpCat.{u + 1}} (α : F ⟶ F')
    (I : InjectiveResolution F) (I' : InjectiveResolution F')
    (φ : I.cocomplex ⟶ I'.cocomplex) (_hφ : I.ι.f 0 ≫ φ.f 0 = α ≫ I'.ι.f 0)
    (h : coefficientMap J V φ ≫ restrictionComplex J f I'.cocomplex =
      restrictionComplex J f I.cocomplex ≫ coefficientMap J W φ) (q : ℕ),
    homologyMap (relativeFiberMap _ _ (coefficientMap J V φ) (coefficientMap J W φ) h)
      (q : ℤ) ≫ ((realization f hf I').e q).hom =
    ((realization f hf I).e q).hom ≫
      ((Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f).rightDerived q).map α ∧
    TriangleSquare _ _ (coefficientMap J V φ) (coefficientMap J W φ) h
  objects : ∀ {V W V' W' : C} (f : W ⟶ V) (f' : W' ⟶ V') (hf : P f) (hf' : P f')
    (v : V' ⟶ V) (w : W' ⟶ W) (hs : f' ≫ v = w ≫ f)
    {F : Sheaf J AddCommGrpCat.{u + 1}} (I : InjectiveResolution F)
    (h : restrictionComplex J v I.cocomplex ≫ restrictionComplex J f' I.cocomplex =
      restrictionComplex J f I.cocomplex ≫ restrictionComplex J w I.cocomplex) (q : ℕ),
    homologyMap (relativeFiberMap _ _ (restrictionComplex J v I.cocomplex)
      (restrictionComplex J w I.cocomplex) h) (q : ℤ) ≫
      ((realization f' hf' I).e q).hom =
    ((realization f hf I).e q).hom ≫
      (NatTrans.rightDerived (supportRestriction J f f' v w hs) q).app F ∧
    TriangleSquare _ _ (restrictionComplex J v I.cocomplex)
      (restrictionComplex J w I.cocomplex) h

end RelativeCone

namespace RelativeCone

/-- The termwise pullback of the chosen etale resolution.
Source: blueprint comparison proof, Step 4 (blueprint: lem-pur-divisor-relative-cone). -/
noncomputable abbrev pulledResolution (T : Scheme.{u})
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :=
  ((AlgebraicGeometry.ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).mapHomologicalComplex
    (.up ℕ)).obj I

/-- The canonical section pullback: the comparison adjunction unit followed by a lift
of the coefficient map. Neither section arrow is existentially chosen.
Source: blueprint comparison proof, Step 4 (blueprint: lem-pur-divisor-relative-cone). -/
noncomputable def pullbackSections (T : Scheme.{u}) (V : T.Etale)
    {I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    {K : CochainComplex (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) ℕ}
    (β : pulledResolution T I ⟶ K) :
    sections T.smallEtaleTopology V I ⟶
      sections (Scheme.ProEt.topology T) ((Scheme.toProEt T).obj V) K :=
  extendMap (((evaluationFunctor T.smallEtaleTopology V).mapHomologicalComplex (.up ℕ)).map
    ((NatTrans.mapHomologicalComplex
      (AlgebraicGeometry.ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit _).app I ≫
      ((AlgebraicGeometry.ProEtale.comparisonLowerStar
          AddCommGrpCat.{u + 1} T).mapHomologicalComplex
        (.up ℕ)).map β)) ComplexShape.embeddingUpNat

/-- An augmented lift, including the arbitrary pro-etale coefficient map of the node's
last sentence. Source: blueprint comparison proof, Steps 4-5
(blueprint: lem-pur-divisor-relative-cone). -/
def IsLift (T : Scheme.{u})
    {F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {F' : Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}}
    (γ : (AlgebraicGeometry.ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj F ⟶ F')
    (I : InjectiveResolution F) (K : InjectiveResolution F')
    (β : pulledResolution T I.cocomplex ⟶ K.cocomplex) : Prop :=
  (AlgebraicGeometry.ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).map (I.ι.f 0) ≫
    β.f 0 = γ ≫ K.ι.f 0

/-- The full change-of-topology assertion. In addition to the comparison isomorphism,
this records its kernel normalization, projection and boundary squares, independence
of augmented lifts, restriction squares, and postcomposition by an arbitrary coefficient
morphism. Source: blueprint comparison proof, Steps 4-5
(blueprint: lem-pur-divisor-relative-cone). -/
structure TopologyComparison (T : Scheme.{u})
    (E : System T.smallEtaleTopology (fun {_ _} f ↦ IsOpenImmersion f.left))
    (P : System (Scheme.ProEt.topology T)
      (fun {V _} f ↦ IsOpenImmersion f.left ∧ Etale V.hom)) where
  lift_exists : ∀ (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1})
    (γ : (AlgebraicGeometry.ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj F ⟶ F')
    (I : InjectiveResolution F) (K : InjectiveResolution F'),
    ∃ β : pulledResolution T I.cocomplex ⟶ K.cocomplex, IsLift T γ I K β
  square : ∀ {V W : T.Etale} (f : W ⟶ V)
    {I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    {K : CochainComplex (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) ℕ}
    (β : pulledResolution T I ⟶ K),
    pullbackSections T V β ≫ restrictionComplex (Scheme.ProEt.topology T)
      ((Scheme.toProEt T).map f) K =
    restrictionComplex T.smallEtaleTopology f I ≫ pullbackSections T W β
  sections_isIso : ∀ (V : T.Etale)
    {F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}} (I : InjectiveResolution F)
    (K : InjectiveResolution
      ((AlgebraicGeometry.ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj F))
    (β : pulledResolution T I.cocomplex ⟶ K.cocomplex), IsLift T (𝟙 _) I K β →
    ∀ q : ℕ, IsIso (homologyMap (pullbackSections T V β) (q : ℤ))
  cone_isIso : ∀ {V W : T.Etale} (f : W ⟶ V) (_hf : IsOpenImmersion f.left)
    {F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}} (I : InjectiveResolution F)
    (K : InjectiveResolution
      ((AlgebraicGeometry.ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj F))
    (β : pulledResolution T I.cocomplex ⟶ K.cocomplex), IsLift T (𝟙 _) I K β →
    ∀ q : ℕ, IsIso (homologyMap (relativeFiberMap _ _
      (pullbackSections T V β) (pullbackSections T W β) (square f β)) (q : ℤ))
  support : ∀ {V W : T.Etale} (f : W ⟶ V) (hf : IsOpenImmersion f.left)
    {F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {F' : Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}}
    (γ : (AlgebraicGeometry.ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj F ⟶ F')
    (I : InjectiveResolution F) (K : InjectiveResolution F')
    (β : pulledResolution T I.cocomplex ⟶ K.cocomplex), IsLift T γ I K β → ∀ q : ℕ,
    ((E.realization f hf I).e q).inv ≫
      homologyMap (relativeFiberMap _ _ (pullbackSections T V β)
        (pullbackSections T W β) (square f β)) (q : ℤ) ≫
      ((P.realization ((Scheme.toProEt T).map f)
        ⟨hf, (by change Etale V.hom; infer_instance)⟩ K).e q).hom =
    (computation T.smallEtaleTopology
      (Sheaf.supportedSectionsFunctor T.smallEtaleTopology AddCommGrpCat.{u + 1} f) I q).hom ≫
    homologyMap (E.realization f hf I).kernelIso.hom (q : ℤ) ≫
    homologyMap (kernel.map _ _ (pullbackSections T V β) (pullbackSections T W β)
      (square f β).symm) (q : ℤ) ≫
    homologyMap (P.realization ((Scheme.toProEt T).map f)
        ⟨hf, (by change Etale V.hom; infer_instance)⟩ K).kernelIso.inv (q : ℤ) ≫
    (computation (Scheme.ProEt.topology T)
      (Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}
        ((Scheme.toProEt T).map f)) K q).inv
  projection_boundary : ∀ {V W : T.Etale} (f : W ⟶ V) (_hf : IsOpenImmersion f.left)
    {I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    {K : CochainComplex (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) ℕ}
    (β : pulledResolution T I ⟶ K),
    relativeFiberMap _ _ (pullbackSections T V β) (pullbackSections T W β) (square f β) ≫
      projection (restrictionComplex (Scheme.ProEt.topology T)
        ((Scheme.toProEt T).map f) K) =
    projection (restrictionComplex T.smallEtaleTopology f I) ≫ pullbackSections T V β ∧
    (CategoryTheory.shiftFunctor _ (-1 : ℤ)).map (pullbackSections T W β) ≫
      boundary (restrictionComplex (Scheme.ProEt.topology T) ((Scheme.toProEt T).map f) K) =
    boundary (restrictionComplex T.smallEtaleTopology f I) ≫
      relativeFiberMap _ _ (pullbackSections T V β) (pullbackSections T W β) (square f β)
  lift_independence : ∀ {V W : T.Etale} (f : W ⟶ V) (_hf : IsOpenImmersion f.left)
    {F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {F' : Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}}
    (γ : (AlgebraicGeometry.ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj F ⟶ F')
    (I : InjectiveResolution F) (K : InjectiveResolution F')
    (β β' : pulledResolution T I.cocomplex ⟶ K.cocomplex),
    IsLift T γ I K β → IsLift T γ I K β' → ∀ q : ℕ,
    homologyMap (relativeFiberMap _ _ (pullbackSections T V β)
      (pullbackSections T W β) (square f β)) (q : ℤ) =
    homologyMap (relativeFiberMap _ _ (pullbackSections T V β')
      (pullbackSections T W β') (square f β')) (q : ℤ)
  postcomposition : ∀ {V W : T.Etale} (f : W ⟶ V) (_hf : IsOpenImmersion f.left)
    {F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {F' F'' : Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}}
    (γ : (AlgebraicGeometry.ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj F ⟶ F')
    (δ : F' ⟶ F'') (I : InjectiveResolution F)
    (K : InjectiveResolution F') (K' : InjectiveResolution F'')
    (β : pulledResolution T I.cocomplex ⟶ K.cocomplex)
    (β' : pulledResolution T I.cocomplex ⟶ K'.cocomplex)
    (φ : K.cocomplex ⟶ K'.cocomplex) (_hφ : K.ι.f 0 ≫ φ.f 0 = δ ≫ K'.ι.f 0)
    (h : coefficientMap (Scheme.ProEt.topology T) ((Scheme.toProEt T).obj V) φ ≫
      restrictionComplex (Scheme.ProEt.topology T) ((Scheme.toProEt T).map f) K'.cocomplex =
      restrictionComplex (Scheme.ProEt.topology T) ((Scheme.toProEt T).map f) K.cocomplex ≫
      coefficientMap (Scheme.ProEt.topology T) ((Scheme.toProEt T).obj W) φ),
    IsLift T γ I K β → IsLift T (γ ≫ δ) I K' β' → ∀ q : ℕ,
    homologyMap (relativeFiberMap _ _ (pullbackSections T V β')
      (pullbackSections T W β') (square f β')) (q : ℤ) =
    homologyMap (relativeFiberMap _ _ (pullbackSections T V β)
      (pullbackSections T W β) (square f β)) (q : ℤ) ≫
    homologyMap (relativeFiberMap _ _
      (coefficientMap (Scheme.ProEt.topology T) ((Scheme.toProEt T).obj V) φ)
      (coefficientMap (Scheme.ProEt.topology T) ((Scheme.toProEt T).obj W) φ) h) (q : ℤ)

  coefficients : ∀ {V W : T.Etale} (f : W ⟶ V) (_hf : IsOpenImmersion f.left)
    {F F₁ : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}} (α : F ⟶ F₁)
    (I : InjectiveResolution F) (I₁ : InjectiveResolution F₁)
    (K : InjectiveResolution
      ((AlgebraicGeometry.ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj F))
    (K₁ : InjectiveResolution
      ((AlgebraicGeometry.ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj F₁))
    (β : pulledResolution T I.cocomplex ⟶ K.cocomplex)
    (β₁ : pulledResolution T I₁.cocomplex ⟶ K₁.cocomplex)
    (φ : I.cocomplex ⟶ I₁.cocomplex) (ψ : K.cocomplex ⟶ K₁.cocomplex)
    (_hφ : I.ι.f 0 ≫ φ.f 0 = α ≫ I₁.ι.f 0)
    (_hψ : K.ι.f 0 ≫ ψ.f 0 =
      (AlgebraicGeometry.ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).map α ≫
        K₁.ι.f 0)
    (h : coefficientMap T.smallEtaleTopology V φ ≫
      restrictionComplex T.smallEtaleTopology f I₁.cocomplex =
      restrictionComplex T.smallEtaleTopology f I.cocomplex ≫
        coefficientMap T.smallEtaleTopology W φ)
    (hp : coefficientMap (Scheme.ProEt.topology T) ((Scheme.toProEt T).obj V) ψ ≫
      restrictionComplex (Scheme.ProEt.topology T) ((Scheme.toProEt T).map f) K₁.cocomplex =
      restrictionComplex (Scheme.ProEt.topology T) ((Scheme.toProEt T).map f) K.cocomplex ≫
        coefficientMap (Scheme.ProEt.topology T) ((Scheme.toProEt T).obj W) ψ),
    IsLift T (𝟙 _) I K β → IsLift T (𝟙 _) I₁ K₁ β₁ → ∀ q : ℕ,
    homologyMap (relativeFiberMap _ _ (coefficientMap T.smallEtaleTopology V φ)
      (coefficientMap T.smallEtaleTopology W φ) h) (q : ℤ) ≫
      homologyMap (relativeFiberMap _ _ (pullbackSections T V β₁)
        (pullbackSections T W β₁) (square f β₁)) (q : ℤ) =
    homologyMap (relativeFiberMap _ _ (pullbackSections T V β)
      (pullbackSections T W β) (square f β)) (q : ℤ) ≫
      homologyMap (relativeFiberMap _ _
        (coefficientMap (Scheme.ProEt.topology T) ((Scheme.toProEt T).obj V) ψ)
        (coefficientMap (Scheme.ProEt.topology T) ((Scheme.toProEt T).obj W) ψ) hp) (q : ℤ)
  objects : ∀ {V W V' W' : T.Etale} (f : W ⟶ V) (f' : W' ⟶ V')
    (_hf : IsOpenImmersion f.left) (_hf' : IsOpenImmersion f'.left)
    (v : V' ⟶ V) (w : W' ⟶ W) (_hs : f' ≫ v = w ≫ f)
    {I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    {K : CochainComplex (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) ℕ}
    (β : pulledResolution T I ⟶ K)
    (h : restrictionComplex T.smallEtaleTopology v I ≫
      restrictionComplex T.smallEtaleTopology f' I =
      restrictionComplex T.smallEtaleTopology f I ≫ restrictionComplex T.smallEtaleTopology w I)
    (hp : restrictionComplex (Scheme.ProEt.topology T) ((Scheme.toProEt T).map v) K ≫
      restrictionComplex (Scheme.ProEt.topology T) ((Scheme.toProEt T).map f') K =
      restrictionComplex (Scheme.ProEt.topology T) ((Scheme.toProEt T).map f) K ≫
        restrictionComplex (Scheme.ProEt.topology T) ((Scheme.toProEt T).map w) K),
    relativeFiberMap _ _ (restrictionComplex T.smallEtaleTopology v I)
      (restrictionComplex T.smallEtaleTopology w I) h ≫
      relativeFiberMap _ _ (pullbackSections T V' β) (pullbackSections T W' β) (square f' β) =
    relativeFiberMap _ _ (pullbackSections T V β) (pullbackSections T W β) (square f β) ≫
      relativeFiberMap _ _
        (restrictionComplex (Scheme.ProEt.topology T) ((Scheme.toProEt T).map v) K)
        (restrictionComplex (Scheme.ProEt.topology T) ((Scheme.toProEt T).map w) K) hp

end RelativeCone

/-- The relative cone computes support cohomology on either small site, with canonical
resolution-independent identifications and the canonical etale--pro-etale comparison.

Source: Stacks, cohomology with support; blueprint main-20261015,
sec-smooth-purity/sk-prop-an/lem-pur-divisor-class.proof.md, first sentence and last paragraph
(blueprint: lem-pur-divisor-relative-cone).

Proof. Step 1: restriction of every injective sheaf along the open monomorphism is
surjective (`lem-weil-pbc-injective-sheaf-mono-restriction`); its kernel is the supported
section functor of `def-pur-support-cohomology`. Step 2: the canonical map `(k,0)` from
this kernel to the shifted cone is a quasi-isomorphism by
`CochainComplex.exists_kernel_to_shifted_mappingCone_of_degreewise_epi`; changing a cycle
`(a,b)` by a boundary coming from a lift of `b` proves this directly.
Step 3: `InjectiveResolution.isoRightDerivedObj` and extension by zero give the normalized
identifications. The kernel inclusion gives forgetting support. The kernel short exact
sequence's connecting map gives the shifted `inr`, hence `(0,-b)` in the signed model.
Resolution lifts commute with restriction; two such lifts are homotopic, with cone
homotopy `(Ha,-Hb)`. Thus coefficients, etale object restriction, support enlargement and
resolution changes give the stated equations (`lem-weil-pbc-derived-functor-map-via-lift`).
Step 4: exactness of L makes L(I) a resolution of L(F). Lift it inductively to a
pro-etale injective resolution using injectivity in each degree. Apply the comparison
unit followed by this lift at each etale object V. The unit is an isomorphism on etale
sections (`lem-cbc-comparison-pullback-sections`). Each L(I^n) is G-acyclic
(`lem-cbc-abelian-comparison-injective-acyclicity`), so `lemma-weil-pbc-leray-acyclicity`
and the unit identify the higher G-images of L(F) with the positive homology of I,
which vanishes. The Leray edge at V is therefore invertible
(`lem-weil-pbc-site-leray-degenerate`). Coefficient naturality and the adjunction
triangle identity identify its composite with cohomology of the unit with the canonical
section pullback. Both factors are invertible, proving the objectwise comparison.
Step 5: the cone map gives a morphism of the kernel and cone exact sequences. The
long exact homology sequences and five lemma make it an isomorphism. The same chain
squares give support, projection and boundary compatibility. Homotopy uniqueness of
augmented lifts gives coefficient naturality, restriction and arbitrary pro-etale
coefficient postcomposition, including the identity coefficient map. -/
theorem relativeConeSupportComparison (T : Scheme.{u}) {Z : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i]
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    ∃ (E : RelativeCone.System T.smallEtaleTopology
        (fun {_ _} f ↦ IsOpenImmersion f.left))
      (P : RelativeCone.System (Scheme.ProEt.topology T)
        (fun {V _} f ↦ IsOpenImmersion f.left ∧ Etale V.hom))
      (e : ∀ q : ℕ, relativeCohomology T (Scheme.Etale.mk i.openComplement.ι) I q ≅
        supportCohomology i q F),
      Nonempty (RelativeCone.TopologyComparison T E P) ∧
      ∀ q : ℕ, (e q).hom =
        ((E.realization (supportRestrictionArrow i)
          (by change IsOpenImmersion i.openComplement.ι; infer_instance) I).e q).hom := by
  sorry

end Etale
end AlgebraicGeometry
