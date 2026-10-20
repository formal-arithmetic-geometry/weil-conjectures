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
import Sheaf.Algebra.Homology.KernelShiftedConeBoundary
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolution
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.CategoryTheory.InjectiveSheafMonoRestriction

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

private noncomputable def supportedInclusion
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {V W : C} (f : W ⟶ V)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℕ) :
    supported J f I ⟶ sections J V I :=
  extendMap ((NatTrans.mapHomologicalComplex (forgetSupport J f) _).app I)
    ComplexShape.embeddingUpNat

private lemma supportedInclusion_condition
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {V W : C} (f : W ⟶ V)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℕ) :
    supportedInclusion J f I ≫ restrictionComplex J f I = 0 := by
  rw [supportedInclusion, restrictionComplex, ← extendMap_comp]
  have h : (NatTrans.mapHomologicalComplex (forgetSupport J f) _).app I ≫
      (NatTrans.mapHomologicalComplex (restriction J f) _).app I = 0 := by
    ext n : 1
    exact kernel.condition ((I.X n).obj.map f.op)
  rw [h]
  exact (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}).map_zero _ _

set_option backward.isDefEq.respectTransparency false in
@[irreducible]
private noncomputable def supportedInclusion_isKernel
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {V W : C} (f : W ⟶ V)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℕ) :
    IsLimit (KernelFork.ofι (supportedInclusion J f I)
      (supportedInclusion_condition J f I)) := by
  apply HomologicalComplex.isLimitOfEval
  intro n
  refine (KernelFork.isLimitMapConeEquiv _ (eval _ _ n)).symm ?_
  cases n with
  | ofNat n =>
    let S := ((Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f).mapHomologicalComplex
       (.up ℕ)).obj I
    let A := ((evaluationFunctor J V).mapHomologicalComplex (.up ℕ)).obj I
    let B := ((evaluationFunctor J W).mapHomologicalComplex (.up ℕ)).obj I
    let s := S.extendXIso ComplexShape.embeddingUpNat (show
      ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)
    let a := A.extendXIso ComplexShape.embeddingUpNat (show
      ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)
    let b := B.extendXIso ComplexShape.embeddingUpNat (show
      ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)
    have hi : (supportedInclusion J f I).f n =
        s.hom ≫ kernel.ι ((I.X n).obj.map f.op) ≫ a.inv := by
      exact extendMap_f _ _ (by rfl)
    have hr : (restrictionComplex J f I).f n =
        a.hom ≫ (I.X n).obj.map f.op ≫ b.inv := by
      exact extendMap_f _ _ (by rfl)
    have hm : Mono ((supportedInclusion J f I).f n) := by
      rw [hi]
      infer_instance
    refine KernelFork.IsLimit.ofι' ((supportedInclusion J f I).f n)
      (show (supportedInclusion J f I).f n ≫ (restrictionComplex J f I).f n = 0 from
        congr_hom (supportedInclusion_condition J f I) n) ?_
    intro D k hk
    change k ≫ (restrictionComplex J f I).f n = 0 at hk
    have hk' : (k ≫ a.hom) ≫ (I.X n).obj.map f.op = 0 := by
      apply (cancel_mono b.inv).1
      rw [hr] at hk
      simpa only [Category.assoc, zero_comp] using hk
    refine ⟨kernel.lift _ (k ≫ a.hom) hk' ≫ s.inv, ?_⟩
    rw [hi]
    simp
  | negSucc n =>
    refine KernelFork.IsLimit.ofι ((supportedInclusion J f I).f (Int.negSucc n))
      (show (supportedInclusion J f I).f (Int.negSucc n) ≫
        (restrictionComplex J f I).f (Int.negSucc n) = 0 from
        congr_hom (supportedInclusion_condition J f I) (Int.negSucc n))
      (fun _ _ ↦ 0) ?_ ?_
    · intro D g hg
      exact (((evaluationFunctor J V).mapHomologicalComplex (.up ℕ)).obj I
        |>.isZero_extend_X ComplexShape.embeddingUpNat (Int.negSucc n)
          (fun m hm ↦ by change (m : ℤ) = Int.negSucc n at hm; omega)).eq_of_tgt _ _
    · intro D g hg m hm
      exact (((Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f).mapHomologicalComplex
       (.up ℕ)).obj I
        |>.isZero_extend_X ComplexShape.embeddingUpNat (Int.negSucc n)
          (fun m hm ↦ by change (m : ℤ) = Int.negSucc n at hm; omega)).eq_of_tgt _ _

set_option backward.isDefEq.respectTransparency false in
private lemma restrictionComplex_epi
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {V W : C} (f : W ⟶ V) [Mono f]
    {F : Sheaf J AddCommGrpCat.{u + 1}} (I : InjectiveResolution F) (n : ℤ) :
    Epi ((restrictionComplex J f I.cocomplex).f n) := by
  cases n with
  | ofNat n =>
    have : Epi ((I.cocomplex.X n).obj.map f.op) :=
      (AddCommGrpCat.epi_iff_surjective _).mpr
        (injective_sheaf_mono_restriction.{u + 1, u, u + 1} J _ f)
    have h := extendMap_f
      ((NatTrans.mapHomologicalComplex (restriction J f) _).app I.cocomplex)
      ComplexShape.embeddingUpNat (show
        ComplexShape.embeddingUpNat.f n = Int.ofNat n from rfl)
    dsimp only [restrictionComplex]
    rw [h]
    change Epi (_ ≫ (I.cocomplex.X n).obj.map f.op ≫ _)
    infer_instance
  | negSucc n =>
    exact (HomologicalComplex.isZero_extend_X
      (((evaluationFunctor J W).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
      ComplexShape.embeddingUpNat (Int.negSucc n)
      (fun m hm ↦ by change (m : ℤ) = Int.negSucc n at hm; omega)).epi _

@[irreducible]
private noncomputable def supportKernelIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {V W : C} (f : W ⟶ V)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℕ) :
    supported J f I ≅ kernel (restrictionComplex J f I) := by
  let e := (supportedInclusion_isKernel J f I).conePointUniqueUpToIso
    (kernelIsKernel (restrictionComplex J f I))
  exact e

private lemma supportKernelIso_ι
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {V W : C} (f : W ⟶ V)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℕ) :
    (supportKernelIso J f I).hom ≫ kernel.ι (restrictionComplex J f I) =
      supportedInclusion J f I := by
  unfold supportKernelIso
  exact (supportedInclusion_isKernel J f I).conePointUniqueUpToIso_hom_comp
    (kernelIsKernel (restrictionComplex J f I)) WalkingParallelPair.zero

set_option backward.isDefEq.respectTransparency false in
private lemma projection_f {A B : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (p : ℤ) :
    (projection r).f p =
      ((CochainComplex.mappingCone r).shiftFunctorObjXIso (-1) p (p - 1) (by omega)).hom ≫
      homotopyCofiber.fstX r (p - 1) p (by change p - 1 + 1 = p; omega) := by
  simp [projection, CochainComplex.HomComplex.Cocycle.equivHomShift_symm_apply,
    CochainComplex.shiftFunctorAdd_inv_app_f, CochainComplex.shiftFunctorZero_hom_app_f,
    CochainComplex.mappingCone.fst,
    CochainComplex.HomComplex.Cochain.rightShift_v]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma fiberMap_fst {A B A' B' : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (r' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ r' = r ≫ b) (p : ℤ) :
    (relativeFiberMap r r' a b h).f p ≫
      ((CochainComplex.mappingCone r').shiftFunctorObjXIso (-1) p (p - 1) (by omega)).hom ≫
      homotopyCofiber.fstX r' (p - 1) p (by change p - 1 + 1 = p; omega) =
    ((CochainComplex.mappingCone r).shiftFunctorObjXIso (-1) p (p - 1) (by omega)).hom ≫
      homotopyCofiber.fstX r (p - 1) p (by change p - 1 + 1 = p; omega) ≫ a.f p := by
  change (homotopyCofiber.mapArrowHom r r'
      (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (Arrow.homMk a b h)).f (p - 1) ≫
        (𝟙 _ ≫ homotopyCofiber.fstX r' (p - 1) p _) =
      (𝟙 _ ≫ homotopyCofiber.fstX r (p - 1) p _) ≫ a.f p
  simp only [Category.id_comp]
  apply homotopyCofiber.ext_from_X r p (p - 1) (by change p - 1 + 1 = p; omega)
  all_goals simp [homotopyCofiber.mapArrowHom, homotopyCofiber.desc_f,
    homotopyCofiber.inrCompHomotopy_hom, sub_add_cancel]

set_option backward.isDefEq.respectTransparency false in
private lemma fiberMap_snd {A B A' B' : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (r' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ r' = r ≫ b) (p : ℤ) :
    (relativeFiberMap r r' a b h).f p ≫
      ((CochainComplex.mappingCone r').shiftFunctorObjXIso (-1) p (p - 1) (by omega)).hom ≫
      homotopyCofiber.sndX r' (p - 1) =
    ((CochainComplex.mappingCone r).shiftFunctorObjXIso (-1) p (p - 1) (by omega)).hom ≫
      homotopyCofiber.sndX r (p - 1) ≫ b.f (p - 1) := by
  change (homotopyCofiber.mapArrowHom r r'
      (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (Arrow.homMk a b h)).f (p - 1) ≫
        (𝟙 _ ≫ homotopyCofiber.sndX r' (p - 1)) =
      (𝟙 _ ≫ homotopyCofiber.sndX r (p - 1)) ≫ b.f (p - 1)
  simp only [Category.id_comp]
  apply homotopyCofiber.ext_from_X r p (p - 1) (by change p - 1 + 1 = p; omega)
  all_goals simp [homotopyCofiber.mapArrowHom, homotopyCofiber.desc_f,
    homotopyCofiber.inrCompHomotopy_hom, sub_add_cancel]

private lemma triangleSquare {A B A' B' : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (r' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ r' = r ≫ b) : TriangleSquare r r' a b h := by
  constructor
  · ext p : 1
    simpa only [comp_f, projection_f, Category.assoc] using fiberMap_fst r r' a b h p
  · ext p : 1
    change b.f (p - 1) ≫ (CochainComplex.mappingCone.inr r').f (p - 1) =
      (CochainComplex.mappingCone.inr r).f (p - 1) ≫
        (homotopyCofiber.mapArrowHom r r'
          (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (Arrow.homMk a b h)).f (p - 1)
    simp [CochainComplex.mappingCone.inr, homotopyCofiber.mapArrowHom]

private lemma exists_kernelModel
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {V W : C} (f : W ⟶ V) [Mono f]
    {F : Sheaf J AddCommGrpCat.{u + 1}} (I : InjectiveResolution F) :
    ∃ κ : kernel (restrictionComplex J f I.cocomplex) ⟶ fiber J f I.cocomplex,
      QuasiIso κ ∧ κ ≫ projection (restrictionComplex J f I.cocomplex) =
        kernel.ι (restrictionComplex J f I.cocomplex) ∧
      ∀ n : ℤ,
        κ.f n ≫ ((CochainComplex.mappingCone
          (restrictionComplex J f I.cocomplex)).shiftFunctorObjXIso
            (-1) n (n - 1) (by omega)).hom ≫
          homotopyCofiber.sndX (restrictionComplex J f I.cocomplex) (n - 1) = 0 ∧
        κ.f n ≫ ((CochainComplex.mappingCone
          (restrictionComplex J f I.cocomplex)).shiftFunctorObjXIso
            (-1) n (n - 1) (by omega)).hom ≫
          homotopyCofiber.fstX (restrictionComplex J f I.cocomplex) (n - 1) n
            (by change n - 1 + 1 = n; omega) =
          (kernel.ι (restrictionComplex J f I.cocomplex)).f n := by
  let _ := HasDerivedCategory.standard AddCommGrpCat.{u + 1}
  obtain ⟨κ, hc, hq, _⟩ :=
    CochainComplex.exists_kernel_to_shifted_mappingCone_of_degreewise_epi
      (restrictionComplex J f I.cocomplex) (restrictionComplex_epi J f I)
  refine ⟨κ, hq, ?_, hc⟩
  ext p : 1
  simpa only [comp_f, projection_f, Category.assoc] using (hc p).2

set_option backward.isDefEq.respectTransparency false in
private lemma kernelSquare
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]
    [EnoughInjectives (Sheaf K AddCommGrpCat.{u + 1})]
    {V W : C} {V' W' : D} (f : W ⟶ V) (f' : W' ⟶ V')
    {F : Sheaf J AddCommGrpCat.{u + 1}} {F' : Sheaf K AddCommGrpCat.{u + 1}}
    (I : InjectiveResolution F) (I' : InjectiveResolution F')
    (R : Realization J f I) (R' : Realization K f' I')
    (a : sections J V I.cocomplex ⟶ sections K V' I'.cocomplex)
    (b : sections J W I.cocomplex ⟶ sections K W' I'.cocomplex)
    (h : a ≫ restrictionComplex K f' I'.cocomplex =
      restrictionComplex J f I.cocomplex ≫ b) :
    kernel.map _ _ a b h.symm ≫ R'.κ =
      R.κ ≫ relativeFiberMap _ _ a b h := by
  ext n : 1
  apply (cancel_mono ((CochainComplex.mappingCone
    (restrictionComplex K f' I'.cocomplex)).shiftFunctorObjXIso
      (-1) n (n - 1) (by omega)).hom).1
  apply homotopyCofiber.ext_to_X (restrictionComplex K f' I'.cocomplex) (n - 1) n
    (by change n - 1 + 1 = n; omega)
  · simp only [comp_f, Category.assoc, (R'.κ_components n).2,
      fiberMap_fst, reassoc_of% ((R.κ_components n).2)]
    have hh : kernel.map _ _ a b h.symm ≫
        kernel.ι (restrictionComplex K f' I'.cocomplex) =
      kernel.ι (restrictionComplex J f I.cocomplex) ≫ a := by simp
    exact congr_hom hh n
  · simp only [comp_f, Category.assoc, (R'.κ_components n).1,
      fiberMap_snd, reassoc_of% ((R.κ_components n).1), comp_zero, zero_comp]

set_option backward.isDefEq.respectTransparency false in
private lemma computation_natural
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]
    {G H : Sheaf J AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1}}
    [G.Additive] [H.Additive] (τ : G ⟶ H)
    {F : Sheaf J AddCommGrpCat.{u + 1}} (I : InjectiveResolution F) (q : ℕ) :
    (computation J G I q).inv ≫ (NatTrans.rightDerived τ q).app F =
      homologyMap (extendMap ((NatTrans.mapHomologicalComplex τ _).app I.cocomplex)
        ComplexShape.embeddingUpNat) (q : ℤ) ≫ (computation J H I q).inv := by
  rw [InjectiveResolution.rightDerived_app_eq τ I q]
  dsimp only [computation, Iso.trans_inv, Iso.symm_inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change _ ≫ homologyMap _ q ≫ _ = _
  rw [extendHomologyIso_hom_naturality_assoc]

set_option backward.isDefEq.respectTransparency false in
private lemma computation_coefficients
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]
    (G : Sheaf J AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1}) [G.Additive]
    {F F' : Sheaf J AddCommGrpCat.{u + 1}} (α : F ⟶ F')
    (I : InjectiveResolution F) (I' : InjectiveResolution F')
    (φ : I.cocomplex ⟶ I'.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = α ≫ I'.ι.f 0)
    (q : ℕ) :
    (computation J G I q).inv ≫ (G.rightDerived q).map α =
      homologyMap (extendMap ((G.mapHomologicalComplex (.up ℕ)).map φ)
        ComplexShape.embeddingUpNat) (q : ℤ) ≫ (computation J G I' q).inv := by
  dsimp only [computation, Iso.trans_inv, Iso.symm_inv]
  rw [Category.assoc,
    InjectiveResolution.isoRightDerivedObj_inv_naturality α I I' φ hφ G q]
  rw [extendHomologyIso_hom_naturality_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem exists_realization
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]
    {V W : C} (f : W ⟶ V) [Mono f]
    {F : Sheaf J AddCommGrpCat.{u + 1}} (I : InjectiveResolution F) :
    Nonempty (Realization J f I) := by
  obtain ⟨κ, hκ, hproj, hc⟩ := exists_kernelModel J f I
  have : QuasiIso κ := hκ
  let k := supportKernelIso J f I.cocomplex
  have hr : Epi (restrictionComplex J f I.cocomplex) :=
    epi_of_epi_f _ (restrictionComplex_epi J f I)
  have hs : (ShortComplex.mk (kernel.ι (restrictionComplex J f I.cocomplex))
      (restrictionComplex J f I.cocomplex) (kernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_kernel _
      mono_f := inferInstance
      epi_g := hr }
  let e (q : ℕ) :=
    (asIso (homologyMap κ (q : ℤ))).symm ≪≫
      (homologyFunctor AddCommGrpCat.{u + 1} (.up ℤ) (q : ℤ)).mapIso k.symm ≪≫
      (computation J (Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f) I q).symm
  refine ⟨{ kernelIso := k
            kernel_components := ?_
            κ := κ
            κ_quasiIso := hκ
            κ_components := hc
            exact := hs
            e := e
            normalization := ?_
            forget := ?_
            localization := ?_ }⟩
  · intro n
    change (k.hom ≫ kernel.ι (restrictionComplex J f I.cocomplex)).f n = _
    rw [supportKernelIso_ι]
    exact extendMap_f _ _ (by rfl)
  · intro q
    change homologyMap k.hom (q : ℤ) ≫ homologyMap κ (q : ℤ) ≫
      inv (homologyMap κ (q : ℤ)) ≫ homologyMap k.inv (q : ℤ) ≫ _ = _
    simp only [IsIso.hom_inv_id_assoc]
    rw [← homologyMap_comp_assoc, k.hom_inv_id, homologyMap_id, Category.id_comp]
    rfl
  · intro q
    apply (cancel_epi (homologyMap k.hom (q : ℤ) ≫ homologyMap κ (q : ℤ))).1
    simp only [Category.assoc, e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      asIso_inv, IsIso.hom_inv_id_assoc]
    change homologyMap k.hom (q : ℤ) ≫ homologyMap k.inv (q : ℤ) ≫ _ = _
    rw [← homologyMap_comp_assoc, k.hom_inv_id, homologyMap_id, Category.id_comp]
    rw [computation_natural]
    have hp := congrArg (fun t ↦ homologyMap t (q : ℤ)) hproj
    rw [homologyMap_comp] at hp
    rw [reassoc_of% hp, ← homologyMap_comp_assoc, supportKernelIso_ι]
    rfl
  · intro q
    have hb := CochainComplex.kernelShiftedCone_boundary
      (restrictionComplex J f I.cocomplex) hs κ hc (q : ℤ)
    dsimp only [boundary]
    rw [hb]
    simp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_inv,
      Category.assoc, IsIso.hom_inv_id_assoc]
    rfl

set_option backward.isDefEq.respectTransparency false in
private lemma realization_ι
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]
    {V W : C} (f : W ⟶ V)
    {F : Sheaf J AddCommGrpCat.{u + 1}} (I : InjectiveResolution F)
    (R : Realization J f I) :
    R.kernelIso.hom ≫ kernel.ι (restrictionComplex J f I.cocomplex) =
      supportedInclusion J f I.cocomplex := by
  ext n : 1
  cases n with
  | ofNat n =>
    rw [comp_f]
    have hi := extendMap_f
      ((NatTrans.mapHomologicalComplex (forgetSupport J f) _).app I.cocomplex)
      ComplexShape.embeddingUpNat
      (show ComplexShape.embeddingUpNat.f n = Int.ofNat n from rfl)
    exact (R.kernel_components n).trans hi.symm
  | negSucc n =>
    exact (((Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f).mapHomologicalComplex
       (.up ℕ)).obj I.cocomplex
      |>.isZero_extend_X ComplexShape.embeddingUpNat (Int.negSucc n)
        (fun m hm ↦ by change (m : ℤ) = Int.negSucc n at hm; omega)).eq_of_src _ _

@[irreducible]
private noncomputable def realizationIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]
    {V W : C} {f : W ⟶ V} {F : Sheaf J AddCommGrpCat.{u + 1}}
    {I : InjectiveResolution F} (R : Realization J f I) (q : ℤ) :
    (supported J f I.cocomplex).homology q ≅ (fiber J f I.cocomplex).homology q := by
  have : QuasiIso R.κ := R.κ_quasiIso
  exact (homologyFunctor AddCommGrpCat.{u + 1} (.up ℤ) q).mapIso R.kernelIso ≪≫
    asIso (homologyMap R.κ q)

private lemma realizationIso_hom
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]
    {V W : C} {f : W ⟶ V} {F : Sheaf J AddCommGrpCat.{u + 1}}
    {I : InjectiveResolution F} (R : Realization J f I) (q : ℤ) :
    (realizationIso J R q).hom = homologyMap R.kernelIso.hom q ≫ homologyMap R.κ q := by
  unfold realizationIso
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma realization_homologySquare
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]
    [EnoughInjectives (Sheaf K AddCommGrpCat.{u + 1})]
    {V W : C} {V' W' : D} (f : W ⟶ V) (f' : W' ⟶ V')
    {F : Sheaf J AddCommGrpCat.{u + 1}} {F' : Sheaf K AddCommGrpCat.{u + 1}}
    (I : InjectiveResolution F) (I' : InjectiveResolution F')
    (R : Realization J f I) (R' : Realization K f' I')
    (a : sections J V I.cocomplex ⟶ sections K V' I'.cocomplex)
    (b : sections J W I.cocomplex ⟶ sections K W' I'.cocomplex)
    (h : a ≫ restrictionComplex K f' I'.cocomplex =
      restrictionComplex J f I.cocomplex ≫ b)
    (s : supported J f I.cocomplex ⟶ supported K f' I'.cocomplex)
    (hs : s ≫ supportedInclusion K f' I'.cocomplex =
      supportedInclusion J f I.cocomplex ≫ a)
    (q : ℤ) :
    homologyMap R.kernelIso.hom q ≫ homologyMap R.κ q ≫
        homologyMap (relativeFiberMap _ _ a b h) q =
      homologyMap s q ≫ homologyMap R'.kernelIso.hom q ≫ homologyMap R'.κ q := by
  have hs' : s ≫ R'.kernelIso.hom =
      R.kernelIso.hom ≫ kernel.map _ _ a b h.symm := by
    apply (cancel_mono (kernel.ι (restrictionComplex K f' I'.cocomplex))).1
    simp only [Category.assoc, kernel.lift_ι]
    rw [realization_ι, ← Category.assoc, realization_ι, hs]
  have hh : R.kernelIso.hom ≫ R.κ ≫ relativeFiberMap _ _ a b h =
      s ≫ R'.kernelIso.hom ≫ R'.κ := by
    rw [← kernelSquare J K f f' I I' R R' a b h, ← Category.assoc, ← hs']
    simp only [Category.assoc]
  simpa only [homologyMap_comp] using congrArg (fun t ↦ homologyMap t q) hh

set_option backward.isDefEq.respectTransparency false in
private lemma realization_modelSquare
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]
    [EnoughInjectives (Sheaf K AddCommGrpCat.{u + 1})]
    {V W : C} {V' W' : D} (f : W ⟶ V) (f' : W' ⟶ V')
    {F : Sheaf J AddCommGrpCat.{u + 1}} {F' : Sheaf K AddCommGrpCat.{u + 1}}
    (I : InjectiveResolution F) (I' : InjectiveResolution F')
    (R : Realization J f I) (R' : Realization K f' I')
    (a : sections J V I.cocomplex ⟶ sections K V' I'.cocomplex)
    (b : sections J W I.cocomplex ⟶ sections K W' I'.cocomplex)
    (h : a ≫ restrictionComplex K f' I'.cocomplex =
      restrictionComplex J f I.cocomplex ≫ b)
    (s : supported J f I.cocomplex ⟶ supported K f' I'.cocomplex)
    (hs : s ≫ supportedInclusion K f' I'.cocomplex =
      supportedInclusion J f I.cocomplex ≫ a)
    (q : ℤ) :
    (realizationIso J R q).hom ≫ homologyMap (relativeFiberMap _ _ a b h) q =
      homologyMap s q ≫ (realizationIso K R' q).hom := by
  rw [realizationIso_hom, realizationIso_hom, Category.assoc]
  exact realization_homologySquare J K f f' I I' R R' a b h s hs q

set_option backward.isDefEq.respectTransparency false in
private lemma realization_normalization_inv
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]
    {V W : C} (f : W ⟶ V)
    {F : Sheaf J AddCommGrpCat.{u + 1}} (I : InjectiveResolution F)
    (R : Realization J f I) (q : ℕ) :
    (R.e q).inv =
      (computation J (Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f) I q).hom ≫
        homologyMap R.kernelIso.hom (q : ℤ) ≫ homologyMap R.κ (q : ℤ) := by
  apply (cancel_mono (R.e q).hom).1
  simp only [Iso.inv_hom_id, Category.assoc, R.normalization, Iso.hom_inv_id]

set_option backward.isDefEq.respectTransparency false in
private lemma realization_transport
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]
    [EnoughInjectives (Sheaf K AddCommGrpCat.{u + 1})]
    {V W : C} {V' W' : D} (f : W ⟶ V) (f' : W' ⟶ V')
    {F : Sheaf J AddCommGrpCat.{u + 1}} {F' : Sheaf K AddCommGrpCat.{u + 1}}
    (I : InjectiveResolution F) (I' : InjectiveResolution F')
    (R : Realization J f I) (R' : Realization K f' I')
    (a : sections J V I.cocomplex ⟶ sections K V' I'.cocomplex)
    (b : sections J W I.cocomplex ⟶ sections K W' I'.cocomplex)
    (h : a ≫ restrictionComplex K f' I'.cocomplex =
      restrictionComplex J f I.cocomplex ≫ b) (q : ℕ) :
    (R.e q).inv ≫ homologyMap (relativeFiberMap _ _ a b h) (q : ℤ) ≫ (R'.e q).hom =
      (computation J (Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f) I q).hom ≫
        homologyMap R.kernelIso.hom (q : ℤ) ≫
        homologyMap (kernel.map _ _ a b h.symm) (q : ℤ) ≫
        homologyMap R'.kernelIso.inv (q : ℤ) ≫
        (computation K (Sheaf.supportedSectionsFunctor K AddCommGrpCat.{u + 1} f') I' q).inv := by
  have hk := congrArg (fun t ↦ homologyMap t (q : ℤ))
    (kernelSquare J K f f' I I' R R' a b h)
  simp only [homologyMap_comp] at hk
  rw [realization_normalization_inv, Category.assoc, Category.assoc,
    ← reassoc_of% hk]
  congr 1
  congr 1
  congr 1
  apply (cancel_epi (homologyMap R'.kernelIso.hom (q : ℤ))).1
  simp only [R'.normalization]
  rw [← homologyMap_comp_assoc, R'.kernelIso.hom_inv_id, homologyMap_id]
  simp only [Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private lemma realization_natural
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]
    [EnoughInjectives (Sheaf K AddCommGrpCat.{u + 1})]
    {V W : C} {V' W' : D} (f : W ⟶ V) (f' : W' ⟶ V')
    {F : Sheaf J AddCommGrpCat.{u + 1}} {F' : Sheaf K AddCommGrpCat.{u + 1}}
    (I : InjectiveResolution F) (I' : InjectiveResolution F')
    (R : Realization J f I) (R' : Realization K f' I')
    (a : sections J V I.cocomplex ⟶ sections K V' I'.cocomplex)
    (b : sections J W I.cocomplex ⟶ sections K W' I'.cocomplex)
    (h : a ≫ restrictionComplex K f' I'.cocomplex =
      restrictionComplex J f I.cocomplex ≫ b)
    (s : supported J f I.cocomplex ⟶ supported K f' I'.cocomplex)
    (hs : s ≫ supportedInclusion K f' I'.cocomplex =
      supportedInclusion J f I.cocomplex ≫ a)
    (q : ℕ)
    (d : ((Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f).rightDerived q).obj F ⟶
      ((Sheaf.supportedSectionsFunctor K AddCommGrpCat.{u + 1} f').rightDerived q).obj F')
    (hd : (computation J
        (Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f) I q).inv ≫ d =
      homologyMap s (q : ℤ) ≫ (computation K
        (Sheaf.supportedSectionsFunctor K AddCommGrpCat.{u + 1} f') I' q).inv) :
    homologyMap (relativeFiberMap _ _ a b h) (q : ℤ) ≫ (R'.e q).hom =
      (R.e q).hom ≫ d := by
  have : QuasiIso R.κ := R.κ_quasiIso
  have hs' : s ≫ R'.kernelIso.hom =
      R.kernelIso.hom ≫ kernel.map _ _ a b h.symm := by
    apply (cancel_mono (kernel.ι (restrictionComplex K f' I'.cocomplex))).1
    simp only [Category.assoc, kernel.lift_ι]
    rw [realization_ι, ← Category.assoc, realization_ι, hs]
  have hh : R.kernelIso.hom ≫ R.κ ≫ relativeFiberMap _ _ a b h =
      s ≫ R'.kernelIso.hom ≫ R'.κ := by
    rw [← kernelSquare J K f f' I I' R R' a b h, ← Category.assoc, ← hs']
    simp only [Category.assoc]
  have hH := congrArg (fun t ↦ homologyMap t (q : ℤ)) hh
  simp only [homologyMap_comp] at hH
  apply (cancel_epi (homologyMap R.kernelIso.hom (q : ℤ) ≫
    homologyMap R.κ (q : ℤ))).1
  simp only [Category.assoc]
  rw [reassoc_of% hH, R'.normalization, ← hd, reassoc_of% (R.normalization q)]

set_option backward.isDefEq.respectTransparency false in
private theorem exists_system
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]
    (P : ∀ {V W : C}, (W ⟶ V) → Prop)
    (hmono : ∀ {V W : C} (f : W ⟶ V), P f → Mono f) : Nonempty (System J P) := by
  classical
  let R : ∀ {V W : C} (f : W ⟶ V), P f →
      ∀ {F : Sheaf J AddCommGrpCat.{u + 1}} (I : InjectiveResolution F),
        Realization J f I := fun {V W} f hf {F} I ↦ Classical.choice (by
    have := hmono f hf
    exact exists_realization J f I)
  refine ⟨{ realization := R, coefficients := ?_, objects := ?_ }⟩
  · intro V W f hf F F' α I I' φ hφ h q
    refine ⟨?_, triangleSquare _ _ _ _ h⟩
    refine realization_natural J J f f I I' (R f hf I) (R f hf I')
      _ _ h
      (extendMap (((Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f).mapHomologicalComplex
         (.up ℕ)).map φ) ComplexShape.embeddingUpNat) ?_ q _
      (computation_coefficients J _ α I I' φ hφ q)
    dsimp only [supportedInclusion, coefficientMap]
    rw [← extendMap_comp, ← extendMap_comp]
    congr 1
    exact (NatTrans.mapHomologicalComplex (forgetSupport J f) (.up ℕ)).naturality φ
  · intro V W V' W' f f' hf hf' v w hs F I h q
    refine ⟨?_, triangleSquare _ _ _ _ h⟩
    refine realization_natural J J f f' I I (R f hf I) (R f' hf' I)
      _ _ h
      (extendMap ((NatTrans.mapHomologicalComplex (supportRestriction J f f' v w hs)
        (.up ℕ)).app I.cocomplex) ComplexShape.embeddingUpNat) ?_ q _
      (computation_natural J (supportRestriction J f f' v w hs) I q)
    dsimp only [supportedInclusion, restrictionComplex]
    rw [← extendMap_comp, ← extendMap_comp]
    congr 1
    ext n : 1
    simp [supportRestriction, forgetSupport, restriction]

private noncomputable def transposeLift (T : Scheme.{u})
    {I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    {K : CochainComplex (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) ℕ}
    (β : pulledResolution T I ⟶ K) :
    I ⟶ ((ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T).mapHomologicalComplex
       (.up ℕ)).obj K :=
  (NatTrans.mapHomologicalComplex
    (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit _).app I ≫
    ((ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T).mapHomologicalComplex
       (.up ℕ)).map β

private noncomputable def supportPullback (T : Scheme.{u}) {V W : T.Etale}
    (f : W ⟶ V)
    {I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    {K : CochainComplex (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) ℕ}
    (β : pulledResolution T I ⟶ K) :
    supported T.smallEtaleTopology f I ⟶
      supported (Scheme.ProEt.topology T) ((Scheme.toProEt T).map f) K :=
  extendMap (((Sheaf.supportedSectionsFunctor T.smallEtaleTopology
    AddCommGrpCat.{u + 1} f).mapHomologicalComplex (.up ℕ)).map (transposeLift T β))
    ComplexShape.embeddingUpNat

set_option backward.isDefEq.respectTransparency false in
private lemma topologySquare (T : Scheme.{u}) {V W : T.Etale} (f : W ⟶ V)
    {I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    {K : CochainComplex (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) ℕ}
    (β : pulledResolution T I ⟶ K) :
    pullbackSections T V β ≫
        restrictionComplex (Scheme.ProEt.topology T) ((Scheme.toProEt T).map f) K =
      restrictionComplex T.smallEtaleTopology f I ≫ pullbackSections T W β := by
  dsimp only [pullbackSections, restrictionComplex]
  rw [← extendMap_comp, ← extendMap_comp]
  congr 1
  ext n : 1
  exact ((transposeLift T β).f n).hom.naturality f.op |>.symm

set_option backward.isDefEq.respectTransparency false in
private lemma supportPullback_inclusion (T : Scheme.{u}) {V W : T.Etale} (f : W ⟶ V)
    {I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    {K : CochainComplex (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) ℕ}
    (β : pulledResolution T I ⟶ K) :
    supportPullback T f β ≫
        supportedInclusion (Scheme.ProEt.topology T) ((Scheme.toProEt T).map f) K =
      supportedInclusion T.smallEtaleTopology f I ≫ pullbackSections T V β := by
  dsimp only [supportPullback, supportedInclusion, pullbackSections]
  rw [← extendMap_comp, ← extendMap_comp]
  congr 1
  exact (NatTrans.mapHomologicalComplex (forgetSupport T.smallEtaleTopology f)
    (.up ℕ)).naturality (transposeLift T β)

set_option backward.isDefEq.respectTransparency false in
private lemma transposeLift_augmentation (T : Scheme.{u})
    {F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {F' : Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}}
    (γ : (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj F ⟶ F')
    (I : InjectiveResolution F) (K : InjectiveResolution F')
    (β : pulledResolution T I.cocomplex ⟶ K.cocomplex) (hβ : IsLift T γ I K β) :
    I.ι.f 0 ≫ (transposeLift T β).f 0 =
      (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app F ≫
        (ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T).map γ ≫
        (ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T).map (K.ι.f 0) := by
  change I.ι.f 0 ≫
    ((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app (I.cocomplex.X 0) ≫
      (ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T).map (β.f 0)) = _
  have hn := (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.naturality
    (I.ι.f 0)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp, hβ]
  simp only [Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[irreducible]
private noncomputable def transposeLift_homotopy (T : Scheme.{u})
    {F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {F' : Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}}
    (γ : (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj F ⟶ F')
    (I : InjectiveResolution F) (K : InjectiveResolution F')
    (β β' : pulledResolution T I.cocomplex ⟶ K.cocomplex)
    (hβ : IsLift T γ I K β) (hβ' : IsLift T γ I K β') :
    Homotopy (transposeLift T β) (transposeLift T β') := by
  letI := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T)
  have (n : ℕ) : Injective ((((ProEtale.comparisonLowerStar
      AddCommGrpCat.{u + 1} T).mapHomologicalComplex (.up ℕ)).obj K.cocomplex).X n) := by
    change Injective ((ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T).obj
      (K.cocomplex.X n))
    infer_instance
  exact CochainComplex.homotopyOfQuasiIso I.ι _ _
    ((transposeLift_augmentation T γ I K β hβ).trans
      (transposeLift_augmentation T γ I K β' hβ').symm)


private lemma mapResolution_f_zero
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (L : A ⥤ B) [L.Additive] {F : A} {I : CochainComplex A ℕ}
    (ι : (CochainComplex.single₀ A).obj F ⟶ I) :
    (L.mapResolution ι).f 0 = L.map (ι.f 0) := by
  simp [Functor.mapResolution, singleMapHomologicalComplex_inv_app_self,
    singleObjXSelf, singleObjXIsoOfEq]


private theorem lift_resolution
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {F : A} {F' : B} (γ : L.obj F ⟶ F')
    (I : InjectiveResolution F) (K : InjectiveResolution F') :
    ∃ β : (L.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ K.cocomplex,
      L.map (I.ι.f 0) ≫ β.f 0 = γ ≫ K.ι.f 0 := by
  let β := InjectiveResolution.descOfQuasiIso γ K (L.mapResolution I.ι)
  refine ⟨β, ?_⟩
  have h := InjectiveResolution.descOfQuasiIso_commutes γ K (L.mapResolution I.ι)
  simpa only [comp_f, mapResolution_f_zero, CochainComplex.single₀_map_f_zero]
    using congrArg (fun f ↦ f.f 0) h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exists_lift (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1})
    (γ : (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj F ⟶ F')
    (I : InjectiveResolution F) (K : InjectiveResolution F') :
    ∃ β : pulledResolution T I.cocomplex ⟶ K.cocomplex, IsLift T γ I K β := by
  exact lift_resolution (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T) γ I K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma adjunction_lift_quasiIso
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasInjectiveResolutions B] (L : A ⥤ B) (G : B ⥤ A)
    [L.Additive] [G.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ G) [IsIso adj.unit]
    (hacyc : ∀ (X : A) [Injective X], G.rightAcyclic (L.obj X))
    {F : A} (I : InjectiveResolution F) (K : InjectiveResolution (L.obj F))
    (β : (L.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ K.cocomplex)
    (hβ : L.map (I.ι.f 0) ≫ β.f 0 = K.ι.f 0) :
    QuasiIso ((NatTrans.mapHomologicalComplex adj.unit _).app I.cocomplex ≫
      (G.mapHomologicalComplex (.up ℕ)).map β) := by
  let : G.IsRightAdjoint := adj.isRightAdjoint
  have hcomm : L.mapResolution I.ι ≫ β = K.ι := by
    apply HomologicalComplex.from_single_hom_ext
    simpa only [comp_f, mapResolution_f_zero] using hβ
  have : QuasiIso (L.mapResolution I.ι ≫ β) := by rw [hcomm]; infer_instance
  have : QuasiIso β := quasiIso_of_comp_left (L.mapResolution I.ι) β
  have : QuasiIso ((G.mapHomologicalComplex (.up ℕ)).map β) :=
    G.quasiIso_map_of_rightAcyclic_nat β (fun n ↦ hacyc (I.cocomplex.X n))
      (fun n ↦ Functor.rightAcyclic_of_injective (F := G) (K.cocomplex.X n))
  have : IsIso ((NatTrans.mapHomologicalComplex adj.unit _).app I.cocomplex) := by
    have (n : ℕ) : IsIso
        (((NatTrans.mapHomologicalComplex adj.unit _).app I.cocomplex).f n) := by
      change IsIso (adj.unit.app (I.cocomplex.X n))
      infer_instance
    exact HomologicalComplex.Hom.isIso_of_components _
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma transposeLift_quasiIso (T : Scheme.{u})
    {F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}} (I : InjectiveResolution F)
    (K : InjectiveResolution
      ((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj F))
    (β : pulledResolution T I.cocomplex ⟶ K.cocomplex)
    (hβ : IsLift T (𝟙 _) I K β) : QuasiIso (transposeLift T β) := by
  have : IsIso (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit :=
    ProEtale.isIso_comparisonAdjunction_unit AddCommGrpCat.{u + 1} T
  exact adjunction_lift_quasiIso
    (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T)
    (ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T)
    (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T)
    (fun X _ ↦ ProEtale.rightAcyclic_comparisonUpperStar_obj_of_injective
      AddCommGrpCat.{u + 1} T X) I K β
    (by simpa only [IsLift, Category.id_comp] using hβ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem transposeLift_equivalence (T : Scheme.{u})
    {F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}} (I : InjectiveResolution F)
    (K : InjectiveResolution
      ((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj F))
    (β : pulledResolution T I.cocomplex ⟶ K.cocomplex)
    (hβ : IsLift T (𝟙 _) I K β) :
    homotopyEquivalences _ (.up ℕ) (transposeLift T β) := by
  let G := ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T
  have : G.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T)
  have (n : ℕ) : Injective (((G.mapHomologicalComplex (.up ℕ)).obj K.cocomplex).X n) :=
    G.injective_obj (K.cocomplex.X n)
  exact (CochainComplex.quasiIso_iff_of_injective (transposeLift T β)).1
    (transposeLift_quasiIso T I K β hβ)

set_option backward.isDefEq.respectTransparency false in
private lemma map_transposeLift_quasiIso (T : Scheme.{u})
    {F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}} (I : InjectiveResolution F)
    (K : InjectiveResolution
      ((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj F))
    (β : pulledResolution T I.cocomplex ⟶ K.cocomplex)
    (hβ : IsLift T (𝟙 _) I K β)
    (H : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1})
    [H.Additive] :
    QuasiIso (extendMap ((H.mapHomologicalComplex (.up ℕ)).map (transposeLift T β))
      ComplexShape.embeddingUpNat) := by
  obtain ⟨e, he⟩ := transposeLift_equivalence T I K β hβ
  have : QuasiIso ((H.mapHomologicalComplex (.up ℕ)).map (transposeLift T β)) := by
    rw [← he]
    exact (H.mapHomotopyEquiv e).quasiIso_hom
  infer_instance

private noncomputable def supportedCoefficientMap
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {V W : C} (f : W ⟶ V)
    {I I' : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℕ} (φ : I ⟶ I') :
    supported J f I ⟶ supported J f I' :=
  extendMap (((Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} f).mapHomologicalComplex
     (.up ℕ)).map φ) ComplexShape.embeddingUpNat

set_option backward.isDefEq.respectTransparency false in
private lemma supportedCoefficientMap_inclusion
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {V W : C} (f : W ⟶ V)
    {I I' : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℕ} (φ : I ⟶ I') :
    supportedCoefficientMap J f φ ≫ supportedInclusion J f I' =
      supportedInclusion J f I ≫ coefficientMap J V φ := by
  dsimp only [supportedCoefficientMap, supportedInclusion, coefficientMap]
  rw [← extendMap_comp, ← extendMap_comp]
  congr 1
  exact (NatTrans.mapHomologicalComplex (forgetSupport J f) (.up ℕ)).naturality φ

set_option backward.isDefEq.respectTransparency false in
private lemma supportedCoefficientMap_comparison (T : Scheme.{u}) {V W : T.Etale}
    (f : W ⟶ V)
    {K K' : CochainComplex (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) ℕ}
    (φ : K ⟶ K') :
    supportedCoefficientMap (Scheme.ProEt.topology T) ((Scheme.toProEt T).map f) φ =
      supportedCoefficientMap T.smallEtaleTopology f
        (((ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T).mapHomologicalComplex
          (.up ℕ)).map φ) := by
  dsimp only [supportedCoefficientMap]
  congr 1


set_option backward.isDefEq.respectTransparency false in
private lemma coefficient_homologySquare
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]
    {V W : C} (f : W ⟶ V)
    {F F' : Sheaf J AddCommGrpCat.{u + 1}}
    (I : InjectiveResolution F) (I' : InjectiveResolution F')
    (R : Realization J f I) (R' : Realization J f I')
    (φ : I.cocomplex ⟶ I'.cocomplex)
    (h : coefficientMap J V φ ≫ restrictionComplex J f I'.cocomplex =
      restrictionComplex J f I.cocomplex ≫ coefficientMap J W φ) (q : ℤ) :
    (realizationIso J R q).hom ≫ homologyMap (relativeFiberMap _ _ (coefficientMap J V φ)
          (coefficientMap J W φ) h) q =
      homologyMap (supportedCoefficientMap J f φ) q ≫ (realizationIso J R' q).hom :=
  realization_modelSquare J J f f I I' R R' _ _ h
    (supportedCoefficientMap J f φ) (supportedCoefficientMap_inclusion J f φ) q

private lemma fiberMap_square
    {A₀ B₀ A₁ B₁ A₂ B₂ A₃ B₃ : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r₀ : A₀ ⟶ B₀) (r₁ : A₁ ⟶ B₁) (r₂ : A₂ ⟶ B₂) (r₃ : A₃ ⟶ B₃)
    (a₀₁ : A₀ ⟶ A₁) (b₀₁ : B₀ ⟶ B₁) (a₁₃ : A₁ ⟶ A₃) (b₁₃ : B₁ ⟶ B₃)
    (a₀₂ : A₀ ⟶ A₂) (b₀₂ : B₀ ⟶ B₂) (a₂₃ : A₂ ⟶ A₃) (b₂₃ : B₂ ⟶ B₃)
    (h₀₁ : a₀₁ ≫ r₁ = r₀ ≫ b₀₁) (h₁₃ : a₁₃ ≫ r₃ = r₁ ≫ b₁₃)
    (h₀₂ : a₀₂ ≫ r₂ = r₀ ≫ b₀₂) (h₂₃ : a₂₃ ≫ r₃ = r₂ ≫ b₂₃)
    (ha : a₀₁ ≫ a₁₃ = a₀₂ ≫ a₂₃) (hb : b₀₁ ≫ b₁₃ = b₀₂ ≫ b₂₃) :
    relativeFiberMap r₀ r₁ a₀₁ b₀₁ h₀₁ ≫ relativeFiberMap r₁ r₃ a₁₃ b₁₃ h₁₃ =
      relativeFiberMap r₀ r₂ a₀₂ b₀₂ h₀₂ ≫ relativeFiberMap r₂ r₃ a₂₃ b₂₃ h₂₃ := by
  unfold relativeFiberMap
  rw [← Functor.map_comp, ← Functor.map_comp,
    ← homotopyCofiber.mapArrowHom_comp, ← homotopyCofiber.mapArrowHom_comp]
  congr 1
  congr 1
  exact Arrow.hom_ext _ _ ha hb

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exists_topologyComparison (T : Scheme.{u})
    (E : System T.smallEtaleTopology (fun {_ _} f ↦ IsOpenImmersion f.left))
    (P : System (Scheme.ProEt.topology T)
      (fun {V _} f ↦ IsOpenImmersion f.left ∧ Etale V.hom)) :
    Nonempty (TopologyComparison T E P) := by
  have et (V : T.Etale) : Etale ((Scheme.toProEt T).obj V).hom := by
    change Etale V.hom
    infer_instance
  have hh {V W : T.Etale} (f : W ⟶ V) (hf : IsOpenImmersion f.left)
      {F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
      {F' : Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}}
      (I : InjectiveResolution F) (K : InjectiveResolution F')
      (β : pulledResolution T I.cocomplex ⟶ K.cocomplex) (q : ℤ) :=
    realization_modelSquare T.smallEtaleTopology (Scheme.ProEt.topology T)
      f ((Scheme.toProEt T).map f) I K (E.realization f hf I)
      (P.realization ((Scheme.toProEt T).map f) ⟨hf, et V⟩ K)
      (pullbackSections T V β) (pullbackSections T W β)
      (topologySquare T f β) (supportPullback T f β)
      (supportPullback_inclusion T f β) q
  refine ⟨{
    lift_exists := exists_lift T
    square := topologySquare T
    sections_isIso := ?_
    cone_isIso := ?_
    support := ?_
    projection_boundary := ?_
    lift_independence := ?_
    postcomposition := ?_
    coefficients := ?_
    objects := ?_ }⟩
  · intro V F I K β hβ q
    have : QuasiIso (pullbackSections T V β) :=
      map_transposeLift_quasiIso T I K β hβ (evaluationFunctor T.smallEtaleTopology V)
    infer_instance
  · intro V W f hf F I K β hβ q
    have : QuasiIso (supportPullback T f β) :=
      map_transposeLift_quasiIso T I K β hβ
        (Sheaf.supportedSectionsFunctor T.smallEtaleTopology AddCommGrpCat.{u + 1} f)
    apply (isIso_comp_left_iff
      (realizationIso T.smallEtaleTopology (E.realization f hf I) (q : ℤ)).hom _).1
    rw [hh f hf I K β]
    infer_instance
  · intro V W f hf F F' γ I K β hβ q
    exact realization_transport T.smallEtaleTopology (Scheme.ProEt.topology T)
      f ((Scheme.toProEt T).map f) I K (E.realization f hf I)
      (P.realization ((Scheme.toProEt T).map f) ⟨hf, et V⟩ K)
      (pullbackSections T V β) (pullbackSections T W β) (topologySquare T f β) q
  · intro V W f hf I K β
    exact triangleSquare (restrictionComplex T.smallEtaleTopology f I)
      (restrictionComplex (Scheme.ProEt.topology T) ((Scheme.toProEt T).map f) K)
      (pullbackSections T V β) (pullbackSections T W β) (topologySquare T f β)
  · intro V W f hf F F' γ I K β β' hβ hβ' q
    have heq : homologyMap (supportPullback T f β) (q : ℤ) =
        homologyMap (supportPullback T f β') (q : ℤ) :=
      (((Sheaf.supportedSectionsFunctor T.smallEtaleTopology AddCommGrpCat.{u + 1} f).mapHomotopy
         (transposeLift_homotopy T γ I K β β' hβ hβ')).extend
          ComplexShape.embeddingUpNat).homologyMap_eq (q : ℤ)
    apply (cancel_epi (realizationIso T.smallEtaleTopology (E.realization f hf I) (q : ℤ)).hom).1
    rw [hh f hf I K β, hh f hf I K β', heq]
  · intro V W f hf F F' F'' γ δ I K K' β β' φ hφ h hβ hβ' q
    let G := ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T
    have hβφ : IsLift T (γ ≫ δ) I K' (β ≫ φ) := by
      change _ ≫ (β.f 0 ≫ φ.f 0) = (γ ≫ δ) ≫ _
      rw [← Category.assoc, hβ, Category.assoc, hφ, Category.assoc]
    have heq₀ :=
      (((Sheaf.supportedSectionsFunctor T.smallEtaleTopology AddCommGrpCat.{u + 1} f).mapHomotopy
         (transposeLift_homotopy T (γ ≫ δ) I K' β' (β ≫ φ)
          hβ' hβφ)).extend ComplexShape.embeddingUpNat).homologyMap_eq (q : ℤ)
    have heq : homologyMap (supportPullback T f β') (q : ℤ) =
        homologyMap (supportPullback T f β) (q : ℤ) ≫
          homologyMap (supportedCoefficientMap (Scheme.ProEt.topology T)
            ((Scheme.toProEt T).map f) φ) (q : ℤ) := by
      rw [← homologyMap_comp]
      refine heq₀.trans ?_
      congr 1
      let H := (Sheaf.supportedSectionsFunctor T.smallEtaleTopology
        AddCommGrpCat.{u + 1} f).mapHomologicalComplex (.up ℕ)
      change extendMap (H.map (transposeLift T (β ≫ φ))) _ =
        extendMap (H.map (transposeLift T β)) _ ≫
          extendMap (H.map ((G.mapHomologicalComplex (.up ℕ)).map φ)) _
      rw [← extendMap_comp, ← Functor.map_comp]
      congr 2
    apply (cancel_epi (realizationIso T.smallEtaleTopology (E.realization f hf I) (q : ℤ)).hom).1
    rw [hh f hf I K' β', reassoc_of% (hh f hf I K β)]
    rw [coefficient_homologySquare (Scheme.ProEt.topology T) ((Scheme.toProEt T).map f) K K'
      (P.realization ((Scheme.toProEt T).map f) ⟨hf, et V⟩ K)
      (P.realization ((Scheme.toProEt T).map f) ⟨hf, et V⟩ K') φ h]
    simpa only [Category.assoc] using congrArg
      (fun t ↦ t ≫ (realizationIso (Scheme.ProEt.topology T)
        (P.realization ((Scheme.toProEt T).map f) ⟨hf, et V⟩ K') (q : ℤ)).hom) heq
  · intro V W f hf F F₁ α I I₁ K K₁ β β₁ φ ψ hφ hψ h hp hβ hβ₁ q
    let G := ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T
    let η := (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit
    have : G.PreservesInjectiveObjects :=
      Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
        (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T)
    have (n : ℕ) : Injective (((G.mapHomologicalComplex (.up ℕ)).obj K₁.cocomplex).X n) :=
      G.injective_obj (K₁.cocomplex.X n)
    have ha : I.ι.f 0 ≫ (transposeLift T β).f 0 = η.app F ≫ G.map (K.ι.f 0) := by
      calc
        I.ι.f 0 ≫ (transposeLift T β).f 0 =
            η.app F ≫ G.map (𝟙 _) ≫ G.map (K.ι.f 0) :=
          transposeLift_augmentation T (𝟙 _) I K β hβ
        _ = η.app F ≫ G.map (K.ι.f 0) := by
          rw [G.map_id]
          exact congrArg (fun t ↦ η.app F ≫ t) (Category.id_comp (G.map (K.ι.f 0)))
    have ha₁ : I₁.ι.f 0 ≫ (transposeLift T β₁).f 0 =
        η.app F₁ ≫ G.map (K₁.ι.f 0) := by
      calc
        I₁.ι.f 0 ≫ (transposeLift T β₁).f 0 =
            η.app F₁ ≫ G.map (𝟙 _) ≫ G.map (K₁.ι.f 0) :=
          transposeLift_augmentation T (𝟙 _) I₁ K₁ β₁ hβ₁
        _ = η.app F₁ ≫ G.map (K₁.ι.f 0) := by
          rw [G.map_id]
          exact congrArg (fun t ↦ η.app F₁ ≫ t) (Category.id_comp (G.map (K₁.ι.f 0)))
    have haug : I.ι.f 0 ≫ (φ ≫ transposeLift T β₁).f 0 =
        I.ι.f 0 ≫ (transposeLift T β ≫ (G.mapHomologicalComplex (.up ℕ)).map ψ).f 0 := by
      change I.ι.f 0 ≫ (φ.f 0 ≫ (transposeLift T β₁).f 0) =
        I.ι.f 0 ≫ ((transposeLift T β).f 0 ≫ G.map (ψ.f 0))
      rw [← Category.assoc, hφ, Category.assoc, ha₁,
        ← Category.assoc (I.ι.f 0), ha, Category.assoc, ← G.map_comp, hψ, G.map_comp]
      have hn := η.naturality α
      dsimp only [Functor.id_map, Functor.comp_map] at hn
      simpa only [Category.assoc] using
        congrArg (fun t ↦ t ≫ G.map (K₁.ι.f 0)) hn
    let ht := CochainComplex.homotopyOfQuasiIso I.ι (φ ≫ transposeLift T β₁)
      (transposeLift T β ≫ (G.mapHomologicalComplex (.up ℕ)).map ψ) haug
    have heq₀ :=
      (((Sheaf.supportedSectionsFunctor T.smallEtaleTopology AddCommGrpCat.{u + 1} f).mapHomotopy
         ht).extend ComplexShape.embeddingUpNat).homologyMap_eq (q : ℤ)
    have heq :
        homologyMap (supportedCoefficientMap T.smallEtaleTopology f φ) (q : ℤ) ≫
          homologyMap (supportPullback T f β₁) (q : ℤ) =
        homologyMap (supportPullback T f β) (q : ℤ) ≫
          homologyMap (supportedCoefficientMap (Scheme.ProEt.topology T)
            ((Scheme.toProEt T).map f) ψ) (q : ℤ) := by
      rw [supportedCoefficientMap_comparison]
      dsimp only [supportedCoefficientMap, supportPullback]
      simpa only [Functor.map_comp, extendMap_comp, homologyMap_comp] using heq₀
    apply (cancel_epi (realizationIso T.smallEtaleTopology (E.realization f hf I) (q : ℤ)).hom).1
    rw [reassoc_of% (coefficient_homologySquare T.smallEtaleTopology f I I₁
      (E.realization f hf I) (E.realization f hf I₁) φ h (q : ℤ)),
      hh f hf I₁ K₁ β₁, reassoc_of% (hh f hf I K β)]
    rw [coefficient_homologySquare (Scheme.ProEt.topology T) ((Scheme.toProEt T).map f) K K₁
      (P.realization ((Scheme.toProEt T).map f) ⟨hf, et V⟩ K)
      (P.realization ((Scheme.toProEt T).map f) ⟨hf, et V⟩ K₁) ψ hp]
    simpa only [Category.assoc] using congrArg
      (fun t ↦ t ≫ (realizationIso (Scheme.ProEt.topology T)
        (P.realization ((Scheme.toProEt T).map f) ⟨hf, et V⟩ K₁) (q : ℤ)).hom) heq
  · intro V W V' W' f f' hf hf' v w hs I K β h hp
    exact fiberMap_square _ _ _ _ _ _ _ _ _ _ _ _ h (topologySquare T f' β)
      (topologySquare T f β) hp (topologySquare T v β).symm (topologySquare T w β).symm


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
identifications. The kernel inclusion gives forgetting support. The theorem
`CochainComplex.kernelShiftedCone_boundary` identifies the connecting map of the kernel
sequence with shifted `inr`, hence `(0,-b)` in the signed model. Coordinate uniqueness
makes every kernel/cone square commute. Naturality of the injective-resolution
computation gives coefficient and object/support restriction compatibility.
Step 4: exactness of L makes L(I) a resolution of L(F). Lift it to a pro-etale injective
resolution K. This lift β is a quasi-isomorphism between complexes of G-acyclic objects:
L(I^n) is G-acyclic by `lem-cbc-abelian-comparison-injective-acyclicity`, while K^n is
injective. The acyclic-resolution comparison criterion makes Gβ a quasi-isomorphism.
Compose with the unit isomorphism of `lem-weil-pbc-comparison-grothendieck-unit` to obtain
a quasi-isomorphism I→G(K). The right adjoint G preserves injectives because L is exact.
Thus this map is a homotopy equivalence of nonnegative complexes of injectives. Applying
any additive functor, in particular evaluation at an etale object or supported sections,
preserves this equivalence. Its extension by zero is consequently a quasi-isomorphism.
Step 5: the kernel/cone squares transfer these homology isomorphisms to the cones and
identify the support maps. For arbitrary coefficient maps, two transposed augmented
lifts into a complex of injectives are homotopic. Apply supported sections and cancel
the kernel-to-cone homology isomorphism to obtain lift independence and postcomposition.
The same argument, using unit naturality on the augmentation, gives coefficient
compatibility. Object restriction squares commute strictly, and cone functoriality gives
their composite square. The component formulas give projection and boundary naturality. -/
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
  obtain ⟨E⟩ := RelativeCone.exists_system T.smallEtaleTopology
    (fun {_ _} f ↦ IsOpenImmersion f.left) (by
      intro V W f hf
      let : IsOpenImmersion f.left := hf
      exact (MorphismProperty.Over.forget @Etale ⊤ T ⋙ Over.forget T).mono_of_mono_map
         (by change Mono f.left; infer_instance))
  obtain ⟨P⟩ := RelativeCone.exists_system (Scheme.ProEt.topology T)
    (fun {V _} f ↦ IsOpenImmersion f.left ∧ Etale V.hom) (by
      intro V W f hf
      let : IsOpenImmersion f.left := hf.1
      exact (MorphismProperty.Over.forget @WeaklyEtale ⊤ T ⋙ Over.forget T).mono_of_mono_map
         (by change Mono f.left; infer_instance))
  refine ⟨E, P, fun q ↦ (E.realization (supportRestrictionArrow i)
    (by change IsOpenImmersion i.openComplement.ι; infer_instance) I).e q,
    RelativeCone.exists_topologyComparison T E P, fun q ↦ rfl⟩

end Etale
end AlgebraicGeometry
