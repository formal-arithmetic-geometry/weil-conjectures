/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Relative.RelativeEtaleCohomology
public import Submission.WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.Refinements
import Submission.WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolution
import Submission.WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Submission.WeilConjectures.CategoryTheory.Sites.SheafCohomologyTorsion
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

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

end RelativeCone

end Etale
end AlgebraicGeometry
