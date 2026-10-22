/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
public import Sheaf.AlgebraicGeometry.ProEtaleModulePullbackComposition
public import Sheaf.AlgebraicGeometry.ProEtaleTensorCompositionUnit
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Endomorphism
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Normalized sheaf insertion at an automorphic point

Source: Stacks Project, Sites and Sheaves, Tags 03CE, 03CB and 06UM;
Modules on Sites, Tags 03CZ, 03EK and 03D3; Deligne, Weil II, (1.1.7)
(blueprint: lem-trf-point-sheaf-insertion-calculus).

The natural-number index `n` denotes the positive exponent `n + 1` throughout.
All helper constructions use the original small pro-etale site, with object universe
`u + 1` and morphism universe `u`. Coefficients and modules use the standard `ULift`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Ordinary tensor pullback along the positive power `h^(n+1)`.
Source: Stacks 03D2 (blueprint: lem-trf-point-sheaf-insertion-calculus). -/
abbrev pointSheafPullback {s : Scheme.{u}} (h : Aut s) (A : Type u) [CommRing A]
    (n : ℕ) :=
  proEtaleConstantRingPullback A (h ^ (n + 1)).hom

/-- The constant-ring comparison for restriction along an automorphism. It is the
sheafification compatibility of the continuous and cocontinuous postcomposition functor,
so its hom preserves each constant section.
Source: Stacks 03CE and 0H7J (blueprint: lem-trf-point-sheaf-insertion-calculus). -/
def pointSheafRestrictionCoefficients {s : Scheme.{u}} (h : Aut s)
    (A : Type u) [CommRing A] (n : ℕ) :
    proEtaleConstantRing s A ≅
      (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        (h ^ (n + 1)).hom (inferInstance : WeaklyEtale (h ^ (n + 1)).hom)).obj
          (proEtaleConstantRing s A) :=
  let F := MorphismProperty.Over.map (f := (h ^ (n + 1)).hom) (P := @WeaklyEtale)
    ⊤ (inferInstance : WeaklyEtale (h ^ (n + 1)).hom)
  letI : F.IsContinuous (ProEt.topology s) (ProEt.topology s) :=
    ProEt.isContinuous_overMap (inferInstance : WeaklyEtale (h ^ (n + 1)).hom)
  letI : F.IsCocontinuous (ProEt.topology s) (ProEt.topology s) :=
    ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale (h ^ (n + 1)).hom)
  (F.pushforwardContinuousSheafificationCompatibility CommRingCat.{u + 1}
    (ProEt.topology s) (ProEt.topology s)).app
      ((Functor.const s.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))

/-- Reindex module sections by postcomposition with `h^(n+1)`. Scalars are transported
by the canonical constant-ring restriction comparison, not an arbitrary ring map.
Source: Stacks 03CE (blueprint: lem-trf-point-sheaf-insertion-calculus). -/
abbrev pointSheafRestriction {s : Scheme.{u}} (h : Aut s) (A : Type u) [CommRing A]
    (n : ℕ) :=
  proEtaleObjectModuleRestriction (ProEt.mk (h ^ (n + 1)).hom) A
    (pointSheafRestrictionCoefficients h A n)

/-- The graph `(u,id)` in the inverse-image comma index. Mathlib orders the fibre
product factors as `(U,s)`; this is `(id,u)` in that order.
Source: Stacks 03CE and 00VC (blueprint: lem-trf-point-sheaf-insertion-calculus). -/
abbrev pointSheafGraph {s : Scheme.{u}} (h : Aut s) (n : ℕ) (U : s.ProEt) :=
  (proEtaleObjectInverseImageIndexPoint (ProEt.mk (h ^ (n + 1)).hom) U).hom

/-- The graph-index colimit insertion, sheafification, and scalar unit. The published
module adjunction is normalized by precisely that tensor insertion.
Source: Stacks 03D3 and 00VC (blueprint: lem-trf-point-sheaf-insertion-calculus). -/
def pointSheafGraphInsertion {s : Scheme.{u}} (h : Aut s) (A : Type u) [CommRing A]
    (n : ℕ) (F : proEtaleRingModules s (proEtaleConstantRing s A)) (U : s.ProEt)
    (x : F.val.obj (op ((MorphismProperty.Over.map (f := (h ^ (n + 1)).hom)
      (P := @WeaklyEtale) ⊤ (inferInstance : WeaklyEtale (h ^ (n + 1)).hom)).obj U))) :
    ((pointSheafPullback h A n).obj F).val.obj (op U) :=
  proEtalePullbackTensorGenerator (h ^ (n + 1)).hom
    (proEtaleConstantRing s A) (proEtaleConstantRing s A)
    (proEtaleConstantRingComparison (h ^ (n + 1)).hom A) F _ U
    (pointSheafGraph h n U) x 1

/-- Restriction along `h^(n+1) : (s,h^(n+1)) → (s,id)`.
Source: Stacks 06UM (blueprint: lem-trf-point-sheaf-insertion-calculus). -/
def pointSheafRestrictionArrow {s : Scheme.{u}} (h : Aut s) (n : ℕ) :
    ProEt.mk (h ^ (n + 1)).hom ⟶ ProEt.mk (𝟙 s) :=
  MorphismProperty.Over.homMk (h ^ (n + 1)).hom (Category.comp_id _)

/-- The specified section insertion `j`: first restrict, then insert at the graph and
extend scalars by the tensor unit.
Source: Stacks 06UM (blueprint: lem-trf-point-sheaf-insertion-calculus). -/
def pointSheafInsertion {s : Scheme.{u}} (h : Aut s) (A : Type u) [CommRing A]
    (n : ℕ) (F : proEtaleRingModules s (proEtaleConstantRing s A))
    (x : F.val.obj (op (ProEt.mk (𝟙 s)))) :
    ((pointSheafPullback h A n).obj F).val.obj (op (ProEt.mk (𝟙 s))) :=
  pointSheafGraphInsertion h A n F (ProEt.mk (𝟙 s))
    (F.val.map (pointSheafRestrictionArrow h n).op x)

/-- Sections at the final object with scalars restricted along the actual constant
section homomorphism. `ULift A` is canonically the original ring `A`.
Source: Stacks 06UM and 0H7J (blueprint: lem-trf-point-sheaf-insertion-calculus). -/
abbrev pointSheafSections (s : Scheme.{u}) (A : Type u) [CommRing A] :
    proEtaleRingModules s (proEtaleConstantRing s A) ⥤
      ModuleCat.{u + 1} (ULift.{u + 1, u} A) :=
  SheafOfModules.forget
    ((sheafCompose (ProEt.topology s) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (proEtaleConstantRing s A)) ⋙
    PresheafOfModules.evaluation _ (op (ProEt.mk (𝟙 s))) ⋙
    ModuleCat.restrictScalars
      ((toSheafify (ProEt.topology s)
        ((Functor.const s.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app
          (op (ProEt.mk (𝟙 s)))).hom

/-- The canonical module compositor, oriented from successive to direct pullback.
Its chosen presentation comes from the uniquely characterized adjunction comparison;
the last equality merely identifies the composite power with `h^(m+2)`.
Source: Stacks 03CB and 03D3 (blueprint: lem-trf-point-sheaf-insertion-calculus). -/
def pointSheafCompositor {s : Scheme.{u}} (h : Aut s) (A : Type u) [CommRing A]
    (m : ℕ) :
    pointSheafPullback h A m ⋙ pointSheafPullback h A 0 ≅
      pointSheafPullback h A (m + 1) :=
  (proEtaleConstantRingModulePullbackComposition (h ^ (0 + 1)).hom
    (h ^ (m + 1)).hom A).choose.symm ≪≫
      eqToIso (congrArg (proEtaleConstantRingPullback A)
        (by
          simp only [zero_add, pow_one]
          exact (congrArg Iso.hom (pow_succ h (m + 1))).symm))

/-- The canonical identification of direct and successive reindexing site objects.
Source: Stacks 03CB (blueprint: lem-trf-point-sheaf-insertion-calculus). -/
def pointSheafReindexCompositor {s : Scheme.{u}} (h : Aut s) (m : ℕ) :=
  MorphismProperty.Over.mapComp (Q := ⊤)
    (inferInstance : WeaklyEtale (h ^ (0 + 1)).hom)
    (inferInstance : WeaklyEtale (h ^ (m + 1)).hom)
    (h ^ ((m + 1) + 1)).hom
    (by
      simp only [zero_add, pow_one]
      exact congrArg Iso.hom (pow_succ h (m + 1)))

/-- Cochain complexes of sections, with their actual sectionwise differentials.
Source: Stacks 06UM (blueprint: lem-trf-point-sheaf-insertion-calculus). -/
abbrev pointSheafSectionComplex (s : Scheme.{u}) (A : Type u) [CommRing A] :=
  (pointSheafSections s A).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Termwise ordinary pullback of cochain complexes.
Source: Stacks 06UM (blueprint: lem-trf-point-sheaf-insertion-calculus). -/
abbrev pointSheafPullbackComplex {s : Scheme.{u}} (h : Aut s) (A : Type u) [CommRing A]
    (n : ℕ) :=
  (pointSheafPullback h A n).mapHomologicalComplex (ComplexShape.up ℤ)

private theorem sectionFunctor_preservesZero (s : Scheme.{u})
    (A : Type u) [CommRing A] : (pointSheafSections s A).PreservesZeroMorphisms := by
  infer_instance

private theorem pullbackFunctor_preservesZero {s : Scheme.{u}} (h : Aut s)
    (A : Type u) [CommRing A] (n : ℕ) :
    (pointSheafPullback h A n).PreservesZeroMorphisms := by
  infer_instance

attribute [local instance] sectionFunctor_preservesZero pullbackFunctor_preservesZero

attribute [local irreducible] proEtaleRingModulePullback
  proEtaleRingModulePullbackObj
  proEtaleRingModulePullbackMap proEtaleRingModuleAdjunction
  pointSheafCompositor

private theorem coefficientDirect_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] (U : Y.ProEtᵒᵖ) :
    (toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app U ≫
      (proEtaleCoefficientDirectImageMap f A).hom.app U =
    (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app
        ((proEtaleBaseChange f).op.obj U) := by
  have h := ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))
      ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        (proEtaleConstantRing X A))).apply_symm_apply
      (Functor.whiskerLeft (proEtaleBaseChange f).op
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))))
  exact congrArg (fun z ↦ z.app U) h
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficient_restriction_counit {X : Scheme.{u}} (W : X.ProEt)
    (A : Type u) [CommRing A]
    (e : proEtaleConstantRing W.left A ≅
      (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        W.hom W.prop).obj (proEtaleConstantRing X A))
    (he : ∀ U : W.left.ProEt,
      (toSheafify (ProEt.topology W.left)
        ((Functor.const W.left.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))).app (op U) ≫ e.hom.hom.app (op U) =
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1, u} A)))).app
              (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U))) :
    Functor.whiskerRight (NatTrans.op
      (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom W.prop trivial).counit)
        (proEtaleConstantRing X A).obj =
      (proEtaleCoefficientDirectImageMap W.hom A).hom ≫
        (proEtaleBaseChange W.hom).op.whiskerLeft e.hom.hom := by
  let T := (proEtaleSheafDirectImage W.hom CommRingCat.{u + 1}).obj
    ((AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
      W.hom W.prop).obj (proEtaleConstantRing X A))
  apply sheafify_hom_ext (ProEt.topology X) _ _ T.property
  apply NatTrans.ext
  funext U
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← Category.assoc, coefficientDirect_unit]
  erw [he]
  have h := (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).naturality
      ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤
        W.hom W.prop trivial).counit.app U.unop).op
  simpa [proEtaleConstantRing, constantSheaf, proEtaleBaseChange] using h.symm

set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficient_restriction_unit {X : Scheme.{u}} (W : X.ProEt)
    (A : Type u) [CommRing A]
    (e : proEtaleConstantRing W.left A ≅
      (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        W.hom W.prop).obj (proEtaleConstantRing X A))
    (he : ∀ U : W.left.ProEt,
      (toSheafify (ProEt.topology W.left)
        ((Functor.const W.left.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))).app (op U) ≫ e.hom.hom.app (op U) =
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1, u} A)))).app
              (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U))) :
    e.hom.hom ≫ (MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).op.whiskerLeft
      (proEtaleCoefficientDirectImageMap W.hom A).hom ≫
      Functor.whiskerRight (NatTrans.op
        (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom W.prop trivial).unit)
          (proEtaleConstantRing W.left A).obj = 𝟙 _ := by
  apply sheafify_hom_ext (ProEt.topology W.left) _ _ (proEtaleConstantRing W.left A).property
  apply NatTrans.ext
  funext U
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.id_app]
  rw [← Category.assoc, ← Category.assoc, he]
  erw [coefficientDirect_unit]
  have h := (toSheafify (ProEt.topology W.left)
    ((Functor.const W.left.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).naturality
      ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤
        W.hom W.prop trivial).unit.app U.unop).op
  simpa [proEtaleConstantRing, constantSheaf, proEtaleBaseChange] using h.symm

set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def pointRestrictionAdjunction {X : Scheme.{u}} (W : X.ProEt)
    (A : Type u) [CommRing A]
    (e : proEtaleConstantRing W.left A ≅
      (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        W.hom W.prop).obj (proEtaleConstantRing X A))
    (he : ∀ U : W.left.ProEt,
      (toSheafify (ProEt.topology W.left)
        ((Functor.const W.left.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))).app (op U) ≫ e.hom.hom.app (op U) =
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1, u} A)))).app
              (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U))) :
    proEtaleObjectModuleRestriction W A e ⊣ proEtaleConstantRingPushforward A W.hom := by
  let : (MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).IsContinuous
      (ProEt.topology W.left) (ProEt.topology X) :=
    ProEt.isContinuous_overMap (V := W.left) (U := X) W.prop
  let : (proEtaleBaseChange W.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology W.left) :=
    ProEt.isContinuous_overPullback W.hom
  let R := proEtaleConstantRing X A
  let S := proEtaleConstantRing W.left A
  let c := asIso (proEtaleCoefficientInverseImageMap W.hom A)
  have hψ : proEtaleRingDirectImageMap W.hom R S c =
      proEtaleCoefficientDirectImageMap W.hom A := by
    exact ((proEtaleSheafAdjunction W.hom CommRingCat.{u + 1}).homEquiv R S).apply_symm_apply
      (proEtaleCoefficientDirectImageMap W.hom A)
  let φ : ((sheafCompose (ProEt.topology W.left)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) ⟶
      ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).sheafPushforwardContinuous
        RingCat.{u + 1} (ProEt.topology W.left) (ProEt.topology X)).obj
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) :=
    ⟨Functor.whiskerRight e.hom.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let ψ : ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⟶
      ((proEtaleBaseChange W.hom).sheafPushforwardContinuous
        RingCat.{u + 1} (ProEt.topology X) (ProEt.topology W.left)).obj
        ((sheafCompose (ProEt.topology W.left)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) :=
    ⟨Functor.whiskerRight (proEtaleRingDirectImageMap W.hom R S c).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom W.prop trivial
  have H₁ : Functor.whiskerRight (NatTrans.op adj.counit) R.obj =
      (proEtaleCoefficientDirectImageMap W.hom A).hom ≫
        (proEtaleBaseChange W.hom).op.whiskerLeft e.hom.hom :=
    coefficient_restriction_counit W A e he
  have H₂ := coefficient_restriction_unit W A e he
  have H₁' : Functor.whiskerRight (NatTrans.op adj.counit)
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj =
      ψ.hom ≫ (proEtaleBaseChange W.hom).op.whiskerLeft φ.hom := by
    apply NatTrans.ext
    funext U
    dsimp only [ψ, φ, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    rw [hψ]
    exact congrArg (fun t ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      (t.app U)) H₁
  have H₂' : φ.hom ≫
      (MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op adj.unit)
        ((sheafCompose (ProEt.topology W.left)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj = 𝟙 _ := by
    apply NatTrans.ext
    funext U
    dsimp only [ψ, φ, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    rw [hψ]
    exact congrArg (fun t ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      (t.app U)) H₂
  exact SheafOfModules.pushforwardPushforwardAdj.{u + 1} adj φ ψ H₁' H₂'

private def GraphNormalized {s : Scheme.{u}} (h : Aut s)
    (A : Type u) [CommRing A] (n : ℕ)
    (e : pointSheafPullback h A n ≅ pointSheafRestriction h A n) : Prop :=
  ∀ (F : proEtaleRingModules s (proEtaleConstantRing s A)) (U : s.ProEt)
        (x : F.val.obj (op ((MorphismProperty.Over.map (f := (h ^ (n + 1)).hom)
          (P := @WeaklyEtale) ⊤
            (inferInstance : WeaklyEtale (h ^ (n + 1)).hom)).obj U))),
        (e.hom.app F).val.app (op U) (pointSheafGraphInsertion h A n F U x) = x

set_option backward.isDefEq.respectTransparency.types false in
private theorem pointRestrictionComparison {s : Scheme.{u}} (h : Aut s)
    (A : Type u) [CommRing A] (n : ℕ) :
    ∃ e : pointSheafPullback h A n ≅ pointSheafRestriction h A n,
      GraphNormalized h A n e := by
  let W := ProEt.mk (h ^ (n + 1)).hom
  have he : ∀ U : s.ProEt,
      (toSheafify (ProEt.topology s)
        ((Functor.const s.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))).app (op U) ≫
          (pointSheafRestrictionCoefficients h A n).hom.hom.app (op U) =
        (toSheafify (ProEt.topology s)
          ((Functor.const s.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1, u} A)))).app
              (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U)) := by
    intro U
    let Q := MorphismProperty.Over.map (f := W.hom) ⊤ W.prop
    let : Q.IsContinuous (ProEt.topology s) (ProEt.topology s) :=
      ProEt.isContinuous_overMap W.prop
    let : Q.IsCocontinuous (ProEt.topology s) (ProEt.topology s) :=
      ProEt.isCocontinuous_overMap W.prop
    exact congrArg (fun f ↦ f.app (op U))
      (Q.toSheafify_pullbackSheafificationCompatibility CommRingCat.{u + 1}
        (ProEt.topology s) (ProEt.topology s)
        ((Functor.const s.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A))))
  let a := pointRestrictionAdjunction W A (pointSheafRestrictionCoefficients h A n) he
  let b := proEtaleConstantRingAdjunction A W.hom
  let e := b.leftAdjointUniq a
  refine ⟨e, ?_⟩
  intro F U x
  let Q := MorphismProperty.Over.map (f := W.hom) ⊤ W.prop
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom W.prop trivial
  have hu := b.unit_leftAdjointUniq_hom_app a F
  have hu' := congrArg (fun z ↦ z.val.app (op (Q.obj U)) x) hu
  have hn := PresheafOfModules.naturality_apply (e.hom.app F).val
    (pointSheafGraph h n U).op
    (((proEtaleConstantRingAdjunction A W.hom).unit.app F).val.app (op (Q.obj U)) x)
  dsimp only [pointSheafGraphInsertion, proEtalePullbackTensorGenerator]
  rw [one_smul]
  change (e.hom.app F).val.app (op U)
    (((pointSheafPullback h A n).obj F).val.map (pointSheafGraph h n U).op
      (((proEtaleConstantRingAdjunction A W.hom).unit.app F).val.app
        (op (Q.obj U)) x)) = x
  erw [hn]
  change F.val.map (Q.map (pointSheafGraph h n U)).op
    ((e.hom.app F).val.app (op ((proEtaleBaseChange W.hom).obj (Q.obj U)))
      (((proEtaleConstantRingAdjunction A W.hom).unit.app F).val.app
        (op (Q.obj U)) x)) = x
  change (e.hom.app F).val.app (op ((proEtaleBaseChange W.hom).obj (Q.obj U)))
    (((proEtaleConstantRingAdjunction A W.hom).unit.app F).val.app
      (op (Q.obj U)) x) = F.val.map (adj.counit.app (Q.obj U)).op x at hu'
  rw [hu']
  change (F.val.presheaf.map (adj.counit.app (Q.obj U)).op ≫
    F.val.presheaf.map (Q.map (adj.unit.app U)).op) x = x
  rw [← Functor.map_comp, ← op_comp]
  erw [adj.left_triangle_components]
  change (F.val.presheaf.map (𝟙 (op (Q.obj U)))) x = x
  exact ConcreteCategory.congr_hom (F.val.presheaf.map_id _) x

set_option backward.isDefEq.respectTransparency.types false in
private theorem pointRestrictionScalar {s : Scheme.{u}} (h : Aut s)
    (A : Type u) [CommRing A] (n : ℕ) (a : ULift.{u + 1, u} A) :
    ((proEtaleConstantRing s A).obj.map (pointSheafRestrictionArrow h n).op).hom
      (((toSheafify (ProEt.topology s)
        ((Functor.const s.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app
          (op (ProEt.mk (𝟙 s)))).hom a) =
    ((pointSheafRestrictionCoefficients h A n).hom.hom.app
      (op (ProEt.mk (𝟙 s)))).hom
      (((toSheafify (ProEt.topology s)
        ((Functor.const s.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app
          (op (ProEt.mk (𝟙 s)))).hom a) := by
  let Q := MorphismProperty.Over.map (f := (h ^ (n + 1)).hom) (P := @WeaklyEtale)
    ⊤ (inferInstance : WeaklyEtale (h ^ (n + 1)).hom)
  let : Q.IsContinuous (ProEt.topology s) (ProEt.topology s) :=
    ProEt.isContinuous_overMap (inferInstance : WeaklyEtale (h ^ (n + 1)).hom)
  let : Q.IsCocontinuous (ProEt.topology s) (ProEt.topology s) :=
    ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale (h ^ (n + 1)).hom)
  have he := congrArg (fun f ↦ f.app (op (ProEt.mk (𝟙 s))))
    (Q.toSheafify_pullbackSheafificationCompatibility CommRingCat.{u + 1}
      (ProEt.topology s) (ProEt.topology s)
      ((Functor.const s.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A))))
  have hn := (toSheafify (ProEt.topology s)
    ((Functor.const s.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1, u} A)))).naturality
        (pointSheafRestrictionArrow h n).op
  exact (ConcreteCategory.congr_hom hn a).symm.trans
    (ConcreteCategory.congr_hom he a).symm

private def sectionRestrictionLinearMap {C : Type (u + 1)} [Category.{u} C]
    (R : Cᵒᵖ ⥤ RingCat.{u + 1}) (F : PresheafOfModules.{u + 1} R)
    {U V : Cᵒᵖ} (a : U ⟶ V) (B : Type (u + 1)) [Ring B]
    (r : B →+* R.obj U) (p : R.obj U →+* R.obj V)
    (ht : ∀ b, (R.map a).hom (r b) = p (r b)) :
    (ModuleCat.restrictScalars r).obj (F.obj U) ⟶
      (ModuleCat.restrictScalars r).obj
        ((ModuleCat.restrictScalars p).obj (F.obj V)) :=
  ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars r).obj (F.obj U))
    (Y := (ModuleCat.restrictScalars r).obj
      ((ModuleCat.restrictScalars p).obj (F.obj V)))
    { toFun := fun x ↦ F.map a x
      map_add' := fun x y ↦ map_add (F.map a).hom x y
      map_smul' := by
        intro b x
        change F.map a (r b • x) = p (r b) • F.map a x
        rw [F.map_smul, ht] }

set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def pointRestrictionSections {s : Scheme.{u}} (h : Aut s)
    (A : Type u) [CommRing A] (n : ℕ) :
    pointSheafSections s A ⟶ pointSheafRestriction h A n ⋙ pointSheafSections s A where
  app F := sectionRestrictionLinearMap _ F.val (pointSheafRestrictionArrow h n).op
    (ULift.{u + 1, u} A)
    ((toSheafify (ProEt.topology s)
      ((Functor.const s.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app
        (op (ProEt.mk (𝟙 s)))).hom
    ((pointSheafRestrictionCoefficients h A n).hom.hom.app
      (op (ProEt.mk (𝟙 s)))).hom
    (pointRestrictionScalar h A n)
  naturality F G v := by
    ext x
    exact (PresheafOfModules.naturality_apply v.val
      (pointSheafRestrictionArrow h n).op x).symm

attribute [local irreducible] constantSheaf

private theorem moduleIso_injective {s : Scheme.{u}} (A : Type u) [CommRing A]
    {F G : proEtaleRingModules s (proEtaleConstantRing s A)} (e : F ≅ G)
    (U : s.ProEt) : Function.Injective (e.hom.val.app (op U)) := by
  intro x y hxy
  have hi (z : F.val.obj (op U)) : e.inv.val.app (op U) (e.hom.val.app (op U) z) = z :=
    congrArg (fun f ↦ f.val.app (op U) z) e.hom_inv_id
  exact (hi x).symm.trans ((congrArg (e.inv.val.app (op U)) hxy).trans (hi y))

private def sectionInsertionMap {s : Scheme.{u}} (h : Aut s)
    (A : Type u) [CommRing A] (n : ℕ)
    (e : pointSheafPullback h A n ≅ pointSheafRestriction h A n) :
    pointSheafSections s A ⟶ pointSheafPullback h A n ⋙ pointSheafSections s A :=
  pointRestrictionSections h A n ≫ Functor.whiskerRight e.inv (pointSheafSections s A)

private theorem sectionInsertionMap_apply {s : Scheme.{u}} (h : Aut s)
    (A : Type u) [CommRing A] (n : ℕ)
    (e : pointSheafPullback h A n ≅ pointSheafRestriction h A n)
    (F : proEtaleRingModules s (proEtaleConstantRing s A))
    (x : F.val.obj (op (ProEt.mk (𝟙 s)))) :
    (sectionInsertionMap h A n e).app F x =
      (e.inv.app F).val.app (op (ProEt.mk (𝟙 s)))
        (F.val.map (pointSheafRestrictionArrow h n).op x) := rfl

attribute [local irreducible] sectionInsertionMap

set_option backward.isDefEq.respectTransparency.types false in
private theorem pointSectionInsertion {s : Scheme.{u}} (h : Aut s)
    (A : Type u) [CommRing A] (n : ℕ)
    (e : pointSheafPullback h A n ≅ pointSheafRestriction h A n)
    (he : GraphNormalized h A n e) :
    (∀ (F : proEtaleRingModules s (proEtaleConstantRing s A))
        (x : F.val.obj (op (ProEt.mk (𝟙 s)))),
        (sectionInsertionMap h A n e).app F x = pointSheafInsertion h A n F x) ∧
      (∀ (F : proEtaleRingModules s (proEtaleConstantRing s A))
        (x : F.val.obj (op (ProEt.mk (𝟙 s)))),
        (e.hom.app F).val.app (op (ProEt.mk (𝟙 s)))
          ((sectionInsertionMap h A n e).app F x) =
          F.val.map (pointSheafRestrictionArrow h n).op x) := by
  let j := sectionInsertionMap h A n e
  have hj (F : proEtaleRingModules s (proEtaleConstantRing s A))
      (x : F.val.obj (op (ProEt.mk (𝟙 s)))) :
      (e.hom.app F).val.app (op (ProEt.mk (𝟙 s))) (j.app F x) =
        F.val.map (pointSheafRestrictionArrow h n).op x := by
    dsimp only [j]
    rw [sectionInsertionMap_apply]
    exact congrArg (fun z ↦ z.val.app (op (ProEt.mk (𝟙 s)))
      (F.val.map (pointSheafRestrictionArrow h n).op x)) (e.inv_hom_id_app F)
  refine ⟨?_, hj⟩
  intro F x
  apply moduleIso_injective A (e.app F) (ProEt.mk (𝟙 s))
  exact (hj F x).trans (he F (ProEt.mk (𝟙 s))
    (F.val.map (pointSheafRestrictionArrow h n).op x)).symm

attribute [local irreducible] pointSheafRestrictionCoefficients
  proEtaleConstantRingComparison

private abbrev constantGenerator {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] :=
  proEtalePullbackTensorGenerator f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
    (proEtaleConstantRingComparison f A)

private noncomputable def constantCompositor {X Y Z : Scheme.{u}}
    (g : Z ⟶ X) (f : X ⟶ Y) (A : Type u) [CommRing A] :
    proEtaleConstantRingPullback A f ⋙ proEtaleConstantRingPullback A g ≅
      proEtaleConstantRingPullback A (g ≫ f) :=
  (proEtaleConstantRingModulePullbackComposition g f A).choose.symm

set_option backward.isDefEq.respectTransparency.types false in
private theorem constantCompositor_unit {X Y Z : Scheme.{u}}
    (g : Z ⟶ X) (f : X ⟶ Y) (A : Type u) [CommRing A]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A)) (U : Y.ProEt)
    (x : F.val.obj (op U)) :
    ((constantCompositor g f A).hom.app F).val.app
      (op ((proEtaleBaseChange g).obj ((proEtaleBaseChange f).obj U)))
      (((proEtaleConstantRingAdjunction A g).unit.app
        ((proEtaleConstantRingPullback A f).obj F)).val.app
          (op ((proEtaleBaseChange f).obj U))
          (((proEtaleConstantRingAdjunction A f).unit.app F).val.app (op U) x)) =
    ((proEtaleConstantRingPullback A (g ≫ f)).obj F).val.map
      ((MorphismProperty.Over.pullbackComp g f).inv.app U).op
      (((proEtaleConstantRingAdjunction A (g ≫ f)).unit.app F).val.app (op U) x) := by
  let a := (proEtaleConstantRingModulePullbackComposition g f A).choose
  obtain ⟨d, hd, hc⟩ := (proEtaleConstantRingModulePullbackComposition g f A).choose_spec
  have hci : (conjugateEquiv (proEtaleConstantRingAdjunction A (g ≫ f))
      ((proEtaleConstantRingAdjunction A f).comp
        (proEtaleConstantRingAdjunction A g))) a.inv = d.inv :=
    congrArg Iso.inv hc
  have hu := unit_conjugateEquiv (proEtaleConstantRingAdjunction A (g ≫ f))
    ((proEtaleConstantRingAdjunction A f).comp (proEtaleConstantRingAdjunction A g))
    a.inv F
  rw [hci, Adjunction.comp_unit_app] at hu
  have hv := congrArg (fun z ↦ z.val.app (op U) x) hu.symm
  have hdinv (N : proEtaleRingModules Z (proEtaleConstantRing Z A))
      (y : ((proEtaleConstantRingPushforward A (g ≫ f)).obj N).val.obj (op U)) :
      (d.inv.app N).val.app (op U) y =
        N.val.map ((MorphismProperty.Over.pullbackComp g f).inv.app U).op y := by
    have hh := congrArg (fun z ↦ z.val.app (op U) y) (d.inv_hom_id_app N)
    change (d.hom.app N).val.app (op U) ((d.inv.app N).val.app (op U) y) = y at hh
    rw [hd] at hh
    have hh' := congrArg (fun z ↦
      N.val.map ((MorphismProperty.Over.pullbackComp g f).inv.app U).op z) hh
    change ((N.val.presheaf.map ((MorphismProperty.Over.pullbackComp g f).hom.app U).op ≫
      N.val.presheaf.map ((MorphismProperty.Over.pullbackComp g f).inv.app U).op))
        ((d.inv.app N).val.app (op U) y) = _ at hh'
    rw [← Functor.map_comp, ← op_comp] at hh'
    erw [Iso.inv_hom_id_app, op_id, CategoryTheory.Functor.map_id] at hh'
    exact hh'
  change ((a.inv.app F).val.app _)
    (((proEtaleConstantRingAdjunction A g).unit.app
      ((proEtaleConstantRingPullback A f).obj F)).val.app _
        (((proEtaleConstantRingAdjunction A f).unit.app F).val.app (op U) x)) =
      (d.inv.app _).val.app (op U)
        (((proEtaleConstantRingAdjunction A (g ≫ f)).unit.app F).val.app (op U) x) at hv
  exact hv.trans (hdinv _ _)

set_option backward.isDefEq.respectTransparency.types false in
private theorem constantCompositor_generators {X Y Z : Scheme.{u}}
    (g : Z ⟶ X) (f : X ⟶ Y) (A : Type u) [CommRing A]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A))
    (U : Y.ProEt) (T : X.ProEt) (P : Z.ProEt)
    (p : T ⟶ (proEtaleBaseChange f).obj U)
    (q : P ⟶ (proEtaleBaseChange g).obj T) (x : F.val.obj (op U)) :
    ((constantCompositor g f A).hom.app F).val.app (op P)
      (constantGenerator g A ((proEtaleConstantRingPullback A f).obj F) T P q
        (constantGenerator f A F U T p x 1) 1) =
    constantGenerator (g ≫ f) A F U P
      (q ≫ (proEtaleBaseChange g).map p ≫
        (MorphismProperty.Over.pullbackComp g f).inv.app U) x 1 := by
  have hu := constantCompositor_unit g f A F U x
  simp only [constantGenerator, proEtalePullbackTensorGenerator, one_smul]
  have hn := PresheafOfModules.naturality_apply
    ((proEtaleConstantRingAdjunction A g).unit.app
      ((proEtaleConstantRingPullback A f).obj F)).val p.op
      (((proEtaleConstantRingAdjunction A f).unit.app F).val.app (op U) x)
  erw [hn]
  let t := constantCompositor g f A
  have hnq := PresheafOfModules.naturality_apply (t.hom.app F).val q.op
    (((proEtaleConstantRingPullback A g).obj
      ((proEtaleConstantRingPullback A f).obj F)).val.map
        ((proEtaleBaseChange g).map p).op
      (((proEtaleConstantRingAdjunction A g).unit.app
        ((proEtaleConstantRingPullback A f).obj F)).val.app
          (op ((proEtaleBaseChange f).obj U))
        (((proEtaleConstantRingAdjunction A f).unit.app F).val.app (op U) x)))
  have hnp := PresheafOfModules.naturality_apply (t.hom.app F).val
    ((proEtaleBaseChange g).map p).op
    (((proEtaleConstantRingAdjunction A g).unit.app
      ((proEtaleConstantRingPullback A f).obj F)).val.app
        (op ((proEtaleBaseChange f).obj U))
      (((proEtaleConstantRingAdjunction A f).unit.app F).val.app (op U) x))
  have heq := hnq.trans (congrArg (fun z ↦
    ((proEtaleConstantRingPullback A (g ≫ f)).obj F).val.map q.op z)
      (hnp.trans (congrArg (fun z ↦
        ((proEtaleConstantRingPullback A (g ≫ f)).obj F).val.map
          ((proEtaleBaseChange g).map p).op z) hu)))
  simp only [op_comp, PresheafOfModules.map_comp_apply]
  convert heq using 1 <;> rfl

private abbrev siteReindex {s : Scheme.{u}} (f : s ⟶ s) [WeaklyEtale f] :=
  MorphismProperty.Over.map (f := f) (P := @WeaklyEtale) ⊤
    (inferInstance : WeaklyEtale f)

private abbrev siteGraph {s : Scheme.{u}} (f : s ⟶ s) [WeaklyEtale f] (U : s.ProEt) :=
  (proEtaleObjectInverseImageIndexPoint (ProEt.mk f) U).hom

private abbrev graphInsertion {s : Scheme.{u}} (f : s ⟶ s) [WeaklyEtale f]
    (A : Type u) [CommRing A]
    (F : proEtaleRingModules s (proEtaleConstantRing s A)) (U : s.ProEt)
    (x : F.val.obj (op ((siteReindex f).obj U))) :=
  constantGenerator f A F _ U (siteGraph f U) x 1

set_option backward.isDefEq.respectTransparency.types false in
private theorem generator_reindex {s : Scheme.{u}} (f : s ⟶ s)
    (A : Type u) [CommRing A]
    (F : proEtaleRingModules s (proEtaleConstantRing s A))
    (U V T : s.ProEt) (a : U ⟶ V) (p : T ⟶ (proEtaleBaseChange f).obj U)
    (x : F.val.obj (op V)) :
    constantGenerator f A F V T (p ≫ (proEtaleBaseChange f).map a) x 1 =
      constantGenerator f A F U T p (F.val.map a.op x) 1 := by
  have hn := PresheafOfModules.naturality_apply
    ((proEtaleConstantRingAdjunction A f).unit.app F).val a.op x
  simp only [constantGenerator, proEtalePullbackTensorGenerator, one_smul, op_comp,
    PresheafOfModules.map_comp_apply]
  exact congrArg (fun y ↦ ((proEtaleConstantRingPullback A f).obj F).val.map p.op y)
    hn.symm

set_option backward.isDefEq.respectTransparency.types false in
private theorem siteGraph_comp {s : Scheme.{u}} (g f : s ⟶ s)
    [WeaklyEtale g] [WeaklyEtale f] (U : s.ProEt) :
    siteGraph g U ≫ (proEtaleBaseChange g).map (siteGraph f ((siteReindex g).obj U)) ≫
      (MorphismProperty.Over.pullbackComp g f).inv.app
        ((siteReindex f).obj ((siteReindex g).obj U)) =
    siteGraph (g ≫ f) U ≫ (proEtaleBaseChange (g ≫ f)).map
      ((MorphismProperty.Over.mapComp (Q := ⊤)
        (inferInstance : WeaklyEtale g) (inferInstance : WeaklyEtale f)).hom.app U) := by
  apply MorphismProperty.Over.Hom.ext
  change (siteGraph g U).left ≫
      ((proEtaleBaseChange g).map (siteGraph f ((siteReindex g).obj U))).left ≫
        ((MorphismProperty.Over.pullbackComp g f).inv.app
          ((siteReindex f).obj ((siteReindex g).obj U))).left =
    (siteGraph (g ≫ f) U).left ≫
      ((proEtaleBaseChange (g ≫ f)).map
        ((MorphismProperty.Over.mapComp (Q := ⊤)
          (inferInstance : WeaklyEtale g) (inferInstance : WeaklyEtale f)).hom.app U)).left
  apply pullback.hom_ext
  · simp only [Functor.id_obj, siteReindex, MorphismProperty.Over.map,
      MorphismProperty.Comma.mapRight, MorphismProperty.Comma.lift,
      MorphismProperty.Comma.forget, CategoryTheory.Comma.mapRight, Functor.const_obj_obj,
      Discrete.natTrans_app, CostructuredArrow.right_eq_id, Functor.comp_obj,
      Lean.Elab.WF.paramLet, Functor.comp_map, proEtaleBaseChange,
      MorphismProperty.Over.pullback, proEtaleObjectInverseImageIndexPoint,
      MorphismProperty.Over.mapPullbackAdj, StructuredArrow.mk_right, siteGraph,
      StructuredArrow.mk_hom_eq_self, MorphismProperty.Over.homMk_hom, Over.homMk_left,
      MorphismProperty.Over.pullbackComp, NatIso.ofComponents_inv_app,
      MorphismProperty.Over.isoMk_inv_left, Iso.trans_inv, Iso.symm_inv,
      pullback.congrHom_inv, pullback.map_id, Category.comp_id, Category.assoc,
      pullbackLeftPullbackSndIso_hom_fst, MorphismProperty.Over.mapComp,
      NatIso.ofComponents_hom_app, MorphismProperty.Over.isoMk_hom_left, Iso.refl_hom,
      limit.lift_π, PullbackCone.mk_π_app]
    erw [pullback.lift_fst_assoc]
    simp only [Category.assoc]
    erw [pullback.lift_fst, Category.comp_id, pullback.lift_fst, pullback.lift_fst]
  · simp only [Functor.id_obj, siteReindex, MorphismProperty.Over.map,
      MorphismProperty.Comma.mapRight, MorphismProperty.Comma.lift,
      MorphismProperty.Comma.forget, CategoryTheory.Comma.mapRight, Functor.const_obj_obj,
      Discrete.natTrans_app, CostructuredArrow.right_eq_id, Functor.comp_obj,
      Lean.Elab.WF.paramLet, Functor.comp_map, proEtaleBaseChange,
      MorphismProperty.Over.pullback, proEtaleObjectInverseImageIndexPoint,
      MorphismProperty.Over.mapPullbackAdj, StructuredArrow.mk_right, siteGraph,
      StructuredArrow.mk_hom_eq_self, MorphismProperty.Over.homMk_hom, Over.homMk_left,
      MorphismProperty.Over.pullbackComp, NatIso.ofComponents_inv_app,
      MorphismProperty.Over.isoMk_inv_left, Iso.trans_inv, Iso.symm_inv,
      pullback.congrHom_inv, pullback.map_id, Category.comp_id, Category.assoc,
      pullbackLeftPullbackSndIso_hom_snd, MorphismProperty.Over.mapComp,
      NatIso.ofComponents_hom_app, MorphismProperty.Over.isoMk_hom_left, Iso.refl_hom,
      limit.lift_π, PullbackCone.mk_π_app]
    erw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]

set_option backward.isDefEq.respectTransparency.types false in
private def compositorValue {s : Scheme.{u}} (g f r : s ⟶ s)
    (hr : r = g ≫ f) (A : Type u) [CommRing A]
    (F : proEtaleRingModules s (proEtaleConstantRing s A)) (U : s.ProEt) :
    ((proEtaleConstantRingPullback A g).obj
      ((proEtaleConstantRingPullback A f).obj F)).val.obj (op U) →
      ((proEtaleConstantRingPullback A r).obj F).val.obj (op U) :=
  fun x ↦ (((constantCompositor g f A) ≪≫
    eqToIso (congrArg (proEtaleConstantRingPullback A) hr.symm)).hom.app F).val.app (op U) x

set_option backward.isDefEq.respectTransparency.types false in
private theorem graphInsertion_comp {s : Scheme.{u}} (g f r : s ⟶ s)
    [WeaklyEtale g] [WeaklyEtale f] [WeaklyEtale r]
    (hr : r = g ≫ f) (A : Type u) [CommRing A]
    (F : proEtaleRingModules s (proEtaleConstantRing s A)) (U : s.ProEt)
    (x : F.val.obj (op ((siteReindex f).obj ((siteReindex g).obj U)))) :
    compositorValue g f r hr A F U
      (graphInsertion g A ((proEtaleConstantRingPullback A f).obj F) U
        (graphInsertion f A F ((siteReindex g).obj U) x)) =
    graphInsertion r A F U
      (F.val.map ((MorphismProperty.Over.mapComp (Q := ⊤)
        (inferInstance : WeaklyEtale g) (inferInstance : WeaklyEtale f) r hr).hom.app U).op
        x) := by
  subst r
  change ((constantCompositor g f A).hom.app F).val.app (op U) _ = _
  have hc := constantCompositor_generators g f A F
    ((siteReindex f).obj ((siteReindex g).obj U)) ((siteReindex g).obj U) U
    (siteGraph f ((siteReindex g).obj U)) (siteGraph g U) x
  have hh := congrArg (fun p ↦ constantGenerator (g ≫ f) A F
    ((siteReindex f).obj ((siteReindex g).obj U)) U p x 1) (siteGraph_comp g f U)
  exact hc.trans (hh.trans
    (generator_reindex (g ≫ f) A F _ _ U _ (siteGraph (g ≫ f) U) x))

set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizedInsertion_inverse {s : Scheme.{u}} (h : Aut s)
    (A : Type u) [CommRing A] (n : ℕ)
    (e : pointSheafPullback h A n ≅ pointSheafRestriction h A n)
    (he : GraphNormalized h A n e)
    (F : proEtaleRingModules s (proEtaleConstantRing s A)) (U : s.ProEt)
    (x : ((pointSheafPullback h A n).obj F).val.obj (op U)) :
    pointSheafGraphInsertion h A n F U ((e.hom.app F).val.app (op U) x) = x := by
  apply moduleIso_injective A (e.app F) U
  exact he F U _

set_option backward.isDefEq.respectTransparency.types false in
private def restrictionValue {s : Scheme.{u}} (h : Aut s) (A : Type u) [CommRing A]
    (n : ℕ) (e : pointSheafPullback h A n ≅ pointSheafRestriction h A n)
    (F : proEtaleRingModules s (proEtaleConstantRing s A)) (U : s.ProEt) :
    ((pointSheafPullback h A n).obj F).val.obj (op U) →
      F.val.obj (op ((siteReindex (h ^ (n + 1)).hom).obj U)) :=
  fun x ↦ (e.hom.app F).val.app (op U) x

private theorem double_generator_coherence {X Y Z D E : Type*}
    (g : Y → X) (p : X → Y) (r : Z → Y) (q : Y → Z)
    (d : E → D) (e : D → E) (T : X → D) (f : Z → E)
    (hp : ∀ x, g (p x) = x) (hq : ∀ y, r (q y) = y)
    (he : ∀ z, e (d z) = z) (hc : ∀ z, T (g (r z)) = d (f z)) (x : X) :
    e (T x) = f (q (p x)) := by
  have hh := hc (q (p x))
  rw [hq, hp] at hh
  exact (congrArg e hh).trans (he _)

set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizedInsertion_coherence {s : Scheme.{u}} (h : Aut s)
    (A : Type u) [CommRing A]
    (e : ∀ n : ℕ, pointSheafPullback h A n ≅ pointSheafRestriction h A n)
    (he : ∀ n, GraphNormalized h A n (e n))
    (m : ℕ) (F : proEtaleRingModules s (proEtaleConstantRing s A)) (U : s.ProEt)
    (x : ((pointSheafPullback h A 0).obj
      ((pointSheafPullback h A m).obj F)).val.obj (op U)) :
    restrictionValue h A (m + 1) (e (m + 1)) F U
      (((pointSheafCompositor h A m).hom.app F).val.app (op U) x) =
    F.val.map ((pointSheafReindexCompositor h m).hom.app U).op
      (restrictionValue h A m (e m) F ((siteReindex (h ^ (0 + 1)).hom).obj U)
        (restrictionValue h A 0 (e 0) ((pointSheafPullback h A m).obj F) U x)) := by
  have hp : (h ^ ((m + 1) + 1)).hom =
      (h ^ (0 + 1)).hom ≫ (h ^ (m + 1)).hom := by
    simp only [zero_add, pow_one]
    exact congrArg Iso.hom (pow_succ h (m + 1))
  refine double_generator_coherence
    (pointSheafGraphInsertion h A 0 ((pointSheafPullback h A m).obj F) U)
    (restrictionValue h A 0 (e 0) ((pointSheafPullback h A m).obj F) U)
    (pointSheafGraphInsertion h A m F ((siteReindex (h ^ (0 + 1)).hom).obj U))
    (restrictionValue h A m (e m) F ((siteReindex (h ^ (0 + 1)).hom).obj U))
    (pointSheafGraphInsertion h A (m + 1) F U)
    (restrictionValue h A (m + 1) (e (m + 1)) F U)
    (((pointSheafCompositor h A m).hom.app F).val.app (op U))
    (F.val.map ((pointSheafReindexCompositor h m).hom.app U).op)
    (normalizedInsertion_inverse h A 0 (e 0) (he 0) _ _)
    (normalizedInsertion_inverse h A m (e m) (he m) _ _)
    (he (m + 1) F U) ?_ x
  intro z
  unfold pointSheafCompositor
  exact graphInsertion_comp (h ^ (0 + 1)).hom (h ^ (m + 1)).hom
    (h ^ ((m + 1) + 1)).hom hp A F U z

set_option backward.isDefEq.respectTransparency.types false in
private theorem pointRestrictionArrow_comp {s : Scheme.{u}} (h : Aut s) (m : ℕ) :
    (pointSheafReindexCompositor h m).hom.app (ProEt.mk (𝟙 s)) ≫
      (siteReindex (h ^ (m + 1)).hom).map (pointSheafRestrictionArrow h 0) ≫
      pointSheafRestrictionArrow h m = pointSheafRestrictionArrow h (m + 1) := by
  apply MorphismProperty.Over.Hom.ext
  change 𝟙 s ≫ (h ^ (0 + 1)).hom ≫ (h ^ (m + 1)).hom = (h ^ ((m + 1) + 1)).hom
  rw [Category.id_comp]
  simp only [zero_add, pow_one]
  exact (congrArg Iso.hom (pow_succ h (m + 1))).symm

set_option backward.isDefEq.respectTransparency.types false in
private theorem pointSectionInsertion_cocycle {s : Scheme.{u}} (h : Aut s)
    (A : Type u) [CommRing A]
    (e : ∀ n : ℕ, pointSheafPullback h A n ≅ pointSheafRestriction h A n)
    (he : ∀ n, GraphNormalized h A n (e n))
    (j : ∀ n : ℕ, pointSheafSections s A ⟶
      pointSheafPullback h A n ⋙ pointSheafSections s A)
    (hj : ∀ (n : ℕ) (F : proEtaleRingModules s (proEtaleConstantRing s A))
      (x : F.val.obj (op (ProEt.mk (𝟙 s)))),
      restrictionValue h A n (e n) F (ProEt.mk (𝟙 s)) ((j n).app F x) =
        F.val.map (pointSheafRestrictionArrow h n).op x)
    (m : ℕ) (F : proEtaleRingModules s (proEtaleConstantRing s A)) :
    (j (m + 1)).app F = (j m).app F ≫
      (j 0).app ((pointSheafPullback h A m).obj F) ≫
      (pointSheafSections s A).map ((pointSheafCompositor h A m).hom.app F) := by
  ext x
  apply moduleIso_injective A ((e (m + 1)).app F) (ProEt.mk (𝟙 s))
  change restrictionValue h A (m + 1) (e (m + 1)) F (ProEt.mk (𝟙 s))
    ((j (m + 1)).app F x) =
    restrictionValue h A (m + 1) (e (m + 1)) F (ProEt.mk (𝟙 s))
      (((pointSheafCompositor h A m).hom.app F).val.app (op (ProEt.mk (𝟙 s)))
        ((j 0).app ((pointSheafPullback h A m).obj F) ((j m).app F x)))
  have hc := normalizedInsertion_coherence h A e he m F (ProEt.mk (𝟙 s))
    ((j 0).app ((pointSheafPullback h A m).obj F) ((j m).app F x))
  have hz := congrArg (fun y ↦
    F.val.map ((pointSheafReindexCompositor h m).hom.app (ProEt.mk (𝟙 s))).op
      (restrictionValue h A m (e m) F
        ((siteReindex (h ^ (0 + 1)).hom).obj (ProEt.mk (𝟙 s))) y))
    (hj 0 ((pointSheafPullback h A m).obj F) ((j m).app F x))
  have hn := congrArg
    (F.val.map ((pointSheafReindexCompositor h m).hom.app (ProEt.mk (𝟙 s))).op)
    (PresheafOfModules.naturality_apply ((e m).hom.app F).val
      (pointSheafRestrictionArrow h 0).op ((j m).app F x))
  have hm := congrArg (fun y ↦
    F.val.map ((pointSheafReindexCompositor h m).hom.app (ProEt.mk (𝟙 s))).op
      (F.val.map ((siteReindex (h ^ (m + 1)).hom).map
        (pointSheafRestrictionArrow h 0)).op y)) (hj m F x)
  have ha := congrArg (fun a ↦ F.val.presheaf.map a.op x)
    (pointRestrictionArrow_comp h m)
  simp only [op_comp, CategoryTheory.Functor.map_comp] at ha
  exact (hj (m + 1) F x).trans (hc.trans (hz.trans (hn.trans (hm.trans ha)))).symm

set_option backward.isDefEq.respectTransparency.types false in
private def sectionChainMap {s : Scheme.{u}} (h : Aut s) (A : Type u) [CommRing A]
    (n : ℕ) (j : pointSheafSections s A ⟶ pointSheafPullback h A n ⋙ pointSheafSections s A)
    (K : CochainComplex (proEtaleRingModules s (proEtaleConstantRing s A)) ℤ) :
    (pointSheafSectionComplex s A).obj K ⟶
      (pointSheafSectionComplex s A).obj ((pointSheafPullbackComplex h A n).obj K) :=
  (NatTrans.mapHomologicalComplex j (ComplexShape.up ℤ)).app K

set_option backward.isDefEq.respectTransparency.types false in
private def sectionChainCompositor {s : Scheme.{u}} (h : Aut s) (A : Type u) [CommRing A]
    (m : ℕ) (K : CochainComplex (proEtaleRingModules s (proEtaleConstantRing s A)) ℤ) :
    (pointSheafSectionComplex s A).obj
      ((pointSheafPullbackComplex h A 0).obj ((pointSheafPullbackComplex h A m).obj K)) ≅
    (pointSheafSectionComplex s A).obj ((pointSheafPullbackComplex h A (m + 1)).obj K) :=
  (NatIso.mapHomologicalComplex (Functor.isoWhiskerRight
    (pointSheafCompositor h A m) (pointSheafSections s A)) (ComplexShape.up ℤ)).app K

private def normalizedComparison {s : Scheme.{u}} (h : Aut s)
    (A : Type u) [CommRing A] (n : ℕ) :
    pointSheafPullback h A n ≅ pointSheafRestriction h A n :=
  (pointRestrictionComparison h A n).choose

private theorem normalizedComparison_graph {s : Scheme.{u}} (h : Aut s)
    (A : Type u) [CommRing A] (n : ℕ)
    (F : proEtaleRingModules s (proEtaleConstantRing s A)) (U : s.ProEt)
    (x : F.val.obj (op ((MorphismProperty.Over.map (f := (h ^ (n + 1)).hom)
      (P := @WeaklyEtale) ⊤
        (inferInstance : WeaklyEtale (h ^ (n + 1)).hom)).obj U))) :
    ((normalizedComparison h A n).hom.app F).val.app (op U)
      (pointSheafGraphInsertion h A n F U x) = x :=
  (pointRestrictionComparison h A n).choose_spec F U x

attribute [local irreducible] normalizedComparison

/-- Normalized insertion calculus, including its equality of chain maps.
Source: Stacks 03CE, 03CB and 06UM; Modules on Sites 03CZ, 03EK and 03D3;
Deligne, Weil II, (1.1.7) (blueprint: lem-trf-point-sheaf-insertion-calculus).

Proof:
1. Postcomposition on the site is left adjoint to base change. Naturality of the
constant-presheaf sheafification unit proves the coefficient unit and counit
identities for the specified restriction comparison. The pushforward adjunction
for module sheaves therefore makes restriction left adjoint to the actual module
direct image. Uniqueness of left adjoints compares it with tensor pullback. The
comparison's unit equation and the site triangle identity prove graph normalization.
2. The conjugation equation of `proEtaleConstantRingModulePullbackComposition`
computes the exact chosen compositor on two successive adjunction units. Naturality
extends this equation to arbitrary indexing arrows, with scalar one throughout.
3. Compute both projections of the composite graph using the fibre-product universal
property. The result is the direct graph followed by base change of the reindexing
comparison. The generator equation from step 2 therefore gives compositor coherence
on graph insertions. The normalized graph maps are inverses of the comparison maps,
so elementary cancellation extends this equation to every section.
4. Naturality of the constant unit makes restriction at the final object linear over
the original constant ring. Compose this natural linear restriction with the inverse
comparison to construct `j`. Graph normalization identifies its function with the
specified insertion and proves its restriction equation.
5. Apply the direct comparison to two successive insertions. The coherence equation,
the restriction equation, and naturality of the intermediate comparison give two
restrictions in the original sheaf. Their composite is restriction along the product
power. Injectivity of the comparison proves the section cocycle.
6. Extend `j` and the compositor degreewise by Mathlib's constructions for natural
transformations and natural isomorphisms. These constructions supply compatibility
with differentials. Componentwise extensionality proves naturality for arbitrary
chain maps and lifts the section cocycle to equality of chain maps.
No boundedness, constructibility or exactness of evaluation is used. -/
theorem pointSheafInsertionCalculus (k : Type u) [Field k] [IsAlgClosed k]
    (h : Aut (Spec (CommRingCat.of k))) (A : Type u) [CommRing A] [Finite A] :
    ∃ (e : ∀ n : ℕ, pointSheafPullback h A n ≅ pointSheafRestriction h A n)
      (j : ∀ n : ℕ, pointSheafSections (Spec (CommRingCat.of k)) A ⟶
        pointSheafPullback h A n ⋙ pointSheafSections (Spec (CommRingCat.of k)) A)
      (J : ∀ (n : ℕ)
        (K : CochainComplex
          (proEtaleRingModules (Spec (CommRingCat.of k))
            (proEtaleConstantRing (Spec (CommRingCat.of k)) A)) ℤ),
        (pointSheafSectionComplex (Spec (CommRingCat.of k)) A).obj K ⟶
          (pointSheafSectionComplex (Spec (CommRingCat.of k)) A).obj
            ((pointSheafPullbackComplex h A n).obj K))
      (t : ∀ (m : ℕ)
        (K : CochainComplex
          (proEtaleRingModules (Spec (CommRingCat.of k))
            (proEtaleConstantRing (Spec (CommRingCat.of k)) A)) ℤ),
        (pointSheafSectionComplex (Spec (CommRingCat.of k)) A).obj
          ((pointSheafPullbackComplex h A 0).obj
            ((pointSheafPullbackComplex h A m).obj K)) ≅
        (pointSheafSectionComplex (Spec (CommRingCat.of k)) A).obj
          ((pointSheafPullbackComplex h A (m + 1)).obj K)),
      (∀ (n : ℕ)
        (F : proEtaleRingModules (Spec (CommRingCat.of k))
          (proEtaleConstantRing (Spec (CommRingCat.of k)) A))
        (U : (Spec (CommRingCat.of k)).ProEt)
        (x : F.val.obj (op ((MorphismProperty.Over.map (f := (h ^ (n + 1)).hom)
          (P := @WeaklyEtale) ⊤ (inferInstance : WeaklyEtale (h ^ (n + 1)).hom)).obj U))),
        ((e n).hom.app F).val.app (op U) (pointSheafGraphInsertion h A n F U x) = x) ∧
      (∀ (m : ℕ)
        (F : proEtaleRingModules (Spec (CommRingCat.of k))
          (proEtaleConstantRing (Spec (CommRingCat.of k)) A))
        (U : (Spec (CommRingCat.of k)).ProEt)
        (x : ((pointSheafPullback h A 0).obj
          ((pointSheafPullback h A m).obj F)).val.obj (op U)),
        ((e (m + 1)).hom.app F).val.app (op U)
          (((pointSheafCompositor h A m).hom.app F).val.app (op U) x) =
        F.val.map ((pointSheafReindexCompositor h m).hom.app U).op
          (((e m).hom.app F).val.app
            (op ((MorphismProperty.Over.map (f := (h ^ (0 + 1)).hom)
              (P := @WeaklyEtale) ⊤
                (inferInstance : WeaklyEtale (h ^ (0 + 1)).hom)).obj U))
            (((e 0).hom.app ((pointSheafPullback h A m).obj F)).val.app (op U) x))) ∧
      (∀ (n : ℕ)
        (F : proEtaleRingModules (Spec (CommRingCat.of k))
          (proEtaleConstantRing (Spec (CommRingCat.of k)) A))
        (x : F.val.obj (op (ProEt.mk (𝟙 (Spec (CommRingCat.of k)))))),
        (j n).app F x = pointSheafInsertion h A n F x) ∧
      (∀ (n : ℕ)
        (F : proEtaleRingModules (Spec (CommRingCat.of k))
          (proEtaleConstantRing (Spec (CommRingCat.of k)) A))
        (x : F.val.obj (op (ProEt.mk (𝟙 (Spec (CommRingCat.of k)))))),
        ((e n).hom.app F).val.app (op (ProEt.mk (𝟙 (Spec (CommRingCat.of k)))))
          ((j n).app F x) = F.val.map (pointSheafRestrictionArrow h n).op x) ∧
      (∀ (m : ℕ)
        (F : proEtaleRingModules (Spec (CommRingCat.of k))
          (proEtaleConstantRing (Spec (CommRingCat.of k)) A)),
        (j (m + 1)).app F = (j m).app F ≫
          (j 0).app ((pointSheafPullback h A m).obj F) ≫
          (pointSheafSections (Spec (CommRingCat.of k)) A).map
            ((pointSheafCompositor h A m).hom.app F)) ∧
      (∀ (n : ℕ)
        (K : CochainComplex
          (proEtaleRingModules (Spec (CommRingCat.of k))
            (proEtaleConstantRing (Spec (CommRingCat.of k)) A)) ℤ) (i : ℤ),
        (J n K).f i = (j n).app (K.X i)) ∧
      (∀ (n : ℕ)
        (K L : CochainComplex
          (proEtaleRingModules (Spec (CommRingCat.of k))
            (proEtaleConstantRing (Spec (CommRingCat.of k)) A)) ℤ) (v : K ⟶ L),
        (pointSheafSectionComplex (Spec (CommRingCat.of k)) A).map v ≫ J n L =
          J n K ≫ (pointSheafSectionComplex (Spec (CommRingCat.of k)) A).map
            ((pointSheafPullbackComplex h A n).map v)) ∧
      (∀ (m : ℕ)
        (K : CochainComplex
          (proEtaleRingModules (Spec (CommRingCat.of k))
            (proEtaleConstantRing (Spec (CommRingCat.of k)) A)) ℤ) (i : ℤ),
        (t m K).hom.f i = (pointSheafSections (Spec (CommRingCat.of k)) A).map
          ((pointSheafCompositor h A m).hom.app (K.X i))) ∧
      (∀ (m : ℕ)
        (K : CochainComplex
          (proEtaleRingModules (Spec (CommRingCat.of k))
            (proEtaleConstantRing (Spec (CommRingCat.of k)) A)) ℤ),
        J (m + 1) K = J m K ≫
          J 0 ((pointSheafPullbackComplex h A m).obj K) ≫ (t m K).hom) := by
  classical
  let e := normalizedComparison h A
  have he := normalizedComparison_graph h A
  let j := fun n ↦ sectionInsertionMap h A n (e n)
  have hj₁ := fun n ↦ (pointSectionInsertion h A n (e n) (he n)).1
  have hj₂ := fun n ↦ (pointSectionInsertion h A n (e n) (he n)).2
  let J := fun n ↦ sectionChainMap h A n (j n)
  let t := sectionChainCompositor h A
  refine ⟨e, j, J, t, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n F U x
    exact he n F U x
  · intro m F U x
    exact normalizedInsertion_coherence h A e he m F U x
  · intro n F x
    exact hj₁ n F x
  · intro n F x
    exact hj₂ n F x
  · intro m F
    exact pointSectionInsertion_cocycle h A e he j hj₂ m F
  · intro n K i
    rfl
  · intro n K L v
    apply HomologicalComplex.hom_ext
    intro i
    exact (j n).naturality (v.f i)
  · intro m K i
    rfl
  · intro m K
    apply HomologicalComplex.hom_ext
    intro i
    exact pointSectionInsertion_cocycle h A e he j hj₂ m (K.X i)

end AlgebraicGeometry.Scheme
