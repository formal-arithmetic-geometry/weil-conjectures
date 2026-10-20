/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Sheaf.Paper.LatticeSheafLocallyConstant
public import Sheaf.Paper.AdicLisseModule
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification

/-!
# Constructible modules over continuous coefficient sheaves

Source: Bhatt--Scholze, The pro-etale topology for schemes, Definitions 6.8.1 and 6.8.10
(blueprint: def-weil-pbc-continuous-constructible-module).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The constant-section map to continuous coefficients, before sheafification.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: def-weil-pbc-continuous-constructible-module). -/
def continuousCoefficientConstants (X : Scheme.{u}) (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A] :
    (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)) ⟶
      (latticeCoefficientSheaf X A).obj where
  app V := CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((ContinuousMap.C : A →+* C(V.unop.left, A)).comp ULift.ringEquiv.toRingHom))
  naturality _ _ _ := rfl

/-- Extend constant sections through constant-ring sheafification.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: def-weil-pbc-continuous-constructible-module). -/
def continuousCoefficientConstantMap (X : Scheme.{u}) (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A] :
    Scheme.adicLisseConstantRing X (ULift.{u + 1} A) ⟶ latticeCoefficientSheaf X A :=
  ((sheafificationAdjunction (Scheme.ProEt.topology X) CommRingCat.{u + 1}).homEquiv
    _ _).symm (continuousCoefficientConstants X A)

/-- The actual sheafified tensor `A_X ⊗_A P`.
Source: Bhatt--Scholze, Definition 6.8.10
(blueprint: def-weil-pbc-continuous-constructible-module). -/
def continuousCoefficientModule (X : Scheme.{u}) (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A]
    (P : ModuleCat.{u + 1} (ULift.{u + 1} A)) :
    SheafOfModules.{u + 1} (latticeModuleRing X A) :=
  SheafOfModules.changeOfRings.{u, u + 1, u + 1}
    (continuousCoefficientConstantMap X A)
    ((Scheme.adicLisseConstantModules X (ULift.{u + 1} A)).obj P)

/-- The section map, precomposition with the base-change projection.
Source: Bhatt--Scholze, Definition 6.8.1; Stacks Tag 09A5
(blueprint: def-weil-pbc-continuous-constructible-module). -/
def continuousCoefficientDirectImageApp {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A] (V : Y.ProEtᵒᵖ) :
    (latticeCoefficientSheaf Y A).obj.obj V ⟶
      ((Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        (latticeCoefficientSheaf X A)).obj.obj V :=
  CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      (((ContinuousMap.compRightAlgHom ℤ A
        (pullback.fst V.unop.hom f).base.hom).toRingHom).comp
          ULift.ringEquiv.toRingHom))

/-- The section maps commute with restrictions.
Source: Bhatt--Scholze, Definition 6.8.1; Stacks Tag 09A5
(blueprint: def-weil-pbc-continuous-constructible-module).
Proof: evaluate on a continuous function and a point. The two composites are
precomposition with the two sides of the naturality square of the first pullback
projection. The defining equation for the map between pullbacks identifies them.
Pointwise equality gives equality of continuous maps and ring homomorphisms. -/
theorem continuousCoefficientDirectImageApp_naturality {X Y : Scheme.{u}}
    (f : X ⟶ Y) (A : Type u) [TopologicalSpace A] [CommRing A] [IsTopologicalRing A]
    {V W : Y.ProEtᵒᵖ} (g : V ⟶ W) :
    (latticeCoefficientSheaf Y A).obj.map g ≫ continuousCoefficientDirectImageApp f A W =
      continuousCoefficientDirectImageApp f A V ≫
        ((Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
          (latticeCoefficientSheaf X A)).obj.map g := by
  apply CommRingCat.hom_ext
  ext s : 1
  apply ULift.ext
  ext x
  change s.down ((pullback.fst W.unop.hom f ≫ g.unop.left).base x) =
    s.down ((((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map g.unop).left ≫
      pullback.fst V.unop.hom f).base x)
  rw [MorphismProperty.Over.pullback_map_left, pullback.lift_fst]
  rfl

/-- Pull continuous functions back along the first projection of the base change.
Source: Bhatt--Scholze, Definition 6.8.1; Stacks Tag 09A5
(blueprint: def-weil-pbc-continuous-constructible-module). -/
def continuousCoefficientDirectImageMap {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A] :
    latticeCoefficientSheaf Y A ⟶
      (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        (latticeCoefficientSheaf X A) :=
  ⟨{ app := continuousCoefficientDirectImageApp f A
     naturality := fun _ _ g ↦ continuousCoefficientDirectImageApp_naturality f A g }⟩

/-- The canonical adjoint coefficient map `f⁻¹ A_Y → A_X`.
Source: Bhatt--Scholze, Definition 6.8.1; Stacks Tag 09A5
(blueprint: def-weil-pbc-continuous-constructible-module). -/
def continuousCoefficientInverseImageMap {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A] :
    (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (latticeCoefficientSheaf Y A) ⟶ latticeCoefficientSheaf X A :=
  ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).symm
    (continuousCoefficientDirectImageMap f A)

/-- Ringed inverse image, using the canonical coefficient map and sheaf tensor.
Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.10; Stacks Tag 03D2
(blueprint: def-weil-pbc-continuous-constructible-module). -/
def continuousModulePullback {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A]
    (N : SheafOfModules.{u + 1} (latticeModuleRing Y A)) :
    SheafOfModules.{u + 1} (latticeModuleRing X A) :=
  SheafOfModules.changeOfRings.{u, u + 1, u + 1} (continuousCoefficientInverseImageMap f A)
    ((Scheme.proEtaleModuleInverseImage f (latticeCoefficientSheaf Y A)).obj N)

/-- On a topologically noetherian scheme, a finite stratification on which the module is
pro-etale locally `A_X ⊗_A P`,
with `P` finitely presented. The cover and the module may vary with the stratum.
Source: Bhatt--Scholze, Definition 6.8.10 and Lemma 6.8.13
(blueprint: def-weil-pbc-continuous-constructible-module). -/
def IsContinuousConstructible (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (A : Type u)
    [TopologicalSpace A] [CommRing A] [IsTopologicalRing A]
    (N : SheafOfModules.{u + 1} (latticeModuleRing X A)) : Prop :=
  ∃ s : Scheme.Stratification X, ∀ k : Fin s.n,
    ∃ (I : Type (u + 1)) (V : I → (s.domain k).ProEt),
      (Scheme.ProEt.topology (s.domain k)).CoversTop V ∧
      ∀ i : I, ∃ P : ModuleCat.{u + 1} (ULift.{u + 1} A),
        Module.FinitePresentation (ULift.{u + 1} A) P ∧
        Nonempty ((continuousModulePullback (s.immersion k) A N).over (V i) ≅
          (continuousCoefficientModule (s.domain k) A P).over (V i))

end AlgebraicGeometry.ProEtale
