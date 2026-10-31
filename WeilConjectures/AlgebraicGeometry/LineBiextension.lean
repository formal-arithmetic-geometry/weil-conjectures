/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-! # Biextensions in invertible modules

Source: Lan, revised thesis, §3.2.1, and Moret-Bailly, I §2.
(blueprint: def-sfb-line-biextension)

The laws are natural families of actual isomorphisms of pulled-back modules on test schemes.
Taking the universal test scheme gives the usual isomorphisms on the triple products;
naturality says that every other component is their pullback. Coherence is tested on all
schemes, including nonreduced ones, rather than only on field-valued points.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
namespace AlgebraicGeometry
namespace LineBiextension

/-- The line at a pair of generalized points. Source: Lan §3.2.1
(blueprint: def-sfb-line-biextension). -/
noncomputable abbrev fiber {S : Scheme.{u}} {P Q : Over S}
    (E : (P ⊗ Q).left.Modules) {T : Over S} (x : T ⟶ P) (y : T ⟶ Q) :
    T.left.Modules :=
  (Scheme.Modules.tensorPullback (lift x y).left).obj E

/-- Equality transport of generalized points. Source: Lan §3.2.1
(blueprint: def-sfb-line-biextension). -/
noncomputable def congr {S : Scheme.{u}} {P Q T : Over S}
    (E : (P ⊗ Q).left.Modules) {x x' : T ⟶ P} {y y' : T ⟶ Q}
    (hx : x = x') (hy : y = y') : fiber E x y ≅ fiber E x' y' :=
  eqToIso (congrArg (fun z : T ⟶ P ⊗ Q ↦
    (Scheme.Modules.tensorPullback z.left).obj E) (congrArg₂ lift hx hy))

/-- Canonical reindexing, using the section-normalized composition comparison.
Source: Lan §3.2.1 (blueprint: def-sfb-line-biextension). -/
noncomputable def reindex {S : Scheme.{u}} {P Q T U : Over S}
    (E : (P ⊗ Q).left.Modules) (h : U ⟶ T) (x : T ⟶ P) (y : T ⟶ Q) :
    (Scheme.Modules.tensorPullback h.left).obj (fiber E x y) ≅
      fiber E (h ≫ x) (h ≫ y) :=
  ((Scheme.Modules.tensorPullbackSectionComp h.left (lift x y).left).app E).symm ≪≫
    eqToIso (congrArg (fun z : U.left ⟶ (P ⊗ Q).left ↦
      (Scheme.Modules.tensorPullback z).obj E)
      (congrArg (fun z : U ⟶ P ⊗ Q ↦ z.left) (comp_lift h x y)))

/-- Canonical pullback of the structure module. Source: Lan §3.2.1
(blueprint: def-sfb-line-biextension). -/
noncomputable abbrev unit {X Y : Scheme.{u}} (h : X ⟶ Y) :
    (Scheme.Modules.tensorPullback h).obj (𝟙_ Y.Modules) ≅ 𝟙_ X.Modules :=
  Scheme.Modules.boundaryPullbackPowIso h (𝟙_ Y.Modules) 0

/-- Reorder four tensor factors from row order to column order. Source: Lan §3.2.1
(blueprint: def-sfb-line-biextension). -/
noncomputable def reorderFour {X : Scheme.{u}} (A B C D : X.Modules) :
    (A ⊗ B) ⊗ (C ⊗ D) ≅ (A ⊗ C) ⊗ (B ⊗ D) :=
  α_ A B (C ⊗ D) ≪≫
    (Iso.refl A ⊗ᵢ (α_ B C D).symm) ≪≫
    (Iso.refl A ⊗ᵢ (β_ B C ⊗ᵢ Iso.refl D)) ≪≫
    (Iso.refl A ⊗ᵢ α_ C B D) ≪≫ (α_ A C (B ⊗ D)).symm

end LineBiextension

/-- A G_m-biextension on an invertible module, with both normalized axes and both laws.
All naturality and group coherence equations are equations of module morphisms.
Multiplicative notation in the test-point groups denotes the source's addition.
Source: Lan §3.2.1; Moret-Bailly I §2
(blueprint: def-sfb-line-biextension). -/
structure LineBiextension {S : Scheme.{u}} (P Q : Over S) [CommGrpObj P] [CommGrpObj Q]
    (E : (P ⊗ Q).left.Modules) where
  /-- The underlying line is invertible. -/
  invertible : E.IsInvertible
  /-- Trivialization on the first identity axis. -/
  leftAxis : ∀ (T : Over S) (y : T ⟶ Q), LineBiextension.fiber E 1 y ≅ 𝟙_ T.left.Modules
  /-- Trivialization on the second identity axis. -/
  rightAxis : ∀ (T : Over S) (x : T ⟶ P), LineBiextension.fiber E x 1 ≅ 𝟙_ T.left.Modules
  /-- Agreement at the intersection of the axes. -/
  origin : ∀ T : Over S, leftAxis T 1 = rightAxis T 1
  /-- Additivity in the first variable. -/
  addLeft : ∀ (T : Over S) (x x' : T ⟶ P) (y : T ⟶ Q),
    LineBiextension.fiber E (x * x') y ≅
      LineBiextension.fiber E x y ⊗ LineBiextension.fiber E x' y
  /-- Additivity in the second variable. -/
  addRight : ∀ (T : Over S) (x : T ⟶ P) (y y' : T ⟶ Q),
    LineBiextension.fiber E x (y * y') ≅
      LineBiextension.fiber E x y ⊗ LineBiextension.fiber E x y'
  /-- The first axis is a global trivialization, expressed by its pullbacks. -/
  leftAxis_natural : ∀ (T U : Over S) (h : U ⟶ T) (y : T ⟶ Q),
    (Scheme.Modules.tensorPullback h.left).map (leftAxis T y).hom ≫
        (LineBiextension.unit h.left).hom =
      (LineBiextension.reindex E h 1 y).hom ≫
        (LineBiextension.congr E (by simp) rfl).hom ≫ (leftAxis U (h ≫ y)).hom
  /-- Naturality of the second axis. -/
  rightAxis_natural : ∀ (T U : Over S) (h : U ⟶ T) (x : T ⟶ P),
    (Scheme.Modules.tensorPullback h.left).map (rightAxis T x).hom ≫
        (LineBiextension.unit h.left).hom =
      (LineBiextension.reindex E h x 1).hom ≫
        (LineBiextension.congr E rfl (by simp)).hom ≫ (rightAxis U (h ≫ x)).hom
  /-- The first law is the pullback of its universal triple-product component. -/
  addLeft_natural : ∀ (T U : Over S) (h : U ⟶ T) (x x' : T ⟶ P) (y : T ⟶ Q),
    (Scheme.Modules.tensorPullback h.left).map (addLeft T x x' y).hom ≫
        (Scheme.Modules.boundaryPullbackTensorIso h.left
          (LineBiextension.fiber E x y) (LineBiextension.fiber E x' y)).hom ≫
        ((LineBiextension.reindex E h x y).hom ⊗ₘ
          (LineBiextension.reindex E h x' y).hom) =
      (LineBiextension.reindex E h (x * x') y).hom ≫
        (LineBiextension.congr E
          (MonObj.comp_mul h x x') rfl).hom ≫
          (addLeft U (h ≫ x) (h ≫ x') (h ≫ y)).hom
  /-- Naturality of the second law. -/
  addRight_natural : ∀ (T U : Over S) (h : U ⟶ T) (x : T ⟶ P) (y y' : T ⟶ Q),
    (Scheme.Modules.tensorPullback h.left).map (addRight T x y y').hom ≫
        (Scheme.Modules.boundaryPullbackTensorIso h.left
          (LineBiextension.fiber E x y) (LineBiextension.fiber E x y')).hom ≫
        ((LineBiextension.reindex E h x y).hom ⊗ₘ
          (LineBiextension.reindex E h x y').hom) =
      (LineBiextension.reindex E h x (y * y')).hom ≫
        (LineBiextension.congr E rfl
          (MonObj.comp_mul h y y')).hom ≫
          (addRight U (h ≫ x) (h ≫ y) (h ≫ y')).hom
  /-- Associativity in the first variable. -/
  assocLeft : ∀ (T : Over S) (x x' x'' : T ⟶ P) (y : T ⟶ Q),
    (addLeft T (x * x') x'' y).hom ≫
        ((addLeft T x x' y).hom ▷ LineBiextension.fiber E x'' y) ≫
        (α_ _ _ _).hom =
      (LineBiextension.congr E (mul_assoc x x' x'') rfl).hom ≫
        (addLeft T x (x' * x'') y).hom ≫
        (LineBiextension.fiber E x y ◁ (addLeft T x' x'' y).hom)
  /-- Associativity in the second variable. -/
  assocRight : ∀ (T : Over S) (x : T ⟶ P) (y y' y'' : T ⟶ Q),
    (addRight T x (y * y') y'').hom ≫
        ((addRight T x y y').hom ▷ LineBiextension.fiber E x y'') ≫
        (α_ _ _ _).hom =
      (LineBiextension.congr E rfl (mul_assoc y y' y'')).hom ≫
        (addRight T x y (y' * y'')).hom ≫
        (LineBiextension.fiber E x y ◁ (addRight T x y' y'').hom)
  /-- Commutativity in the first variable. -/
  commLeft : ∀ (T : Over S) (x x' : T ⟶ P) (y : T ⟶ Q),
    (addLeft T x x' y).hom ≫ (β_ _ _).hom =
      (LineBiextension.congr E (mul_comm x x') rfl).hom ≫ (addLeft T x' x y).hom
  /-- Commutativity in the second variable. -/
  commRight : ∀ (T : Over S) (x : T ⟶ P) (y y' : T ⟶ Q),
    (addRight T x y y').hom ≫ (β_ _ _).hom =
      (LineBiextension.congr E rfl (mul_comm y y')).hom ≫ (addRight T x y' y).hom
  /-- Left unit for the first law. The other unit follows by commutativity. -/
  unitLeft : ∀ (T : Over S) (x : T ⟶ P) (y : T ⟶ Q),
    (addLeft T 1 x y).hom ≫ ((leftAxis T y).hom ▷ LineBiextension.fiber E x y) ≫
        (λ_ _).hom = (LineBiextension.congr E (one_mul x) rfl).hom
  /-- Left unit for the second law. The other unit follows by commutativity. -/
  unitRight : ∀ (T : Over S) (x : T ⟶ P) (y : T ⟶ Q),
    (addRight T x 1 y).hom ≫ ((rightAxis T x).hom ▷ LineBiextension.fiber E x y) ≫
        (λ_ _).hom = (LineBiextension.congr E rfl (one_mul y)).hom
  /-- Expanding in either order gives the same four-factor map. -/
  interchange : ∀ (T : Over S) (x x' : T ⟶ P) (y y' : T ⟶ Q),
    (addLeft T x x' (y * y')).hom ≫
        ((addRight T x y y').hom ⊗ₘ (addRight T x' y y').hom) =
      (addRight T (x * x') y y').hom ≫
        ((addLeft T x x' y).hom ⊗ₘ (addLeft T x x' y').hom) ≫
        (LineBiextension.reorderFour
          (LineBiextension.fiber E x y) (LineBiextension.fiber E x' y)
          (LineBiextension.fiber E x y') (LineBiextension.fiber E x' y')).hom

/-- An isomorphism preserves both partial laws and both identity trivializations.
Source: Lan §3.2.1, isomorphisms of biextensions
(blueprint: def-sfb-line-biextension). -/
structure LineBiextension.Iso {S : Scheme.{u}} {P Q : Over S}
    [CommGrpObj P] [CommGrpObj Q] {E F : (P ⊗ Q).left.Modules}
    (B : LineBiextension P Q E) (C : LineBiextension P Q F) where
  /-- Isomorphism of underlying invertible modules. -/
  lineIso : E ≅ F
  /-- Preservation of the first axis. -/
  leftAxis : ∀ (T : Over S) (y : T ⟶ Q),
    (Scheme.Modules.tensorPullback (lift (1 : T ⟶ P) y).left).map lineIso.hom ≫
      (C.leftAxis T y).hom = (B.leftAxis T y).hom
  /-- Preservation of the second axis. -/
  rightAxis : ∀ (T : Over S) (x : T ⟶ P),
    (Scheme.Modules.tensorPullback (lift x (1 : T ⟶ Q)).left).map lineIso.hom ≫
      (C.rightAxis T x).hom = (B.rightAxis T x).hom
  /-- Preservation of the first partial law. -/
  addLeft : ∀ (T : Over S) (x x' : T ⟶ P) (y : T ⟶ Q),
    (Scheme.Modules.tensorPullback (lift (x * x') y).left).map lineIso.hom ≫
      (C.addLeft T x x' y).hom =
    (B.addLeft T x x' y).hom ≫
      ((Scheme.Modules.tensorPullback (lift x y).left).map lineIso.hom ⊗ₘ
        (Scheme.Modules.tensorPullback (lift x' y).left).map lineIso.hom)
  /-- Preservation of the second partial law. -/
  addRight : ∀ (T : Over S) (x : T ⟶ P) (y y' : T ⟶ Q),
    (Scheme.Modules.tensorPullback (lift x (y * y')).left).map lineIso.hom ≫
      (C.addRight T x y y').hom =
    (B.addRight T x y y').hom ≫
      ((Scheme.Modules.tensorPullback (lift x y).left).map lineIso.hom ⊗ₘ
        (Scheme.Modules.tensorPullback (lift x y').left).map lineIso.hom)

end AlgebraicGeometry
