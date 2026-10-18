/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.Paper.AdicExceptionalComposition

/-! # Scalar, shift, and projection equations
Source: Bhatt--Scholze Section 6.7 and Remark 6.8.15
(blueprint: def-per-adic-exceptional-coherent-system).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicExceptionalProjection

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]

/-- The complete conclusion, retaining each canonical map and the diagrams between them.
Finite exceptional compatibility is specified by the reduction isomorphism and the
counit equation; its scalar mate is uniquely fixed by the scalar counit square.
Source: Lemmas 6.7.2, 6.7.14, 6.7.19 and Remark 6.8.15
(blueprint: def-per-adic-exceptional-coherent-system). -/
structure System where
  operation : Operations (k := k) l
  composition : Compositions l operation
  scalars : Scalars (k := k) l
  scalarOperation : ∀ {X Y : Spaces k} (f : X ⟶ Y) (c : Compactification (arrow f)),
    ScalarOperation l scalars f c (fun E ↦ operation E f c)
  projection : ∀ (E : Coefficient.{u} l) {X Y : Spaces k} (f : X ⟶ Y)
    (c : Compactification (arrow f)),
    Projection l E f c (operation E f c) (composition.ringed E).tensor
  projectionScalar : ∀ (E L : Coefficient.{u} l)
    (i : E.carrier →ₐ[ℚ_[l]] L.carrier) {X Y : Spaces k} (f : X ⟶ Y)
    (c : Compactification (arrow f)) (K : C l E X) (M : C l E Y),
    (scalar l E L i Y).map ((projection E f c).iso.hom.app (K, M)) ≫
      (scalars.tensor E L i Y).hom.app ((support l E f c).obj K, M) ≫
      (tensor l L Y).map (Prod.mkHom
        (((scalarOperation f c).support.iso E L i).hom.app K) (𝟙 _)) =
    ((scalarOperation f c).support.iso E L i).hom.app
        ((tensor l E X).obj (K, (pull l E f).obj M)) ≫
      (support l L f c).map ((scalars.tensor E L i X).hom.app
          (K, (pull l E f).obj M) ≫
        (tensor l L X).map (Prod.mkHom (𝟙 _)
          (((scalarOperation f c).pull.iso E L i).hom.app M))) ≫
      (projection L f c).iso.hom.app
        ((scalar l E L i X).obj K, (scalar l E L i Y).obj M)
  compositionScalar : ∀ (E L : Coefficient.{u} l)
    (i : E.carrier →ₐ[ℚ_[l]] L.carrier) {X Y Z : Spaces k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification (arrow f)) (cg : Compactification (arrow g))
    (cfg : Compactification (arrow (f ≫ g))) (K : C l E X),
    (scalar l E L i Z).map ((composition.comp E f g cf cg cfg).hom.app K) ≫
      ((scalarOperation (f ≫ g) cfg).support.iso E L i).hom.app K =
    ((scalarOperation g cg).support.iso E L i).hom.app ((support l E f cf).obj K) ≫
      (support l L g cg).map (((scalarOperation f cf).support.iso E L i).hom.app K) ≫
      (composition.comp L f g cf cg cfg).hom.app ((scalar l E L i X).obj K)
  identityScalar : ∀ (E L : Coefficient.{u} l)
    (i : E.carrier →ₐ[ℚ_[l]] L.carrier) (X : Spaces k)
    (c : Compactification (arrow (𝟙 X))) (K : C l E X),
    ((scalarOperation (𝟙 X) c).support.iso E L i).hom.app K ≫
      (composition.unit L X c).hom.app ((scalar l E L i X).obj K) =
      (scalar l E L i X).map ((composition.unit E X c).hom.app K)
  reductionScalar : ∀ (E L : Coefficient.{u} l)
    (i : E.carrier →ₐ[ℚ_[l]] L.carrier) (e : ℕ)
    (he : PurCompactSupport.Ramification l E.carrier L.carrier i e) (hepos : 1 ≤ e)
    (n m : ℕ) (hm : m + 1 = e * (n + 1)),
    let φ := ramifiedFiniteMap l E L i e he n m hm
    let h := scalars.ramifiedSquare E L i e he hepos n m hm
    ∀ {X Y : Spaces k} (f : X ⟶ Y) (c : Compactification (arrow f)) (M : C l E Y),
    (red l L X m).map (((scalarOperation f c).exceptional.iso E L i).hom.app M) ≫
        ((operation L f c).reduction m).hom.app ((scalar l E L i Y).obj M) ≫
        (finiteExceptional l L f c m).map ((scalars.finiteBalance l E L i n m φ h Y M).hom) =
      (scalars.finiteBalance l E L i n m φ h X ((operation E f c).exceptional.obj M)).hom ≫
        (finiteScalar φ X).map (((operation E f c).reduction n).hom.app M) ≫
        finiteExceptionalScalar φ f c ((red l E Y n).obj M)
  pullScalarShift : ∀ (E L : Coefficient.{u} l)
    (i : E.carrier →ₐ[ℚ_[l]] L.carrier) {X Y : Spaces k} (f : X ⟶ Y)
    (c : Compactification (arrow f)),
    letI := (operation E f c).ordinary.leftShift
    letI := (operation L f c).ordinary.leftShift
    letI := scalars.shift l E L i X
    letI := scalars.shift l E L i Y
    (((scalarOperation f c).pull.iso E L i).hom).CommShift ℤ
  directScalarShift : ∀ (E L : Coefficient.{u} l)
    (i : E.carrier →ₐ[ℚ_[l]] L.carrier) {X Y : Spaces k} (f : X ⟶ Y)
    (c : Compactification (arrow f)),
    letI := (operation E f c).ordinary.rightShift
    letI := (operation L f c).ordinary.rightShift
    letI := scalars.shift l E L i X
    letI := scalars.shift l E L i Y
    (((scalarOperation f c).direct.iso E L i).hom).CommShift ℤ
  supportScalarShift : ∀ (E L : Coefficient.{u} l)
    (i : E.carrier →ₐ[ℚ_[l]] L.carrier) {X Y : Spaces k} (f : X ⟶ Y)
    (c : Compactification (arrow f)),
    letI := (operation E f c).shriek.leftShift
    letI := (operation L f c).shriek.leftShift
    letI := scalars.shift l E L i X
    letI := scalars.shift l E L i Y
    (((scalarOperation f c).support.iso E L i).hom).CommShift ℤ
  exceptionalScalarShift : ∀ (E L : Coefficient.{u} l)
    (i : E.carrier →ₐ[ℚ_[l]] L.carrier) {X Y : Spaces k} (f : X ⟶ Y)
    (c : Compactification (arrow f)),
    letI := (operation E f c).shriek.rightShift
    letI := (operation L f c).shriek.rightShift
    letI := scalars.shift l E L i X
    letI := scalars.shift l E L i Y
    (((scalarOperation f c).exceptional.iso E L i).hom).CommShift ℤ
  compositionShift : ∀ (E : Coefficient.{u} l) {X Y Z : Spaces k}
    (f : X ⟶ Y) (g : Y ⟶ Z) (cf : Compactification (arrow f))
    (cg : Compactification (arrow g)) (cfg : Compactification (arrow (f ≫ g))),
    letI := (operation E f cf).shriek.leftShift
    letI := (operation E g cg).shriek.leftShift
    letI := (operation E (f ≫ g) cfg).shriek.leftShift
    (composition.comp E f g cf cg cfg).hom.CommShift ℤ
  exceptionalCompositionShift : ∀ (E : Coefficient.{u} l) {X Y Z : Spaces k}
    (f : X ⟶ Y) (g : Y ⟶ Z) (cf : Compactification (arrow f))
    (cg : Compactification (arrow g)) (cfg : Compactification (arrow (f ≫ g))),
    letI := (operation E f cf).shriek.rightShift
    letI := (operation E g cg).shriek.rightShift
    letI := (operation E (f ≫ g) cfg).shriek.rightShift
    (exceptionalComposition l operation composition E f g cf cg cfg).hom.CommShift ℤ
  changeShift : ∀ (E : Coefficient.{u} l) {X Y : Spaces k} (f : X ⟶ Y)
    (c d : Compactification (arrow f)),
    letI := (operation E f c).shriek.leftShift
    letI := (operation E f d).shriek.leftShift
    (composition.change E f c d).hom.CommShift ℤ
  identityShift : ∀ (E : Coefficient.{u} l) (X : Spaces k)
    (c : Compactification (arrow (𝟙 X))),
    letI := (operation E (𝟙 X) c).shriek.leftShift
    (composition.unit E X c).hom.CommShift ℤ

  reductionShift : ∀ (E : Coefficient.{u} l) {X Y : Spaces k} (f : X ⟶ Y)
    (c : Compactification (arrow f)) (n : ℕ),
    letI := (operation E f c).shriek.rightShift
    letI := redShift l E X n
    letI := redShift l E Y n
    letI := finiteExceptionalShift l E f c n
    ((operation E f c).reduction n).hom.CommShift ℤ
  scalarUnitShift : ∀ (E : Coefficient.{u} l) (X : Spaces k),
    letI := scalars.shift l E E (AlgHom.id ℚ_[l] E.carrier) X
    (scalars.unit E X).hom.CommShift ℤ
  scalarCompShift : ∀ (E L N : Coefficient.{u} l)
    (i : E.carrier →ₐ[ℚ_[l]] L.carrier) (j : L.carrier →ₐ[ℚ_[l]] N.carrier) (X : Spaces k),
    letI := scalars.shift l E L i X
    letI := scalars.shift l L N j X
    letI := scalars.shift l E N (j.comp i) X
    (scalars.comp E L N i j X).hom.CommShift ℤ

end WeilConjectures.AdicExceptionalProjection
