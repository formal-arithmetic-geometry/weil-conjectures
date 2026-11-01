/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldExceptionalSystem.FieldExceptionalSystemEvaluation

/-! # Exceptional coefficient comparison on whole systems

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension,
sk-lem-sp-field-extension-towers.proof.md (2), counit transpose
(blueprint: def-sp-field-exceptional-system-laws).

Natural-number level n means exponent n+1. All morphisms are in ordinary derived
categories of strict systems, in the dependency's section-preserving coordinates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldExceptionalSystem

open FieldShriekSystem
variable (P : PurityFiniteSetting.{u})

attribute [local irreducible] component finiteComponent finiteComposite
attribute [local irreducible] sourceEvaluation targetEvaluation
attribute [local irreducible] FieldShriekSystem.iso scalarAssoc scalarUnit


/-- The invertible clause for the actual exceptional coefficient transpose.
Source: blueprint (2), finite and whole-system coefficient compatibility
(blueprint: def-sp-field-exceptional-system-laws). -/
@[irreducible]
def invertibleLaw (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : FieldShriekSystem.Laws P D c) (a : Domains P D c) (A : Adjoints P D c b a) : Prop :=
  ∀ (E F : Index P) (h : E ≤ F) (K : N P D E Y),
    IsIso (component P D c b a A h K)

/-- The naturality clause for the actual exceptional coefficient transpose.
Source: blueprint (2), finite and whole-system coefficient compatibility
(blueprint: def-sp-field-exceptional-system-laws). -/
@[irreducible]
def naturalityLaw (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : FieldShriekSystem.Laws P D c) (a : Domains P D c) (A : Adjoints P D c b a) : Prop :=
  ∀ (E F : Index P) (h : E ≤ F) {K L : N P D E Y} (v : K ⟶ L),
    (scalar P D a h X).map ((A.right E).map v) ≫ component P D c b a A h L =
      component P D c b a A h K ≫ (A.right F).map ((scalar P D a h Y).map v)

/-- The counit clause for the actual exceptional coefficient transpose.
Source: blueprint (2), finite and whole-system coefficient compatibility
(blueprint: def-sp-field-exceptional-system-laws). -/
@[irreducible]
def counitLaw (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : FieldShriekSystem.Laws P D c) (a : Domains P D c) (A : Adjoints P D c b a) : Prop :=
  ∀ (E F : Index P) (h : E ≤ F) (K : N P D E Y),
    (support P D c a F).map (component P D c b a A h K) ≫
        (A.adj F).counit.app ((scalar P D a h Y).obj K) =
      ObjectProperty.homMk ((FieldShriekSystem.iso P D c b h).inv.app
        ((A.right E).obj K) ≫ (D.scalars E F h Y).T.map ((A.adj E).counit.app K).hom)

/-- The unit clause for the actual exceptional coefficient transpose.
Source: blueprint (2), finite and whole-system coefficient compatibility
(blueprint: def-sp-field-exceptional-system-laws). -/
@[irreducible]
def unitLaw (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : FieldShriekSystem.Laws P D c) (a : Domains P D c) (A : Adjoints P D c b a) : Prop :=
  ∀ (E F : Index P) (h : E ≤ F) (M : N P D E X),
    (scalar P D a h X).map ((A.adj E).unit.app M) ≫
      component P D c b a A h ((support P D c a E).obj M) ≫
      (A.right F).map (ObjectProperty.homMk
        (Y := (support P D c a F).obj ((scalar P D a h X).obj M))
        ((FieldShriekSystem.iso P D c b h).hom.app M)) =
      (A.adj F).unit.app ((scalar P D a h X).obj M)

/-- The evaluation clause for the actual exceptional coefficient transpose.
Source: blueprint (2), finite and whole-system coefficient compatibility
(blueprint: def-sp-field-exceptional-system-laws). -/
@[irreducible]
def evaluationLaw (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : FieldShriekSystem.Laws P D c) (a : Domains P D c) (A : Adjoints P D c b a) : Prop :=
  ∀ (E F : Index P) (h : E ≤ F) (n : ℕ) (K : N P D E Y),
    (sourceEvaluation P D c b a A h n K).inv ≫
      (SpTowerShriek.Ev P.coefficients.l F.val X n).map
        (component P D c b a A h K).hom ≫ (targetEvaluation P D c b a A h n K).hom =
      (finiteComponent P D c b a A ((D.coefficients E F h).quotient n)
        ((level P D a E Y n).obj K)).hom

/-- The rightReduction clause for the actual exceptional coefficient transpose.
Source: blueprint (2), finite and whole-system coefficient compatibility
(blueprint: def-sp-field-exceptional-system-laws). -/
@[irreducible]
def rightReductionLaw (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : FieldShriekSystem.Laws P D c) (a : Domains P D c) (A : Adjoints P D c b a) : Prop :=
  ∀ (E : Index P) (m n : ℕ) (v : m ≤ n) (K : N P D E Y),
    (scalarExtensionFunctor (SpTowerCalculus.quotient P.coefficients.l E.val v) X).map
        ((A.evaluation E n).hom.app K).hom ≫
      (finiteComponent P D c b a A (SpTowerCalculus.quotient P.coefficients.l E.val v)
        ((level P D a E Y n).obj K)).hom ≫
      ((A.finite E m).right.map (ObjectProperty.homMk
        (Y := (level P D a E Y m).obj K)
        (systemReduction P E Y v (b.quotientCoordinates E Y v) K.obj))).hom =
    systemReduction P E X v (b.quotientCoordinates E X v) ((A.right E).obj K).obj ≫
      ((A.evaluation E m).hom.app K).hom

/-- The mixed clause for the actual exceptional coefficient transpose.
Source: blueprint (2), finite and whole-system coefficient compatibility
(blueprint: def-sp-field-exceptional-system-laws). -/
@[irreducible]
def mixedLaw (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : FieldShriekSystem.Laws P D c) (a : Domains P D c) (A : Adjoints P D c b a) : Prop :=
  ∀ (E F : Index P) (h : E ≤ F) (m n : ℕ) (v : m ≤ n)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R P.coefficients.l E.val n)),
    HEq (finiteComposite P D c b a A ((D.coefficients E F h).quotient n)
      (SpTowerCalculus.quotient P.coefficients.l F.val v) K)
      (finiteComponent P D c b a A
        ((SpTowerCalculus.quotient P.coefficients.l F.val v).comp
          ((D.coefficients E F h).quotient n)) K).hom ∧
    HEq (finiteComposite P D c b a A (SpTowerCalculus.quotient P.coefficients.l E.val v)
      ((D.coefficients E F h).quotient m) K)
      (finiteComponent P D c b a A
        ((SpTowerCalculus.quotient P.coefficients.l F.val v).comp
          ((D.coefficients E F h).quotient n)) K).hom

/-- The transition clause for the actual exceptional coefficient transpose.
Source: blueprint (2), finite and whole-system coefficient compatibility
(blueprint: def-sp-field-exceptional-system-laws). -/
@[irreducible]
def transitionLaw (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : FieldShriekSystem.Laws P D c) (a : Domains P D c) (A : Adjoints P D c b a) : Prop :=
  ∀ (E F : Index P) (h : E ≤ F) (m n : ℕ) (v : m ≤ n) (K : N P D E Y),
    (scalarExtensionFunctor (SpTowerCalculus.quotient P.coefficients.l F.val v) X).map
        ((SpTowerShriek.Ev P.coefficients.l F.val X n).map
          (component P D c b a A h K).hom) ≫
      systemReduction P F X v (b.quotientCoordinates F X v)
        (((A.right F).obj ((scalar P D a h Y).obj K)).obj) =
    systemReduction P F X v (b.quotientCoordinates F X v)
        (((scalar P D a h X).obj ((A.right E).obj K)).obj) ≫
      (SpTowerShriek.Ev P.coefficients.l F.val X m).map
        (component P D c b a A h K).hom

/-- The composition clause for the actual exceptional coefficient transpose.
Source: blueprint (2), finite and whole-system coefficient compatibility
(blueprint: def-sp-field-exceptional-system-laws). -/
@[irreducible]
def compositionLaw (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : FieldShriekSystem.Laws P D c) (a : Domains P D c) (A : Adjoints P D c b a) : Prop :=
  ∀ (E F L : Index P) (h : E ≤ F) (k : F ≤ L) (K : N P D E Y),
    (D.scalars F L k X).T.map (component P D c b a A h K).hom ≫
      (component P D c b a A k ((scalar P D a h Y).obj K)).hom ≫
      ((A.right L).map (ObjectProperty.homMk
        (Y := (scalar P D a (h.trans k) Y).obj K)
        ((scalarAssoc P D h k Y (b.coefficientComposition E F L h k Y)).hom.app K.obj))).hom =
    (scalarAssoc P D h k X (b.coefficientComposition E F L h k X)).hom.app
        ((A.right E).obj K).obj ≫ (component P D c b a A (h.trans k) K).hom

/-- The identity clause for the actual exceptional coefficient transpose.
Source: blueprint (2), finite and whole-system coefficient compatibility
(blueprint: def-sp-field-exceptional-system-laws). -/
@[irreducible]
def identityLaw (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : FieldShriekSystem.Laws P D c) (a : Domains P D c) (A : Adjoints P D c b a) : Prop :=
  ∀ (E : Index P) (K : N P D E Y),
    (component P D c b a A (E := E) (F := E) le_rfl K).hom ≫
      ((A.right E).map (ObjectProperty.homMk (Y := K)
        ((scalarUnit P D E Y (b.coefficientIdentity E Y)).hom.app K.obj))).hom =
    (scalarUnit P D E X (b.coefficientIdentity E X)).hom.app ((A.right E).obj K).obj

/-- All laws for the actual transpose, retaining all finite and whole-system clauses.
Source: blueprint (2), exceptional coefficient comparison
(blueprint: def-sp-field-exceptional-system-laws). -/
structure Laws (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : FieldShriekSystem.Laws P D c) (a : Domains P D c) (A : Adjoints P D c b a) : Prop where
  invertible : invertibleLaw P D c b a A
  naturality : naturalityLaw P D c b a A
  counit : counitLaw P D c b a A
  unit : unitLaw P D c b a A
  evaluation : evaluationLaw P D c b a A
  rightReduction : rightReductionLaw P D c b a A
  mixed : mixedLaw P D c b a A
  transition : transitionLaw P D c b a A
  composition : compositionLaw P D c b a A
  identity : identityLaw P D c b a A

end AlgebraicGeometry.ProEtale.FieldExceptionalSystem
