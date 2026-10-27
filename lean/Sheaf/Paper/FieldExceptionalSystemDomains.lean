module

public import Sheaf.Paper.FieldShriekSystemComparison
public import Sheaf.Paper.SmoothPurityTowerGluing
public import Sheaf.SecSmoothPurity.ReductionExceptional

/-! # Exceptional coefficient comparison on whole systems

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension,
sk-lem-sp-field-extension-towers.proof.md (2), counit transpose
(blueprint: def-sp-field-exceptional-system-domains).

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

attribute [local irreducible] FieldShriekSystem.coefficientMap HasDerivedCategory.standard
attribute [local irreducible] supportEvaluation FieldShriekSystem.restrictionEvaluation
attribute [local irreducible] comparison normalized
attribute [local irreducible] scalarAssoc scalarUnit
attribute [local irreducible] reductionCtfCompactSupport
attribute [local irreducible] reductionCtfScalar scalarExtensionFunctor
attribute [local irreducible] reductionDirectImageComparison

/-- The dependency's normalized constructible full subcategory, with uniform bounds.
Source: blueprint (2), N_A(T) (blueprint: def-sp-field-exceptional-system-domains). -/
abbrev N (D : Models P) (E : Index P) (T : Scheme.{u}) :=
  (normalized P D E T).FullSubcategory

/-- Preservation and finite evaluation domains, all asserted as conclusions below.
As in the node, the schemes T range only over the source X and target Y of f.
Source: blueprint (1)--(2) (blueprint: def-sp-field-exceptional-system-domains). -/
structure Domains (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : Prop where
  scalar : ∀ (E F : Index P) (h : E ≤ F) (T : Scheme.{u}), (T = X ∨ T = Y) →
    ∀ (K : N P D E T), normalized P D F T ((D.scalars E F h T).T.obj K.obj)
  support : ∀ (E : Index P) (M : N P D E X), normalized P D E Y
    ((SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c).obj M.obj)
  finite : ∀ (E : Index P) (T : Scheme.{u}), (T = X ∨ T = Y) → ∀ (n : ℕ) (K : N P D E T),
    spFiniteConstructibleTor T (SpTowerShriek.R P.coefficients.l E.val n)
      ((SpTowerShriek.Ev P.coefficients.l E.val T n).obj K.obj)
  finiteScalar : ∀ (E F : Index P) (n m : ℕ)
    (φ : SpTowerShriek.R P.coefficients.l E.val n →+*
      SpTowerShriek.R P.coefficients.l F.val m) (T : Scheme.{u}), (T = X ∨ T = Y) →
    ∀ (K : spFiniteConstructibleTorCategory T (SpTowerShriek.R P.coefficients.l E.val n)),
    spFiniteConstructibleTor T (SpTowerShriek.R P.coefficients.l F.val m)
      ((scalarExtensionFunctor φ T).obj K.obj)

/-- Restriction of the actual scalar functor; it changes no ambient arrow.
Source: blueprint (2), C_T (blueprint: def-sp-field-exceptional-system-domains). -/
def scalar (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (a : Domains P D c) {E F : Index P} (h : E ≤ F) (T : Scheme.{u})
    (hT : T = X ∨ T = Y := by first | exact Or.inl rfl | exact Or.inr rfl) :
    N P D E T ⥤ N P D F T :=
  ObjectProperty.lift _ ((normalized P D E T).ι ⋙ (D.scalars E F h T).T)
    (a.scalar E F h T hT)

/-- Restriction of the same proper/open compact-support functor for every coefficient.
Source: blueprint (2), P_A (blueprint: def-sp-field-exceptional-system-domains). -/
def support (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (a : Domains P D c) (E : Index P) : N P D E X ⥤ N P D E Y :=
  ObjectProperty.lift _ ((normalized P D E X).ι ⋙
    SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c) (a.support E)

/-- Exact evaluation restricted to normalized constructible objects.
Source: blueprint (2), K_n (blueprint: def-sp-field-exceptional-system-domains). -/
def level (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (a : Domains P D c) (E : Index P) (T : Scheme.{u}) (n : ℕ)
    (hT : T = X ∨ T = Y := by first | exact Or.inl rfl | exact Or.inr rfl) :
    N P D E T ⥤ spFiniteConstructibleTorCategory T (SpTowerShriek.R P.coefficients.l E.val n) :=
  ObjectProperty.lift _ ((normalized P D E T).ι ⋙
    SpTowerShriek.Ev P.coefficients.l E.val T n) (a.finite E T hT n)


end AlgebraicGeometry.ProEtale.FieldExceptionalSystem
