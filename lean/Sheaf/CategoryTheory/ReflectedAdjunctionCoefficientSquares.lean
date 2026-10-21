/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil SHEAF project
-/
module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import Mathlib.CategoryTheory.Shift.Adjunction

/-! # Unit-normalized reflection of coefficient squares

Source: literature/blueprint/main-20261015/blueprint/sec-proper-base-change/
sk-thm-properbasechange/prop-weil-pbc-scalar-extension.md, coherent comparisons;
Stacks Tags 0037, 07A7, 0DV0, 0E46 and 0E47.
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares).

The structures below only package the specified reflective subcategories,
adjunctions and coefficient squares. All constructions use Mathlib's full
subcategories, reflectors and mate correspondence. In particular, the mate is
never required to be invertible.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CategoryTheory.ReflectedCoefficient

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ u₅ v₅

/-- The specified full reflective, isomorphism-closed subcategory of local objects.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
structure Context (C : Type u₀) [Category.{v₀} C] where
  /-- The local objects. -/
  localObjects : ObjectProperty C
  /-- Locality is invariant under isomorphism. -/
  closed : localObjects.IsClosedUnderIsomorphisms
  /-- The specified reflector and its adjunction to the full inclusion. -/
  reflective : Reflective localObjects.ι

attribute [instance] Context.closed Context.reflective

variable {C₀ : Type u₀} [Category.{v₀} C₀]
  {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] {C₄ : Type u₄} [Category.{v₄} C₄]
  {C₅ : Type u₅} [Category.{v₅} C₅]

/-- The specified reflector followed by the inclusion, denoted Λ in the node.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Context.completion (A : Context C₀) : C₀ ⥤ C₀ :=
  reflector A.localObjects.ι ⋙ A.localObjects.ι

/-- The unit η of the specified reflection.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Context.unit (A : Context C₀) : 𝟭 C₀ ⟶ A.completion :=
  (reflectorAdjunction A.localObjects.ι).unit

/-- An adjunction with a local-object-preserving right adjoint and normalized γ.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
structure Arrow (A : Context C₀) (B : Context C₁) where
  /-- The specified left adjoint. -/
  F : C₀ ⥤ C₁
  /-- The specified right adjoint. -/
  G : C₁ ⥤ C₀
  /-- The specified adjunction. -/
  adj : F ⊣ G
  /-- The right adjoint preserves local objects. -/
  preserves : ∀ Y, B.localObjects Y → A.localObjects (G.obj Y)
  /-- The specified completion comparison. -/
  gamma : G ⋙ A.completion ≅ B.completion ⋙ G
  /-- Normalization by the reflection units. -/
  gamma_unit : ∀ Y, A.unit.app (G.obj Y) ≫ gamma.hom.app Y = G.map (B.unit.app Y)

/-- Coefficient change with its specified unit-normalized comparison κ.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
structure Change (A : Context C₀) (B : Context C₁) where
  /-- The ambient coefficient functor. -/
  F : C₀ ⥤ C₁
  /-- The specified coefficient/reflection comparison. -/
  kappa : A.completion ⋙ F ≅ F ⋙ B.completion
  /-- Its reflection-unit normalization. -/
  kappa_unit : ∀ X, F.map (A.unit.app X) ≫ kappa.hom.app X = B.unit.app (F.obj X)

/-- Coefficient functors preserve local objects.

Proof: step 1. Locality is equivalent to invertibility of the unit. The
normalized κ expresses the target unit as a composite of isomorphisms.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Change.preserves {A : Context C₀} {B : Context C₁} (c : Change A B)
    (X : C₀) (hX : A.localObjects X) : B.localObjects (c.F.obj X) := by
  sorry

/-- The restriction of a coefficient change, using its proved locality clause.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Change.restrict {A : Context C₀} {B : Context C₁} (c : Change A B) :
    A.localObjects.FullSubcategory ⥤ B.localObjects.FullSubcategory :=
  B.localObjects.lift (A.localObjects.ι ⋙ c.F) (fun X ↦ c.preserves X.obj X.property)

/-- The left adjoint on local inputs, followed by reflection in the target.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
abbrev Arrow.left {A : Context C₀} {B : Context C₁} (a : Arrow A B) :
    A.localObjects.FullSubcategory ⥤ B.localObjects.FullSubcategory :=
  A.localObjects.ι ⋙ a.F ⋙ reflector B.localObjects.ι

/-- The restriction of the right adjoint to the full local subcategories.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
abbrev Arrow.right {A : Context C₀} {B : Context C₁} (a : Arrow A B) :
    B.localObjects.FullSubcategory ⥤ A.localObjects.FullSubcategory :=
  A.localObjects.lift (B.localObjects.ι ⋙ a.G)
    (fun Y ↦ a.preserves Y.obj Y.property)

/-- Existence of the reflected adjunction with its specified Hom bijection.

Proof: step 2. Compose the fully faithful inclusion Hom bijections,
precomposition by the reflection unit, and the original adjunct. Reflection
into a local target makes the middle operation bijective. Naturality follows
from naturality of the unit and the original Hom bijection. Apply
Adjunction.mkOfHomEquiv (the natural-bijection dependency).

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Arrow.adjunction_exists {A : Context C₀} {B : Context C₁} (a : Arrow A B) :
    ∃ h : a.left ⊣ a.right, ∀ (X : A.localObjects.FullSubcategory)
      (Y : B.localObjects.FullSubcategory) (t : a.left.obj X ⟶ Y),
      A.localObjects.ι.map (h.homEquiv X Y t) =
        a.adj.homEquiv X.obj Y.obj
          (B.unit.app (a.F.obj X.obj) ≫ B.localObjects.ι.map t) := by
  sorry

/-- The adjunction determined uniquely by the displayed Hom bijections.
The postponed existence theorem determines the entire adjunction, rather than
choosing arbitrary data from a mere existence assertion.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Arrow.reflectedAdjunction {A : Context C₀} {B : Context C₁} (a : Arrow A B) :
    a.left ⊣ a.right :=
  Classical.choose a.adjunction_exists

/-- A coefficient square of the two specified left adjoints.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
structure Square {A₀ : Context C₀} {B₀ : Context C₁}
    {A₁ : Context C₂} {B₁ : Context C₃}
    (a₀ : Arrow A₀ B₀) (a₁ : Arrow A₁ B₁)
    (cA : Change A₀ A₁) (cB : Change B₀ B₁) where
  /-- The specified left comparison δ. -/
  delta : cA.F ⋙ a₁.F ≅ a₀.F ⋙ cB.F

variable {A₀ : Context C₀} {B₀ : Context C₁}
  {A₁ : Context C₂} {B₁ : Context C₃}
  {a₀ : Arrow A₀ B₀} {a₁ : Arrow A₁ B₁}
  {cA : Change A₀ A₁} {cB : Change B₀ B₁}

/-- The ambient right mate β, using the dependency CategoryTheory.mateEquiv.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Square.beta (s : Square a₀ a₁ cA cB) : a₀.G ⋙ cA.F ⟶ cB.F ⋙ a₁.G :=
  mateEquiv a₀.adj a₁.adj s.delta.hom

/-- The ambient formula κ_B⁻¹ Λ_B(δ) whose restriction is the reflected square.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Square.comparison (s : Square a₀ a₁ cA cB) :
    cA.F ⋙ a₁.F ⋙ B₁.completion ≅ a₀.F ⋙ B₀.completion ⋙ cB.F :=
  isoWhiskerRight s.delta B₁.completion ≪≫ isoWhiskerLeft a₀.F cB.kappa.symm

/-- Naturality needed to construct the local comparison from its ambient formula.

Proof: step 3. Both components are lifted by the full inclusion; apply
faithfulness to the ambient comparison naturality equation.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Square.comparison_naturality (s : Square a₀ a₁ cA cB)
    (X Y : A₀.localObjects.FullSubcategory) (f : X ⟶ Y) :
    (cA.restrict ⋙ a₁.left).map f ≫
        (B₁.localObjects.isoMk (s.comparison.app Y.obj)).hom =
      (B₁.localObjects.isoMk (s.comparison.app X.obj)).hom ≫
        (a₀.left ⋙ cB.restrict).map f := by
  sorry

/-- The canonical comparison on local objects, with actual isomorphism data.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Square.localComparison (s : Square a₀ a₁ cA cB) :
    cA.restrict ⋙ a₁.left ≅ a₀.left ⋙ cB.restrict :=
  NatIso.ofComponents (fun X ↦ B₁.localObjects.isoMk (s.comparison.app X.obj))
    (fun {X Y} f ↦ s.comparison_naturality X Y f)

/-- The reflected coefficient square has exactly the restricted ambient right mate.

Proof: steps 3 and 4. The comparison satisfies δhat k₁=C_B(k₀)δ by
naturality of η and normalization of κ. The reflected counit satisfies
ehat k=e by the specified Hom bijection. Thus the reflected transpose, after
precomposition by k₁, is C_B(e₀)δ, whose ordinary adjunct is β. The Hom
bijection defining the reflected adjunction proves the claimed equality;
no invertibility of β is used.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Square.mate (s : Square a₀ a₁ cA cB)
    (Y : B₀.localObjects.FullSubcategory) :
    A₁.localObjects.ι.map
        ((mateEquiv a₀.reflectedAdjunction a₁.reflectedAdjunction
          s.localComparison.hom).app Y) = s.beta.app Y.obj := by
  sorry

/-- The ambient γ/κ normalization equation, including nonlocal inputs.

Proof: step 5. Both sides target the local object G₁C_BΛ₀M.
Precomposition with C_A(η₀) is injective by κ_A and reflection. After
precomposition, γ₀ normalization and β naturality give G₁C_B(η₀)β
on the left. On the right use κ_A normalization, η₁ naturality, γ₁
normalization, then κ_B normalization to obtain the same map.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Square.normalization (s : Square a₀ a₁ cA cB) (M : C₁) :
    cA.F.map (a₀.gamma.hom.app M) ≫ s.beta.app (B₀.completion.obj M) =
      cA.kappa.hom.app (a₀.G.obj M) ≫ A₁.completion.map (s.beta.app M) ≫
        a₁.gamma.hom.app (cB.F.obj M) ≫ a₁.G.map (cB.kappa.inv.app M) := by
  sorry

variable {A₂ : Context C₄} {B₂ : Context C₅}
  {a₂ : Arrow A₂ B₂} {dA : Change A₁ A₂} {dB : Change B₁ B₂}

/-- The composite coefficient comparison is unit-normalized.

Proof: step 6. Apply D to the normalization for C, and then use the
normalization for D at C X. Functoriality gives the stated equation.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Change.comp_kappa_unit
    {A : Context C₀} {B : Context C₁} {D : Context C₂}
    (c : Change A B) (d : Change B D) (X : C₀) :
    d.F.map (c.F.map (A.unit.app X)) ≫
      d.F.map (c.kappa.hom.app X) ≫ d.kappa.hom.app (c.F.obj X) =
        D.unit.app (d.F.obj (c.F.obj X)) := by
  sorry

/-- The specified composite coefficient data: κ_DC=κ_D D(κ_C).

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Change.comp {A : Context C₀} {B : Context C₁} {D : Context C₂}
    (c : Change A B) (d : Change B D) : Change A D where
  F := c.F ⋙ d.F
  kappa := isoWhiskerRight c.kappa d.F ≪≫ isoWhiskerLeft c.F d.kappa
  kappa_unit := c.comp_kappa_unit d

/-- The specified coefficient squares paste by whiskering their δ isomorphisms.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Square.coefficientComp (s : Square a₀ a₁ cA cB)
    (t : Square a₁ a₂ dA dB) : Square a₀ a₂ (cA.comp dA) (cB.comp dB) where
  delta := isoWhiskerLeft cA.F t.delta ≪≫ isoWhiskerRight s.delta dB.F

/-- Coefficient-square pasting commutes with reflection and taking right mates.

Proof: step 6. The pasted κ is κ_D D(κ_C). Precompose both left
comparisons by the reflection unit k₂ and use δhat k₁=C_B(k₀)δ
twice. Their local target makes this test injective. The mate equality is
mateEquiv_vcomp, the first clause of the mate-pasting dependency. Iteration
uses associativity of composition and functoriality, as in step 9.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Square.coefficient_pasting (s : Square a₀ a₁ cA cB)
    (t : Square a₁ a₂ dA dB) (X : A₀.localObjects.FullSubcategory) (M : C₁) :
    (B₂.completion.map
        (t.delta.hom.app (cA.F.obj X.obj) ≫ dB.F.map (s.delta.hom.app X.obj)) ≫
      dB.kappa.inv.app (cB.F.obj (a₀.F.obj X.obj)) ≫
      dB.F.map (cB.kappa.inv.app (a₀.F.obj X.obj)) =
        t.comparison.hom.app (cA.F.obj X.obj) ≫
          dB.F.map (s.comparison.hom.app X.obj)) ∧
    ((mateEquiv (G := cA.F ⋙ dA.F) (H := cB.F ⋙ dB.F) a₀.adj a₂.adj
        (whiskerLeft cA.F t.delta.hom ≫ whiskerRight s.delta.hom dB.F)).app M =
      dA.F.map (s.beta.app M) ≫ t.beta.app (cB.F.obj M)) := by
  sorry

/-- The composite completion comparison has the required unit normalization.

Proof: step 9. Substitute γ_G η_A=G(η_B), then naturality and
γ_J η_B=J(η_D). Functoriality gives GJ(η_D).

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Arrow.comp_gamma_unit {A : Context C₀} {B : Context C₁} {D : Context C₂}
    (a : Arrow A B) (h : Arrow B D) (M : C₂) :
    A.unit.app (a.G.obj (h.G.obj M)) ≫
      a.gamma.hom.app (h.G.obj M) ≫ a.G.map (h.gamma.hom.app M) =
        a.G.map (h.G.map (D.unit.app M)) := by
  sorry

/-- The specified composite adjunction and normalized completion comparison.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Arrow.comp {A : Context C₀} {B : Context C₁} {D : Context C₂}
    (a : Arrow A B) (h : Arrow B D) : Arrow A D where
  F := a.F ⋙ h.F
  G := h.G ⋙ a.G
  adj := a.adj.comp h.adj
  preserves Y hY := a.preserves _ (h.preserves Y hY)
  gamma := isoWhiskerLeft h.G a.gamma ≪≫ isoWhiskerRight h.gamma a.G
  gamma_unit := a.comp_gamma_unit h

/-- The comparison q=Λ_D H(η_B F) between reflecting before and after
composition. This is actual canonical morphism data, not an arbitrary iso.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Arrow.compositionComparison {A : Context C₀} {B : Context C₁} {D : Context C₂}
    (a : Arrow A B) (h : Arrow B D) :
    a.F ⋙ h.F ⋙ D.completion ⟶ a.F ⋙ B.completion ⋙ h.F ⋙ D.completion :=
  whiskerRight (whiskerLeft a.F B.unit) (h.F ⋙ D.completion)

/-- The composition comparison is invertible on local inputs and identifies
the Hom bijections of the reflected composite and the composite reflections.

Proof: step 7. Testing q into every local Z identifies precomposition by
q with precomposition by k:F X→Λ_B F X into the local J Z. The latter
is bijective. Testing Z=Q and Z=P supplies a two-sided inverse of q.
The displayed equality follows from naturality of the reflection unit and
the composite Hom formula of Adjunction.comp. This does not require H to
preserve local objects. Iterated comparisons are determined by these Hom
bijections, so their parenthesizations agree (step 9).

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Arrow.compositionComparison_spec
    {A : Context C₀} {B : Context C₁} {D : Context C₂}
    (a : Arrow A B) (h : Arrow B D) (X : A.localObjects.FullSubcategory) :
    IsIso ((a.compositionComparison h).app X.obj) ∧
    ∀ (Z : D.localObjects.FullSubcategory)
      (t : D.completion.obj (h.F.obj (B.completion.obj (a.F.obj X.obj))) ⟶ Z.obj),
      (a.adj.comp h.adj).homEquiv X.obj Z.obj
          (D.unit.app (h.F.obj (a.F.obj X.obj)) ≫
            (a.compositionComparison h).app X.obj ≫ t) =
        a.adj.homEquiv X.obj (h.G.obj Z.obj)
          (B.unit.app (a.F.obj X.obj) ≫
            h.adj.homEquiv (B.completion.obj (a.F.obj X.obj)) Z.obj
              (D.unit.app (h.F.obj (B.completion.obj (a.F.obj X.obj))) ≫ t)) := by
  sorry

/-- Pasting along adjunctions uses the specified composite adjunctions and δ squares.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Square.adjunctionComp
    {D₀ : Context C₄} {D₁ : Context C₅}
    {h₀ : Arrow B₀ D₀} {h₁ : Arrow B₁ D₁} {cD : Change D₀ D₁}
    (s : Square a₀ a₁ cA cB) (t : Square h₀ h₁ cB cD) :
    Square (a₀.comp h₀) (a₁.comp h₁) cA cD where
  delta := isoWhiskerRight s.delta h₁.F ≪≫ isoWhiskerLeft a₀.F t.delta

/-- Pasting adjunction squares commutes with reflection under the canonical q
comparisons, and the right mate is the pasted right mate.

Proof: step 8. Precompose the left equality by s₁, use naturality of the
second reflection unit, δhat k₁=C_B(k₀)δ for both squares, and
naturality of ε at k₀. Both sides become C_D(q₀)ρhat s₁. Cancel s₁
into the local target. The specified Hom bijections from step 7 identify
the adjunctions; mateEquiv_hcomp gives the right equality. Step 9 gives
associativity for iterations by uniqueness under these Hom tests.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Square.adjunction_pasting
    {D₀ : Context C₄} {D₁ : Context C₅}
    {h₀ : Arrow B₀ D₀} {h₁ : Arrow B₁ D₁} {cD : Change D₀ D₁}
    (s : Square a₀ a₁ cA cB) (t : Square h₀ h₁ cB cD)
    (X : A₀.localObjects.FullSubcategory) (Z : C₄) :
    ((a₁.compositionComparison h₁).app (cA.F.obj X.obj) ≫
      D₁.completion.map (h₁.F.map (s.comparison.hom.app X.obj)) ≫
      t.comparison.hom.app (B₀.completion.obj (a₀.F.obj X.obj)) =
        D₁.completion.map
          (h₁.F.map (s.delta.hom.app X.obj) ≫ t.delta.hom.app (a₀.F.obj X.obj)) ≫
          cD.kappa.inv.app (h₀.F.obj (a₀.F.obj X.obj)) ≫
          cD.F.map ((a₀.compositionComparison h₀).app X.obj)) ∧
    ((mateEquiv (a₀.adj.comp h₀.adj) (a₁.adj.comp h₁.adj)
        (whiskerRight s.delta.hom h₁.F ≫ whiskerLeft a₀.F t.delta.hom)).app Z =
      s.beta.app (h₀.G.obj Z) ≫ a₁.G.map (t.beta.app Z)) := by
  sorry

/-- Repeated coefficient composition is associative with its specified κ.

Proof: step 9. Expand the composite κ formula. Functoriality and
associativity of morphism composition give the same iterated product.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Change.associativity
    {A : Context C₀} {B : Context C₁} {D : Context C₂} {E : Context C₃}
    (c : Change A B) (d : Change B D) (e : Change D E) (X : C₀) :
    ((c.comp d).comp e).kappa.hom.app X = (c.comp (d.comp e)).kappa.hom.app X := by
  sorry

/-- Repeated adjunction pasting gives the same normalized comparisons and
Hom bijections for either parenthesization.

Proof: steps 7 and 9. Naturality of the D reflection unit applied to
H(k) proves the q equality, or equivalently test both sides by their
composite Hom bijections. Expansion and functoriality prove the γ
equality. Adjunction.comp has Hom bijection the composite of functions,
which is associative. These normalizations together with the two binary
pasting theorems give the asserted iterated square coherence.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Arrow.associativity
    {A : Context C₀} {B : Context C₁} {D : Context C₂} {E : Context C₃}
    (a : Arrow A B) (h : Arrow B D) (k : Arrow D E)
    (X : A.localObjects.FullSubcategory) (Y : C₃) :
    (((a.comp h).compositionComparison k).app X.obj ≫
      E.completion.map (k.F.map ((a.compositionComparison h).app X.obj)) =
        (a.compositionComparison (h.comp k)).app X.obj ≫
          (h.compositionComparison k).app (B.completion.obj (a.F.obj X.obj))) ∧
    (((a.comp h).comp k).gamma.hom.app Y = (a.comp (h.comp k)).gamma.hom.app Y) ∧
    ∀ (t : k.F.obj (h.F.obj (a.F.obj X.obj)) ⟶ Y),
      ((a.comp h).comp k).adj.homEquiv X.obj Y t =
        (a.comp (h.comp k)).adj.homEquiv X.obj Y t := by
  sorry

/-- The identity coefficient data, with literal identity functor.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Change.id (A : Context C₀) : Change A A where
  F := 𝟭 C₀
  kappa := Iso.refl A.completion
  kappa_unit X := Category.comp_id (A.unit.app X)

/-- The identity coefficient square of a specified adjunction.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Square.id {A : Context C₀} {B : Context C₁} (a : Arrow A B) :
    Square a a (Change.id A) (Change.id B) where
  delta := Iso.refl a.F

/-- Identity coefficient squares give identity comparisons on both sides.

Proof: step 9. The comparison precomposed with k is k, so reflection
uniqueness gives the identity. The identity clause of mate-pasting gives
the identity right mate. The same unit test proves iterated identity laws.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Square.identity {A : Context C₀} {B : Context C₁} (a : Arrow A B)
    (X : A.localObjects.FullSubcategory) (Y : C₁) :
    (Square.id a).comparison.hom.app X.obj = 𝟙 _ ∧
      (Square.id a).beta.app Y = 𝟙 _ := by
  sorry

/-- The identity adjunction with its literal functors and normalized γ.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
def Arrow.id (A : Context C₀) : Arrow A A where
  F := 𝟭 C₀
  G := 𝟭 C₀
  adj := Adjunction.id
  preserves _ h := h
  gamma := Iso.refl A.completion
  gamma_unit X := Category.comp_id (A.unit.app X)

/-- The identity adjunction reflects to the identity under η_X⁻¹.

Proof: step 9. Locality makes η_X invertible. The reflected identity
Hom bijection is precomposition by η_X, so its unit is η_X and its
counit is its inverse; this gives the normalized identity comparison.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Arrow.identity {A : Context C₀} (X : A.localObjects.FullSubcategory) :
    IsIso (A.unit.app X.obj) ∧
    A.localObjects.ι.map ((Arrow.id A).reflectedAdjunction.unit.app X) =
      A.unit.app X.obj ∧
    A.unit.app X.obj ≫
      A.localObjects.ι.map ((Arrow.id A).reflectedAdjunction.counit.app X) = 𝟙 _ := by
  sorry

/-- Local objects are stable under all specified shifts.

Proof: step 10. The shift comparison of Λ and compatibility of η
identify η_(X[a]) with the shifted invertible unit η_X. Thus X[a] is
local by the locality criterion from step 1.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Context.stableUnderShift (A : Context C₀) [HasShift C₀ ℤ]
    [A.completion.CommShift ℤ] [NatTrans.CommShift A.unit ℤ] :
    A.localObjects.IsStableUnderShift ℤ := by
  sorry

attribute [instance] Context.stableUnderShift

/-- The reflector commutes with shifts by fully faithful transport from Λ.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
instance Context.reflectorCommShift (A : Context C₀) [HasShift C₀ ℤ]
    [A.completion.CommShift ℤ] [NatTrans.CommShift A.unit ℤ] :
    (reflector A.localObjects.ι).CommShift ℤ :=
  Functor.CommShift.ofComp (Iso.refl A.completion) ℤ

/-- The reflected left functor has the composite specified shift comparison.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
instance Arrow.leftCommShift {A : Context C₀} {B : Context C₁} (a : Arrow A B)
    [HasShift C₀ ℤ] [HasShift C₁ ℤ]
    [A.completion.CommShift ℤ] [NatTrans.CommShift A.unit ℤ]
    [B.completion.CommShift ℤ] [NatTrans.CommShift B.unit ℤ] [a.F.CommShift ℤ] :
    a.left.CommShift ℤ :=
  inferInstanceAs ((A.localObjects.ι ⋙ a.F ⋙ reflector B.localObjects.ι).CommShift ℤ)

/-- The restricted right functor carries the shift comparison induced by G.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
instance Arrow.rightCommShift {A : Context C₀} {B : Context C₁} (a : Arrow A B)
    [HasShift C₀ ℤ] [HasShift C₁ ℤ]
    [A.completion.CommShift ℤ] [NatTrans.CommShift A.unit ℤ]
    [B.completion.CommShift ℤ] [NatTrans.CommShift B.unit ℤ] [a.G.CommShift ℤ] :
    a.right.CommShift ℤ :=
  inferInstanceAs ((A.localObjects.lift (B.localObjects.ι ⋙ a.G)
    (fun Y ↦ a.preserves Y.obj Y.property)).CommShift ℤ)

/-- Restricted coefficient changes carry the specified composite shift comparison.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
instance Change.restrictCommShift {A : Context C₀} {B : Context C₁} (c : Change A B)
    [HasShift C₀ ℤ] [HasShift C₁ ℤ]
    [A.completion.CommShift ℤ] [NatTrans.CommShift A.unit ℤ]
    [B.completion.CommShift ℤ] [NatTrans.CommShift B.unit ℤ] [c.F.CommShift ℤ] :
    c.restrict.CommShift ℤ :=
  inferInstanceAs ((B.localObjects.lift (A.localObjects.ι ⋙ c.F)
    (fun X ↦ c.preserves X.obj X.property)).CommShift ℤ)

/-- The reflected adjunction respects the specified shifts.

Proof: step 10. Its unit is G(k)u, which commutes with shifts by the
closure dependency. The adjunction-shift dependency, clause (i), gives
compatibility of the counit from that of the unit.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Arrow.reflectedAdjunction_commShift {A : Context C₀} {B : Context C₁}
    (a : Arrow A B) [HasShift C₀ ℤ] [HasShift C₁ ℤ]
    [A.completion.CommShift ℤ] [NatTrans.CommShift A.unit ℤ]
    [B.completion.CommShift ℤ] [NatTrans.CommShift B.unit ℤ]
    [a.F.CommShift ℤ] [a.G.CommShift ℤ] [a.adj.CommShift ℤ] :
    a.reflectedAdjunction.CommShift ℤ := by
  sorry

/-- The reflected coefficient comparison and its right mate respect shifts.

Proof: step 10. Inverses of shift-compatible isomorphisms are compatible
by cancelling the isomorphism in the shift square. Composition and
whiskering preserve compatibility. Apply these rules to κ_B⁻¹Λ_Bδ
and to the unit-square-counit formula defining β. Fully faithful
restriction gives the same conclusion for the local comparison and its
mate, since the reflected adjunctions commute with shifts.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Square.commShift (s : Square a₀ a₁ cA cB)
    [HasShift C₀ ℤ] [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift C₃ ℤ]
    [A₀.completion.CommShift ℤ] [NatTrans.CommShift A₀.unit ℤ]
    [B₀.completion.CommShift ℤ] [NatTrans.CommShift B₀.unit ℤ]
    [A₁.completion.CommShift ℤ] [NatTrans.CommShift A₁.unit ℤ]
    [B₁.completion.CommShift ℤ] [NatTrans.CommShift B₁.unit ℤ]
    [a₀.F.CommShift ℤ] [a₀.G.CommShift ℤ] [a₀.adj.CommShift ℤ]
    [a₁.F.CommShift ℤ] [a₁.G.CommShift ℤ] [a₁.adj.CommShift ℤ]
    [cA.F.CommShift ℤ] [cB.F.CommShift ℤ]
    [NatTrans.CommShift cA.kappa.hom ℤ] [NatTrans.CommShift cB.kappa.hom ℤ]
    [NatTrans.CommShift a₀.gamma.hom ℤ] [NatTrans.CommShift a₁.gamma.hom ℤ]
    [NatTrans.CommShift s.delta.hom ℤ] :
    NatTrans.CommShift s.comparison.hom ℤ ∧ NatTrans.CommShift s.beta ℤ ∧
      NatTrans.CommShift s.localComparison.hom ℤ ∧
      NatTrans.CommShift
        (mateEquiv a₀.reflectedAdjunction a₁.reflectedAdjunction
          s.localComparison.hom).natTrans ℤ := by
  sorry

/-- The composition comparisons also commute with shifts. Consequently all
composites in the normalization and both pasting equations are compatible.

Proof: step 10. The comparison is Λ_D H(k); the given compatibility
of η_B and the closure rules for composition and whiskering imply the
claim. Invertibility on local inputs gives compatible inverse comparisons.

Source: scalar-extension blueprint, coherent pullback/direct-image comparisons;
Stacks Tags 0037, 07A7 and 0DV0
(blueprint: lem-weil-pbc-reflected-adjunction-coefficient-squares). -/
theorem Arrow.compositionComparison_commShift
    {A : Context C₀} {B : Context C₁} {D : Context C₂}
    (a : Arrow A B) (h : Arrow B D)
    [HasShift C₀ ℤ] [HasShift C₁ ℤ] [HasShift C₂ ℤ]
    [B.completion.CommShift ℤ] [D.completion.CommShift ℤ]
    [a.F.CommShift ℤ] [h.F.CommShift ℤ] [NatTrans.CommShift B.unit ℤ] :
    NatTrans.CommShift (a.compositionComparison h) ℤ := by
  sorry

end CategoryTheory.ReflectedCoefficient
