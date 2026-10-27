/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Sheaf.AlgebraicGeometry.SpaceSmoothLocalSourceTarget
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.ModuliChartNormalization
public import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.CategoryTheory.MorphismProperty.Limits
import Sheaf.AlgebraicGeometry.EtaleSmoothAtlasFppfDescent
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

/-! # Smooth chart comparison for Deligne--Mumford stack morphisms

Source: Stacks Project, Morphisms of Stacks, Tag 06FM, lemma-local-source-target;
Descent on Spaces, Tag 06F8; Criteria for Representability, Tag 076V
(blueprint: lem-sfb-stack-smooth-chart-comparison).

`SmoothChartAll` and `SmoothChartSome` encode (A) and (B). Their chart class is
`fun _ ↦ True` for algebraic spaces, and representable presheaves for schemes.
The specified based natural isomorphism determines the actual comparison map in (A).

## Main statements

- `stack_smooth_chart_comparison`: the four chart conditions.
- `space_smooth_chart_comparison`: compatibility with an ordinary algebraic-space map.
- `representable_smooth_chart_comparison`: compatibility with scheme base changes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory.Limits

namespace CategoryTheory

/-- Condition (A), with charts in the specified class. Smooth scheme-base-change tests
include representability of both vertical maps and of the induced comparison map.
Source: Stacks Project, Tag 06FM, condition (1)
(blueprint: lem-sfb-stack-smooth-chart-comparison). -/
def SmoothChartAll {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    (C : AlgebraicSpace S → Prop)
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) : Prop :=
  ∀ (U V : AlgebraicSpace S), C U → C V →
    ∀ (a : BasedFunctor (discreteModuli U.obj.obj) F)
      (b : BasedFunctor (discreteModuli V.obj.obj) G) (h : U ⟶ V)
      (e : a.comp f ≅ (discreteModuliMap h.hom.hom).comp b),
      ModuliSpaceTest @Smooth a → ModuliSpaceTest @Smooth b →
      ModuliSpaceTest @Smooth (moduliTwoFiberLift a (discreteModuliMap h.hom.hom) e) →
      P h

/-- Condition (B), with charts in the specified class. Surjectivity is the existing
field-extension-local lifting condition, including the comparison isomorphism.
Source: Stacks Project, Tag 06FM, condition (2)
(blueprint: lem-sfb-stack-smooth-chart-comparison). -/
def SmoothChartSome {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    (C : AlgebraicSpace S → Prop)
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) : Prop :=
  ∃ (U V : AlgebraicSpace S), C U ∧ C V ∧
    ∃ (a : BasedFunctor (discreteModuli U.obj.obj) F)
      (b : BasedFunctor (discreteModuli V.obj.obj) G) (h : U ⟶ V),
      Nonempty (a.comp f ≅ (discreteModuliMap h.hom.hom).comp b) ∧
        ModuliSpaceTest @Smooth a ∧ ModuliSpaceTest @Smooth b ∧
          IsSurjectiveModuliMap a ∧ P h

/-- All four chart conditions are equivalent, for spaces and for schemes.
Source: Stacks Project, Tag 06FM and Tag 076V
(blueprint: lem-sfb-stack-smooth-chart-comparison).

Proof: (1) An étale atlas is smooth by lem-sfb-stack-chartwise-smooth-etale-calculus;
lem-sfb-etale-smooth-atlas-fppf-descent identifies these étale stacks with fppf stacks.
(2) Choose an étale scheme atlas V of G and an étale scheme atlas U of F ×_G V.
By lem-sfb-dm-etale-atlas-calculus and the chartwise calculus, these give an admissible
scheme diagram in (A), with a smooth surjective; hence A_sch implies B_sch.
(3) Given B_sp and an admissible primed diagram, form W = U ×_F U', D = V ×_G V'
and R = U ×_V D. These are spaces by lem-sfb-representable-pullback-over-space and
lem-trf-space-fibre-products-etale-covers. Identify W with R ×_(F ×_G V') U'. Thus
W → R is smooth; W → U' is smooth surjective; D → V and D → V' are smooth.
(4) Smooth base change of h gives P(R → D), and smooth precomposition gives P(W → D).
Lift each point of U' to W and apply the pointwise locality clause to obtain P(h').
Thus B_sp implies A_sp. (5) A_sp implies A_sch by restriction, and B_sch implies B_sp
by inclusion, using def-trf-scheme-algebraic-space. These implications form a cycle.
No comparison smoothness or target-surjectivity condition is added to (B). -/
theorem stack_smooth_chart_comparison {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) [P.RespectsIso]
    (hP : IsSmoothLocalOnSourceAndTarget P)
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (hF : IsDeligneMumfordModuliStack F) (hG : IsDeligneMumfordModuliStack G)
    (f : BasedFunctor F G) :
    (SmoothChartAll P (fun _ ↦ True) f ↔ SmoothChartSome P (fun _ ↦ True) f) ∧
      (SmoothChartAll P (fun _ ↦ True) f ↔
        SmoothChartAll P (fun U ↦ U.obj.obj.IsRepresentable) f) ∧
      (SmoothChartSome P (fun _ ↦ True) f ↔
        SmoothChartSome P (fun U ↦ U.obj.obj.IsRepresentable) f) := by
  sorry

/-- For an ordinary algebraic-space map, the chart conditions recover its property P.
Together with stack_smooth_chart_comparison this applies to all four chart conditions.
Source: Stacks Project, Tag 06FM, algebraic-space compatibility paragraph
(blueprint: lem-sfb-stack-smooth-chart-comparison).

Proof: apply (A) to the identity vertical maps to get P(r). Conversely, smooth base
change gives P(X ×_Y V → V), and precomposition with the assumed smooth comparison
U → X ×_Y V gives P(h). The four-condition cycle in the first five proof steps of
stack_smooth_chart_comparison then gives the same statement for (B) and scheme charts;
spaces have étale scheme atlases by def-trf-algebraic-space. -/
theorem space_smooth_chart_comparison {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) [P.RespectsIso]
    (hP : IsSmoothLocalOnSourceAndTarget P)
    {X Y : AlgebraicSpace S} (r : X ⟶ Y) :
    (SmoothChartAll P (fun _ ↦ True) (discreteModuliMap r.hom.hom) ↔ P r) ∧
      (SmoothChartSome P (fun _ ↦ True) (discreteModuliMap r.hom.hom) ↔ P r) ∧
      (SmoothChartAll P (fun U ↦ U.obj.obj.IsRepresentable)
        (discreteModuliMap r.hom.hom) ↔ P r) ∧
      (SmoothChartSome P (fun U ↦ U.obj.obj.IsRepresentable)
        (discreteModuliMap r.hom.hom) ↔ P r) := by
  sorry

/-- For a representable map, chart conditions agree with P on every scheme base change.
Fppf locality tests actual pullback projections along every fppf target-cover family.
Source: Stacks Project, Tag 06FM, final paragraph; Tag 03Y8 for covering families
(blueprint: lem-sfb-stack-smooth-chart-comparison).

Proof: use the four-condition equivalence proved by the atlas construction and comparison
square in stack_smooth_chart_comparison (node proof steps 1--5). For step (6), given a
witness (U,V,a,b,h) for (B) and T → G, put Z = F ×_G T, H = T ×_G V and
G₀ = Z ×_F U. By lem-sfb-representable-pullback-over-space these are spaces and the
fibre-product triples identify G₀ with H ×_V U. Arbitrary base change gives P(G₀ → H).
The vertical maps to Z → T are smooth and the source one is surjective by
lem-sfb-stack-chartwise-smooth-etale-calculus; pointwise locality gives P(Z → T).
Step (7): conversely choose an étale scheme atlas V → G. Representability makes
F ×_G V a space with P over V. Choose its étale scheme atlas U and apply smooth
precomposition to obtain P(U → V). The composite U → F is smooth surjective by
the chartwise calculus, giving (B). The assumed fppf locality is retained as in 06FM;
its extra use is unnecessary for this pointwise-locality argument. -/
theorem representable_smooth_chart_comparison {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) [P.RespectsIso]
    (hP : IsSmoothLocalOnSourceAndTarget P) [P.IsStableUnderBaseChange]
    (hfppf : ∀ {X Y : AlgebraicSpace S} (r : X ⟶ Y) (I : Type (u + 1))
      (V : I → AlgebraicSpace S) (b : ∀ i : I, V i ⟶ Y), IsFppfCover b →
        (P r ↔ ∀ (i : I) (W : AlgebraicSpace S) (a : W ⟶ X) (q : W ⟶ V i),
          IsPullback a q r (b i) → P q))
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (hF : IsDeligneMumfordModuliStack F) (hG : IsDeligneMumfordModuliStack G)
    (f : BasedFunctor F G) (hf : IsRepresentableByAlgebraicSpaces f) :
    SmoothChartAll P (fun _ ↦ True) f ↔
      ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) G)
        (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange f T t Z p →
          P (ObjectProperty.homMk (⟨p⟩ : Z.obj ⟶ (schemeSpace T).obj)) := by
  sorry

end CategoryTheory
