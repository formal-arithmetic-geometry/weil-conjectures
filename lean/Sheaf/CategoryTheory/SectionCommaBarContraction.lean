/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.CategoryTheory.DerivedColimitBar
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Vertical sections contract augmented comma bar complexes

Source: Stacks Project, cotangent.tex, Tag 08QW, cases 1 and 2; sites-cohomology.tex,
Tags 08PG and 08PH and lemma-initial-final, with the explicit vertical-section refinement
(blueprint: lem-trf-section-comma-bar-contraction).

The records below expand the assertion into its maps, generator formulas and natural
homotopies. They do not select a bar model or a contraction from a postponed theorem.
The topology is the bottom (identity-cover) topology already used by the bar system;
its constant-ring module sheaves are ordinary module presheaves.
-/

@[expose] public noncomputable section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {E D : Type u} [SmallCategory E] [SmallCategory D]
  {R : Type u} [CommRing R]

/-- The comma projection `(U,a) ↦ (uU,a)`, with arrow map `u`.
Source: Stacks 08QW and 08PH
(blueprint: lem-trf-section-comma-bar-contraction). -/
abbrev sectionCommaBarProjection (f : E ⥤ D) (V : D) :
    StructuredArrow V f ⥤ StructuredArrow V (𝟭 D) :=
  StructuredArrow.pre V f (𝟭 D)

/-- The coherently identified comma section: `(W,a) ↦ (sW,a ≫ ε.inv.app W)`.
Its arrow map is `s`. Source: Stacks 08QW and 08PH, vertical-section refinement
(blueprint: lem-trf-section-comma-bar-contraction). -/
def sectionCommaBarSection (f : E ⥤ D) (s : D ⥤ E) (ε : s ⋙ f ≅ 𝟭 D) (V : D) :
    StructuredArrow V (𝟭 D) ⥤ StructuredArrow V f :=
  StructuredArrow.map₂ (F := s) (G := 𝟭 D) (𝟙 V) ε.inv

/-- The comma bar coefficients `(U,a) ↦ K(uU)`, functorially in `K`.
Source: Stacks 08PG and 08PH
(blueprint: lem-trf-section-comma-bar-contraction). -/
abbrev sectionCommaBarCoefficients (f : E ⥤ D) (V : D) :
    (Dᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ((StructuredArrow V f)ᵒᵖ ⥤ ModuleCat.{u} R) :=
  (Functor.whiskeringLeft _ _ _).obj ((StructuredArrow.proj V f) ⋙ f).op

/-- The specified comma bar complex, using the recorded bar model without another copy.
Source: Stacks 08PG (blueprint: lem-trf-section-comma-bar-contraction). -/
abbrev sectionCommaBarComplex (B : CategoryColimitBarSystem.{u}) (f : E ⥤ D) (V : D) :
    (Dᵒᵖ ⥤ ModuleCat.{u} R) ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  sectionCommaBarCoefficients f V ⋙ (B.models (StructuredArrow V f) R).bar

/-- Evaluation placed in degree zero: the augmentation target `K(V)[0]`.
Source: Stacks 08PG and lemma-initial-final
(blueprint: lem-trf-section-comma-bar-contraction). -/
abbrev sectionCommaBarPoint (V : D) :
    (Dᵒᵖ ⥤ ModuleCat.{u} R) ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  (evaluation Dᵒᵖ (ModuleCat.{u} R)).obj (op V) ⋙
    CochainComplex.singleFunctor (ModuleCat.{u} R) 0

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The maps and contractions asserted by the lemma, including their normalizations
and naturality in every module-presheaf map. The strict case is expressed by
`ε = eqToIso h`, so all occurrences of `us = 1` use the same identification.
Source: Stacks 08QW, 08PG, 08PH and lemma-initial-final, explicit section refinement
(blueprint: lem-trf-section-comma-bar-contraction). -/
structure SectionCommaBarContraction (B : CategoryColimitBarSystem.{u})
    (f : E ⥤ D) (s : D ⥤ E) (ε : s ⋙ f ≅ 𝟭 D) (R : Type u) [CommRing R] (V : D) where
  projection : sectionCommaBarComplex (R := R) B f V ⟶
    sectionCommaBarComplex B (𝟭 D) V
  sectionMap : sectionCommaBarComplex (R := R) B (𝟭 D) V ⟶
    sectionCommaBarComplex B f V
  projectionFormula : ∀ (K : Dᵒᵖ ⥤ ModuleCat.{u} R) (n : ℕ)
    (c : ComposableArrows (StructuredArrow V f) n) (x : K.obj (op (f.obj c.right.right))),
    ((projection.app K).f (-(n : ℤ)))
      ((B.models (StructuredArrow V f) R).generator
        ((sectionCommaBarCoefficients f V).obj K) n c x) =
      (B.models (StructuredArrow V (𝟭 D)) R).generator
        ((sectionCommaBarCoefficients (𝟭 D) V).obj K) n
        (c ⋙ sectionCommaBarProjection f V) x
  sectionFormula : ∀ (K : Dᵒᵖ ⥤ ModuleCat.{u} R) (n : ℕ)
    (c : ComposableArrows (StructuredArrow V (𝟭 D)) n) (x : K.obj (op c.right.right)),
    ((sectionMap.app K).f (-(n : ℤ)))
      ((B.models (StructuredArrow V (𝟭 D)) R).generator
        ((sectionCommaBarCoefficients (𝟭 D) V).obj K) n c x) =
      (B.models (StructuredArrow V f) R).generator
        ((sectionCommaBarCoefficients f V).obj K) n (c ⋙ sectionCommaBarSection f s ε V)
        (K.map (ε.hom.app c.right.right).op x)
  augmentationI : sectionCommaBarComplex (R := R) B f V ⟶ sectionCommaBarPoint V
  augmentationJ : sectionCommaBarComplex (R := R) B (𝟭 D) V ⟶ sectionCommaBarPoint V
  augmentationIFormula : ∀ (K : Dᵒᵖ ⥤ ModuleCat.{u} R)
    (c : ComposableArrows (StructuredArrow V f) 0) (x : K.obj (op (f.obj c.right.right))),
    ((augmentationI.app K).f 0 ≫
      (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 (K.obj (op V)) 0 rfl).hom)
        ((B.models (StructuredArrow V f) R).generator
          ((sectionCommaBarCoefficients f V).obj K) 0 c x) = K.map c.right.hom.op x
  augmentationJFormula : ∀ (K : Dᵒᵖ ⥤ ModuleCat.{u} R)
    (c : ComposableArrows (StructuredArrow V (𝟭 D)) 0) (x : K.obj (op c.right.right)),
    ((augmentationJ.app K).f 0 ≫
      (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 (K.obj (op V)) 0 rfl).hom)
        ((B.models (StructuredArrow V (𝟭 D)) R).generator
          ((sectionCommaBarCoefficients (𝟭 D) V).obj K) 0 c x) = K.map c.right.hom.op x
  preservesProjection : projection ≫ augmentationJ = augmentationI
  preservesSection : sectionMap ≫ augmentationI = augmentationJ
  inclusionI : sectionCommaBarPoint (R := R) V ⟶ sectionCommaBarComplex B f V
  inclusionJ : sectionCommaBarPoint (R := R) V ⟶ sectionCommaBarComplex B (𝟭 D) V
  inclusionIFormula : ∀ (K : Dᵒᵖ ⥤ ModuleCat.{u} R),
    (inclusionI.app K).f 0 =
      (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 (K.obj (op V)) 0 rfl).hom ≫
      K.map (ε.hom.app V).op ≫ (B.models (StructuredArrow V f) R).generator
        ((sectionCommaBarCoefficients f V).obj K) 0
        (ComposableArrows.mk₀ (StructuredArrow.mk (ε.inv.app V)))
  inclusionJFormula : ∀ (K : Dᵒᵖ ⥤ ModuleCat.{u} R),
    (inclusionJ.app K).f 0 =
      (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 (K.obj (op V)) 0 rfl).hom ≫
      (B.models (StructuredArrow V (𝟭 D)) R).generator
        ((sectionCommaBarCoefficients (𝟭 D) V).obj K) 0
        (ComposableArrows.mk₀ (StructuredArrow.mk (𝟙 V)))
  inclusionIZero : ∀ (K : Dᵒᵖ ⥤ ModuleCat.{u} R) (r : ℤ), r ≠ 0 →
    (inclusionI.app K).f r = 0
  inclusionJZero : ∀ (K : Dᵒᵖ ⥤ ModuleCat.{u} R) (r : ℤ), r ≠ 0 →
    (inclusionJ.app K).f r = 0
  inverseI : inclusionI ≫ augmentationI = 𝟙 _
  inverseJ : inclusionJ ≫ augmentationJ = 𝟙 _
  contractionI : ∀ K : Dᵒᵖ ⥤ ModuleCat.{u} R,
    Homotopy (augmentationI.app K ≫ inclusionI.app K) (𝟙 _)
  contractionJ : ∀ K : Dᵒᵖ ⥤ ModuleCat.{u} R,
    Homotopy (augmentationJ.app K ≫ inclusionJ.app K) (𝟙 _)
  contractionINatural : ∀ {K L : Dᵒᵖ ⥤ ModuleCat.{u} R} (θ : K ⟶ L) (i j : ℤ),
    ((sectionCommaBarComplex B f V).map θ).f i ≫ (contractionI L).hom i j =
      (contractionI K).hom i j ≫ ((sectionCommaBarComplex B f V).map θ).f j
  contractionJNatural : ∀ {K L : Dᵒᵖ ⥤ ModuleCat.{u} R} (θ : K ⟶ L) (i j : ℤ),
    ((sectionCommaBarComplex B (𝟭 D) V).map θ).f i ≫ (contractionJ L).hom i j =
      (contractionJ K).hom i j ≫ ((sectionCommaBarComplex B (𝟭 D) V).map θ).f j
  strictProjectionSection : ∀ (h : s ⋙ f = 𝟭 D), ε = eqToIso h →
    sectionMap ≫ projection = 𝟙 _
  strictSectionProjection : ∀ (h : s ⋙ f = 𝟭 D), ε = eqToIso h →
    ∀ K : Dᵒᵖ ⥤ ModuleCat.{u} R, Homotopy (projection.app K ≫ sectionMap.app K) (𝟙 _)
  strictSectionProjectionNatural : ∀ (h : s ⋙ f = 𝟭 D) (he : ε = eqToIso h)
    {K L : Dᵒᵖ ⥤ ModuleCat.{u} R} (θ : K ⟶ L) (i j : ℤ),
    ((sectionCommaBarComplex B f V).map θ).f i ≫
        (strictSectionProjection h he L).hom i j =
      (strictSectionProjection h he K).hom i j ≫
        ((sectionCommaBarComplex B f V).map θ).f j

/-- Vertical sections contract the specified augmented comma bar complexes, including
coherent identifications and the strict retraction identities.
Source: Stacks Project, cotangent.tex, Tag 08QW, cases 1 and 2; sites-cohomology.tex,
Tags 08PG, 08PH and lemma-initial-final; explicit section refinement
(blueprint: lem-trf-section-comma-bar-contraction).

Proof:
1. The comma equation and functoriality give K(a) K(u(h)) = K(a'), so the
   stated degree-zero formulas kill the bar differential and define augmentations.
   Small comma categories have small sets of chains and hence the required sums.
2. In the strict case the functors p and s_V have p s_V = 1. Reindexing and
   composition in lem-trf-derived-colimit-bar give P B = 1. The components η_U
   define 1 ⇒ s_V p and their coefficient restrictions are identities; the same
   dependency's natural-transformation homotopy gives B P homotopic to 1.
   The generator formulas prove both augmentation-preservation equations.
3. The object (V,1) is initial in (V ↓ D). Insert it at the beginning of every
   chain. The first face of this insertion is the identity; all later faces
   cancel against insertion after deletion, including the coefficient face.
   In degree zero the remaining term is i A_J. Thus i A_J is homotopic to 1,
   while A_J i = 1, with the stated inclusion and zero other components.
4. Put b = B i. Then A_I b = 1 and b A_I is homotopic to B P and hence to 1.
   Its degree-zero component is the specified inclusion at (sV,1).
5. For ε : us ≅ 1 use a ≫ ε_W⁻¹ and coefficient K(ε_W). Naturality of ε
   verifies the comma section. The transformation p s_V ⇒ 1 has component ε_W;
   the transformation 1 ⇒ s_V p has component η_U, whose comma equation follows
   from u(η_U) ≫ ε_uU = 1. The bar homotopy of lem-trf-derived-colimit-bar
   applies: its coefficient composite is K(u(η_U)) K(ε_uU) = 1.
6. The coefficient identity K(a ≫ ε_W⁻¹) K(ε_W) = K(a) proves augmentation
   preservation and the formula for b. Whisker and compose the preceding homotopies
   to contract A_I. Every coefficient map commutes with θ : K ⇒ L by naturality.
   Initial-object insertion leaves coefficients unchanged, and each prism summand
   inserts η or ε and applies its specified coefficient map. Hence the homotopies,
   too, commute with θ, as the coefficient-prism proof dependency explains. -/
theorem sectionCommaBarContraction_exists (B : CategoryColimitBarSystem.{u})
    (f : E ⥤ D) (s : D ⥤ E) (ε : s ⋙ f ≅ 𝟭 D) (η : 𝟭 E ⟶ f ⋙ s)
    (vertical : ∀ U : E, f.map (η.app U) ≫ ε.hom.app (f.obj U) = 𝟙 (f.obj U))
    (R : Type u) [CommRing R] (V : D) :
    Nonempty (SectionCommaBarContraction B f s ε R V) := by
  sorry

end CategoryTheory
