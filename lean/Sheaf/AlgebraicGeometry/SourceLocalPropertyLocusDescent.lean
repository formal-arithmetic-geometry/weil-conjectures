/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus

/-! # Descent of canonical source-open property loci

Source: Stacks Project, stacks-properties.tex, Tag 06M3, lemma-local-source,
(A),(B), with Q locally of finite type and R all morphisms, and scheme refinements
of the algebraic-space target charts
(blueprint: lem-sfb-source-local-property-locus-descent).

The helper predicates spell out representation transport of P, its scheme-test
extension, largestness, and the actual projections of a space-valued 2-base change.
They make no choices of atlases, opens, maps, or presentations.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃ z

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory.Limits

namespace CategoryTheory

/-- Apply an isomorphism-invariant algebraic-space property to a map of presheaves
presented by algebraic spaces. The equality pins down the presented arrow.
This permits literal open subfunctors without choosing algebraicity proofs for them.
Source: Stacks, Tag 06M3, property and open-subspace conventions
(blueprint: lem-sfb-source-local-property-locus-descent). -/
def SpaceMapProperty {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    {E F : (Over S)ᵒᵖ ⥤ Type u} (f : E ⟶ F) : Prop :=
  ∃ (X Y : AlgebraicSpace S) (e : X.obj.obj ≅ E) (d : Y.obj.obj ≅ F)
      (a : X ⟶ Y),
    e.hom ≫ f = a.hom.hom ≫ d.hom ∧ P a

/-- The scheme-base-change extension of an algebraic-space morphism property.
Each presentation is compatible with the actual projection to the test scheme.
Source: Stacks, Tag 06M3 and lemma-check-property-covering
(blueprint: lem-sfb-source-local-property-locus-descent). -/
def ModuliSpaceMapProperty {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) : Prop :=
  ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) G),
    ∃ (X : AlgebraicSpace S) (a : X.obj.obj ⟶ yoneda.obj T),
      HasSpaceBaseChange f T t X a ∧ SpaceMapProperty P a

/-- Largestness among source opens with the scheme-test extension of P.
Source: Stacks, Tag 06M3(A)
(blueprint: lem-sfb-source-local-property-locus-descent). -/
def IsLargestSpaceSourceOpen {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) (A : AlgebraicSpace S)
    {Y : BasedCategory.{v₁, w₁} (Over S)}
    (f : BasedFunctor (discreteModuli A.obj.obj) Y) (W : OpenSubspace A) : Prop :=
  ModuliSpaceMapProperty P ((discreteModuliMap W.val.ι).comp f) ∧
    ∀ J : OpenSubspace A,
      ModuliSpaceMapProperty P ((discreteModuliMap J.val.ι).comp f) → J ≤ W

/-- A space presentation of the 2-base change, retaining BOTH projections.
The first projection goes to the new target; the second goes to the old source.
Source: Stacks, Tag 06M3(B), and Tag 003R
(blueprint: lem-sfb-source-local-property-locus-descent). -/
def HasSpaceSourceBaseChange {S : Scheme.{u}} {A : AlgebraicSpace S}
    {Y : BasedCategory.{v₁, w₁} (Over S)} {Z : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor (discreteModuli A.obj.obj) Y) (b : BasedFunctor Z Y)
    (B : AlgebraicSpace S) (p : B.obj.obj ⟶ A.obj.obj)
    (q : BasedFunctor (discreteModuli B.obj.obj) Z) : Prop :=
  ∃ e : BasedFunctor (discreteModuli B.obj.obj) (moduliTwoFiberProduct b f),
    e.toFunctor.IsEquivalence ∧
      Nonempty (ModuliTwoIso (e.comp (moduliTwoFiberFst b f)) q) ∧
      Nonempty (ModuliTwoIso (e.comp (moduliTwoFiberSnd b f)) (discreteModuliMap p))

/-- The base change is a space and its largest source open is the literal inverse
image of the old one, for the specified 2-pullback projection.
Source: Stacks, Tag 06M3(B)
(blueprint: lem-sfb-source-local-property-locus-descent). -/
def HasCompatibleLargestSourceOpen {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {A : AlgebraicSpace S}
    {Y : BasedCategory.{v₁, w₁} (Over S)} {Z : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor (discreteModuli A.obj.obj) Y) (W : OpenSubspace A)
    (b : BasedFunctor Z Y) : Prop :=
  ∃ (B : AlgebraicSpace S) (p : B.obj.obj ⟶ A.obj.obj)
      (q : BasedFunctor (discreteModuli B.obj.obj) Z),
    HasSpaceSourceBaseChange f b B p q ∧
      ∃ Wb : OpenSubspace B,
        Wb.val = W.val.preimage p ∧ IsLargestSpaceSourceOpen P B q Wb

/-- Canonical largest opens known on scheme targets descend to algebraic-stack targets,
compatibly with every representable base change, including every scheme target map.
Source: Stacks Project, stacks-properties.tex, Tag 06M3, lemma-local-source, (A),(B),
with Q locally of finite type and R all morphisms, using scheme refinements on overlaps
(blueprint: lem-sfb-source-local-property-locus-descent).

Proof, following the six DAG steps:
1. Choose a smooth surjective scheme atlas V of Y. The diagonal criterion
   (lem-sfb-stack-diagonal-space-source-representability) makes f representable.
   Put U = A ×_Y V, B = V ×_Y V and R = U ×_A U. The representable-pullback-over-space
   lemma and lem-sfb-stack-chartwise-smooth-etale-calculus make these spaces and give
   smooth surjective projections and a locally finite type map g : U → V.
   The explicit 2-pullback triples identify R with A ×_Y B: compose one comparison
   isomorphism with the inverse of the other; insertion reverses this on objects
   and arrows. Take O = W_g by the scheme-target hypothesis.
2. Choose a surjective etale scheme atlas D → B. The two scheme maps D → V identify
   both inverse images of O with the canonical open for A ×_Y D → D. Thus they agree
   on R after a surjective etale cover, hence agree on R: open subfunctor membership
   is etale local by def-trf-algebraic-space and def-a1-space-open-subspace.
   No hypothesis on loci over the nonscheme target B was used.
3. Refine U by an etale scheme atlas H. Then H → A is smooth surjective and the
   inverse image O_H is invariant on H ×_A H. Apply
   lem-sfb-invariant-open-substack-descent to obtain W. It is a space by
   lem-sfb-representable-pullback-over-space, since its open inclusion is
   representable by schemes. Its pullback to U is O by etale detection on H.
4. For any scheme T → Y, the space C = T ×_Y V is smooth surjective over T, hence
   flat and locally finitely presented by the chartwise calculus. The pullback of
   W_T → T to C is O ×_V C → C. Base-change stability and fppf target locality
   give P for W_T → T. Thus W → Y has extended P. Every other such open J pulls
   back inside O by scheme-target largestness; invariant-open descent's
   factorization criterion gives J ⊆ W.
5. For any scheme T → Y choose an etale scheme atlas D of C = T ×_Y V. The two
   scheme maps D → V and D → T identify both candidate opens in A ×_Y D with
   the same canonical scheme-target locus. Refining its smooth surjective map
   to A ×_Y T by an etale scheme atlas, injectivity of invariant-open descent
   gives W ×_Y T = W_{f_T}. The map T → Y need not be flat.
6. For a representable b : Z → Y, its pullback over A is a space by
   lem-sfb-representable-pullback-over-space. Apply steps 1--4 to its locally
   finite type projection. A smooth scheme atlas T → Z identifies the inverse
   images of its largest open and W ×_Y Z by step 5. Refine to a smooth scheme
   atlas of the source and use invariant-open descent's injectivity to obtain
   equality. Scheme maps are representable by the diagonal criterion, giving
   the particular scheme clause. Covers may be arbitrary; no quasi-compactness
   or Noetherian assumption is introduced. -/
theorem source_local_property_locus_descent {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    (hiso : ∀ {X Y X' Y' : AlgebraicSpace S} (f : X ⟶ Y) (f' : X' ⟶ Y')
      (eX : X ≅ X') (eY : Y ≅ Y'),
      f ≫ eY.hom = eX.hom ≫ f' → (P f ↔ P f'))
    (hbase : ∀ {X Y X' Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y)
      (p : X' ⟶ X) (q : X' ⟶ Y'),
      IsPullback p.hom.hom q.hom.hom f.hom.hom g.hom.hom → P f → P q)
    (htarget : ∀ {X Y X' Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y)
      (p : X' ⟶ X) (q : X' ⟶ Y'),
      IsPullback p.hom.hom q.hom.hom f.hom.hom g.hom.hom →
      MapIsFlat g → MapIsLocallyOfFinitePresentation g →
      IsJointlySurjective (fun _ : Unit ↦ g.hom.hom) → (P f ↔ P q))
    (hsource_preserve : ∀ {X Y X' : AlgebraicSpace S} (f : X ⟶ Y) (e : X' ⟶ X),
      MapIsLocally (@Etale) e → P f → P (e ≫ f))
    (hsource_detect : ∀ {I : Type (max u z)} {X Y : AlgebraicSpace S}
      (f : X ⟶ Y) (Xi : I → AlgebraicSpace S) (e : ∀ i : I, Xi i ⟶ X),
      (∀ i : I, MapIsLocally (@Etale) (e i)) →
      IsJointlySurjective (fun i : I ↦ (e i).hom.hom) →
      (∀ i : I, P (e i ≫ f)) → P f)
    (hscheme : ∀ (E : AlgebraicSpace S) (T : Over S) (g : E.obj.obj ⟶ yoneda.obj T),
      MapToSchemeIsLocally (@LocallyOfFiniteType) E T g →
      ∃ W : OpenSubspace E,
        IsGreatest {J : OpenSubspace E | SpaceMapProperty P (J.val.ι ≫ g)} W ∧
        ∀ (T' : Over S) (b : T' ⟶ T) (E' : AlgebraicSpace S)
          (p : E'.obj.obj ⟶ E.obj.obj) (g' : E'.obj.obj ⟶ yoneda.obj T'),
          IsPullback p g' g (yoneda.map b) →
          ∃ W' : OpenSubspace E', W'.val = W.val.preimage p ∧
            IsGreatest {J : OpenSubspace E' | SpaceMapProperty P (J.val.ι ≫ g')} W')
    (A : AlgebraicSpace S) (Y : BasedCategory.{v₁, w₁} (Over S))
    (hY : IsAlgebraicModuliStack Y) (f : BasedFunctor (discreteModuli A.obj.obj) Y)
    (hf : ModuliSpaceTest (@LocallyOfFiniteType) f) :
    ∃ W : OpenSubspace A, IsLargestSpaceSourceOpen P A f W ∧
      (∀ (Z : BasedCategory.{v₂, w₂} (Over S)) (hZ : IsAlgebraicModuliStack Z)
        (b : BasedFunctor Z Y), IsRepresentableByAlgebraicSpaces b →
        HasCompatibleLargestSourceOpen P f W b) ∧
      (∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) Y),
        HasCompatibleLargestSourceOpen P f W t) := by
  sorry

end CategoryTheory
