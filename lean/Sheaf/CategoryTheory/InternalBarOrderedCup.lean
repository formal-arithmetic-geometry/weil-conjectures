/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Sheaf.CategoryTheory.CondensedDerivedInvariantBar
public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift

/-! # Ordered character cups in the internal derived bar

Source: main-20261015 blueprint, six-functors direct-images proof, paragraph (3),
agent-formulated internal bar-diagonal obligation; exact reference wanted
(blueprint: lem-sfb-internal-bar-ordered-cup).
The chain maps are specified on all generalized sections. The augmentation is the
actual resolution-normalized arrow, using the small-Hom localization of the cup calculus.
No underived bar term is assumed acyclic.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.CondensedBar CategoryTheory.CondensedDerivedRestriction
namespace CategoryTheory.CondensedBar.OrderedCup

/-- The regular coefficient in the cup calculus's ordinary derived category.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def regularZero (A : CondensedBar.Ring.{u}) :=
  (DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X)

/-- The source A[-q].
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def degreeSource (A : CondensedBar.Ring.{u}) (q : ℕ) :=
  (regularZero A)⟦(-(q : ℤ))⟧

/-- Multiplication of an object identified with the tensor unit, abstractly.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def unitMultiply {C : Type v} [Category.{w} C] [MonoidalCategory C]
    {U : C} (e : 𝟙_ C ≅ U) : U ⊗ U ≅ U :=
  tensorIso e.symm (Iso.refl _) ≪≫ λ_ U

/-- Assemble the ordered source convention without unfolding the condensed tensor.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def assembleSource {C : Type v} [Category.{w} C] [MonoidalCategory C]
    (D : ℕ → C) (e : D 0 ≅ 𝟙_ C) (s : ∀ q : ℕ, D (q + 1) ≅ D 1 ⊗ D q) :
    ∀ q : ℕ, D q ≅ tensorPower (D 1) q
  | 0 => e
  | q + 1 => s q ≪≫ tensorIso (Iso.refl _) (assembleSource D e s q)

/-- Assemble the fixed convention in an abstract monoidal category with shifts.
The supplied two-variable comparison is used without permutations; in length zero
use the unit and the zero-shift isomorphism.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def assembleShiftedSource {D : Type v} [Category.{w} D] [MonoidalCategory D]
    [HasShift D ℤ] (U : D) (e : 𝟙_ D ≅ U)
    (s : ∀ a b : ℤ, U⟦a⟧ ⊗ U⟦b⟧ ≅ (U ⊗ U)⟦a + b⟧) (q : ℕ) :
    U⟦-(q : ℤ)⟧ ≅ tensorPower (U⟦(-1 : ℤ)⟧) q :=
  assembleSource (fun n : ℕ ↦ U⟦-(n : ℤ)⟧)
    ((shiftFunctorZero' D (0 : ℤ) rfl).app U ≪≫ e.symm)
    (fun n ↦
      (eqToIso (congrArg (fun k : ℤ ↦ U⟦k⟧) (by omega)) :
        U⟦-((n + 1 : ℕ) : ℤ)⟧ ≅ U⟦(-1 : ℤ) + -(n : ℤ)⟧) ≪≫
      ((shiftFunctor D ((-1 : ℤ) + -(n : ℤ))).mapIso (unitMultiply e)).symm ≪≫
      (s (-1 : ℤ) (-(n : ℤ))).symm) q

/-- The fixed right-associated shift convention, including the empty tensor unit.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def sourceTensor (A : CondensedBar.Ring.{u}) (q : ℕ) :
    degreeSource A q ≅ tensorPower (degreeSource A 1) q :=
  assembleShiftedSource (regularZero A) (baseUnitIso A)
    (DerivedCategory.shiftTensorShiftIso (Modules A) (regularZero A) (regularZero A)) q

/-- Tensor a list of arrows in order, without unfolding the concrete tensor construction.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def tensorList {C : Type v} [Category.{w} C] [MonoidalCategory C] {X Y : C} :
    ∀ (q : ℕ) (_f : Fin q → (X ⟶ Y)), tensorPower X q ⟶ tensorPower Y q
  | 0, _ => 𝟙 _
  | q + 1, f => f 0 ⊗ₘ tensorList q (fun i ↦ f i.succ)

variable {A : CondensedBar.Ring.{u}} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The actual unital ordered derived cup with the fixed shift convention.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def characterCup (q : ℕ) (a : Fin q → Character A G) :
    degreeSource A q ⟶ cohomology A G :=
  (sourceTensor A q).hom ≫ tensorList q (fun k ↦ characterClass (a k)) ≫
    orderedProduct (cupUnit (A := A) (G := G)) (cup (A := A) (G := G)) q

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The underived inhomogeneous bar for the trivial regular coefficient.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
abbrev underived {F : InternalFunctions A} (B : BarDiagram (G := G) F) :=
  (cochains B).obj (regularTrivial A G)

/-- The compatible nonnegative derived total on an equivariant injective resolution.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
abbrev resolved {F : InternalFunctions A} (B : BarDiagram (G := G) F)
    (I : InjectiveResolution (regularTrivial A G)) :=
  (totalCochains B).obj I.cocomplex

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The resolution-normalized augmentation in the cup calculus's small-Hom localization.
This maps the resolution augmentation, inverts the computation unit on injectives,
and applies the total augmentation, exactly as `Computation.normalization`.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def augmentationArrow {F : InternalFunctions A} {B : BarDiagram (G := G) F}
    {a : Augmentation (invariants A G) B}
    (t : TotalAugmentation (invariants A G) B a)
    (I : InjectiveResolution (regularTrivial A G)) :
    cohomology A G ⟶ DerivedCategory.Q.obj (extend (resolved B I)) := by
  letI : QuasiIso I.ι' := inferInstance
  letI : I.cochainComplex.IsKInjective := by
    dsimp only [InjectiveResolution.cochainComplex]
    infer_instance
  exact (derived A G).map (DerivedCategory.Q.map I.ι') ≫
    ((invariants A G).functor.rightDerivedFunctorObjQIso I.cochainComplex).hom ≫
    DerivedCategory.Q.map
      (HomologicalComplex.mapExtendIso I.cocomplex ComplexShape.embeddingUpNat
        (invariants A G).functor).hom ≫
    DerivedCategory.Q.map (HomologicalComplex.extendMap (t.map.app I.cocomplex)
      ComplexShape.embeddingUpNat)

/-- The canonical total comparison is fixed by the resolution map into bidegree (n,0).
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def IsUnderivedComparison {F : InternalFunctions A} (B : BarDiagram (G := G) F)
    (I : InjectiveResolution (regularTrivial A G))
    (j : underived B ⟶ resolved B I) : Prop :=
  ∀ n : ℕ, j.f n = (B.diagram.map (I.ι.f 0)).app (SimplexCategory.mk n) ≫
    (doubleComplex B I.cocomplex).ιTotal (.up ℕ) n 0 n (by simp)

/-- The cocycle formula on every generalized section. Linearity and evaluation at the
regular unit determine the whole internal map, with empty product 1 for q=0.
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def IsCharacterCocycle {F : InternalFunctions A} (B : BarDiagram (G := G) F)
    (q : ℕ) (a : Fin q → Character A G)
    (c : (HomologicalComplex.single (Modules A) (.up ℤ) (q : ℤ)).obj
      (Mod.regular A.X) ⟶ extend (underived B)) : Prop :=
  ∀ (S T : Profinite.{u}) (f : T ⟶ S) (g : Fin q → C(T, G)),
    (F.evaluate (power G q) S (Mod.regular A.X)
      (((HomologicalComplex.singleObjXSelf (.up ℤ) (q : ℤ) (Mod.regular A.X)).inv ≫
        c.f (q : ℤ) ≫ ((underived B).extendXIso ComplexShape.embeddingUpNat rfl).hom ≫
        (B.term (regularTrivial A G) q).hom).hom.hom.app (op S)
          (1 : sectionRing A S))).val T f (tupleMap g) =
      ∏ k : Fin q, (a k).app T (g k)

/-- The actual localized cocycle followed by the actual total comparison, with source A[-q].
Source: paragraph (3) (blueprint: lem-sfb-internal-bar-ordered-cup). -/
def cocycleArrow {F : InternalFunctions A} {B : BarDiagram (G := G) F}
    {I : InjectiveResolution (regularTrivial A G)}
    (j : underived B ⟶ resolved B I) (q : ℕ)
    (c : (HomologicalComplex.single (Modules A) (.up ℤ) (q : ℤ)).obj
      (Mod.regular A.X) ⟶ extend (underived B)) :
    degreeSource A q ⟶ DerivedCategory.Q.obj (extend (resolved B I)) :=
  ((DerivedCategory.singleFunctors (Modules A)).shiftIso (-(q : ℤ)) (q : ℤ) 0
    (by omega)).hom.app (Mod.regular A.X) ≫
      DerivedCategory.Q.map c ≫
      DerivedCategory.Q.map (HomologicalComplex.extendMap j ComplexShape.embeddingUpNat)

/-- Ordered character cocycles equal the specified derived cups up to a universal sign.
The sign is quantified before the ring, group, compatible model, resolution and characters.
Source: main-20261015 direct-images proof, paragraph (3), agent-formulated internal bar
obligation; exact reference wanted (blueprint: lem-sfb-internal-bar-ordered-cup).

Proof:
1. lem-sfb-condensed-internal-bar-resolution supplies the exact homogeneous resolution P,
   its free-module property and its inhomogeneous coordinate change.
2. For a character a put b(g,h)=a(g⁻¹h). Define L_a by deleting g_0 and multiplying
   by b(g_0,g_1). In dL+Ld the deletion terms with index at least two cancel; the
   remainder is b(g_0,g_1)+b(g_1,g_2)-b(g_0,g_2)=0. Thus P → P[1] is a chain map.
3. Compose the shifted L operators in the supplied order. Augmentation gives coefficient
   product_k a_k(g_{k-1}⁻¹g_k), whose coordinate change is precisely the displayed z.
   Its chain-map law proves cocyclicity. For q=0 use the augmentation and empty product.
4. In the character extension lift the quotient unit by [g] ↦ (a(g),1). Its boundary
   is (b(g,h),0). lem-sfb-internal-bar-roof-adjunction identifies this roof with the
   positive connecting class of lem-sfb-condensed-derived-restriction-calculus.
5. lem-sfb-internal-inflation-graded-cup identifies repeated ordered cup with shifted
   roof composition up to universal signs T_q with T_0=T_1=1. The intervening shifted
   inverse augmentations cancel, leaving the composite in step 3.
6. lem-sfb-internal-bar-roof-adjunction sends that roof to jz with universal sign s_q.
   Consequently epsilon_q=s_q T_q, independent of every input and equal to 1 at q=0,1.
   lem-sfb-condensed-derived-invariant-bar fixes the augmentation used here; its
   formula is the same in the equivalent small-Hom localization. No inverse of j or
   acyclicity of any underived internal-Hom term is used.
-/
theorem internal_bar_ordered_cup :
    ∃ ε : ℕ → ℤ, (∀ q : ℕ, ε q = 1 ∨ ε q = -1) ∧ ε 0 = 1 ∧ ε 1 = 1 ∧
    ∀ (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
      [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      (F : InternalFunctions A) (B : BarDiagram (G := G) F)
      (a : Augmentation (invariants A G) B)
      (t : TotalAugmentation (invariants A G) B a)
      (I : InjectiveResolution (regularTrivial A G)),
      IsIso (augmentationArrow t I) ∧
      ∃ j : underived B ⟶ resolved B I, IsUnderivedComparison B I j ∧
        ∀ (q : ℕ) (a : Fin q → Character A G),
          ∃ c : (HomologicalComplex.single (Modules A) (.up ℤ) (q : ℤ)).obj
              (Mod.regular A.X) ⟶ extend (underived B),
            IsCharacterCocycle B q a c ∧
            cocycleArrow j q c = (ε q) • (characterCup q a ≫ augmentationArrow t I) := by
  sorry

end CategoryTheory.CondensedBar.OrderedCup
