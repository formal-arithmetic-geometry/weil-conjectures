/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SecSmoothPurity.NormalizedCoefficientDiagram
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.BifunctorShift

import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-! # Units and successive composition of strict coefficient comparisons

Source: Stacks, sites-modules.tex, Section 03EK and Tag 03EL; the seven agent
calculations in the DAG (blueprint: lem-pur-coefficient-comparisons-unit-composition).

Only the definition interface of StrictCoefficientComparisonCalculus is used.
Its downstream existence theorem is neither a hypothesis nor a proof input.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace CategoryTheory.CochainPullback.StrictCoefficient

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The multiplication and insertion formulas for the already constructed unit.
Source: Stacks 03EK, agent proof step 2
(blueprint: lem-pur-coefficient-comparisons-unit-composition). -/
def UnitMultiplication (B : Index ⥤ Sheaf J CommRingCat.{w}) : Prop :=
  ∀ (i : Index) (P : Complex (B.obj i)) (p : ℤ) (U : Cᵒᵖ)
    (c : (B.obj i).obj.obj U) (x : (P.X p).val.obj U),
    ((((diagramUnit B i).app P).hom.f p).val.app U
        (extensionTmul (B.map (𝟙 i)) (P.X p) U c x) = c • x) ∧
    ((((diagramUnit B i).app P).inv.f p).val.app U x =
      extensionTmul (B.map (𝟙 i)) (P.X p) U 1 x)

/-- Multiplication of the two scalar factors, and insertion of one for the inverse.
Source: Stacks 03EK, agent proof step 2
(blueprint: lem-pur-coefficient-comparisons-unit-composition). -/
def CompositionMultiplication (B : Index ⥤ Sheaf J CommRingCat.{w}) : Prop :=
  ∀ {i j k : Index} (a : i ⟶ j) (b : j ⟶ k) (P : Complex (B.obj i))
    (p : ℤ) (U : Cᵒᵖ) (c : (B.obj k).obj.obj U) (d : (B.obj j).obj.obj U)
    (x : (P.X p).val.obj U),
    ((((diagramComp B a b).app P).hom.f p).val.app U
        (extensionTmul (B.map b) ((extensionFunctor (B.map a)).obj (P.X p)) U c
          (extensionTmul (B.map a) (P.X p) U d x)) =
      extensionTmul (B.map (a ≫ b)) (P.X p) U (c * (B.map b).hom.app U d) x) ∧
    ((((diagramComp B a b).app P).inv.f p).val.app U
        (extensionTmul (B.map (a ≫ b)) (P.X p) U c x) =
      extensionTmul (B.map b) ((extensionFunctor (B.map a)).obj (P.X p)) U c
        (extensionTmul (B.map a) (P.X p) U 1 x))

/-- The scalar action unit and its inverse commute with every semilinear transition.
The map f is arbitrary, in particular it can be zero.
Source: Stacks 03EK, agent proof step 3
(blueprint: lem-pur-coefficient-comparisons-unit-composition). -/
def UnitStrictness (B : Index ⥤ Sheaf J CommRingCat.{w}) : Prop :=
  ∀ {i j : Index} (r : i ⟶ j) (P : Complex (B.obj i)) (Q : Complex (B.obj j))
    (f : (extend (B.map r)).obj P ⟶ Q),
    ((extend (B.map r)).map ((diagramUnit B i).app P).hom ≫ f =
      squareArrow B (𝟙 i) (𝟙 j) r r (CategoryTheory.Prod.hom_ext
        (Subsingleton.elim _ _) (Subsingleton.elim _ _)) P Q f ≫
        ((diagramUnit B j).app Q).hom) ∧
    ((extend (B.map r)).map ((diagramUnit B i).app P).inv ≫
        squareArrow B (𝟙 i) (𝟙 j) r r (CategoryTheory.Prod.hom_ext
        (Subsingleton.elim _ _) (Subsingleton.elim _ _)) P Q f =
      f ≫ ((diagramUnit B j).app Q).inv)

/-- Successive transport of an arbitrary semilinear map through two coefficient squares.
This is a composite of the recorded square transports, with no chosen transition.
Source: Stacks 03EK, agent proof step 3
(blueprint: lem-pur-coefficient-comparisons-unit-composition). -/
def twiceSquareArrow (B : Index ⥤ Sheaf J CommRingCat.{w})
    {i j k i' j' k' : Index} (a : i ⟶ j) (b : j ⟶ k)
    (a' : i' ⟶ j') (b' : j' ⟶ k') (r : i ⟶ i') (s : j ⟶ j') (t : k ⟶ k')
    (P : Complex (B.obj i)) (Q : Complex (B.obj i'))
    (f : (extend (B.map r)).obj P ⟶ Q) :
    (extend (B.map t)).obj ((extend (B.map b)).obj ((extend (B.map a)).obj P)) ⟶
      (extend (B.map b')).obj ((extend (B.map a')).obj Q) :=
  squareArrow B b b' s t (CategoryTheory.Prod.hom_ext
        (Subsingleton.elim _ _) (Subsingleton.elim _ _))
    ((extend (B.map a)).obj P) ((extend (B.map a')).obj Q)
    (squareArrow B a a' r s (CategoryTheory.Prod.hom_ext
        (Subsingleton.elim _ _) (Subsingleton.elim _ _)) P Q f)

/-- The multiplication associator and its inverse commute with all semilinear transitions.
All squares commute because the coefficient/sequence index is a thin category.
Source: Stacks 03EK, agent proof step 3
(blueprint: lem-pur-coefficient-comparisons-unit-composition). -/
def CompositionStrictness (B : Index ⥤ Sheaf J CommRingCat.{w}) : Prop :=
  ∀ {i j k i' j' k' : Index} (a : i ⟶ j) (b : j ⟶ k)
    (a' : i' ⟶ j') (b' : j' ⟶ k') (r : i ⟶ i') (s : j ⟶ j') (t : k ⟶ k')
    (P : Complex (B.obj i)) (Q : Complex (B.obj i'))
    (f : (extend (B.map r)).obj P ⟶ Q),
    ((extend (B.map t)).map ((diagramComp B a b).app P).hom ≫
        squareArrow B (a ≫ b) (a' ≫ b') r t (CategoryTheory.Prod.hom_ext
        (Subsingleton.elim _ _) (Subsingleton.elim _ _)) P Q f =
      twiceSquareArrow B a b a' b' r s t P Q f ≫ ((diagramComp B a' b').app Q).hom) ∧
    ((extend (B.map t)).map ((diagramComp B a b).app P).inv ≫
        twiceSquareArrow B a b a' b' r s t P Q f =
      squareArrow B (a ≫ b) (a' ≫ b') r t (CategoryTheory.Prod.hom_ext
        (Subsingleton.elim _ _) (Subsingleton.elim _ _)) P Q f ≫
        ((diagramComp B a' b').app Q).inv)

/-- Unit and successive-composition laws, in the category of strict chain systems.
Source: Stacks 03EK and 03EL, and the seven agent calculations in the DAG
(blueprint: lem-pur-coefficient-comparisons-unit-composition).

Proof:
1. Use lem-pc-sites-sheaf-tensor-bilinear-universal, the quotient tensor in
   def-weil-pbc-module-tensor-product, and def-weil-presheaf-modules-sheafification.
   Extend inner pairings with lem-pc-sites-module-sheafification-bilinear-extension.
   Iteration proves that maps out of nested sheaf tensors agree if their values on
   generalized local tensors agree; no global lifting of inverse-image sections is used.
2. Multiplication ax and d i12(b) tensor x is balanced over each intermediate ring.
   Its inverse inserts one. Both composites reduce to balancing, proving the unit
   and associator formulas and natural isomorphisms. These are the existing
   adjoint-uniqueness maps diagramUnit and diagramComp.
3. In each degree these formulas commute with the differential and with arbitrary
   semilinear transitions: both paths multiply the transported coefficient by the
   transported section. The same calculation proves the inverse squares.
   The signed direct-sum total from def-pc-tensor-complex-sheaves is checked on
   coproduct summands. Use lem-pc-sheaf-modules-tensor-closed to test maps after
   one or two scalar extensions on those same summands, without boundedness.
4. On b tensor (a tensor x), k followed by the unit gives ba tensor x on either
   route. On b tensor (x tensor y), s followed by the two units gives b(x tensor y).
5. Both successive k routes on d tensor (b tensor (a tensor x)) give
   d i12(b) i02(a) tensor (1 tensor x), using the coefficient composition square.
6. Both successive s routes on d tensor (b tensor (x tensor y)) give
   (d i12(b) tensor x) tensor (1 tensor y). There is no permutation or extra sign.
7. Generalized-tensor and coproduct uniqueness give equalities of strict chain
   isomorphisms. Equality of isomorphisms includes equality of their inverses;
   alternatively cancel the isomorphisms in the four equations in reverse order.
   No exactness, flatness, boundedness or invertibility of transitions is used.
-/
theorem coefficientComparisonsUnitComposition (d : Diagram (J := J) (K := K))
    (k : ∀ i : Index, Comparison (d.ringed i)) (e : Comparisons d)
    (_normalized : e.Normalized k)
    (_strict : e.KappaTransitionLaws ∧
      TensorTransitionLaws d.R e.sigmaR ∧ TensorTransitionLaws d.S e.sigmaS) :
    UnitMultiplication d.R ∧ UnitMultiplication d.S ∧
    CompositionMultiplication d.R ∧ CompositionMultiplication d.S ∧
    UnitStrictness d.R ∧ UnitStrictness d.S ∧
    CompositionStrictness d.R ∧ CompositionStrictness d.S ∧
    TensorLaws d.R e.sigmaR ∧ TensorLaws d.S e.sigmaS ∧
    (∀ (i : Index) (P : Complex (d.R.obj i)),
      e.kappaC (𝟙 i) P ≪≫
          (pull (d.ringed i)).mapIso ((diagramUnit d.R i).app P) =
        (diagramUnit d.S i).app ((pull (d.ringed i)).obj P)) ∧
    (∀ {i j l : Index} (a : i ⟶ j) (b : j ⟶ l) (P : Complex (d.R.obj i)),
      (extend (d.S.map b)).mapIso (e.kappaC a P) ≪≫
          e.kappaC b ((extend (d.R.map a)).obj P) ≪≫
          (pull (d.ringed l)).mapIso ((diagramComp d.R a b).app P) =
        (diagramComp d.S a b).app ((pull (d.ringed i)).obj P) ≪≫ e.kappaC (a ≫ b) P) := by
  sorry

end CategoryTheory.CochainPullback.StrictCoefficient
