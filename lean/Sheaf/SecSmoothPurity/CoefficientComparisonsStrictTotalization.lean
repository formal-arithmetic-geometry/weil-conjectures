/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SecSmoothPurity.NormalizedCoefficientDiagram
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.SecSmoothPurity.NormalizedKappaTransitions
public import Sheaf.SecSmoothPurity.NormalizedScalarTensorTransitions
public import Sheaf.SecSmoothPurity.PullTensorGeneratorSections
import all Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
import Sheaf.SecSmoothPurity.ModuleTensorCoefficientEquations
import all Sheaf.SecSmoothPurity.NormalizedKappaTransitions
import all Sheaf.SecSmoothPurity.NormalizedScalarTensorTransitions
import Sheaf.SecSmoothPurity.CoefficientTransitionSquares

/-! # Strict totalization of the normalized coefficient comparisons

Source: Stacks Project, Modules on Sites, Section 03EK and Tag 03EL, and
Cohomology on Sites, Tag 07A4; the eight calculations of
(blueprint: lem-pur-coefficient-comparisons-strict-totalization).

The existing coefficient-diagram definitions provide the comparison maps and
arbitrary semilinear chain arrows. No existence or coherence theorem from the
downstream strict coefficient calculus is used. Its third coefficient row is
irrelevant: any two-row diagram extends by repeating its last row.

## Main definitions

* `TotalDifferentials`, `KappaDifferentials`: the separate signed differential laws.
* `TotalSummands`, `TotalNaturality`: the full total maps and their naturality.
* `KappaTransitionValues`, `TensorTransitionValues`, `PullTensorTransitionValues`:
  the prescribed values for arbitrary semilinear transitions.
* `TensorSquare`, `TensorSquareValue`: the coefficient/tensor square and its value.

## Main statements

* `coefficientComparisonsStrictTotalization`: all the strict totalization laws.
-/

set_option Elab.async false
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] SheafOfModules.monoidalCategory
universe w uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open SheafOfModules
open scoped TensorProduct ChangeOfRings
namespace CategoryTheory.CochainPullback.StrictCoefficient

attribute [local irreducible] scalarComp scalarUnit extensionAdjunction generator
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal


variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The normalized comparison of signed tensor totals, with the inferred tensor
structures fixed once. Source: Stacks 03EL and 07A4
(blueprint: lem-pur-coefficient-comparisons-strict-totalization). -/
noncomputable abbrev tensorComparison {R : Sheaf J CommRingCat.{w}}
    {S : Sheaf K CommRingCat.{w}} (f : RingedPullback R S) (c : Comparison f)
    (P Q : Complex R) : (pull f).obj (total P Q) ≅
      total ((pull f).obj P) ((pull f).obj Q) := comparison f c P Q

/-- The existing map on tensor totals, with its monoidal instances shared.
Source: Stacks 07A4 (blueprint: lem-pur-coefficient-comparisons-strict-totalization). -/
noncomputable abbrev tensorTotalMap {R : Sheaf J CommRingCat.{w}}
    {P Q P' Q' : Complex R} (f : P ⟶ P') (g : Q ⟶ Q') :
    total P Q ⟶ total P' Q' := totalMap f g

/-- The existing isomorphism on tensor totals, with its monoidal instances shared.
Source: Stacks 07A4 (blueprint: lem-pur-coefficient-comparisons-strict-totalization). -/
noncomputable abbrev tensorTotalIso {R : Sheaf J CommRingCat.{w}}
    {P Q P' Q' : Complex R} (f : P ≅ P') (g : Q ≅ Q') :
    total P Q ≅ total P' Q' := totalIso f g

/-- First summand of the signed total differential. Source: Stacks 07A4
(blueprint: lem-pur-coefficient-comparisons-strict-totalization). -/
noncomputable def tensorD₁ {R : Sheaf J CommRingCat.{w}}
    (P Q : Complex R) (n m : ℤ) : (total P Q).X n ⟶ (total P Q).X m :=
  HomologicalComplex.mapBifunctor.D₁ P Q (curriedTensor (Modules R)) (.up ℤ) n m

/-- Second, signed summand of the total differential. Source: Stacks 07A4
(blueprint: lem-pur-coefficient-comparisons-strict-totalization). -/
noncomputable def tensorD₂ {R : Sheaf J CommRingCat.{w}}
    (P Q : Complex R) (n m : ℤ) : (total P Q).X n ⟶ (total P Q).X m :=
  HomologicalComplex.mapBifunctor.D₂ P Q (curriedTensor (Modules R)) (.up ℤ) n m

/-- Inclusion of a homogeneous tensor summand. Source: Stacks 07A4
(blueprint: lem-pur-coefficient-comparisons-strict-totalization). -/
noncomputable abbrev tensorι {R : Sheaf J CommRingCat.{w}}
    (P Q : Complex R) (p q n : ℤ) (h : p + q = n) :
    P.X p ⊗ Q.X q ⟶ (total P Q).X n :=
  ScalarCalculation.tensorι P Q p q n h

/-- Separate commutation with the two total differential summands, in both directions.
D₁ is d tensor 1; D₂ includes the sign (-1)^p, for every integer p.
Source: Stacks 07A4, agent proof steps 2 and 4
(blueprint: lem-pur-coefficient-comparisons-strict-totalization). -/
def TotalDifferentials {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}
    (f : RingedPullback R S) (c : Comparison f) : Prop :=
  ∀ (P Q : Complex R) (n n' : ℤ),
    (f.L.map (tensorD₁ P Q n n') ≫ (tensorComparison f c P Q).hom.f n' =
      (tensorComparison f c P Q).hom.f n ≫
        tensorD₁ ((pull f).obj P) ((pull f).obj Q) n n') ∧
    (f.L.map (tensorD₂ P Q n n') ≫ (tensorComparison f c P Q).hom.f n' =
      (tensorComparison f c P Q).hom.f n ≫
        tensorD₂ ((pull f).obj P) ((pull f).obj Q) n n') ∧
    (tensorD₁ ((pull f).obj P) ((pull f).obj Q) n n' ≫ (tensorComparison f c P Q).inv.f n' =
      (tensorComparison f c P Q).inv.f n ≫
        f.L.map (tensorD₁ P Q n n')) ∧
    (tensorD₂ ((pull f).obj P) ((pull f).obj Q) n n' ≫ (tensorComparison f c P Q).inv.f n' =
      (tensorComparison f c P Q).inv.f n ≫
        f.L.map (tensorD₂ P Q n n'))

/-- The k comparison commutes separately with either differential in a tensor total.
Source: Stacks 03EL and 07A4, agent proof step 3
(blueprint: lem-pur-coefficient-comparisons-strict-totalization). -/
def Comparisons.KappaDifferentials {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) : Prop :=
  ∀ {i j : Index} (a : i ⟶ j) (P Q : Complex (d.R.obj i)) (n n' : ℤ)
    (v : Fin 2),
    ((d.L i ⋙ extensionFunctor (d.S.map a)).map
        ((if v = 0 then tensorD₁ else
          tensorD₂) P Q n n') ≫ (e.kappaC a (total P Q)).hom.f n' =
      (e.kappaC a (total P Q)).hom.f n ≫
        (extensionFunctor (d.R.map a) ⋙ d.L j).map
          ((if v = 0 then tensorD₁ else
            tensorD₂) P Q n n')) ∧
    ((extensionFunctor (d.R.map a) ⋙ d.L j).map
        ((if v = 0 then tensorD₁ else
          tensorD₂) P Q n n') ≫ (e.kappaC a (total P Q)).inv.f n' =
      (e.kappaC a (total P Q)).inv.f n ≫
        (d.L i ⋙ extensionFunctor (d.S.map a)).map
          ((if v = 0 then tensorD₁ else
            tensorD₂) P Q n n'))

/-- Naturality of both directions of the total tensor comparisons.
Source: Stacks 03EL and 07A4, agent proof steps 3, 4 and 6
(blueprint: lem-pur-coefficient-comparisons-strict-totalization). -/
def TotalNaturality {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}
    (f : RingedPullback R S) (c : Comparison f) : Prop :=
  ∀ (P Q P' Q' : Complex R) (a : P ⟶ P') (b : Q ⟶ Q'),
    (pull f).map (tensorTotalMap a b) ≫ (tensorComparison f c P' Q').hom =
      (tensorComparison f c P Q).hom ≫ tensorTotalMap ((pull f).map a) ((pull f).map b) ∧
    tensorTotalMap ((pull f).map a) ((pull f).map b) ≫ (tensorComparison f c P' Q').inv =
      (tensorComparison f c P Q).inv ≫ (pull f).map (tensorTotalMap a b)

/-- The whole direct-sum total comparison restricts to its normalized module
comparison in each bidegree, in both directions. These are coproduct equations,
not a claim that every sheaf section is globally a sum of pure tensors.
Source: Stacks 03EL and 07A4, agent proof steps 1, 2 and 4
(blueprint: lem-pur-coefficient-comparisons-strict-totalization). -/
def TotalSummands {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}
    (f : RingedPullback R S) (c : Comparison f) : Prop :=
  ∀ (P Q : Complex R) (p q n : ℤ) (h : p + q = n),
    (f.L.map (tensorι P Q p q n h) ≫
        (tensorComparison f c P Q).hom.f n =
      (c.mu (P.X p) (Q.X q)).hom ≫
        tensorι ((pull f).obj P) ((pull f).obj Q) p q n h) ∧
    (tensorι ((pull f).obj P) ((pull f).obj Q) p q n h ≫ (tensorComparison f c P Q).inv.f n =
      (c.mu (P.X p) (Q.X q)).inv ≫
        f.L.map (tensorι P Q p q n h))

/-- The coefficient/tensor square as equality of chain isomorphisms, hence also
of their inverses. Every map acts on the full unbounded direct-sum total.
Source: Stacks 03EL and 07A4, agent proof steps 7 and 8
(blueprint: lem-pur-coefficient-comparisons-strict-totalization). -/
def Comparisons.TensorSquare {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) (c : ∀ i : Index, Comparison (d.ringed i)) : Prop :=
  ∀ {i j : Index} (a : i ⟶ j) (P Q : Complex (d.R.obj i)),
    e.kappaC a (total P Q) ≪≫
        (pull (d.ringed j)).mapIso (e.sigmaRC a P Q) ≪≫
        tensorComparison (d.ringed j) (c j)
          ((extend (d.R.map a)).obj P) ((extend (d.R.map a)).obj Q) =
      (extend (d.S.map a)).mapIso (tensorComparison (d.ringed i) (c i) P Q) ≪≫
        e.sigmaSC a ((pull (d.ringed i)).obj P) ((pull (d.ringed i)).obj Q) ≪≫
        tensorTotalIso (e.kappaC a P) (e.kappaC a Q)

/-- The normalized c comparisons commute with all arbitrary semilinear arrows.
The maps f and g are arbitrary scalar-extension adjoints, including zero maps.
The inverse equation follows by cancellation of the comparison isomorphisms.
Source: Stacks 03EL and 07A4, agent proof step 6
(blueprint: lem-pur-coefficient-comparisons-strict-totalization). -/
def Comparisons.PullTensorTransitions {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) (c : ∀ i : Index, Comparison (d.ringed i)) : Prop :=
  ∀ {i j : Index} (t : i ⟶ j)
    (P Q : Complex (d.R.obj i)) (P' Q' : Complex (d.R.obj j))
    (f : (extend (d.R.map t)).obj P ⟶ P')
    (g : (extend (d.R.map t)).obj Q ⟶ Q'),
    (extend (d.S.map t)).map (tensorComparison (d.ringed i) (c i) P Q).hom ≫
        (e.sigmaSC t ((pull (d.ringed i)).obj P) ((pull (d.ringed i)).obj Q)).hom ≫
        tensorTotalMap (e.pullArrow t P P' f) (e.pullArrow t Q Q' g) =
      e.pullArrow t (total P Q) (total P' Q') (e.tensorArrow t P Q P' Q' f g) ≫
        (tensorComparison (d.ringed j) (c j) P' Q').hom

/-- The section map of a semilinear chain arrow, obtained using the scalar unit.
Source: Stacks 03CY, agent proof steps 5 and 6
(blueprint: lem-pur-coefficient-comparisons-strict-totalization). -/
def semilinearSectionMap {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    {P : Complex A} {Q : Complex B} (f : (extend a).obj P ⟶ Q) (p : ℤ) :
    (underlying A).obj (P.X p) ⟶ (underlying B).obj (Q.X p) :=
  KappaCalculation.semilinearSectionMap a f p

/-- The actual algebraic inverse image of an arbitrary semilinear section map.
Its domain contains every local inverse-image section.
Source: Stacks 03D2 and 03EL, agent proof step 5
(blueprint: lem-pur-coefficient-comparisons-strict-totalization). -/
def inverseSectionMap (d : Diagram (J := J) (K := K)) {i j : Index} (a : i ⟶ j)
    {P : Complex (d.R.obj i)} {Q : Complex (d.R.obj j)}
    (f : (extend (d.R.map a)).obj P ⟶ Q) (p : ℤ) :
    (underlying (d.RI.obj i)).obj ((d.algebraic i).modules.obj (P.X p)) ⟶
      (underlying (d.RI.obj j)).obj ((d.algebraic j).modules.obj (Q.X p)) :=
  KappaCalculation.inverseSectionMap d a f p

/-- Algebraic inverse image of scalar-unit insertion across a coefficient arrow.
Source: Stacks 03EL, agent proof steps 5 and 7
(blueprint: lem-pur-coefficient-comparisons-strict-totalization). -/
def diagramInsertion (d : Diagram (J := J) (K := K)) {i j : Index} (a : i ⟶ j)
    (M : Modules (d.R.obj i)) :
    (underlying (d.RI.obj i)).obj ((d.algebraic i).modules.obj M) ⟶
      (underlying (d.RI.obj j)).obj
        ((d.algebraic j).modules.obj ((extensionFunctor (d.R.map a)).obj M)) :=
  KappaCalculation.diagramInsertion d a M

/-- A genuine pullback section b tensor x, with only the recorded presentation cast.
Source: Stacks 03CY and 03EL, agent proof steps 5 and 7
(blueprint: lem-pur-coefficient-comparisons-strict-totalization). -/
def diagramPullSection (d : Diagram (J := J) (K := K)) (i : Index)
    (M : Modules (d.R.obj i)) (U : Dᵒᵖ) (b : (d.S.obj i).obj.obj U)
    (x : ((d.algebraic i).modules.obj M).val.obj U) : ((d.L i).obj M).val.obj U :=
  KappaCalculation.diagramPullSection d i M U b x

/-- A generalized pullback generator as a section of the module presentation.
Source: Stacks 03EL, agent proof steps 1, 6 and 7
(blueprint: lem-pur-coefficient-comparisons-strict-totalization). -/
def diagramGeneratorSection (d : Diagram (J := J) (K := K))
    (c : ∀ i : Index, Comparison (d.ringed i)) (i : Index)
    (M : Modules (d.R.obj i)) (Z : Sheaf J (Type w))
    (x : Z ⟶ (underlying (d.R.obj i)).obj M) (U : Dᵒᵖ)
    (v : (d.inverse.obj Z).obj.obj U) : ((d.L i).obj M).val.obj U :=
  PullCalculation.diagramGeneratorSection d c i M Z x U v

/-- The comparison-then-transition route for k, in scalar-extension adjoint form.
Source: Stacks 03EL, agent proof step 5
(blueprint: lem-pur-coefficient-comparisons-strict-totalization). -/
def Comparisons.kappaTransitionForward {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) {i j k l : Index} (a : i ⟶ j) (b : k ⟶ l)
    (r : i ⟶ k) (s : j ⟶ l) (h : a ≫ s = r ≫ b)
    (P : Complex (d.R.obj i)) (Q : Complex (d.R.obj k))
    (f : (extend (d.R.map r)).obj P ⟶ Q) :=
  KappaCalculation.kappaTransitionForward e a b r s h P Q f

/-- The comparison-then-transition route for inverse k.
Source: Stacks 03EL, agent proof step 5
(blueprint: lem-pur-coefficient-comparisons-strict-totalization). -/
def Comparisons.kappaTransitionInverse {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) {i j k l : Index} (a : i ⟶ j) (b : k ⟶ l)
    (r : i ⟶ k) (s : j ⟶ l) (h : a ≫ s = r ≫ b)
    (P : Complex (d.R.obj i)) (Q : Complex (d.R.obj k))
    (f : (extend (d.R.map r)).obj P ⟶ Q) :=
  KappaCalculation.kappaTransitionInverse e a b r s h P Q f

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The two displayed k transition values. The coefficients are respectively
rho(b) i_n(rho(a)) and rho(b) phi_n(u^{-1}rho(d)); no transition is inverted.
Together with KappaTransitionLaws these give the values after either order.
Source: Stacks 03EL, agent proof step 5
(blueprint: lem-pur-coefficient-comparisons-strict-totalization). -/
def Comparisons.KappaTransitionValues {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) : Prop :=
  KappaCalculation.KappaTransitionValues e

/-- A homogeneous tensor included in the actual direct-sum total.
Source: Stacks 03EK and 07A4, agent proof steps 2, 6 and 7
(blueprint: lem-pur-coefficient-comparisons-strict-totalization). -/
def totalPure {A : Sheaf J CommRingCat.{w}} (P Q : Complex A)
    (p q n : ℤ) (h : p + q = n) (U : Cᵒᵖ) (x : (P.X p).val.obj U)
    (y : (Q.X q).val.obj U) : ((total P Q).X n).val.obj U :=
  ScalarCalculation.totalPure P Q p q n h U x y

/-- Comparison followed by tensor transition, in its scalar-extension adjoint form.
Source: Stacks 03EL and 07A4, agent proof step 6
(blueprint: lem-pur-coefficient-comparisons-strict-totalization). -/
def tensorTransitionForward (B : Index ⥤ Sheaf J CommRingCat.{w})
    (z : ∀ {i j : Index} (a : i ⟶ j), Comparison (extensionPullback (B.map a)))
    {i j k l : Index} (a : i ⟶ j) (b : k ⟶ l) (r : i ⟶ k) (s : j ⟶ l)
    (h : a ≫ s = r ≫ b) (P Q : Complex (B.obj i)) (P' Q' : Complex (B.obj k))
    (f : (extend (B.map r)).obj P ⟶ P') (g : (extend (B.map r)).obj Q ⟶ Q') :=
  ScalarCalculation.tensorTransitionForward B z a b r s h P Q P' Q' f g

/-- Inverse comparison followed by tensor transition.
Source: Stacks 03EL and 07A4, agent proof step 6
(blueprint: lem-pur-coefficient-comparisons-strict-totalization). -/
def tensorTransitionInverse (B : Index ⥤ Sheaf J CommRingCat.{w})
    (z : ∀ {i j : Index} (a : i ⟶ j), Comparison (extensionPullback (B.map a)))
    {i j k l : Index} (a : i ⟶ j) (b : k ⟶ l) (r : i ⟶ k) (s : j ⟶ l)
    (h : a ≫ s = r ≫ b) (P Q : Complex (B.obj i)) (P' Q' : Complex (B.obj k))
    (f : (extend (B.map r)).obj P ⟶ P') (g : (extend (B.map r)).obj Q ⟶ Q') :=
  ScalarCalculation.tensorTransitionInverse B z a b r s h P Q P' Q' f g

/-- The two s transition values on every homogeneous summand of the full total.
Together with TensorTransitionLaws these are the values after either order.
Source: Stacks 03EL and 07A4, agent proof step 6
(blueprint: lem-pur-coefficient-comparisons-strict-totalization). -/
def TensorTransitionValues (B : Index ⥤ Sheaf J CommRingCat.{w})
    (z : ∀ {i j : Index} (a : i ⟶ j), Comparison (extensionPullback (B.map a))) : Prop :=
  ScalarCalculation.TensorTransitionValues B z

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The displayed value of c followed by an arbitrary sequence transition.
The generalized x, y and z are tested after algebraic inverse image, as in the
recorded normalized comparison; this does not assume lifting of local sections.
Source: Stacks 03EL and 07A4, agent proof steps 1 and 6
(blueprint: lem-pur-coefficient-comparisons-strict-totalization). -/
def Comparisons.PullTensorTransitionValues {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) (c : ∀ i : Index, Comparison (d.ringed i)) : Prop :=
  PullCalculation.PullTensorTransitionValues e c

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The full-generator value of the coefficient/tensor square. Tensor inputs are
included in their bidegree summand before the composites are applied.
TensorSquare says that both whole-total routes have this value.
Source: Stacks 03EL and 07A4, agent proof steps 1 and 7
(blueprint: lem-pur-coefficient-comparisons-strict-totalization). -/
def Comparisons.TensorSquareValue {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) (c : ∀ i : Index, Comparison (d.ringed i)) : Prop :=
  ∀ {i j : Index} (a : i ⟶ j) (P Q : Complex (d.R.obj i))
    (p q n : ℤ) (hpq : p + q = n) (Z : Sheaf J (Type w))
    (x : Z ⟶ (underlying (d.R.obj i)).obj (P.X p))
    (y : Z ⟶ (underlying (d.R.obj i)).obj (Q.X q))
    (z : Z ⟶ (underlying (d.R.obj i)).obj ((total P Q).X n)),
    (∀ (V : Cᵒᵖ) (v : Z.obj.obj V),
      z.hom.app V v = totalPure P Q p q n hpq V (x.hom.app V v) (y.hom.app V v)) →
    ∀ (U : Dᵒᵖ) (v : (d.inverse.obj Z).obj.obj U)
      (b : (d.S.obj j).obj.obj U) (b' : (d.S.obj i).obj.obj U),
      ((e.kappaC a (total P Q) ≪≫
          (pull (d.ringed j)).mapIso (e.sigmaRC a P Q) ≪≫
          tensorComparison (d.ringed j) (c j)
            ((extend (d.R.map a)).obj P) ((extend (d.R.map a)).obj Q)).hom.f n).val.app U
        (extensionTmul (d.S.map a) ((d.L i).obj ((total P Q).X n)) U b
          (b' • (diagramGeneratorSection d c i ((total P Q).X n) Z z U v))) =
        totalPure ((pull (d.ringed j)).obj ((extend (d.R.map a)).obj P))
          ((pull (d.ringed j)).obj ((extend (d.R.map a)).obj Q)) p q n hpq U
          ((b * (d.S.map a).hom.app U b') •
            (diagramGeneratorSection d c j ((extensionFunctor (d.R.map a)).obj (P.X p)) Z
              (x ≫ insertion (d.R.map a) (P.X p)) U v))
          (diagramGeneratorSection d c j ((extensionFunctor (d.R.map a)).obj (Q.X q)) Z
            (y ≫ insertion (d.R.map a) (Q.X q)) U v)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[no_expose] private noncomputable instance tensorCoproducts (R : Sheaf J CommRingCat.{w}) :
    HasCoproducts.{0} (Modules R) := inferInstance

@[no_expose] private noncomputable instance hasTensorTotal (R : Sheaf J CommRingCat.{w})
    (P Q : Complex R) :
    HomologicalComplex.HasMapBifunctor P Q (curriedTensor (Modules R)) (.up ℤ) :=
  inferInstance

@[reassoc]
private theorem tensorComparison_ι {R : Sheaf J CommRingCat.{w}}
    {S : Sheaf K CommRingCat.{w}} (f : RingedPullback R S) (c : Comparison f)
    (P Q : Complex R) (p q n : ℤ) (h : p + q = n) :
    f.L.map (CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules R)) p q n h) ≫
        (tensorComparison f c P Q).hom.f n =
      (c.mu (P.X p) (Q.X q)).hom ≫
        CochainComplex.ιMapBifunctor ((pull f).obj P) ((pull f).obj Q)
          (curriedTensor (Modules S)) p q n h := by
  exact CategoryTheory.CochainPullback.comparison_ι f c P Q p q n h

@[reassoc]
private theorem tensorComparison_inv_ι {R : Sheaf J CommRingCat.{w}}
    {S : Sheaf K CommRingCat.{w}} (f : RingedPullback R S) (c : Comparison f)
    (P Q : Complex R) (p q n : ℤ) (h : p + q = n) :
    CochainComplex.ιMapBifunctor ((pull f).obj P) ((pull f).obj Q)
        (curriedTensor (Modules S)) p q n h ≫ (tensorComparison f c P Q).inv.f n =
      (c.mu (P.X p) (Q.X q)).inv ≫
        f.L.map (CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules R)) p q n h)  := by
  exact ScalarCalculation.tensorComparison_inv_ι f c P Q p q n h


private theorem totalSummands {R : Sheaf J CommRingCat.{w}}
    {S : Sheaf K CommRingCat.{w}} (f : RingedPullback R S) (c : Comparison f) :
    TotalSummands f c := by
  intro P Q p q n h
  exact ⟨tensorComparison_ι f c P Q p q n h, tensorComparison_inv_ι f c P Q p q n h⟩

private theorem totalNaturality {R : Sheaf J CommRingCat.{w}}
    {S : Sheaf K CommRingCat.{w}} (f : RingedPullback R S) (c : Comparison f) :
    TotalNaturality f c := by
  intro P Q P' Q' a b
  have h : (pull f).map (tensorTotalMap a b) ≫ (tensorComparison f c P' Q').hom =
      (tensorComparison f c P Q).hom ≫ tensorTotalMap ((pull f).map a) ((pull f).map b) :=
    (cochainComparison_monoidal f c).1 P Q P' Q' a b
  refine ⟨h, ?_⟩
  apply (cancel_epi (tensorComparison f c P Q).hom).1
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.hom_inv_id_assoc]

private theorem kappaDifferentials (d : Diagram (J := J) (K := K))
    (e : Comparisons d) : e.KappaDifferentials := by
  intro i j a P Q n n' v
  exact ⟨(e.kappa a).hom.naturality _, (e.kappa a).inv.naturality _⟩

private theorem genericDifferentialInv
    {A B : Type*} [Category A] [Preadditive A] [MonoidalCategory A]
    [Category B] [Preadditive B] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [HasCoproducts.{0} A] [HasCoproducts.{0} B]
    (L : A ⥤ B) [L.Additive]
    (mu : ∀ X Y, L.obj (X ⊗ Y) ≅ L.obj X ⊗ L.obj Y)
    (hn : ∀ {X X' Y Y'} (a : X ⟶ X') (b : Y ⟶ Y'),
      L.map (a ⊗ₘ b) ≫ (mu X' Y').hom =
        (mu X Y).hom ≫ (L.map a ⊗ₘ L.map b))
    (P Q : CochainComplex A ℤ)
    [HomologicalComplex.HasMapBifunctor P Q (curriedTensor A) (.up ℤ)]
    [HomologicalComplex.HasMapBifunctor
      ((L.mapHomologicalComplex (.up ℤ)).obj P)
      ((L.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor B) (.up ℤ)]
    (t : CochainComplex.mapBifunctor
      ((L.mapHomologicalComplex (.up ℤ)).obj P)
      ((L.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor B) ⟶
      (L.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor P Q (curriedTensor A)))
    (hι : ∀ p q n (h : p + q = n),
      CochainComplex.ιMapBifunctor ((L.mapHomologicalComplex (.up ℤ)).obj P)
        ((L.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor B) p q n h ≫
        t.f n = (mu (P.X p) (Q.X q)).inv ≫ L.map
          (CochainComplex.ιMapBifunctor P Q (curriedTensor A) p q n h)) (n m : ℤ) (v : Fin 2) :
    (if v = 0 then HomologicalComplex.mapBifunctor.D₁ else
        HomologicalComplex.mapBifunctor.D₂)
        ((L.mapHomologicalComplex (.up ℤ)).obj P)
        ((L.mapHomologicalComplex (.up ℤ)).obj Q)
        (curriedTensor (B)) (.up ℤ) n m ≫ t.f m =
      t.f n ≫ L.map
        ((if v = 0 then HomologicalComplex.mapBifunctor.D₁ else
          HomologicalComplex.mapBifunctor.D₂) P Q (curriedTensor (A))
            (.up ℤ) n m) := by
  have hιa (p q n : ℤ) (h : p + q = n) {Y : B}
      (g : L.obj ((CochainComplex.mapBifunctor P Q (curriedTensor A)).X n) ⟶ Y) :
      CochainComplex.ιMapBifunctor ((L.mapHomologicalComplex (.up ℤ)).obj P)
        ((L.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor B) p q n h ≫
          t.f n ≫ g = (mu (P.X p) (Q.X q)).inv ≫ L.map
            (CochainComplex.ιMapBifunctor P Q (curriedTensor A) p q n h) ≫ g := by
    rw [← Category.assoc, hι, Category.assoc]
  have hi {X X' Y Y' : A} (a : X ⟶ X') (b : Y ⟶ Y') :
      (mu X Y).inv ≫ L.map (a ⊗ₘ b) =
        (L.map a ⊗ₘ L.map b) ≫ (mu X' Y').inv := by
    apply (cancel_mono (mu X' Y').hom).1
    rw [Category.assoc, hn, Iso.inv_hom_id_assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  by_cases hnm : (ComplexShape.up ℤ).Rel n m
  · change n + 1 = m at hnm
    subst m
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    change p + q = n at hpq
    fin_cases v
    · simp only [Fin.zero_eta, ↓reduceIte]
      rw [HomologicalComplex.mapBifunctor.ι_D₁_assoc, hιa,
        ← L.map_comp, HomologicalComplex.mapBifunctor.ι_D₁]
      rw [HomologicalComplex.mapBifunctor.d₁_eq P Q _ _
          (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl) q (n + 1) (by
            change p + 1 + q = n + 1
            omega),
        HomologicalComplex.mapBifunctor.d₁_eq
          ((L.mapHomologicalComplex (.up ℤ)).obj P)
          ((L.mapHomologicalComplex (.up ℤ)).obj Q) _ _
          (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl) q (n + 1) (by
            change p + 1 + q = n + 1
            omega)]
      simp only [ComplexShape.ε₁_def, one_smul,
        hι, Functor.map_comp, Category.assoc,
        curriedTensor_map_app, Functor.mapHomologicalComplex_obj_d, ← tensorHom_id]
      have ht := (congrArg (fun z ↦ z ≫ L.map
          (CochainComplex.ιMapBifunctor P Q (curriedTensor (A))
            (p + 1) q (n + 1) (by omega)))
          (hi (P.d p (p + 1)) (𝟙 (Q.X q)))).symm
      simp only [L.map_id, Category.assoc] at ht
      exact ht
    · simp only [Fin.reduceFinMk, Fin.isValue, one_ne_zero, ↓reduceIte]
      rw [HomologicalComplex.mapBifunctor.ι_D₂_assoc, hιa,
        ← L.map_comp, HomologicalComplex.mapBifunctor.ι_D₂]
      rw [HomologicalComplex.mapBifunctor.d₂_eq P Q _ _ p
          (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl) (n + 1) (by
            change p + (q + 1) = n + 1
            omega),
        HomologicalComplex.mapBifunctor.d₂_eq
          ((L.mapHomologicalComplex (.up ℤ)).obj P)
          ((L.mapHomologicalComplex (.up ℤ)).obj Q) _ _ p
          (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl) (n + 1) (by
            change p + (q + 1) = n + 1
            omega)]
      simp only [ComplexShape.ε₂_def, ComplexShape.ε_up_ℤ,
        Functor.map_units_smul, Functor.map_comp,
        Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc,
        hι, curriedTensor_obj_map,
        Functor.mapHomologicalComplex_obj_d, ← id_tensorHom]
      have ht := (congrArg (fun z ↦ p.negOnePow • (z ≫ L.map
          (CochainComplex.ιMapBifunctor P Q (curriedTensor (A))
            p (q + 1) (n + 1) (by omega))))
          (hi (𝟙 (P.X p)) (Q.d q (q + 1)))).symm
      simp only [L.map_id, Category.assoc] at ht
      exact ht
  · fin_cases v <;>
      simp only [Fin.zero_eta, Fin.reduceFinMk, Fin.isValue, one_ne_zero, ↓reduceIte,
        HomologicalComplex.mapBifunctor.D₁, HomologicalComplex.mapBifunctor.D₂,
        HomologicalComplex₂.D₁_shape _ _ _ _ hnm,
        HomologicalComplex₂.D₂_shape _ _ _ _ hnm, L.map_zero, comp_zero, zero_comp]

private theorem totalDifferential_inv {R : Sheaf J CommRingCat.{w}}
    {S : Sheaf K CommRingCat.{w}} (f : RingedPullback R S) (c : Comparison f)
    (P Q : Complex R) (n m : ℤ) (v : Fin 2) :
    (if v = 0 then HomologicalComplex.mapBifunctor.D₁ else
        HomologicalComplex.mapBifunctor.D₂) ((pull f).obj P) ((pull f).obj Q)
        (curriedTensor (Modules S)) (.up ℤ) n m ≫ (tensorComparison f c P Q).inv.f m =
      (tensorComparison f c P Q).inv.f n ≫ f.L.map
        ((if v = 0 then HomologicalComplex.mapBifunctor.D₁ else
          HomologicalComplex.mapBifunctor.D₂) P Q (curriedTensor (Modules R))
            (.up ℤ) n m) := by
  exact genericDifferentialInv f.L c.mu c.naturality P Q
    (tensorComparison f c P Q).inv (tensorComparison_inv_ι f c P Q) n m v

private theorem totalDifferentials {R : Sheaf J CommRingCat.{w}}
    {S : Sheaf K CommRingCat.{w}} (f : RingedPullback R S) (c : Comparison f) :
    TotalDifferentials f c := by
  dsimp only [TotalDifferentials, tensorD₁, tensorD₂]
  intro P Q n m
  have h₁ := totalDifferential_inv f c P Q n m 0
  have h₂ := totalDifferential_inv f c P Q n m 1
  simp only [Fin.isValue, one_ne_zero, ↓reduceIte] at h₁ h₂
  refine ⟨?_, ?_, h₁, h₂⟩
  · apply (cancel_mono ((tensorComparison f c P Q).inv.f m)).1
    simp only [Category.assoc, ← HomologicalComplex.comp_f,
      Iso.hom_inv_id, HomologicalComplex.id_f]
    rw [h₁, ← Category.assoc, ← HomologicalComplex.comp_f,
      Iso.hom_inv_id, HomologicalComplex.id_f]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · apply (cancel_mono ((tensorComparison f c P Q).inv.f m)).1
    simp only [Category.assoc, ← HomologicalComplex.comp_f,
      Iso.hom_inv_id, HomologicalComplex.id_f]
    rw [h₂, ← Category.assoc, ← HomologicalComplex.comp_f,
      Iso.hom_inv_id, HomologicalComplex.id_f]
    exact (Category.comp_id _).trans (Category.id_comp _).symm

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem tensorComparison_unique {R : Sheaf J CommRingCat.{w}}
    {S : Sheaf K CommRingCat.{w}} (f : RingedPullback R S)
    (c c' : Comparison f) : c = c' := by
  let := f.finiteLimits
  exact (SheafOfModules.CochainTensorComparison.canonicalRingedTensorComparison_existsUnique
    R S f.RI f.uInv f.I f.coefficient f.L f.hobj f.uPush f.adj f.hmap).2.elim c c'

@[no_expose] private def canonicalComparisons (d : Diagram (J := J) (K := K))
    (c : ∀ i : Index, Comparison (d.ringed i)) : Comparisons d where
  kappa a := (scalarAssociation (d.ringed _) (c _) (d.square a) (c _)).symm
  sigmaR a := extensionComparison (d.R.map a)
  sigmaS a := extensionComparison (d.S.map a)

private theorem comparisons_eq (d : Diagram (J := J) (K := K))
    (c : ∀ i : Index, Comparison (d.ringed i)) (e : Comparisons d)
    (hn : e.Normalized c) : e = canonicalComparisons d c := by
  have hk : @e.kappa = @(canonicalComparisons d c).kappa := by
    funext i j a
    have h := (Classical.choose_spec
      (scalarAssociation_existsUnique (d.ringed i) (c i) (d.square a) (c j))).2
        (e.kappa a).symm (hn a)
    exact congrArg Iso.symm h
  have hr : @e.sigmaR = @(canonicalComparisons d c).sigmaR := by
    funext i j a
    exact tensorComparison_unique _ _ _
  have hs : @e.sigmaS = @(canonicalComparisons d c).sigmaS := by
    funext i j a
    exact tensorComparison_unique _ _ _
  cases e with
  | mk a b f =>
    change @a = @(canonicalComparisons d c).kappa at hk
    change @b = @(canonicalComparisons d c).sigmaR at hr
    change @f = @(canonicalComparisons d c).sigmaS at hs
    subst a
    subst b
    subst f
    rfl


private theorem rotateIsoSquare {A : Type*} [Category A] {W X Y Z : A}
    (i : W ≅ X) (j : Y ≅ Z) (f : X ⟶ Z) (g : W ⟶ Y)
    (h : f ≫ j.inv = i.inv ≫ g) : i.hom ≫ f = g ≫ j.hom := by
  apply (cancel_mono j.inv).1
  rw [Category.assoc, h, ← Category.assoc, Iso.hom_inv_id, Category.id_comp,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorSquare (d : Diagram (J := J) (K := K))
    (c : ∀ i : Index, Comparison (d.ringed i)) (e : Comparisons d)
    (hn : e.Normalized c) : e.TensorSquare c := by
  rw [comparisons_eq d c e hn]
  intro i j a P Q
  have h := coefficients_extension_of_modules (d.ringed i) (c i) (d.square a) (c j)
    (cochainModuleTensorCoefficients (d.ringed i) (c i) (d.square a) (c j)).1 P Q
  apply Iso.ext
  change (kappa (d.ringed i) (c i) (d.square a) (c j) (total P Q)).inv ≫
      (pull (d.ringed j)).map (epsilon (d.R.map a) P Q).hom ≫
      (comparison (d.ringed j) (c j)
        ((extend (d.R.map a)).obj P) ((extend (d.R.map a)).obj Q)).hom =
    (extend (d.S.map a)).map (comparison (d.ringed i) (c i) P Q).hom ≫
      (epsilon (d.S.map a) ((pull (d.ringed i)).obj P) ((pull (d.ringed i)).obj Q)).hom ≫
        (totalIso (kappa (d.ringed i) (c i) (d.square a) (c j) P).symm
          (kappa (d.ringed i) (c i) (d.square a) (c j) Q).symm).hom
  conv_rhs => rw [← Category.assoc]
  apply rotateIsoSquare (kappa (d.ringed i) (c i) (d.square a) (c j) (total P Q)).symm
    (totalIso (kappa (d.ringed i) (c i) (d.square a) (c j) P).symm
      (kappa (d.ringed i) (c i) (d.square a) (c j) Q).symm)
  rw [Category.assoc]
  change (pull (d.ringed j)).map (epsilon (d.R.map a) P Q).hom ≫
      (comparison (d.ringed j) (c j)
        ((extend (d.R.map a)).obj P) ((extend (d.R.map a)).obj Q)).hom ≫
      totalMap (kappa (d.ringed i) (c i) (d.square a) (c j) P).hom
        (kappa (d.ringed i) (c i) (d.square a) (c j) Q).hom =
    (kappa (d.ringed i) (c i) (d.square a) (c j) (total P Q)).hom ≫
      ((extend (d.S.map a)).map (comparison (d.ringed i) (c i) P Q).hom ≫
        (epsilon (d.S.map a) ((pull (d.ringed i)).obj P) ((pull (d.ringed i)).obj Q)).hom)
  exact h




private theorem tensorTotalMap_comp {R : Sheaf J CommRingCat.{w}}
    {P P' P'' Q Q' Q'' : Complex R}
    (f : P ⟶ P') (f' : P' ⟶ P'') (g : Q ⟶ Q') (g' : Q' ⟶ Q'') :
    tensorTotalMap (f ≫ f') (g ≫ g') =
      tensorTotalMap f g ≫ tensorTotalMap f' g' := by
  exact (tensorHom_comp_tensorHom f g f' g').symm

private theorem pullTensorTransitions (d : Diagram (J := J) (K := K))
    (c : ∀ i : Index, Comparison (d.ringed i)) (e : Comparisons d)
    (hn : e.Normalized c) : e.PullTensorTransitions c := by
  intro i j a P Q P' Q' f g
  have hs := congrArg Iso.hom (tensorSquare d c e hn a P Q)
  change (e.kappaC a (total P Q)).hom ≫
      (pull (d.ringed j)).map (e.sigmaRC a P Q).hom ≫
        (tensorComparison (d.ringed j) (c j)
          ((extend (d.R.map a)).obj P) ((extend (d.R.map a)).obj Q)).hom =
    (extend (d.S.map a)).map (tensorComparison (d.ringed i) (c i) P Q).hom ≫
      (e.sigmaSC a ((pull (d.ringed i)).obj P) ((pull (d.ringed i)).obj Q)).hom ≫
        tensorTotalMap (e.kappaC a P).hom (e.kappaC a Q).hom at hs
  have ht := congrArg (fun z ↦ z ≫
    tensorTotalMap ((pull (d.ringed j)).map f) ((pull (d.ringed j)).map g)) hs
  simp only [Category.assoc] at ht
  change (extend (d.S.map a)).map (tensorComparison (d.ringed i) (c i) P Q).hom ≫
      (e.sigmaSC a ((pull (d.ringed i)).obj P) ((pull (d.ringed i)).obj Q)).hom ≫
        tensorTotalMap ((e.kappaC a P).hom ≫ (pull (d.ringed j)).map f)
          ((e.kappaC a Q).hom ≫ (pull (d.ringed j)).map g) =
    ((e.kappaC a (total P Q)).hom ≫
      (pull (d.ringed j)).map ((e.sigmaRC a P Q).hom ≫ tensorTotalMap f g)) ≫
        (tensorComparison (d.ringed j) (c j) P' Q').hom
  rw [tensorTotalMap_comp]
  rw [← ht]
  have hh := (totalNaturality (d.ringed j) (c j) _ _ _ _ f g).1
  simpa only [Functor.map_comp, Category.assoc] using congrArg
    (fun z ↦ (e.kappaC a (total P Q)).hom ≫
      (pull (d.ringed j)).map (e.sigmaRC a P Q).hom ≫ z) hh.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorSquareValue (d : Diagram (J := J) (K := K))
    (c : ∀ i : Index, Comparison (d.ringed i)) (e : Comparisons d)
    (hn : e.Normalized c) (hp : e.PullTensorTransitionValues c) :
    e.TensorSquareValue c := by
  intro i j a P Q p q n hpq Z x y z hz U v b b'
  have ht := hp a P Q ((extend (d.R.map a)).obj P)
    ((extend (d.R.map a)).obj Q) (𝟙 _) (𝟙 _)
    p q n hpq Z x y z hz U v b'
  have hs := congrArg (fun t ↦ (t.hom.f n).val.app U
    (extensionTmul (d.S.map a) ((d.L i).obj ((total P Q).X n)) U b
      (b' • diagramGeneratorSection d c i ((total P Q).X n) Z z U v)))
    (tensorSquare d c e hn a P Q)
  refine hs.trans ?_
  change (((extend (d.S.map a)).map
      (tensorComparison (d.ringed i) (c i) P Q).hom ≫
        (e.sigmaSC a ((pull (d.ringed i)).obj P) ((pull (d.ringed i)).obj Q)).hom ≫
        tensorTotalMap (e.kappaC a P).hom (e.kappaC a Q).hom).f n).val.app U _ = _
  simp only [Comparisons.pullArrow, Functor.map_id, Category.comp_id,
    KappaCalculation.semilinearSectionMap, HomologicalComplex.id_f, Functor.map_id,
    Category.comp_id] at ht
  erw [Functor.map_id, Category.comp_id, Functor.map_id, Category.comp_id] at ht
  erw [KappaCalculation.extension_smul, map_smul]
  have hb := congrArg (fun t : ((total
    ((pull (d.ringed j)).obj ((extend (d.R.map a)).obj P))
    ((pull (d.ringed j)).obj ((extend (d.R.map a)).obj Q))).X n).val.obj U ↦ b • t) ht
  refine hb.trans ?_
  change b • ScalarCalculation.totalPure _ _ p q n hpq U _ _ = _
  erw [← ScalarCalculation.totalPure_smul, smul_smul]
  rfl

/-- Strict signed totalization of the degreewise normalized coefficient comparisons.
Source: Stacks 03EK, 03EL and 07A4, and the eight agent calculations of the node
(blueprint: lem-pur-coefficient-comparisons-strict-totalization).

Proof:
1. Use lem-pur-coefficient-comparisons-balanced-construction at every vertex.
   Test nested scalar-extension maps by lem-weil-pbc-ringed-topoi-module-adjunction
   and tensors by lem-pc-sites-sheaf-tensor-bilinear-universal. These test arbitrary
   generalized inverse-image sections; no local section lifting is assumed.
2. By lem-weil-pbc-left-adjoint-preserves-colimits, pullback and scalar extension
   preserve each coproduct indexed by p+q=n. Sum the prescribed module maps and
   their inverses. The uniqueness in def-weil-pbc-category-colimit gives inverse
   maps on the whole total. This is the fixed comparison in
   lem-pur-cochain-pullback-tensor-coherence.
3. Naturality of k gives b i(a) tensor (1 tensor dx), and the inverse gives
   b phi(d) tensor (1 tensor dx). It preserves each homogeneous degree.
4. For s and c, the first differential gives (b tensor dx) tensor (1 tensor y);
   the second gives (-1)^p (b tensor x) tensor (1 tensor dy). The inverse gives
   bd tensor (dx tensor y) and (-1)^p bd tensor (x tensor dy). Thus the maps and
   inverses commute with both summands, also for negative odd p.
5. For an arbitrary transition, the two k routes have coefficient
   rho(b) i_n(rho(a)); the inverse routes have coefficient rho(b) phi_n(rho(d)).
   The coefficient and inverse-image graph squares give these identities.
   No transition adjoint is inverted.
6. Both s routes give (rho(b) tensor t_K x) tensor (1 tensor t_H y); the inverse
   routes give rho(b)rho(d) tensor (t_K x tensor t_H y). The c routes have the
   same formula after algebraic inverse image. Multiplicativity and unitality
   of rho, balancing, generalized-tensor tests and coproduct uniqueness suffice.
   The same calculations with module maps prove naturality in strict morphisms.
7. On b tensor (a tensor (x tensor y)), both square routes give
   (b i(a) tensor (1 tensor x)) tensor (1 tensor (1 tensor y)). Test by the two
   adjunctions and bilinear universal properties, then by every coproduct inclusion.
8. All maps are chain isomorphisms commuting with every transition. Cancel them
   in the square to obtain its inverse equality. The argument uses neither
   flatness nor boundedness, and works for zero rings and zero modules.
-/
theorem coefficientComparisonsStrictTotalization
    (d : Diagram (J := J) (K := K))
    (c : ∀ i : Index, Comparison (d.ringed i)) (e : Comparisons d)
    (_normalized : e.Normalized c) :
    e.KappaDifferentials ∧ e.KappaTransitionLaws ∧ e.KappaTransitionValues ∧
    TensorTransitionLaws d.R e.sigmaR ∧ TensorTransitionLaws d.S e.sigmaS ∧
    TensorTransitionValues d.R e.sigmaR ∧ TensorTransitionValues d.S e.sigmaS ∧
    (∀ i : Index, TotalDifferentials (d.ringed i) (c i) ∧
      TotalNaturality (d.ringed i) (c i) ∧ TotalSummands (d.ringed i) (c i)) ∧
    (∀ {i j : Index} (a : i ⟶ j),
      (TotalDifferentials (extensionPullback (d.R.map a)) (e.sigmaR a) ∧
        TotalNaturality (extensionPullback (d.R.map a)) (e.sigmaR a) ∧
        TotalSummands (extensionPullback (d.R.map a)) (e.sigmaR a)) ∧
      (TotalDifferentials (extensionPullback (d.S.map a)) (e.sigmaS a) ∧
        TotalNaturality (extensionPullback (d.S.map a)) (e.sigmaS a) ∧
        TotalSummands (extensionPullback (d.S.map a)) (e.sigmaS a))) ∧
    e.PullTensorTransitions c ∧ e.PullTensorTransitionValues c ∧
    e.TensorSquare c ∧ e.TensorSquareValue c := by
  obtain ⟨hk, hR, hS⟩ := normalizedCoefficientTransitionSquares d c e _normalized
  have hv : TensorTransitionValues d.R e.sigmaR ∧
      TensorTransitionValues d.S e.sigmaS :=
    ⟨(ScalarCalculation.normalizedScalarTensorTransitions d.R e.sigmaR).2,
      (ScalarCalculation.normalizedScalarTensorTransitions d.S e.sigmaS).2⟩
  have hp : e.PullTensorTransitionValues c :=
    PullCalculation.normalizedPullTensorGeneratorSections d c e _normalized
  have hkv : e.KappaTransitionValues :=
    KappaCalculation.normalizedKappaTransitionValues d c e _normalized
  refine ⟨kappaDifferentials d e, hk, hkv, hR, hS, hv.1, hv.2, ?_, ?_,
    pullTensorTransitions d c e _normalized, hp, tensorSquare d c e _normalized,
    tensorSquareValue d c e _normalized hp⟩
  · intro i
    exact ⟨totalDifferentials _ _, totalNaturality _ _, totalSummands _ _⟩
  · intro i j a
    exact ⟨⟨totalDifferentials _ _, totalNaturality _ _, totalSummands _ _⟩,
      ⟨totalDifferentials _ _, totalNaturality _ _, totalSummands _ _⟩⟩

end CategoryTheory.CochainPullback.StrictCoefficient
