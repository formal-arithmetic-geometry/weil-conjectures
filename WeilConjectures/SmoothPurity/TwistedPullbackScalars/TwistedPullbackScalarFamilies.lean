/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.TwistedPullbackScalars.TwistedPullbackSquareMaps

/-! # Naturality, unit and tower predicates for the twisted pullback scalar families

Source: blueprint sec-smooth-purity/sk-thm-purity-transport, purity transport,
base-change coherence, unit and tower equations of the comparison families
(blueprint: def-pur-twisted-pullback-coefficient-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.TwistedPullbackScalars
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L)
variable {X X' Y Y' : Scheme.{u}}
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ x : X', Invertible (l : X'.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  [∀ y : Y', Invertible (l : Y'.residueField y)]
/-- Uniform naturality predicate for a component family, without choosing a new map.
Source: purity transport, equality of natural transformations
(blueprint: def-pur-twisted-pullback-coefficient-coherence). -/
def Natural {A B : Type (u + 2)} [Category.{u + 2} A] [Category.{u + 2} B]
    {F G : A ⥤ B} (w : ∀ K : A, F.obj K ≅ G.obj K) : Prop :=
  ∀ (K N : A) (b : K ⟶ N), F.map b ≫ (w N).hom = (w K).hom ≫ G.map b

section CoefficientFamilies
variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The existing actual finite subfields of the fixed closure.
Source: purity coefficient convention
(blueprint: def-pur-twisted-pullback-coefficient-coherence). -/
abbrev Fields := Padic.FiniteCoefficientFields l Ω

/-- A uniform name for a comparison family on the already specified coefficient stages.
This only records its functors and component isomorphisms; it asserts no coherence.
Source: purity transport, seven families w
(blueprint: def-pur-twisted-pullback-coefficient-coherence). -/
structure Family (V W : Scheme.{u}) where
  F : ∀ R : Fields l Ω, sfRationalConstructibleCategory l R.val V ⥤
    sfRationalConstructibleCategory l R.val W
  w : ∀ (R S : Fields l Ω) (h : R ≤ S) (K : sfRationalConstructibleCategory l R.val V),
    (T l R.val S.val (IntermediateField.inclusion h) W).obj ((F R).obj K) ≅
      (F S).obj ((T l R.val S.val (IntermediateField.inclusion h) V).obj K)

/-- The tensor associator for literal subfield inclusions, with their transitivity cast.
Source: purity transport, alpha
(blueprint: def-pur-twisted-pullback-coefficient-coherence). -/
def alpha (W : Scheme.{u}) (R S B : Fields l Ω) (h : R ≤ S) (k : S ≤ B) :
    T l R.val S.val (IntermediateField.inclusion h) W ⋙
      T l S.val B.val (IntermediateField.inclusion k) W ≅
        T l R.val B.val (IntermediateField.inclusion (h.trans k)) W :=
  sfRationalScalarComp l R.val S.val (IntermediateField.inclusion h) W 0
      (Fact.out : l.Prime).ne_zero B.val (IntermediateField.inclusion k) ≪≫
    eqToIso (by congr 1)

/-- The coefficient-unit multiplication at an actual subfield.
Source: purity transport, E=L
(blueprint: def-pur-twisted-pullback-coefficient-coherence). -/
def unit (W : Scheme.{u}) (R : Fields l Ω) :
    T l R.val R.val (IntermediateField.inclusion (le_rfl : R ≤ R)) W ≅
      𝟭 (sfRationalConstructibleCategory l R.val W) :=
  eqToIso (by congr 1) ≪≫ sfRationalScalarUnit l R.val W 0 (Fact.out : l.Prime).ne_zero

/-- The full unit and tower equations, with naturality, for a specified family.
Source: purity transport, displayed tower identity and canonical units
(blueprint: def-pur-twisted-pullback-coefficient-coherence). -/
def Coherent {V W : Scheme.{u}} (A : Family l Ω V W) : Prop :=
  (∀ (R S : Fields l Ω) (h : R ≤ S),
    Natural (F := A.F R ⋙ T l R.val S.val (IntermediateField.inclusion h) W)
      (G := T l R.val S.val (IntermediateField.inclusion h) V ⋙ A.F S) (A.w R S h)) ∧
  (∀ (R : Fields l Ω) (K : sfRationalConstructibleCategory l R.val V),
    (A.w R R le_rfl K).hom ≫ (A.F R).map ((unit l Ω V R).hom.app K) =
      (unit l Ω W R).hom.app ((A.F R).obj K)) ∧
  (∀ (R S B : Fields l Ω) (h : R ≤ S) (k : S ≤ B)
      (K : sfRationalConstructibleCategory l R.val V),
    (alpha l Ω W R S B h k).hom.app ((A.F R).obj K) ≫
        (A.w R B (h.trans k) K).hom =
      (T l S.val B.val (IntermediateField.inclusion k) W).map (A.w R S h K).hom ≫
        (A.w S B k ((T l R.val S.val (IntermediateField.inclusion h) V).obj K)).hom ≫
          (A.F B).map ((alpha l Ω V R S B h k).hom.app K))

/-- The actual q family. Source: purity transport
(blueprint: def-pur-twisted-pullback-coefficient-coherence). -/
def qFamily (W : Scheme.{u}) [∀ x : W, Invertible (l : W.residueField x)]
    (d : ℕ) : Family l Ω W W where
  F R := D l R.val W d
  w R S h := q l R.val S.val (IntermediateField.inclusion h) W d

/-- The actual p family for any morphism. Source: purity transport
(blueprint: def-pur-twisted-pullback-coefficient-coherence). -/
def pFamily {A B : Scheme.{u}} (h : A ⟶ B)
    [∀ x : A, Invertible (l : A.residueField x)]
    [∀ x : B, Invertible (l : B.residueField x)] : Family l Ω B A where
  F R := rationalDerivedPullback l R.val h
  w R S k := p l R.val S.val (IntermediateField.inclusion k) h

/-- P_U, also used for P_V by substituting f',v. Source: purity transport
(blueprint: def-pur-twisted-pullback-coefficient-coherence). -/
def compositeFamily (u : X' ⟶ X) (f : X ⟶ Y) : Family l Ω Y X' where
  F R := U l R.val u f
  w R S k := PU l R.val S.val (IntermediateField.inclusion k) u f

/-- The actual a family. Source: purity transport
(blueprint: def-pur-twisted-pullback-coefficient-coherence). -/
def aFamily {A B : Scheme.{u}} (h : A ⟶ B)
    [∀ x : A, Invertible (l : A.residueField x)]
    [∀ x : B, Invertible (l : B.residueField x)] (d : ℕ) : Family l Ω B A where
  F R := H l R.val h d
  w R S k := a l R.val S.val (IntermediateField.inclusion k) h d

/-- The actual r_A family. Source: purity transport
(blueprint: def-pur-twisted-pullback-coefficient-coherence). -/
def rAFamily (u : X' ⟶ X) (f : X ⟶ Y) (d : ℕ) : Family l Ω Y X' where
  F R := H l R.val f d ⋙ rationalDerivedPullback l R.val u
  w R S k := rA l R.val S.val (IntermediateField.inclusion k) u f d

/-- The actual r_B family. Source: purity transport
(blueprint: def-pur-twisted-pullback-coefficient-coherence). -/
def rBFamily (f' : X' ⟶ Y') (v : Y' ⟶ Y) (d : ℕ) : Family l Ω Y X' where
  F R := rationalDerivedPullback l R.val v ⋙ H l R.val f' d
  w R S k := rB l R.val S.val (IntermediateField.inclusion k) f' v d

/-- The seven specified families, including p at every edge of the square.
Source: purity transport, unit and tower clause
(blueprint: def-pur-twisted-pullback-coefficient-coherence). -/
def TowerCoherence (u : X' ⟶ X) (f : X ⟶ Y) (f' : X' ⟶ Y') (v : Y' ⟶ Y)
    (d : ℕ) : Prop :=
  Coherent l Ω (qFamily l Ω X d) ∧ Coherent l Ω (qFamily l Ω X' d) ∧
  Coherent l Ω (pFamily l Ω u) ∧ Coherent l Ω (pFamily l Ω f) ∧
  Coherent l Ω (pFamily l Ω f') ∧ Coherent l Ω (pFamily l Ω v) ∧
  Coherent l Ω (compositeFamily l Ω u f) ∧ Coherent l Ω (compositeFamily l Ω f' v) ∧
  Coherent l Ω (aFamily l Ω f d) ∧ Coherent l Ω (aFamily l Ω f' d) ∧
  Coherent l Ω (rAFamily l Ω u f d) ∧ Coherent l Ω (rBFamily l Ω f' v d)

end CoefficientFamilies



end WeilConjectures.TwistedPullbackScalars
