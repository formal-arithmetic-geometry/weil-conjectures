/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Equivalence

/-! # Cyclic normalization with an arbitrary closing endofunctor

The existing cyclic-return proof specializes the closing functor to an iterate.
Here the same partial-product argument works for an arbitrary return functor,
which is necessary when a component has no chosen root of its return automorphism.
Source: Weil II, paragraph after (1.1.10), p.152.
(blueprint: lem-dl-a1-cyclic-pair-equivalence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory
namespace CategoryTheory.Endofunctor.ComponentCycle

variable {C : Type u} [Category.{v} C]

/-- One component of the twisted shift, expressed using existing evaluation functors.
Source: Weil II, paragraph after (1.1.10), p.152, cyclic normalization.
(blueprint: lem-dl-a1-cyclic-pair-equivalence) -/
def cyclicShiftComponent (P : C ⥤ C) (n : ℕ) (i : Fin (n + 1)) :
    (Discrete (Fin (n + 1)) ⥤ C) ⥤ C :=
  Fin.lastCases ((evaluation (Discrete (Fin (n + 1))) C).obj ⟨0⟩ ⋙ P)
    (fun j ↦ (evaluation (Discrete (Fin (n + 1))) C).obj ⟨j.succ⟩) i

/-- The twisted shift on a tuple of length `n+1`: its entries are `A_(i+1)` at
`i < n` and `P A_0` at the last index. On maps it has the same formulas.
Source: Weil II, paragraph after (1.1.10), p.152, cyclic normalization.
(blueprint: lem-dl-a1-cyclic-pair-equivalence) -/
def cyclicShift (P : C ⥤ C) (n : ℕ) :
    (Discrete (Fin (n + 1)) ⥤ C) ⥤ (Discrete (Fin (n + 1)) ⥤ C) where
  obj A := Discrete.functor fun i ↦ (cyclicShiftComponent P n i).obj A
  map f := Discrete.natTrans fun i ↦ (cyclicShiftComponent P n i.as).map f
  map_id A := by ext; simp
  map_comp f g := by ext; simp

/-- A finite family of functors, viewed as a discrete diagram.
Source: Weil II (1.1.12), componentwise restriction.
(blueprint: lem-dl-a1-cyclic-pair-equivalence). -/
def cyclicDiagram {D : Type*} [Category D] {n : ℕ}
    (J : Fin (n + 1) → D ⥤ C) : D ⥤ (Discrete (Fin (n + 1)) ⥤ C) :=
  Functor.pi' J ⋙ (piEquivalenceFunctorDiscrete _ _).functor

/-- Adjacent and closing natural squares assemble into the cyclic diagram square.
Source: Weil II (1.1.12), componentwise Frobenius restriction.
(blueprint: lem-dl-a1-cyclic-pair-equivalence). -/
def cyclicDiagramSquare {D : Type*} [Category D] (F : D ⥤ D) (P : C ⥤ C)
    (n : ℕ) (J : Fin (n + 1) → D ⥤ C)
    (edge : ∀ i : Fin n, J i.succ ≅ F ⋙ J i.castSucc)
    (close : J 0 ⋙ P ≅ F ⋙ J (Fin.last n)) :
    cyclicDiagram J ⋙ cyclicShift P n ≅ F ⋙ cyclicDiagram J := by
  let ev (i : Fin (n + 1)) :
      cyclicDiagram J ⋙ (evaluation (Discrete (Fin (n + 1))) C).obj ⟨i⟩ ≅ J i := by
    change (Functor.pi' J ⋙ (piEquivalenceFunctorDiscrete _ _).functor) ⋙ _ ≅ _
    exact Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      (piEquivalenceFunctorDiscreteCompEvaluationIso C i) ≪≫ Functor.pi'CompEval J i
  let q : ∀ i : Fin (n + 1),
      cyclicDiagram J ⋙ cyclicShiftComponent P n i ≅ F ⋙ J i := by
    intro i
    induction i using Fin.lastCases with
    | last =>
      simpa only [cyclicShiftComponent, Fin.lastCases_last] using
        (Functor.associator (cyclicDiagram J)
          ((evaluation (Discrete (Fin (n + 1))) C).obj ⟨0⟩) P).symm ≪≫
            Functor.isoWhiskerRight (ev 0) P ≪≫ close
    | cast i =>
      simpa only [cyclicShiftComponent, Fin.lastCases_castSucc] using ev i.succ ≪≫ edge i
  refine NatIso.ofComponents
    (fun M ↦ Discrete.natIso (fun ⟨i⟩ ↦ (q i).app M)) ?_
  intro M N f
  apply NatTrans.ext
  funext ⟨i⟩
  exact (q i).hom.naturality f

/-- Cyclic objects are fixed pairs for the twisted shift. The invertible structure
natural transformation is exactly the tuple of intermediate and closing isomorphisms.
The algebra morphism square gives precisely the equations in the source node.
Source: Weil II, paragraph after (1.1.10), p.152.
(blueprint: lem-dl-a1-cyclic-pair-equivalence) -/
abbrev CyclicTuple (P : C ⥤ C) (n : ℕ) := IsoAlgebra (cyclicShift P n)

/-- The componentwise evaluation of a cyclic tuple, including on morphisms.
Source: Weil II, paragraph after (1.1.10), p.152.
(blueprint: lem-dl-a1-cyclic-pair-equivalence) -/
def cyclicEval (P : C ⥤ C) (n : ℕ) (i : Fin (n + 1)) : CyclicTuple P n ⥤ C :=
  IsoAlgebra.forget (cyclicShift P n) ⋙ (evaluation (Discrete (Fin (n + 1))) C).obj ⟨i⟩

/-- Partial products `r_i : A_i ≅ A_0`, with `r_0 = 1` and `r_(i+1) = a_i ≫ r_i`.
Source: Weil II, paragraph after (1.1.10), p.152, normalization calculation.
(blueprint: lem-dl-a1-cyclic-pair-equivalence) -/
def cyclicPartialProduct (P : C ⥤ C) (n : ℕ) (A : CyclicTuple P n) :
    ∀ i : Fin (n + 1), A.carrier.obj ⟨i⟩ ≅ A.carrier.obj ⟨0⟩ :=
  Fin.induction (Iso.refl _) fun i r ↦
    (by simpa [cyclicShift, cyclicShiftComponent] using
      ((evaluation (Discrete (Fin (n + 1))) C).obj ⟨i.castSucc⟩).mapIso A.str) ≪≫ r

/-- The return isomorphism, the closing arrow followed by the partial product.
Source: Weil II, paragraph after (1.1.10), p.152.
(blueprint: lem-dl-a1-cyclic-pair-equivalence) -/
def cyclicReturnIso (P : C ⥤ C) (n : ℕ) (A : CyclicTuple P n) :
    (P).obj (A.carrier.obj ⟨0⟩) ≅ A.carrier.obj ⟨0⟩ :=
  (by simpa [cyclicShift, cyclicShiftComponent] using
    ((evaluation (Discrete (Fin (n + 1))) C).obj ⟨Fin.last n⟩).mapIso A.str) ≪≫
    cyclicPartialProduct P n A (Fin.last n)

/-- The specified constant tuple: identities at intermediate edges and the original
fixed-pair structure at the closing edge.
Source: Weil II, paragraph after (1.1.10), p.152, inverse normalization.
(blueprint: lem-dl-a1-cyclic-pair-equivalence) -/
def cyclicConstantObj (P : C ⥤ C) (n : ℕ) (B : IsoAlgebra (P)) :
    CyclicTuple P n :=
  IsoAlgebra.mk (Discrete.functor fun _ : Fin (n + 1) ↦ B.carrier)
    (Discrete.natIso fun ⟨i⟩ ↦ by
      induction i using Fin.lastCases with
      | last => simpa [cyclicShift, cyclicShiftComponent] using B.str
      | cast j => exact (by
          simpa [cyclicShift, cyclicShiftComponent] using Iso.refl B.carrier))

private def cyclicEdge (P : C ⥤ C) (n : ℕ) (A : CyclicTuple P n) (i : Fin n) :
    A.carrier.obj ⟨i.succ⟩ ≅ A.carrier.obj ⟨i.castSucc⟩ := by
  simpa [cyclicShift, cyclicShiftComponent] using
    ((evaluation (Discrete (Fin (n + 1))) C).obj ⟨i.castSucc⟩).mapIso A.str

private def cyclicClose (P : C ⥤ C) (n : ℕ) (A : CyclicTuple P n) :
    (P).obj (A.carrier.obj ⟨0⟩) ≅ A.carrier.obj ⟨Fin.last n⟩ := by
  simpa [cyclicShift, cyclicShiftComponent] using
    ((evaluation (Discrete (Fin (n + 1))) C).obj ⟨Fin.last n⟩).mapIso A.str

private lemma cast_iso_source {X X' Y : C} (e : X = X') (a : X ≅ Y)
    (h : (X ≅ Y) = (X' ≅ Y)) : cast h a = eqToIso e.symm ≪≫ a := by
  cases e
  have hh : h = rfl := Subsingleton.elim _ _
  rw [hh]
  ext
  simp

private lemma transport_square {D : Type*} [Category D] {F G : D ⥤ C}
    (e : F = G) {A B : D} {X Y : C} (a : F.obj A ≅ X) (b : F.obj B ≅ Y)
    (f : A ⟶ B) (g : X ⟶ Y) (h : F.map f ≫ b.hom = a.hom ≫ g) :
    G.map f ≫ (eqToIso (Functor.congr_obj e B).symm ≪≫ b).hom =
      (eqToIso (Functor.congr_obj e A).symm ≪≫ a).hom ≫ g := by
  subst G
  simpa using h

private lemma shiftComponent_edge (P : C ⥤ C) (n : ℕ) (i : Fin n) :
    cyclicShiftComponent P n i.castSucc =
      (evaluation (Discrete (Fin (n + 1))) C).obj ⟨i.succ⟩ := by
  unfold cyclicShiftComponent
  rw [Fin.lastCases_castSucc]

private lemma shiftComponent_close (P : C ⥤ C) (n : ℕ) :
    cyclicShiftComponent P n (Fin.last n) =
      (evaluation (Discrete (Fin (n + 1))) C).obj ⟨0⟩ ⋙ P := by
  unfold cyclicShiftComponent
  rw [Fin.lastCases_last]

private lemma edge_cast (P : C ⥤ C) (n : ℕ) (A : CyclicTuple P n) (i : Fin n) :
    cyclicEdge P n A i =
      eqToIso (Functor.congr_obj (shiftComponent_edge P n i) A.carrier).symm ≪≫
        ((evaluation (Discrete (Fin (n + 1))) C).obj ⟨i.castSucc⟩).mapIso A.str := by
  change cast _ _ = _
  exact cast_iso_source (Functor.congr_obj (shiftComponent_edge P n i) A.carrier) _ _

private lemma close_cast (P : C ⥤ C) (n : ℕ) (A : CyclicTuple P n) :
    cyclicClose P n A =
      eqToIso (Functor.congr_obj (shiftComponent_close P n) A.carrier).symm ≪≫
        ((evaluation (Discrete (Fin (n + 1))) C).obj ⟨Fin.last n⟩).mapIso A.str := by
  change cast _ _ = _
  exact cast_iso_source (Functor.congr_obj (shiftComponent_close P n) A.carrier) _ _

private lemma partial_zero (P : C ⥤ C) (n : ℕ) (A : CyclicTuple P n) :
    (cyclicPartialProduct P n A 0).hom = 𝟙 _ := by
  rfl

private lemma partial_succ (P : C ⥤ C) (n : ℕ) (A : CyclicTuple P n) (i : Fin n) :
    (cyclicPartialProduct P n A i.succ).hom =
      (cyclicEdge P n A i).hom ≫ (cyclicPartialProduct P n A i.castSucc).hom := by
  unfold cyclicPartialProduct
  rw [Fin.induction_succ]
  rfl

private lemma edge_naturality (P : C ⥤ C) (n : ℕ) {A B : CyclicTuple P n}
    (f : A ⟶ B) (i : Fin n) :
    f.hom.f.app ⟨i.succ⟩ ≫ (cyclicEdge P n B i).hom =
      (cyclicEdge P n A i).hom ≫ f.hom.f.app ⟨i.castSucc⟩ := by
  rw [edge_cast, edge_cast]
  exact transport_square (shiftComponent_edge P n i) _ _ f.hom.f
    (f.hom.f.app ⟨i.castSucc⟩) (congr_app f.hom.h ⟨i.castSucc⟩)

private lemma partial_naturality (P : C ⥤ C) (n : ℕ) {A B : CyclicTuple P n}
    (f : A ⟶ B) (i : Fin (n + 1)) :
    f.hom.f.app ⟨i⟩ ≫ (cyclicPartialProduct P n B i).hom =
      (cyclicPartialProduct P n A i).hom ≫ f.hom.f.app ⟨0⟩ := by
  induction i using Fin.induction with
  | zero => simp [partial_zero]
  | succ i ih =>
    rw [partial_succ, partial_succ, ← Category.assoc, edge_naturality,
      Category.assoc, ih, Category.assoc]

private lemma close_naturality (P : C ⥤ C) (n : ℕ) {A B : CyclicTuple P n}
    (f : A ⟶ B) :
    (P).map (f.hom.f.app ⟨0⟩) ≫ (cyclicClose P n B).hom =
      (cyclicClose P n A).hom ≫ f.hom.f.app ⟨Fin.last n⟩ := by
  rw [close_cast, close_cast]
  exact transport_square (shiftComponent_close P n) _ _ f.hom.f
    (f.hom.f.app ⟨Fin.last n⟩) (congr_app f.hom.h ⟨Fin.last n⟩)

private lemma return_naturality (P : C ⥤ C) (n : ℕ) {A B : CyclicTuple P n}
    (f : A ⟶ B) :
    (P).map (f.hom.f.app ⟨0⟩) ≫ (cyclicReturnIso P n B).hom =
      (cyclicReturnIso P n A).hom ≫ f.hom.f.app ⟨0⟩ := by
  change _ ≫ ((cyclicClose P n B).hom ≫ _) =
    ((cyclicClose P n A).hom ≫ _) ≫ _
  rw [← Category.assoc, close_naturality, Category.assoc, partial_naturality, Category.assoc]

private def returnFunctor (P : C ⥤ C) (n : ℕ) :
    CyclicTuple P n ⥤ IsoAlgebra (P) where
  obj A := IsoAlgebra.mk (A.carrier.obj ⟨0⟩) (cyclicReturnIso P n A)
  map f := ObjectProperty.homMk
    { f := f.hom.f.app ⟨0⟩
      h := return_naturality P n f }
  map_id _ := ObjectProperty.hom_ext _ (Algebra.Hom.ext (by rfl))
  map_comp _ _ := ObjectProperty.hom_ext _ (Algebra.Hom.ext (by rfl))

private lemma transport_square_iff {D : Type*} [Category D] {F G : D ⥤ C}
    (e : F = G) {A B : D} {X Y : C} (a : F.obj A ≅ X) (b : F.obj B ≅ Y)
    (f : A ⟶ B) (g : X ⟶ Y) :
    (G.map f ≫ (eqToIso (Functor.congr_obj e B).symm ≪≫ b).hom =
      (eqToIso (Functor.congr_obj e A).symm ≪≫ a).hom ≫ g) ↔
        F.map f ≫ b.hom = a.hom ≫ g := by
  subst G
  simp

private lemma cyclic_square (P : C ⥤ C) (n : ℕ) {A B : CyclicTuple P n}
    (f : A.carrier ⟶ B.carrier)
    (hEdge : ∀ i : Fin n, f.app ⟨i.succ⟩ ≫ (cyclicEdge P n B i).hom =
      (cyclicEdge P n A i).hom ≫ f.app ⟨i.castSucc⟩)
    (hClose : (P).map (f.app ⟨0⟩) ≫ (cyclicClose P n B).hom =
      (cyclicClose P n A).hom ≫ f.app ⟨Fin.last n⟩) :
    (cyclicShift P n).map f ≫ B.obj.str = A.obj.str ≫ f := by
  ext ⟨i⟩
  induction i using Fin.lastCases with
  | last =>
    have h := hClose
    rw [close_cast, close_cast] at h
    exact (transport_square_iff (shiftComponent_close P n) _ _ f
      (f.app ⟨Fin.last n⟩)).mp h
  | cast j =>
    have h := hEdge j
    rw [edge_cast, edge_cast] at h
    exact (transport_square_iff (shiftComponent_edge P n j) _ _ f
      (f.app ⟨j.castSucc⟩)).mp h

private def constantStructureIso (P : C ⥤ C) (n : ℕ)
    (B : IsoAlgebra (P)) (i : Fin (n + 1)) :
    ((cyclicShift P n).obj (Discrete.functor fun _ : Fin (n + 1) ↦ B.carrier)).obj
      ⟨i⟩ ≅ B.carrier := by
  induction i using Fin.lastCases with
  | last => simpa [cyclicShift, cyclicShiftComponent] using B.str
  | cast j => exact (by
      simpa [cyclicShift, cyclicShiftComponent] using Iso.refl B.carrier)

private lemma constant_edge (P : C ⥤ C) (n : ℕ)
    (B : IsoAlgebra (P)) (i : Fin n) :
    cyclicEdge P n (cyclicConstantObj P n B) i = Iso.refl B.carrier := by
  apply eq_of_heq
  unfold cyclicEdge
  change HEq (cast _ _) _
  rw [cast_heq_iff_heq]
  have h : (((evaluation (Discrete (Fin (n + 1))) C).obj ⟨i.castSucc⟩).mapIso
      (cyclicConstantObj P n B).str) = constantStructureIso P n B i.castSucc := by
    apply Iso.ext
    rfl
  rw [h]
  change HEq (constantStructureIso P n B i.castSucc) (Iso.refl B.carrier)
  unfold constantStructureIso
  rw [Fin.lastCases_castSucc]
  change HEq (cast _ _) _
  simp

private lemma constant_close (P : C ⥤ C) (n : ℕ)
    (B : IsoAlgebra (P)) :
    cyclicClose P n (cyclicConstantObj P n B) = B.str := by
  apply eq_of_heq
  unfold cyclicClose
  change HEq (cast _ _) _
  rw [cast_heq_iff_heq]
  have h : (((evaluation (Discrete (Fin (n + 1))) C).obj ⟨Fin.last n⟩).mapIso
      (cyclicConstantObj P n B).str) = constantStructureIso P n B (Fin.last n) := by
    apply Iso.ext
    rfl
  rw [h]
  change HEq (constantStructureIso P n B (Fin.last n)) B.str
  unfold constantStructureIso
  rw [Fin.lastCases_last]
  change HEq (cast _ _) _
  simp

private def constantFunctor (P : C ⥤ C) (n : ℕ) :
    IsoAlgebra (P) ⥤ CyclicTuple P n where
  obj := cyclicConstantObj P n
  map f := ObjectProperty.homMk
    { f := Discrete.natTrans fun _ ↦ f.hom.f
      h := cyclic_square P n _
        (fun i ↦ by
          simp only [Discrete.natTrans_app, constant_edge, Iso.refl_hom]
          exact (Category.comp_id _).trans (Category.id_comp _).symm)
        (by
          simp only [Discrete.natTrans_app, constant_close]
          exact f.hom.h) }
  map_id _ := ObjectProperty.hom_ext _ (Algebra.Hom.ext (by ext; rfl))
  map_comp _ _ := ObjectProperty.hom_ext _ (Algebra.Hom.ext (by ext; rfl))

private lemma partial_constant (P : C ⥤ C) (n : ℕ)
    (B : IsoAlgebra (P)) (i : Fin (n + 1)) :
    (cyclicPartialProduct P n (cyclicConstantObj P n B) i).hom = 𝟙 B.carrier := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    rw [partial_succ, constant_edge, Iso.refl_hom, ih]
    exact Category.id_comp _

private lemma return_constant (P : C ⥤ C) (n : ℕ)
    (B : IsoAlgebra (P)) :
    (cyclicReturnIso P n (cyclicConstantObj P n B)).hom = B.str.hom := by
  change (cyclicClose P n (cyclicConstantObj P n B)).hom ≫
    (cyclicPartialProduct P n (cyclicConstantObj P n B) (Fin.last n)).hom = _
  rw [constant_close, partial_constant]
  exact Category.comp_id _

private def normalizationUnit (P : C ⥤ C) (n : ℕ) :
    𝟭 (CyclicTuple P n) ≅ returnFunctor P n ⋙ constantFunctor P n :=
  NatIso.ofComponents (fun A ↦ ObjectProperty.isoMk _
    (Algebra.isoMk (Discrete.natIso fun ⟨i⟩ ↦ cyclicPartialProduct P n A i)
      (cyclic_square P n _
        (fun i ↦ by
          change (cyclicPartialProduct P n A i.succ).hom ≫
            (cyclicEdge P n (cyclicConstantObj P n ((returnFunctor P n).obj A)) i).hom = _
          rw [constant_edge, Iso.refl_hom]
          change (cyclicPartialProduct P n A i.succ).hom ≫ 𝟙 (A.carrier.obj ⟨0⟩) =
            (cyclicEdge P n A i).hom ≫ (cyclicPartialProduct P n A i.castSucc).hom
          rw [Category.comp_id, partial_succ])
        (by
          change (P).map (cyclicPartialProduct P n A 0).hom ≫
            (cyclicClose P n (cyclicConstantObj P n ((returnFunctor P n).obj A))).hom = _
          rw [partial_zero, Functor.map_id, Category.id_comp, constant_close]
          rfl)))) (by
    intro A B f
    apply ObjectProperty.hom_ext _
    apply Algebra.Hom.ext
    ext ⟨i⟩
    exact partial_naturality P n f i)

private def normalizationCounit (P : C ⥤ C) (n : ℕ) :
    constantFunctor P n ⋙ returnFunctor P n ≅ 𝟭 (IsoAlgebra (P)) :=
  NatIso.ofComponents (fun B ↦ ObjectProperty.isoMk _
    (Algebra.isoMk (Iso.refl _) (by
      change (P).map (𝟙 B.carrier) ≫ B.str.hom =
        (cyclicReturnIso P n (cyclicConstantObj P n B)).hom ≫ 𝟙 B.carrier
      rw [Functor.map_id, Category.id_comp, return_constant]
      exact (Category.comp_id _).symm))) (by
    intro A B f
    apply ObjectProperty.hom_ext _
    apply Algebra.Hom.ext
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

private def normalizationEquivalence (P : C ⥤ C) (n : ℕ) :
    CyclicTuple P n ≌ IsoAlgebra (P) where
  functor := returnFunctor P n
  inverse := constantFunctor P n
  unitIso := normalizationUnit P n
  counitIso := normalizationCounit P n
  functor_unitIso_comp A := by
    apply ObjectProperty.hom_ext _
    apply Algebra.Hom.ext
    change (cyclicPartialProduct P n A 0).hom ≫ 𝟙 _ = 𝟙 _
    rw [partial_zero, Category.id_comp]


/-- The cyclic equivalence has the specified return and constant-tuple formulas.
Source: Weil II, paragraph after (1.1.10), cyclic normalization.
(blueprint: lem-dl-a1-cyclic-pair-equivalence).

Proof: use successive products of the intermediate invertible arrows as the unit.
The return functor evaluates the carrier and every map at component zero; its
structure is the closing arrow followed by the last partial product. The inverse
inserts the specified constant tuple. These three formulas are definitional for
normalizationEquivalence. -/
theorem cyclic_pair_equivalence_with_return (P : C ⥤ C) (n : ℕ) :
    ∃ e : CyclicTuple P n ≌ IsoAlgebra P,
      e.functor ⋙ IsoAlgebra.forget P = cyclicEval P n 0 ∧
      (∀ A, e.functor.obj A = IsoAlgebra.mk (A.carrier.obj ⟨0⟩)
        (cyclicReturnIso P n A)) ∧
      ∀ B, e.inverse.obj B = cyclicConstantObj P n B := by
  exact ⟨normalizationEquivalence P n, rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- Cyclic normalization for an arbitrary closing endofunctor, without a root hypothesis.
Source: Weil II, paragraph after (1.1.10), cyclic normalization.
(blueprint: lem-dl-a1-cyclic-pair-equivalence).

Proof: take the equivalence with the specified return formulas. -/
theorem cyclic_pair_equivalence (P : C ⥤ C) (n : ℕ) :
    Nonempty (CyclicTuple P n ≌ IsoAlgebra P) := by
  obtain ⟨e, _⟩ := cyclic_pair_equivalence_with_return P n
  exact ⟨e⟩

end CategoryTheory.Endofunctor.ComponentCycle
