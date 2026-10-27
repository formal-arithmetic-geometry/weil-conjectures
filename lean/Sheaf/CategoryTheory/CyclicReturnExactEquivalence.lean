module

public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.EndoFunctor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact

/-! # Exact cyclic return equivalence

Source: Deligne, Weil II, paragraph after (1.1.10), p.152; the abstract cyclic
normalization and universal-property calculations in the DAG node.
(blueprint: lem-zl-cyclic-return-exact-equivalence)

The positive cycle length is `n + 1`. Cyclic objects are fixed pairs for the twisted
shift on discrete diagrams. This reuses the upstream category of fixed pairs, with
componentwise morphisms and their commuting squares, rather than copying it.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.unusedSectionVars false

universe u v

namespace CategoryTheory.Endofunctor

open Limits

variable {C : Type u} [Category.{v} C]

/-- One component of the twisted shift, expressed using existing evaluation functors.
Source: Weil II, paragraph after (1.1.10), p.152, cyclic normalization.
(blueprint: lem-zl-cyclic-return-exact-equivalence) -/
def cyclicShiftComponent (P : C ⥤ C) (n : ℕ) (i : Fin (n + 1)) :
    (Discrete (Fin (n + 1)) ⥤ C) ⥤ C :=
  Fin.lastCases ((evaluation (Discrete (Fin (n + 1))) C).obj ⟨0⟩ ⋙ P.iterate (n + 1))
    (fun j ↦ (evaluation (Discrete (Fin (n + 1))) C).obj ⟨j.succ⟩) i

/-- The twisted shift on a tuple of length `n+1`: its entries are `A_(i+1)` at
`i < n` and `P^(n+1) A_0` at the last index. On maps it has the same formulas.
Source: Weil II, paragraph after (1.1.10), p.152, cyclic normalization.
(blueprint: lem-zl-cyclic-return-exact-equivalence) -/
def cyclicShift (P : C ⥤ C) (n : ℕ) :
    (Discrete (Fin (n + 1)) ⥤ C) ⥤ (Discrete (Fin (n + 1)) ⥤ C) where
  obj A := Discrete.functor fun i ↦ (cyclicShiftComponent P n i).obj A
  map f := Discrete.natTrans fun i ↦ (cyclicShiftComponent P n i.as).map f
  map_id A := by ext; simp
  map_comp f g := by ext; simp

/-- Cyclic objects are fixed pairs for the twisted shift. The invertible structure
natural transformation is exactly the tuple of intermediate and closing isomorphisms.
The algebra morphism square gives precisely the equations in the source node.
Source: Weil II, paragraph after (1.1.10), p.152.
(blueprint: lem-zl-cyclic-return-exact-equivalence) -/
abbrev CyclicTuple (P : C ⥤ C) (n : ℕ) := IsoAlgebra (cyclicShift P n)

/-- The componentwise evaluation of a cyclic tuple, including on morphisms.
Source: Weil II, paragraph after (1.1.10), p.152.
(blueprint: lem-zl-cyclic-return-exact-equivalence) -/
def cyclicEval (P : C ⥤ C) (n : ℕ) (i : Fin (n + 1)) : CyclicTuple P n ⥤ C :=
  IsoAlgebra.forget (cyclicShift P n) ⋙ (evaluation (Discrete (Fin (n + 1))) C).obj ⟨i⟩

/-- Partial products `r_i : A_i ≅ A_0`, with `r_0 = 1` and `r_(i+1) = a_i ≫ r_i`.
Source: Weil II, paragraph after (1.1.10), p.152, normalization calculation.
(blueprint: lem-zl-cyclic-return-exact-equivalence) -/
def cyclicPartialProduct (P : C ⥤ C) (n : ℕ) (A : CyclicTuple P n) :
    ∀ i : Fin (n + 1), A.carrier.obj ⟨i⟩ ≅ A.carrier.obj ⟨0⟩ :=
  Fin.induction (Iso.refl _) fun i r ↦
    (by simpa [cyclicShift, cyclicShiftComponent] using
      ((evaluation (Discrete (Fin (n + 1))) C).obj ⟨i.castSucc⟩).mapIso A.str) ≪≫ r

/-- The return isomorphism, the closing arrow followed by the partial product.
Source: Weil II, paragraph after (1.1.10), p.152.
(blueprint: lem-zl-cyclic-return-exact-equivalence) -/
def cyclicReturnIso (P : C ⥤ C) (n : ℕ) (A : CyclicTuple P n) :
    (P.iterate (n + 1)).obj (A.carrier.obj ⟨0⟩) ≅ A.carrier.obj ⟨0⟩ :=
  (by simpa [cyclicShift, cyclicShiftComponent] using
    ((evaluation (Discrete (Fin (n + 1))) C).obj ⟨Fin.last n⟩).mapIso A.str) ≪≫
    cyclicPartialProduct P n A (Fin.last n)

/-- The specified constant tuple: identities at intermediate edges and the original
fixed-pair structure at the closing edge.
Source: Weil II, paragraph after (1.1.10), p.152, inverse normalization.
(blueprint: lem-zl-cyclic-return-exact-equivalence) -/
def cyclicConstantObj (P : C ⥤ C) (n : ℕ) (B : IsoAlgebra (P.iterate (n + 1))) :
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
    (P.iterate (n + 1)).obj (A.carrier.obj ⟨0⟩) ≅ A.carrier.obj ⟨Fin.last n⟩ := by
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
      (evaluation (Discrete (Fin (n + 1))) C).obj ⟨0⟩ ⋙ P.iterate (n + 1) := by
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
    (P.iterate (n + 1)).map (f.hom.f.app ⟨0⟩) ≫ (cyclicClose P n B).hom =
      (cyclicClose P n A).hom ≫ f.hom.f.app ⟨Fin.last n⟩ := by
  rw [close_cast, close_cast]
  exact transport_square (shiftComponent_close P n) _ _ f.hom.f
    (f.hom.f.app ⟨Fin.last n⟩) (congr_app f.hom.h ⟨Fin.last n⟩)

private lemma return_naturality (P : C ⥤ C) (n : ℕ) {A B : CyclicTuple P n}
    (f : A ⟶ B) :
    (P.iterate (n + 1)).map (f.hom.f.app ⟨0⟩) ≫ (cyclicReturnIso P n B).hom =
      (cyclicReturnIso P n A).hom ≫ f.hom.f.app ⟨0⟩ := by
  change _ ≫ ((cyclicClose P n B).hom ≫ _) =
    ((cyclicClose P n A).hom ≫ _) ≫ _
  rw [← Category.assoc, close_naturality, Category.assoc, partial_naturality, Category.assoc]

private def returnFunctor (P : C ⥤ C) (n : ℕ) :
    CyclicTuple P n ⥤ IsoAlgebra (P.iterate (n + 1)) where
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
    (hClose : (P.iterate (n + 1)).map (f.app ⟨0⟩) ≫ (cyclicClose P n B).hom =
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
    (B : IsoAlgebra (P.iterate (n + 1))) (i : Fin (n + 1)) :
    ((cyclicShift P n).obj (Discrete.functor fun _ : Fin (n + 1) ↦ B.carrier)).obj
      ⟨i⟩ ≅ B.carrier := by
  induction i using Fin.lastCases with
  | last => simpa [cyclicShift, cyclicShiftComponent] using B.str
  | cast j => exact (by
      simpa [cyclicShift, cyclicShiftComponent] using Iso.refl B.carrier)

private lemma constant_edge (P : C ⥤ C) (n : ℕ)
    (B : IsoAlgebra (P.iterate (n + 1))) (i : Fin n) :
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
    (B : IsoAlgebra (P.iterate (n + 1))) :
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
    IsoAlgebra (P.iterate (n + 1)) ⥤ CyclicTuple P n where
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
    (B : IsoAlgebra (P.iterate (n + 1))) (i : Fin (n + 1)) :
    (cyclicPartialProduct P n (cyclicConstantObj P n B) i).hom = 𝟙 B.carrier := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    rw [partial_succ, constant_edge, Iso.refl_hom, ih]
    exact Category.id_comp _

private lemma return_constant (P : C ⥤ C) (n : ℕ)
    (B : IsoAlgebra (P.iterate (n + 1))) :
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
          change (P.iterate (n + 1)).map (cyclicPartialProduct P n A 0).hom ≫
            (cyclicClose P n (cyclicConstantObj P n ((returnFunctor P n).obj A))).hom = _
          rw [partial_zero, Functor.map_id, Category.id_comp, constant_close]
          rfl)))) (by
    intro A B f
    apply ObjectProperty.hom_ext _
    apply Algebra.Hom.ext
    ext ⟨i⟩
    exact partial_naturality P n f i)

private def normalizationCounit (P : C ⥤ C) (n : ℕ) :
    constantFunctor P n ⋙ returnFunctor P n ≅ 𝟭 (IsoAlgebra (P.iterate (n + 1))) :=
  NatIso.ofComponents (fun B ↦ ObjectProperty.isoMk _
    (Algebra.isoMk (Iso.refl _) (by
      change (P.iterate (n + 1)).map (𝟙 B.carrier) ≫ B.str.hom =
        (cyclicReturnIso P n (cyclicConstantObj P n B)).hom ≫ 𝟙 B.carrier
      rw [Functor.map_id, Category.id_comp, return_constant]
      exact (Category.comp_id _).symm))) (by
    intro A B f
    apply ObjectProperty.hom_ext _
    apply Algebra.Hom.ext
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

private def normalizationEquivalence (P : C ⥤ C) (n : ℕ) :
    CyclicTuple P n ≌ IsoAlgebra (P.iterate (n + 1)) where
  functor := returnFunctor P n
  inverse := constantFunctor P n
  unitIso := normalizationUnit P n
  counitIso := normalizationCounit P n
  functor_unitIso_comp A := by
    apply ObjectProperty.hom_ext _
    apply Algebra.Hom.ext
    change (cyclicPartialProduct P n A 0).hom ≫ 𝟙 _ = 𝟙 _
    rw [partial_zero, Category.id_comp]

private lemma return_constant_obj (P : C ⥤ C) (n : ℕ)
    (B : IsoAlgebra (P.iterate (n + 1))) :
    (returnFunctor P n).obj ((constantFunctor P n).obj B) = B := by
  apply ObjectProperty.FullSubcategory.ext
  have h := return_constant P n B
  cases B with
  | mk B hB =>
    cases B
    dsimp only [returnFunctor, Functor.comp_obj, constantFunctor, IsoAlgebra.mk_obj]
    congr 1

private lemma isoAlgebra_eqToHom {F : C ⥤ C} {A B : IsoAlgebra F} (h : A = B) :
    (eqToHom h).hom.f = eqToHom (congrArg IsoAlgebra.carrier h) := by
  cases h
  rfl

private lemma constant_return_eq (P : C ⥤ C) (n : ℕ) :
    constantFunctor P n ⋙ returnFunctor P n = 𝟭 (IsoAlgebra (P.iterate (n + 1))) := by
  refine Functor.ext (return_constant_obj P n) ?_
  intro A B f
  apply ObjectProperty.hom_ext _
  apply Algebra.Hom.ext
  simp only [IsoAlgebra.comp_hom_f, isoAlgebra_eqToHom]
  have hA : congrArg IsoAlgebra.carrier (return_constant_obj P n A) = rfl :=
    Subsingleton.elim _ _
  have hB : congrArg IsoAlgebra.carrier (return_constant_obj P n B) = rfl :=
    Subsingleton.elim _ _
  simp [returnFunctor, constantFunctor]

private lemma equivalence_subobjects {D : Type*} [Category D] [Abelian C] [Abelian D]
    (E : C ≌ D) [E.functor.Additive] (A : C) :
    ∃ e : Subobject A ≃o Subobject (E.functor.obj A),
      (∀ U : Subobject A, e U = Subobject.mk (E.functor.map U.arrow)) ∧
      (∀ (U V : Subobject A) (h : U ≤ V),
        Nonempty (E.functor.obj (cokernel (Subobject.ofLE U V h)) ≅
          cokernel (Subobject.ofLE (e U) (e V) (e.monotone h)))) ∧
      (∀ k : ℕ,
        ∃ eF : (Fin k →o Subobject A) ≃ (Fin k →o Subobject (E.functor.obj A)),
          ∀ (s : Fin k →o Subobject A) (i : Fin k), (eF s) i = e (s i)) := by
  let e := (Subobject.lowerEquivalence (MonoOver.congr A E)).toOrderIso
  have he (U : Subobject A) : e U = Subobject.mk (E.functor.map U.arrow) := by
    conv_lhs => rw [← Subobject.mk_arrow U]
    rfl
  refine ⟨e, he, ?_, ?_⟩
  · intro U V h
    let a : (e U : D) ≅ E.functor.obj (U : C) :=
      eqToIso (congrArg (fun S : Subobject (E.functor.obj A) ↦ (S : D)) (he U)) ≪≫
        Subobject.underlyingIso (E.functor.map U.arrow)
    let b : (e V : D) ≅ E.functor.obj (V : C) :=
      eqToIso (congrArg (fun S : Subobject (E.functor.obj A) ↦ (S : D)) (he V)) ≪≫
        Subobject.underlyingIso (E.functor.map V.arrow)
    have ha : a.hom ≫ E.functor.map U.arrow = (e U).arrow := by
      dsimp [a]
      simpa using Subobject.arrow_congr _ _ (he U)
    have hb : b.hom ≫ E.functor.map V.arrow = (e V).arrow := by
      dsimp [b]
      simpa using Subobject.arrow_congr _ _ (he V)
    refine ⟨PreservesCokernel.iso E.functor (Subobject.ofLE U V h) ≪≫
      (cokernel.mapIso (Subobject.ofLE (e U) (e V) (e.monotone h))
        (E.functor.map (Subobject.ofLE U V h)) a b ?_).symm⟩
    apply (cancel_mono (E.functor.map V.arrow)).1
    simp only [Category.assoc, hb, Subobject.ofLE_arrow, ← E.functor.map_comp, ha]
  · intro k
    refine ⟨{
      toFun := fun s ↦ { toFun := fun i ↦ e (s i), monotone' := e.monotone.comp s.monotone }
      invFun := fun s ↦
        { toFun := fun i ↦ e.symm (s i), monotone' := e.symm.monotone.comp s.monotone }
      left_inv := fun s ↦ by
        apply OrderHom.ext
        funext i
        exact e.symm_apply_apply (s i)
      right_inv := fun s ↦ by
        apply OrderHom.ext
        funext i
        exact e.apply_symm_apply (s i) }, fun _ _ ↦ rfl⟩

variable [Abelian C] (P : C ⥤ C) [P.Additive] [P.IsEquivalence] (n : ℕ)

/-- Every positive power of P is additive.
Source: Weil II, paragraph after (1.1.10), p.152; node proof steps 3--6.
(blueprint: lem-zl-cyclic-return-exact-equivalence)
Proof: start with the additive identity functor and compose successively with P.
Composition preserves addition, so induction gives the asserted power. -/
theorem cyclicPower_additive : (P.iterate (n + 1)).Additive := by
  have h : ∀ k : ℕ, (P.iterate k).Additive := by
    intro k
    induction k with
    | zero => exact inferInstanceAs (Functor.Additive (𝟭 C))
    | succ k ih =>
      let := ih
      exact inferInstanceAs (Functor.Additive (P.iterate k ⋙ P))
  exact h (n + 1)

attribute [instance] cyclicPower_additive

/-- Every positive power of P is an equivalence.
Source: Weil II, paragraph after (1.1.10), p.152; node proof steps 3--6.
(blueprint: lem-zl-cyclic-return-exact-equivalence)
Proof: the identity is an equivalence and composites of equivalences are equivalences.
Induct on the number of iterations, using the specified quasi-inverse of P at each step. -/
theorem cyclicPower_isEquivalence : (P.iterate (n + 1)).IsEquivalence := by
  have h : ∀ k : ℕ, (P.iterate k).IsEquivalence := by
    intro k
    induction k with
    | zero => exact inferInstanceAs (Functor.IsEquivalence (𝟭 C))
    | succ k ih =>
      let := ih
      exact inferInstanceAs (Functor.IsEquivalence (P.iterate k ⋙ P))
  exact h (n + 1)

attribute [instance] cyclicPower_isEquivalence

/-- The twisted shift is additive.
Source: Weil II, paragraph after (1.1.10), p.152; node proof step 3.
(blueprint: lem-zl-cyclic-return-exact-equivalence)
Proof: addition of natural transformations is pointwise. At each intermediate edge
shift is evaluation; at the last edge it is evaluation followed by `P^(n+1)`.
Both preserve addition, the latter by iterated additivity of `P`. -/
theorem cyclicShift_additive : (cyclicShift P n).Additive := by
  have h : ∀ i : Fin (n + 1), (cyclicShiftComponent P n i).Additive := by
    intro i
    induction i using Fin.lastCases with
    | last =>
      unfold cyclicShiftComponent
      rw [Fin.lastCases_last]
      infer_instance
    | cast j =>
      unfold cyclicShiftComponent
      rw [Fin.lastCases_castSucc]
      infer_instance
  constructor
  intro A B f g
  ext ⟨i⟩
  exact (cyclicShiftComponent P n i).map_add

private def shiftEvalIso (P : C ⥤ C) (n : ℕ) (i : Fin (n + 1)) :
    cyclicShift P n ⋙ (evaluation (Discrete (Fin (n + 1))) C).obj ⟨i⟩ ≅
      cyclicShiftComponent P n i :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp [cyclicShift])

attribute [instance] cyclicShift_additive

/-- The twisted shift preserves finite limits.
Source: Weil II, paragraph after (1.1.10), p.152; node proof steps 3--5.
(blueprint: lem-zl-cyclic-return-exact-equivalence)
Proof: limits in the discrete diagram category are componentwise. Evaluation
preserves them, and `P^(n+1)` preserves them as an iterated equivalence.
The pointwise limiting cones therefore give the claimed preservation. -/
theorem cyclicShift_preservesFiniteLimits : PreservesFiniteLimits (cyclicShift P n) := by
  have : (P.iterate (n + 1)).IsEquivalence := cyclicPower_isEquivalence P n
  apply preservesFiniteLimits_of_evaluation
  rintro ⟨i⟩
  have h : PreservesFiniteLimits (cyclicShiftComponent P n i) := by
    induction i using Fin.lastCases with
    | last =>
      unfold cyclicShiftComponent
      rw [Fin.lastCases_last]
      exact comp_preservesFiniteLimits _ _
    | cast j =>
      unfold cyclicShiftComponent
      rw [Fin.lastCases_castSucc]
      infer_instance
  exact preservesFiniteLimits_of_natIso (shiftEvalIso P n i).symm

attribute [instance] cyclicShift_preservesFiniteLimits

/-- The twisted shift preserves finite colimits.
Source: Weil II, paragraph after (1.1.10), p.152; node proof steps 3 and 6.
(blueprint: lem-zl-cyclic-return-exact-equivalence)
Proof: colimits in the discrete diagram category are componentwise. Evaluation
preserves them, as does the iterated equivalence `P^(n+1)`. Apply the componentwise
colimit universal property to the shifted cocone. -/
theorem cyclicShift_preservesFiniteColimits : PreservesFiniteColimits (cyclicShift P n) := by
  have : (P.iterate (n + 1)).IsEquivalence := cyclicPower_isEquivalence P n
  apply preservesFiniteColimits_of_evaluation
  rintro ⟨i⟩
  have h : PreservesFiniteColimits (cyclicShiftComponent P n i) := by
    induction i using Fin.lastCases with
    | last =>
      unfold cyclicShiftComponent
      rw [Fin.lastCases_last]
      exact comp_preservesFiniteColimits _ _
    | cast j =>
      unfold cyclicShiftComponent
      rw [Fin.lastCases_castSucc]
      infer_instance
  exact preservesFiniteColimits_of_natIso (shiftEvalIso P n i).symm

attribute [instance] cyclicShift_preservesFiniteColimits

/-- Component evaluation is additive on cyclic tuples.
Source: Weil II, paragraph after (1.1.10), p.152; node proof steps 3 and 9.
(blueprint: lem-zl-cyclic-return-exact-equivalence)
Proof: the upstream fixed-pair forgetful functor preserves addition, as does evaluation
on discrete diagrams, since their addition is pointwise. Their composite is additive. -/
theorem cyclicEval_additive (i : Fin (n + 1)) : (cyclicEval P n i).Additive := by
  dsimp only [cyclicEval]
  infer_instance

attribute [instance] cyclicEval_additive

/-- The return assignment is the specified exact equivalence, with its constant-tuple
quasi-inverse, partial-product unit, identity counit, componentwise abelian operations,
carrier detection of exactness, and transport of subobjects, quotients and finite chains.

Source: Deligne, Weil II, paragraph after (1.1.10), p.152; abstract cyclic normalization.
(blueprint: lem-zl-cyclic-return-exact-equivalence)

Proof plan, following all eleven steps of the node:
1. Compose the structure isomorphisms to form the return. Substituting each commuting
square proves the fixed-pair equation for the zeroth carrier map. Identities and
composition are componentwise. Constant tuples satisfy the intermediate equations
trivially and the closing equation by the original fixed-pair equation. Their return
is the original fixed pair on both objects and arrows.
2. The partial products satisfy r_i a_i = r_(i+1) and the closing square. Iterating the
morphism equations proves naturality. Their inverse components intertwine by cancelling
the invertible structure maps. The zeroth component and the partial products on constant
tuples are identities, so the identity counit and this unit satisfy both triangles.
3. Zero objects and binary biproducts are componentwise, with block diagonal structure
maps. At the closing edge use the canonical additive comparison for P^(n+1). Addition
and bilinearity are inherited on the commuting tuples.
4. Exactness of the power of P takes each carrier kernel to a kernel. The structure
square induces a map on kernels; the inverse structure square induces its inverse.
Cancel the kernel monomorphisms to verify the two inverse identities.
5. Ambient kernel lifts intertwine after composition with the kernel inclusions, by
the given morphism equations; monic cancellation proves the required squares. Uniqueness
is componentwise. The same construction with a single edge applies to fixed pairs.
6. Dually descend the structure and its inverse to cokernels. Cancel their epic
projections to prove inverseness. Test each descent equation after precomposition with
the projection to prove the structured cokernel universal property and uniqueness.
7. Componentwise inverses of an invertible tuple intertwine by rearranging its squares.
For each carrier morphism the coimage factor is monic (lem-weil-pbc-coimage-mono).
Its cokernel is also the cokernel of the original morphism, since the coimage projection
is epic. A monomorphism in an abelian category is the kernel of its cokernel. Kernel
uniqueness therefore makes the carrier coimage-image comparison invertible.
8. Structured kernels, cokernels and their universal factorizations are componentwise,
so their coimage-image comparison has these carrier comparisons. Lift their inverses
using step 7 and apply lem-weil-pbc-abelian-of-coimage-image-iso. Equivalently use the
upstream IsoAlgebra abelian structure for the exact twisted shift and the power of P.
9. Exactness is the zero composite and invertibility of the image-to-kernel comparison.
All these constructions are componentwise by steps 4--6; step 7 detects invertibility.
The partial products identify every carrier sequence with its zeroth sequence. Thus T
and S preserve and reflect exactness, and their explicit map formulas give additivity.
10. Full faithfulness preserves and reflects monos and lifts all inclusion
factorizations. This gives inverse order maps on subobjects, the inverse followed by
the inverse unit at the ambient object. Preservation of cokernels identifies quotients.
Apply these maps at every index of any finite chain; all successive quotients are the
quotients for its pairs of comparable subobjects. Zero and empty chains are included.
11. At n=0 there is just A_0 and the closing map P A_0 ≅ A_0; no intermediate indices
exist. The return is the closing map followed by the identity, S has one entry, and
r_0 is the identity. Thus this same statement includes the singleton case. -/
theorem cyclicReturnExactEquivalence :
    Nonempty (Abelian (CyclicTuple P n)) ∧
    Nonempty (Abelian (IsoAlgebra (P.iterate (n + 1)))) ∧
    (∀ i : Fin (n + 1),
      PreservesFiniteLimits (cyclicEval P n i) ∧
      PreservesFiniteColimits (cyclicEval P n i)) ∧
    PreservesFiniteLimits (IsoAlgebra.forget (P.iterate (n + 1))) ∧
    PreservesFiniteColimits (IsoAlgebra.forget (P.iterate (n + 1))) ∧
    (∀ A : CyclicTuple P n, ∀ i : Fin (n + 1), IsIso (A.str.hom.app ⟨i⟩)) ∧
    (∀ A : IsoAlgebra (P.iterate (n + 1)), IsIso A.str.hom) ∧
    (∀ K : ShortComplex (CyclicTuple P n),
      K.Exact ↔ ∀ i : Fin (n + 1), (K.map (cyclicEval P n i)).Exact) ∧
    (∀ K : ShortComplex (IsoAlgebra (P.iterate (n + 1))),
      K.Exact ↔ (K.map (IsoAlgebra.forget (P.iterate (n + 1)))).Exact) ∧
    ∃ E : CyclicTuple P n ≌ IsoAlgebra (P.iterate (n + 1)),
      (∀ A : CyclicTuple P n,
        E.functor.obj A = IsoAlgebra.mk (A.carrier.obj ⟨0⟩) (cyclicReturnIso P n A)) ∧
      (∀ (A B : CyclicTuple P n) (f : A ⟶ B),
        HEq (E.functor.map f).hom.f (f.hom.f.app ⟨0⟩)) ∧
      (∀ B : IsoAlgebra (P.iterate (n + 1)), E.inverse.obj B = cyclicConstantObj P n B) ∧
      (∀ (A B : IsoAlgebra (P.iterate (n + 1))) (f : A ⟶ B) (i : Fin (n + 1)),
        HEq ((E.inverse.map f).hom.f.app ⟨i⟩) f.hom.f) ∧
      E.inverse ⋙ E.functor = 𝟭 (IsoAlgebra (P.iterate (n + 1))) ∧
      (∀ (A : CyclicTuple P n) (i : Fin (n + 1)),
        HEq ((E.unitIso.hom.app A).hom.f.app ⟨i⟩) (cyclicPartialProduct P n A i).hom) ∧
      (∀ B : IsoAlgebra (P.iterate (n + 1)),
        HEq (E.counitIso.hom.app B).hom.f (𝟙 B.carrier)) ∧
      E.functor.Additive ∧ E.inverse.Additive ∧
      PreservesFiniteLimits E.functor ∧ PreservesFiniteColimits E.functor ∧
      PreservesFiniteLimits E.inverse ∧ PreservesFiniteColimits E.inverse ∧
      (∀ K : ShortComplex (CyclicTuple P n), (K.map E.functor).Exact ↔ K.Exact) ∧
      (∀ K : ShortComplex (IsoAlgebra (P.iterate (n + 1))),
        (K.map E.inverse).Exact ↔ K.Exact) ∧
      (∀ A : CyclicTuple P n,
        ∃ e : Subobject A ≃o Subobject (E.functor.obj A),
          (∀ U : Subobject A, e U = Subobject.mk (E.functor.map U.arrow)) ∧
          (∀ (U V : Subobject A) (h : U ≤ V),
            Nonempty (E.functor.obj (cokernel (Subobject.ofLE U V h)) ≅
              cokernel (Subobject.ofLE (e U) (e V) (e.monotone h)))) ∧
          (∀ k : ℕ,
            ∃ eF : (Fin k →o Subobject A) ≃ (Fin k →o Subobject (E.functor.obj A)),
              ∀ (s : Fin k →o Subobject A) (i : Fin k), (eF s) i = e (s i))) ∧
      (∀ A : IsoAlgebra (P.iterate (n + 1)),
        ∃ e : Subobject A ≃o Subobject (E.inverse.obj A),
          (∀ U : Subobject A, e U = Subobject.mk (E.inverse.map U.arrow)) ∧
          (∀ (U V : Subobject A) (h : U ≤ V),
            Nonempty (E.inverse.obj (cokernel (Subobject.ofLE U V h)) ≅
              cokernel (Subobject.ofLE (e U) (e V) (e.monotone h)))) ∧
          (∀ k : ℕ,
            ∃ eF : (Fin k →o Subobject A) ≃ (Fin k →o Subobject (E.inverse.obj A)),
              ∀ (s : Fin k →o Subobject A) (i : Fin k), (eF s) i = e (s i))) := by
  have hFaithful (F : C ⥤ C) : (IsoAlgebra.forget F).Faithful := by
    dsimp only [IsoAlgebra.forget]
    infer_instance
  let := hFaithful (P.iterate (n + 1))
  have hCyclicFaithful : (IsoAlgebra.forget (cyclicShift P n)).Faithful := by
    dsimp only [IsoAlgebra.forget]
    infer_instance
  have hEval (i : Fin (n + 1)) :
      PreservesFiniteLimits (cyclicEval P n i) ∧
        PreservesFiniteColimits (cyclicEval P n i) := by
    dsimp only [cyclicEval]
    exact ⟨comp_preservesFiniteLimits _ _, comp_preservesFiniteColimits _ _⟩
  have hCycExact (K : ShortComplex (CyclicTuple P n)) :
      K.Exact ↔ ∀ i : Fin (n + 1), (K.map (cyclicEval P n i)).Exact := by
    rw [← K.exact_map_iff_of_faithful (IsoAlgebra.forget (cyclicShift P n)),
      ShortComplex.exact_iff_evaluation]
    constructor
    · intro h i
      simpa only [cyclicEval, ShortComplex.map_comp] using h ⟨i⟩
    · intro h ⟨i⟩
      simpa only [cyclicEval, ShortComplex.map_comp] using h i
  refine ⟨⟨inferInstance⟩, ⟨inferInstance⟩, hEval, inferInstance, inferInstance,
    (fun A i ↦ inferInstance), (fun A ↦ inferInstance), hCycExact,
    (fun K ↦ (K.exact_map_iff_of_faithful (IsoAlgebra.forget (P.iterate (n + 1)))).symm), ?_⟩
  let E := normalizationEquivalence P n
  have hAdd : E.functor.Additive := by
    constructor
    intro A B f g
    apply ObjectProperty.hom_ext _
    apply Algebra.Hom.ext
    rfl
  have hInvAdd : E.inverse.Additive := by infer_instance
  let : E.symm.functor.Additive := hInvAdd
  refine ⟨E, (fun A ↦ rfl), (fun A B f ↦ HEq.rfl), (fun B ↦ rfl),
    (fun A B f i ↦ HEq.rfl), constant_return_eq P n,
    (fun A i ↦ HEq.rfl), (fun B ↦ HEq.rfl), hAdd, hInvAdd,
    inferInstance, inferInstance, inferInstance, inferInstance,
    (fun K ↦ K.exact_map_iff_of_faithful E.functor),
    (fun K ↦ K.exact_map_iff_of_faithful E.inverse),
    (fun A ↦ equivalence_subobjects E A),
    (fun A ↦ equivalence_subobjects E.symm A)⟩

end CategoryTheory.Endofunctor
