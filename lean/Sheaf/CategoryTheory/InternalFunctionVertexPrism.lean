/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.CategoryTheory.CondensedEquivariantBarData
public import Sheaf.Topology.ProfiniteCondensedRing
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.CategoryTheory.ProfiniteVertexPrismBoundary

/-! # The vertex prism for internal functions on profinite tuples

Source: Stacks Project, simplicial.tex, Tag 019S, lemma-homotopy-s-N and
 equation-homotopy-to-homotopy, contravariant internal-function adaptation
(blueprint: lem-sfb-internal-function-vertex-prism).

The specification retains actual internal module morphisms, their formulas on all
profinite slices, and naturality in coefficients and both parameter maps. No action
or injective resolution is supplied or assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.CondensedBar

/-- The tuple (u x₀,...,u xᵢ,v xᵢ,...,v xₙ). `predAbove` duplicates position i.
Source: Stacks 019S, the vertex-prism adaptation
(blueprint: lem-sfb-internal-function-vertex-prism). -/
def vertexPrismTuple {X Y T : Profinite.{u}} (u v : C(X, Y)) {n : ℕ}
    (i : Fin (n + 1)) (g : Fin (n + 1) → C(T, X)) : Fin (n + 2) → C(T, Y) :=
  fun j ↦ if j.val ≤ i.val then u.comp (g (i.predAbove j))
    else v.comp (g (i.predAbove j))

/-- Evaluate a complex term via its identification with the recorded internal functions.
Source: the generalized evaluations of the bar-data definition, used in Stacks 019S
(blueprint: lem-sfb-internal-function-vertex-prism). -/
def vertexPrismValue {A : Ring.{u}} (F : InternalFunctions A) {Z : Profinite.{u}}
    {M K : Modules A} {n : ℕ} (e : K ≅ (F.functor (power Z (n + 1))).obj M)
    (S : Profinite.{u}) (x : sections A K S) (T : Profinite.{u}) (f : T ⟶ S)
    (g : Fin (n + 1) → C(T, Z)) : sections A M T :=
  (F.evaluate (power Z (n + 1)) S M (e.hom.hom.hom.app (op S) x)).val T f (tupleMap g)

/-- The deletion complexes, coordinate pullbacks and signed prisms, specified together.
The coefficient parameter is functorial: pullback is a natural transformation,
and coefficient_naturality gives the corresponding equation for the prism. The slice variables
S,T,f are unrestricted, including empty profinite sets. Negative degrees and P₀ are
supplied by `integerComplex` and `prismZero` below, using extension by zero.

Source: Stacks 019S, equation-homotopy-to-homotopy, internal-function adaptation
(blueprint: lem-sfb-internal-function-vertex-prism). -/
structure InternalFunctionVertexPrism (A : Ring.{u}) (F : InternalFunctions A) where
  complex : Profinite.{u} → Modules A ⥤ CochainComplex (Modules A) ℕ
  term : ∀ (Z : Profinite.{u}) (n : ℕ),
    complex Z ⋙ HomologicalComplex.eval (Modules A) (.up ℕ) n ≅
      F.functor (power Z (n + 1))
  differential : ∀ (Z : Profinite.{u}) (M : Modules A) (n : ℕ) (S : Profinite.{u})
    (x : sections A ((complex Z).obj M |>.X n) S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : Fin (n + 2) → C(T, Z)),
    vertexPrismValue F ((term Z (n + 1)).app M) S
      ((((complex Z).obj M).d n (n + 1)).hom.hom.app (op S) x) T f g =
    ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
      vertexPrismValue F ((term Z n).app M) S x T f (fun k ↦ g (j.succAbove k))
  pullback : ∀ {X Y : Profinite.{u}}, C(X, Y) → (complex Y ⟶ complex X)
  pullback_formula : ∀ {X Y : Profinite.{u}} (u : C(X, Y)) (M : Modules A) (n : ℕ)
    (S : Profinite.{u}) (x : sections A ((complex Y).obj M |>.X n) S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : Fin (n + 1) → C(T, X)),
    vertexPrismValue F ((term X n).app M) S
      ((((pullback u).app M).f n).hom.hom.app (op S) x) T f g =
    vertexPrismValue F ((term Y n).app M) S x T f (fun j ↦ u.comp (g j))
  prism : ∀ {X Y : Profinite.{u}} (_u _v : C(X, Y)) (n : ℕ) (M : Modules A),
    ((complex Y).obj M).X (n + 1) ⟶ ((complex X).obj M).X n
  coefficient_naturality : ∀ {X Y : Profinite.{u}} (u v : C(X, Y)) (n : ℕ)
    {M N : Modules A} (a : M ⟶ N),
    ((complex Y).map a).f (n + 1) ≫ prism u v n N =
      prism u v n M ≫ ((complex X).map a).f n
  prism_formula : ∀ {X Y : Profinite.{u}} (u v : C(X, Y)) (M : Modules A) (n : ℕ)
    (S : Profinite.{u}) (x : sections A ((complex Y).obj M |>.X (n + 1)) S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : Fin (n + 1) → C(T, X)),
    vertexPrismValue F ((term X n).app M) S
      ((prism u v n M).hom.hom.app (op S) x) T f g =
    ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
      vertexPrismValue F ((term Y (n + 1)).app M) S x T f (vertexPrismTuple u v i g)
  identity_zero : ∀ {X Y : Profinite.{u}} (u v : C(X, Y)) (M : Modules A),
    ((complex Y).obj M).d 0 1 ≫ prism u v 0 M =
      ((pullback v).app M).f 0 - ((pullback u).app M).f 0
  identity_succ : ∀ {X Y : Profinite.{u}} (u v : C(X, Y)) (M : Modules A) (n : ℕ),
    prism u v n M ≫ ((complex X).obj M).d n (n + 1) +
      ((complex Y).obj M).d (n + 1) (n + 2) ≫ prism u v (n + 1) M =
      ((pullback v).app M).f (n + 1) - ((pullback u).app M).f (n + 1)
  source_naturality : ∀ {W X Y : Profinite.{u}} (b : C(W, X)) (u v : C(X, Y))
    (M : Modules A) (n : ℕ),
    prism u v n M ≫ ((pullback b).app M).f n =
      prism (u.comp b) (v.comp b) n M
  target_naturality : ∀ {X Y Z : Profinite.{u}} (u v : C(X, Y)) (c : C(Y, Z))
    (M : Modules A) (n : ℕ),
    ((pullback c).app M).f (n + 1) ≫ prism u v n M =
      prism (c.comp u) (c.comp v) n M
  degree_zero_formula : ∀ {X Y : Profinite.{u}} (u v : C(X, Y)) (M : Modules A)
    (S : Profinite.{u}) (x : sections A ((complex Y).obj M |>.X 0) S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : Fin 1 → C(T, X)),
    vertexPrismValue F ((term X 0).app M) S
      ((((complex Y).obj M).d 0 1 ≫ prism u v 0 M).hom.hom.app (op S) x) T f g =
    vertexPrismValue F ((term Y 0).app M) S x T f (fun j ↦ v.comp (g j)) -
      vertexPrismValue F ((term Y 0).app M) S x T f (fun j ↦ u.comp (g j))

/-- The function complex in all integer degrees, equal to zero in negative degrees.
Source: the Bⁿ=0 convention of the vertex-prism statement, Stacks 019S adaptation
(blueprint: lem-sfb-internal-function-vertex-prism). -/
def InternalFunctionVertexPrism.integerComplex {A : Ring.{u}} {F : InternalFunctions A}
    (D : InternalFunctionVertexPrism A F) (Z : Profinite.{u}) (M : Modules A) :
    CochainComplex (Modules A) ℤ :=
  ((D.complex Z).obj M).extend ComplexShape.embeddingUpNat

/-- The prescribed degree-zero prism is the zero map into the negative term.
Source: P₀=0 in the vertex-prism statement, Stacks 019S adaptation
(blueprint: lem-sfb-internal-function-vertex-prism). -/
def InternalFunctionVertexPrism.prismZero {A : Ring.{u}} {F : InternalFunctions A}
    (D : InternalFunctionVertexPrism A F) (X Y : Profinite.{u}) (M : Modules A) :
    ((D.complex Y).obj M).X 0 ⟶ (D.integerComplex X M).X (-1) := 0

/-- Precompose a natural generalized function and transport it through evaluation.
Source: Stacks 019S, internal-function adaptation
(blueprint: lem-sfb-internal-function-vertex-prism). -/
private def parameterValue {A : Ring.{u}} (F : InternalFunctions A)
    {P Q : Profinite.{u}} (q : P ⟶ Q) (M : Modules A) (S : Profinite.{u})
    (x : sections A ((F.functor Q).obj M) S) :
    sections A ((F.functor P).obj M) S :=
  (F.evaluate P S M).symm ⟨fun T f g ↦
    (F.evaluate Q S M x).val T f (q.hom.hom.comp g), by
      intro T V f k g
      simpa only [ContinuousMap.comp_assoc] using
        (F.evaluate Q S M x).property T V f k (q.hom.hom.comp g)⟩

/-- The constructed precomposition has its prescribed value on every slice.
Source: Stacks 019S, internal-function adaptation
(blueprint: lem-sfb-internal-function-vertex-prism). -/
private theorem parameterValue_formula {A : Ring.{u}} (F : InternalFunctions A)
    {P Q : Profinite.{u}} (q : P ⟶ Q) (M : Modules A) (S : Profinite.{u})
    (x : sections A ((F.functor Q).obj M) S) (T : Profinite.{u})
    (f : T ⟶ S) (g : C(T, P)) :
    (F.evaluate P S M (parameterValue F q M S x)).val T f g =
      (F.evaluate Q S M x).val T f (q.hom.hom.comp g) := by
  simp only [parameterValue, Equiv.apply_symm_apply]

/-- Generalized evaluations detect equality of internal-function sections.
Source: Stacks 019S, internal-function adaptation
(blueprint: lem-sfb-internal-function-vertex-prism). -/
private theorem function_ext {A : Ring.{u}} (F : InternalFunctions A)
    {P S : Profinite.{u}} {M : Modules A}
    {x y : sections A ((F.functor P).obj M) S}
    (h : ∀ (T : Profinite.{u}) (f : T ⟶ S) (g : C(T, P)),
      (F.evaluate P S M x).val T f g = (F.evaluate P S M y).val T f g) : x = y := by
  apply (F.evaluate P S M).injective
  apply Subtype.ext
  funext T f g
  exact h T f g

/-- Precomposition is linear over the ring of sections at the base.
Source: Stacks 019S, internal-function adaptation
(blueprint: lem-sfb-internal-function-vertex-prism). -/
private def parameterLinear {A : Ring.{u}} (F : InternalFunctions A)
    {P Q : Profinite.{u}} (q : P ⟶ Q) (M : Modules A) (S : Profinite.{u}) :
    sections A ((F.functor Q).obj M) S →ₗ[sectionRing A S]
      sections A ((F.functor P).obj M) S where
  toFun := parameterValue F q M S
  map_add' x y := by
    apply function_ext F
    intro T f g
    simp only [parameterValue_formula, F.add]
  map_smul' r x := by
    apply function_ext F
    intro T f g
    simp only [parameterValue_formula, F.smul, RingHom.id_apply]

/-- Precomposition commutes with restriction, giving a section-module sheaf map.
Source: Stacks 019S, internal-function adaptation
(blueprint: lem-sfb-internal-function-vertex-prism). -/
private def parameterSectionMap {A : Ring.{u}} (F : InternalFunctions A)
    {P Q : Profinite.{u}} (q : P ⟶ Q) (M : Modules A) :
    (sectionsFunctor A).obj ((F.functor Q).obj M) ⟶
      (sectionsFunctor A).obj ((F.functor P).obj M) :=
  ⟨{ app := fun S ↦ ConcreteCategory.ofHom (parameterLinear F q M (unop S))
     naturality := by
       intro S V k
       ext x
       apply function_ext F
       intro T f g
       change (F.evaluate P (unop V) M
         (parameterValue F q M (unop V)
           (((F.functor Q).obj M).X.obj.map k x))).val T f g =
         (F.evaluate P (unop V) M
           (((F.functor P).obj M).X.obj.map k
             (parameterValue F q M (unop S) x))).val T f g
       rw [parameterValue_formula]
       exact (F.restriction Q (unop S) (unop V) k.unop M x T f
         (q.hom.hom.comp g)).trans
           ((parameterValue_formula F q M (unop S) x T (f ≫ k.unop) g).symm.trans
             (F.restriction P (unop S) (unop V) k.unop M
               (parameterValue F q M (unop S) x) T f g).symm) }⟩

/-- Full faithfulness lifts the constructed section map to an internal module map.
Source: Stacks 019S, internal-function adaptation
(blueprint: lem-sfb-internal-function-vertex-prism). -/
private def parameterMap {A : Ring.{u}} (F : InternalFunctions A)
    {P Q : Profinite.{u}} (q : P ⟶ Q) : F.functor Q ⟶ F.functor P where
  app M := (InternalAbelianSheafModule.sectionModuleFunctor_fullyFaithful
    (coherentTopology Profinite.{u}) A.X).preimage (parameterSectionMap F q M)
  naturality M N a := by
    apply Mod.hom_ext
    ext S x
    apply function_ext F
    intro T f g
    change (F.evaluate P (unop S) N
      (parameterValue F q N (unop S)
        (((F.functor Q).map a).hom.hom.app S x))).val T f g =
      (F.evaluate P (unop S) N
        (((F.functor P).map a).hom.hom.app S
          (parameterValue F q M (unop S) x))).val T f g
    simp only [parameterValue_formula, F.map]

/-- The lifted internal map retains the generalized precomposition formula.
Source: Stacks 019S, internal-function adaptation
(blueprint: lem-sfb-internal-function-vertex-prism). -/
private theorem parameterMap_formula {A : Ring.{u}} (F : InternalFunctions A)
    {P Q : Profinite.{u}} (q : P ⟶ Q) (M : Modules A) (S : Profinite.{u})
    (x : sections A ((F.functor Q).obj M) S) (T : Profinite.{u})
    (f : T ⟶ S) (g : C(T, P)) :
    (F.evaluate P S M (((parameterMap F q).app M).hom.hom.app (op S) x)).val T f g =
      (F.evaluate Q S M x).val T f (q.hom.hom.comp g) :=
  parameterValue_formula F q M S x T f g

/-- The explicit precomposition maps form a contravariant parameter functor.
Source: Stacks 019S, internal-function adaptation
(blueprint: lem-sfb-internal-function-vertex-prism). -/
private def parameterFunctor {A : Ring.{u}} (F : InternalFunctions A) :
    Profinite.{u}ᵒᵖ ⥤ (Modules A ⥤ Modules A) where
  obj P := F.functor (unop P)
  map q := parameterMap F q.unop
  map_id P := by
    apply NatTrans.ext
    funext M
    apply Mod.hom_ext
    ext S x
    apply function_ext F
    intro T f g
    change (F.evaluate (unop P) (unop S) M
      (parameterValue F (𝟙 (unop P)) M (unop S) x)).val T f g =
      (F.evaluate (unop P) (unop S) M x).val T f g
    rw [parameterValue_formula]
    rfl
  map_comp q r := by
    apply NatTrans.ext
    funext M
    apply Mod.hom_ext
    ext S x
    apply function_ext F
    intro T f g
    change (F.evaluate _ (unop S) M
      (parameterValue F (q ≫ r).unop M (unop S) x)).val T f g =
      (F.evaluate _ (unop S) M
        (parameterValue F r.unop M (unop S)
          (parameterValue F q.unop M (unop S) x))).val T f g
    simp only [parameterValue_formula]
    rfl

/-- Generalized evaluation is additive, hence respects finite integer sums.
Source: Stacks 019S, internal-function adaptation
(blueprint: lem-sfb-internal-function-vertex-prism). -/
private def evaluationHom {A : Ring.{u}} (F : InternalFunctions A)
    (P S : Profinite.{u}) (M : Modules A) (T : Profinite.{u})
    (f : T ⟶ S) (g : C(T, P)) :
    sections A ((F.functor P).obj M) S →+ sections A M T :=
  AddMonoidHom.mk' (fun x ↦ (F.evaluate P S M x).val T f g)
    (fun x y ↦ F.add P S M x y T f g)

/-- Applying an internal module morphism to a fixed section is additive.
Source: Stacks 019S, internal-function adaptation
(blueprint: lem-sfb-internal-function-vertex-prism). -/
private def sectionHom {A : Ring.{u}} {K N : Modules A} (S : Profinite.{u})
    (x : sections A K S) : (K ⟶ N) →+ sections A N S where
  toFun q := q.hom.hom.app (op S) x
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The explicit alternating deletion differential defines the coefficient functor.
Source: Stacks 019S, internal-function adaptation
(blueprint: lem-sfb-internal-function-vertex-prism). -/
private def tupleComplex {A : Ring.{u}} (F : InternalFunctions A) (Z : Profinite.{u}) :
    Modules A ⥤ CochainComplex (Modules A) ℕ where
  obj M := CochainComplex.of
    (fun n ↦ (F.functor (power Z (n + 1))).obj M)
    (fun n ↦ (TupleOperators.differential (parameterFunctor F) Z n).app M)
    (fun n ↦ by
      simpa using congrArg (fun a ↦ a.app M)
        (TupleOperators.differential_squared (parameterFunctor F) Z n))
  map a := CochainComplex.ofHom
    (fun n ↦ (F.functor (power Z (n + 1))).map a)
    (fun n ↦ by
      simpa only [CochainComplex.of_d, parameterFunctor, Nat.add_assoc] using
        (TupleOperators.differential (parameterFunctor F) Z n).naturality a)
  map_id M := by
    apply HomologicalComplex.hom_ext
    intro n
    exact (F.functor (power Z (n + 1))).map_id M
  map_comp a b := by
    apply HomologicalComplex.hom_ext
    intro n
    exact (F.functor (power Z (n + 1))).map_comp a b

/-- Coordinatewise precomposition defines a natural cochain map.
Source: Stacks 019S, internal-function adaptation
(blueprint: lem-sfb-internal-function-vertex-prism). -/
private def tuplePullback {A : Ring.{u}} (F : InternalFunctions A)
    {X Y : Profinite.{u}} (a : C(X, Y)) : tupleComplex F Y ⟶ tupleComplex F X where
  app M := CochainComplex.ofHom
    (fun n ↦ ((parameterFunctor F).map (TupleOperators.coordinate a n).op).app M)
    (fun n ↦ by
      simpa only [tupleComplex, CochainComplex.of_d, NatTrans.comp_app,
        parameterFunctor, Nat.add_assoc] using congrArg (fun a ↦ a.app M)
        (TupleOperators.coordinate_differential (parameterFunctor F) a n))
  naturality M N a := by
    apply HomologicalComplex.hom_ext
    intro n
    exact ((parameterFunctor F).map (TupleOperators.coordinate _ n).op).naturality a

/-- The alternating differential has its deletion formula on every slice.
Source: Stacks 019S, internal-function adaptation
(blueprint: lem-sfb-internal-function-vertex-prism). -/
private theorem differential_formula {A : Ring.{u}} (F : InternalFunctions A)
    (Z : Profinite.{u}) (M : Modules A) (n : ℕ) (S : Profinite.{u})
    (x : sections A ((F.functor (power Z (n + 1))).obj M) S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : Fin (n + 2) → C(T, Z)) :
    (F.evaluate (power Z (n + 2)) S M
      (((TupleOperators.differential (parameterFunctor F) Z n).app M).hom.hom.app
        (op S) x)).val T f (tupleMap g) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        (F.evaluate (power Z (n + 1)) S M x).val T f
          (tupleMap (fun j ↦ g (i.succAbove j))) := by
  change evaluationHom F _ S M T f (tupleMap g)
    (sectionHom S x ((TupleOperators.differential (parameterFunctor F) Z n).app M)) = _
  simp only [TupleOperators.differential, NatTrans.app_sum, NatTrans.app_zsmul,
    map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact parameterMap_formula F (TupleOperators.deletion Z n i) M S x T f (tupleMap g)

/-- The signed insertion maps have the specified vertex-prism formula.
Source: Stacks 019S, internal-function adaptation
(blueprint: lem-sfb-internal-function-vertex-prism). -/
private theorem prism_formula {A : Ring.{u}} (F : InternalFunctions A)
    {X Y : Profinite.{u}} (a b : C(X, Y)) (M : Modules A) (n : ℕ) (S : Profinite.{u})
    (x : sections A ((F.functor (power Y (n + 2))).obj M) S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : Fin (n + 1) → C(T, X)) :
    (F.evaluate (power X (n + 1)) S M
      (((TupleOperators.prism (parameterFunctor F) a b n).app M).hom.hom.app
        (op S) x)).val T f (tupleMap g) =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
        (F.evaluate (power Y (n + 2)) S M x).val T f (tupleMap (vertexPrismTuple a b i g)) := by
  change evaluationHom F _ S M T f (tupleMap g)
    (sectionHom S x ((TupleOperators.prism (parameterFunctor F) a b n).app M)) = _
  simp only [TupleOperators.prism, NatTrans.app_sum, NatTrans.app_zsmul,
    map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change (F.evaluate _ S M (parameterValue F _ M S x)).val T f (tupleMap g) = _
  rw [parameterValue_formula]
  apply congrArg ((F.evaluate (power Y (n + 2)) S M x).val T f)
  ext t j
  change (if j.val ≤ i.val then a (g (i.predAbove j) t)
      else b (g (i.predAbove j) t)) =
    (if j.val ≤ i.val then a.comp (g (i.predAbove j))
      else b.comp (g (i.predAbove j))) t
  split_ifs <;> rfl

/-- Every internal-function datum (the generalized evaluations of the bar-data definition)
admits the prescribed deletion complex and vertex prism.
There is no group action, resolution, projectivity or acyclicity hypothesis.

Source: Stacks Project, simplicial.tex, Tag 019S, lemma-homotopy-s-N and
 equation-homotopy-to-homotopy, contravariant internal-function adaptation
(blueprint: lem-sfb-internal-function-vertex-prism).

Proof:
1. Precompose the natural families of F.evaluate by any continuous parameter map.
Transport this operation through the inverse evaluation. The addition, scalar and
restriction laws make it a map of section-module sheaves. Full faithfulness of the
internal-to-section-module functor gives its internal map. Evaluation injectivity
proves the identity and composition laws, constructing parameterFunctor explicitly.
2. The profinite tuple objects form a simplicial object. Apply parameterFunctor to
its right opposite. Mathlib's alternating coface differential squares to zero, so
CochainComplex.of constructs the complexes. Coordinatewise maps commute with deletion,
giving tuplePullback. The term isomorphisms are identities.
3. The continuous vertex insertions induce internal maps. Their finite signed sums
construct the prism. Additive evaluation preserves integer multiples and finite sums,
proving its formula and the differential formula on every profinite slice.
4. Apply lem-sfb-profinite-vertex-prism-boundary to parameterFunctor, then take its
component at M. This is the positive-degree identity. Its proof pairs deletions away
from the doubled vertex with the opposite-signed terms in the other composition;
the two remaining deletions at each vertex telescope to v* minus u*.
5. In degree zero the sole insertion has two deletions, giving v* minus u* directly.
Apply additive generalized evaluation to obtain the stated degree-zero formula.
6. Naturality of the constructed parameter transformations proves coefficient
naturality. Coordinatewise substitution commutes with insertion on either side,
proving source and target naturality by functoriality and bilinearity.
No step chooses a vertex. Empty parameters, the zero ring, the zero module and u=v
are all included, and all formulas are established on arbitrary T→S.
-/
theorem internal_function_vertex_prism (A : Ring.{u}) (F : InternalFunctions A) :
    Nonempty (InternalFunctionVertexPrism A F) := by
  refine ⟨{
    complex := tupleComplex F
    term := fun _ _ ↦ Iso.refl _
    differential := ?_
    pullback := tuplePullback F
    pullback_formula := ?_
    prism := fun a b n M ↦ (TupleOperators.prism (parameterFunctor F) a b n).app M
    coefficient_naturality := ?_
    prism_formula := ?_
    identity_zero := ?_
    identity_succ := ?_
    source_naturality := ?_
    target_naturality := ?_
    degree_zero_formula := ?_ }⟩
  · intro Z M n S x T f g
    change (F.evaluate (power Z (n + 2)) S M
      (((((tupleComplex F Z).obj M).d n (n + 1))).hom.hom.app (op S) x)).val
        T f (tupleMap g) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        (F.evaluate (power Z (n + 1)) S M x).val T f
          (tupleMap (fun j ↦ g (i.succAbove j)))
    convert differential_formula F Z M n S x T f g using 1
    simp only [tupleComplex, CochainComplex.of_d]
    rfl
  · intro X Y a M n S x T f g
    change (F.evaluate _ S M
      (((parameterMap F (TupleOperators.coordinate a n)).app M).hom.hom.app
        (op S) x)).val T f (tupleMap g) = _
    exact parameterMap_formula F (TupleOperators.coordinate a n) M S x T f (tupleMap g)
  · intro X Y a b n M N c
    exact (TupleOperators.prism (parameterFunctor F) a b n).naturality c
  · intro X Y a b M n S x T f g
    exact prism_formula F a b M n S x T f g
  · intro X Y a b M
    simpa [tupleComplex, tuplePullback, parameterFunctor, CochainComplex.of.d] using
      congrArg (fun a ↦ a.app M) (TupleOperators.prism_boundary_zero (parameterFunctor F) a b)
  · intro X Y a b M n
    simpa [tupleComplex, tuplePullback, parameterFunctor, CochainComplex.of.d,
      Nat.add_assoc] using congrArg (fun a ↦ a.app M)
      (TupleOperators.prism_boundary (parameterFunctor F) a b n)
  · intro W X Y c a b M n
    exact congrArg (fun a ↦ a.app M)
      (TupleOperators.prism_source (parameterFunctor F) c a b n)
  · intro X Y Z a b c M n
    exact congrArg (fun a ↦ a.app M)
      (TupleOperators.prism_target (parameterFunctor F) a b c n)
  · intro X Y a b M S x T f g
    change sections A ((F.functor (power Y 1)).obj M) S at x
    have h : (TupleOperators.differential (parameterFunctor F) Y 0).app M ≫
        (TupleOperators.prism (parameterFunctor F) a b 0).app M =
        ((parameterFunctor F).map (TupleOperators.coordinate b 0).op).app M -
          ((parameterFunctor F).map (TupleOperators.coordinate a 0).op).app M := by
      simpa only [NatTrans.comp_app, NatTrans.app_sub] using congrArg (fun a ↦ a.app M)
        (TupleOperators.prism_boundary_zero (parameterFunctor F) a b)
    change (F.evaluate _ S M
      ((((TupleOperators.differential (parameterFunctor F) Y 0).app M) ≫
        (TupleOperators.prism (parameterFunctor F) a b 0).app M).hom.hom.app
          (op S) x)).val T f (tupleMap g) = _
    rw [h]
    change evaluationHom F _ S M T f (tupleMap g)
      (sectionHom S x
        (((parameterMap F (TupleOperators.coordinate b 0)).app M) -
          ((parameterMap F (TupleOperators.coordinate a 0)).app M))) = _
    simp only [map_sub]
    exact congrArg₂ (· - ·)
      (parameterMap_formula F (TupleOperators.coordinate b 0) M S x T f (tupleMap g))
      (parameterMap_formula F (TupleOperators.coordinate a 0) M S x T f (tupleMap g))

end CategoryTheory.CondensedBar
