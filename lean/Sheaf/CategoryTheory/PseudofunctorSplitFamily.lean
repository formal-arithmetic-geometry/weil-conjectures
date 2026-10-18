/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q135
-/
module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# Split-family strictification with a specified coherent map

Source: Stacks Project, Categories, Tag 004A, dualized; the explicit split-family construction
and its coherent-map and restriction refinements are the component calculations in the DAG
(blueprint: lem-coef-pseudofunctor-split-family-strictification).

The input pseudofunctor and coherent map use Mathlib's `Pseudofunctor` and `StrongTrans`.
The family objects and componentwise arrows below implement the model specified in the node.
The existence statement specifies every object, structure isomorphism, and arrow of reindexing
and of the lifted map. The final clause compares strict restrictions as diagrams under the
specified incoming diagram.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Bicategory

namespace Pseudofunctor

variable {J : Type w} [Category.{v} J]

/-- The split families at `j`, with all arrows out of `j` as indices.
The unit and cocycle include the canonical equality transports on indices.
Source: Tag 004A and the explicit family model
(blueprint: lem-coef-pseudofunctor-split-family-strictification). -/
structure SplitFamily (P : Pseudofunctor (LocallyDiscrete J) Cat.{max w v u, max w v u})
    (j : J) where
  /-- The object indexed by `a : j ⟶ k`. -/
  obj (k : J) (a : j ⟶ k) : P.obj ⟨k⟩
  /-- The specified transition isomorphism. -/
  transition (k l : J) (a : j ⟶ k) (b : k ⟶ l) :
    (P.map b.toLoc).toFunctor.obj (obj k a) ≅ obj l (a ≫ b)
  /-- Normalized unit condition, expressed using the pseudofunctor's unit comparison. -/
  unit (k : J) (a : j ⟶ k) :
    transition k k a (𝟙 k) =
      (Cat.Hom.toNatIso (P.mapId ⟨k⟩)).app (obj k a) ≪≫
        eqToIso (congrArg (obj k) (Category.comp_id a).symm)
  /-- The family cocycle. Mathlib's `mapComp` has the inverse orientation to `μ`. -/
  cocycle (k l m : J) (a : j ⟶ k) (b : k ⟶ l) (c : l ⟶ m) :
    (P.map c.toLoc).toFunctor.mapIso (transition k l a b) ≪≫
        transition l m (a ≫ b) c ≪≫
          eqToIso (congrArg (obj m) (Category.assoc a b c)) =
      (Cat.Hom.toNatIso (P.mapComp b.toLoc c.toLoc)).symm.app (obj k a) ≪≫
        transition k m a (b ≫ c)

namespace SplitFamily

variable {P : Pseudofunctor (LocallyDiscrete J) Cat.{max w v u, max w v u}} {j : J}

/-- A morphism of split families is a compatible family of component arrows.
Source: the family-morphism equation in the explicit refinement of Tag 004A
(blueprint: lem-coef-pseudofunctor-split-family-strictification). -/
def Hom (X Y : SplitFamily.{w, v, u} P j) : Type (max w v u) :=
  {t : ∀ (k : J) (a : j ⟶ k), X.obj k a ⟶ Y.obj k a //
    ∀ (k l : J) (a : j ⟶ k) (b : k ⟶ l),
      (X.transition k l a b).hom ≫ t l (a ≫ b) =
        (P.map b.toLoc).toFunctor.map (t k a) ≫ (Y.transition k l a b).hom}

/-- Componentwise identities satisfy the family-morphism equation.
Source: Tag 004A, explicit family model, proof step 1
(blueprint: lem-coef-pseudofunctor-split-family-strictification).
Proof: each side reduces to the transition arrow by the identity laws and preservation
of identities by `P(b)`. This is the identity part of the node's category construction. -/
theorem identity_compatible (X : SplitFamily.{w, v, u} P j) :
    ∀ (k l : J) (a : j ⟶ k) (b : k ⟶ l),
      (X.transition k l a b).hom ≫ 𝟙 (X.obj l (a ≫ b)) =
        (P.map b.toLoc).toFunctor.map (𝟙 (X.obj k a)) ≫
          (X.transition k l a b).hom := by
  sorry

/-- Componentwise composites satisfy the family-morphism equation.
Source: Tag 004A, explicit family model, proof step 1
(blueprint: lem-coef-pseudofunctor-split-family-strictification).
Proof: for compatible `t` and `s`, substitute their compatibility equations successively
in `γX ≫ t ≫ s`, then use preservation of composition by `P(b)`. -/
theorem composition_compatible {X Y Z : SplitFamily.{w, v, u} P j} (t : Hom X Y) (s : Hom Y Z) :
    ∀ (k l : J) (a : j ⟶ k) (b : k ⟶ l),
      (X.transition k l a b).hom ≫ (t.val l (a ≫ b) ≫ s.val l (a ≫ b)) =
        (P.map b.toLoc).toFunctor.map (t.val k a ≫ s.val k a) ≫
          (Z.transition k l a b).hom := by
  sorry

/-- The category of split families, with componentwise identities and composition.
The category laws are the existing category laws in each fibre, transported through
function and subtype extensionality.
Source: Tag 004A, explicit family model, proof step 1
(blueprint: lem-coef-pseudofunctor-split-family-strictification). -/
instance category : Category (SplitFamily.{w, v, u} P j) where
  Hom := Hom
  id X := ⟨fun k a ↦ 𝟙 (X.obj k a), identity_compatible X⟩
  comp t s := ⟨fun k a ↦ t.val k a ≫ s.val k a, composition_compatible t s⟩
  id_comp t := Subtype.ext (funext fun k ↦ funext fun a ↦ Category.id_comp (t.val k a))
  comp_id t := Subtype.ext (funext fun k ↦ funext fun a ↦ Category.comp_id (t.val k a))
  assoc t s r := Subtype.ext
    (funext fun k ↦ funext fun a ↦ Category.assoc (t.val k a) (s.val k a) (r.val k a))

/-- Transport from a chosen diagram value to its specified split-family category.
This is equality transport, with no choice of a comparison equivalence.
Source: the specified split-family model of Tag 004A
(blueprint: lem-coef-pseudofunctor-split-family-strictification). -/
def transport (P : Pseudofunctor (LocallyDiscrete J) Cat.{max w v u, max w v u})
    (F : J ⥤ Cat.{max w v u, max w v u})
    (hF : ∀ j : J, F.obj j = Cat.of (SplitFamily.{w, v, u} P j)) (j : J) :
    F.obj j ⥤ SplitFamily.{w, v, u} P j :=
  (eqToHom (hF j)).toFunctor

end SplitFamily

/-- The split-family strictification, including the specified coherent map and its strict
restriction comparisons.
Source: Stacks Project, Categories, Tag 004A, dualized, refined by the node's explicit
family construction (blueprint: lem-coef-pseudofunctor-split-family-strictification).

Proof (the node's thirteen steps):
1. Give families componentwise identities and composition; compatibility is preserved and
   the category laws follow pointwise (`def-nagata-category`). Work in the universe bound
   containing these families (`def-weil-size-convention`).
2. For `T ∈ P(j)`, set `R(T)_a = P(a)T` and transitions `μ`; the pseudofunctor cocycle gives
   the family cocycle, naturality gives the morphism equation, and normalization gives `ER=1`.
3. The arrows `γ_(a,1)` define the natural isomorphism `RE ≅ 1`. Its compatibility is the
   family cocycle at `(b,a,1)` and its naturality is the family-morphism equation there.
   Inverses satisfy the same equations. Evaluation of this isomorphism at `1` is the identity.
4. Reindex by precomposition: objects, transitions, and arrows are those at `a₀ ≫ a`.
   Associativity of indices proves strict composition; identity indices prove strict units.
5. Take `κ_a = γ_(a,1)`. The family-morphism equation proves naturality, and the cocycle at
   `(b,a,1)` proves its composition coherence; its unit is the family unit equation.
6. Lift `z` to the family `α_k(H(a)z)` with transitions `θ_b(H(a)z)`; the strong transformation
   coherence proves the family cocycle, its unit proves the unit, and naturality gives arrows.
7. Strictness of `H` proves strict naturality of this lift. At identity indices it evaluates
   to `α`, and its comparison under `κ` is precisely `θ`.
8. On a strict restriction form triples `(X,T,ε : E X ≅ T)` and compatible pairs of arrows.
9. Along `r` send the triple to `(F(r)X,P(r)T,P(r)ε ∘ κ_r⁻¹)` and act componentwise on arrows;
   naturality of `κ` proves the pair compatibility equation.
10. The inverse `κ` cocycle and the identity `μ` on the restriction prove strictness of this
    triple diagram. Both projections are strictly natural by their formulas.
11. The first projection has quasi-inverse `X ↦ (X,E X,1)`; `(1,ε)` gives its counit.
12. The second has quasi-inverse `T ↦ (R T,T,1)`; its counit is
    `(η_X ∘ R(ε⁻¹),1)`. Evaluation of `η` and `ER=1` verify compatibility, and naturality
    follows from the pair compatibility equation and naturality of `η`.
13. The specified incoming map is `z ↦ (α̃ z,α z,1)`. Its third component after transport is
    `θ_r⁻¹=1` on the restriction, so it is strictly natural. Its projection composites are
    exactly the two specified maps, as asserted. -/
theorem exists_splitFamily_strictification
    (P : Pseudofunctor (LocallyDiscrete J) Cat.{max w v u, max w v u})
    (hP_id : ∀ j : J,
      (P.map (𝟙 j).toLoc).toFunctor = 𝟭 (P.obj ⟨j⟩))
    (hP_unit : ∀ j : J,
      HEq (Cat.Hom.toNatIso (P.mapId ⟨j⟩)) (Iso.refl (𝟭 (P.obj ⟨j⟩))))
    (H : J ⥤ Cat.{max w v u, max w v u}) (α : StrongTrans H.toPseudofunctor' P) :
    ∃ (F : J ⥤ Cat.{max w v u, max w v u})
      (hF : ∀ j : J, F.obj j = Cat.of (SplitFamily.{w, v, u} P j))
      (E : ∀ j : J, F.obj j ⥤ P.obj ⟨j⟩)
      (κ : ∀ {j k : J} (a : j ⟶ k),
        E j ⋙ (P.map a.toLoc).toFunctor ≅ (F.map a).toFunctor ⋙ E k)
      (αtilde : H ⟶ F),
      (∀ (j : J) (X : F.obj j),
        (E j).obj X = ((SplitFamily.transport.{w, v, u} P F hF j).obj X).obj j (𝟙 j)) ∧
      (∀ (j : J) {X Y : F.obj j} (t : X ⟶ Y),
        HEq ((E j).map t) (((SplitFamily.transport.{w, v, u} P F hF j).map t).val j (𝟙 j))) ∧
      (∀ j : J, (E j).IsEquivalence) ∧
      (∀ (j k l : J) (a : j ⟶ k) (b : k ⟶ l) (X : F.obj j),
        ((SplitFamily.transport.{w, v, u} P F hF k).obj ((F.map a).toFunctor.obj X)).obj l b =
          ((SplitFamily.transport.{w, v, u} P F hF j).obj X).obj l (a ≫ b)) ∧
      (∀ (j k l m : J) (a : j ⟶ k) (b : k ⟶ l) (c : l ⟶ m) (X : F.obj j),
        HEq (((SplitFamily.transport.{w, v, u} P F hF k).obj ((F.map a).toFunctor.obj X)).transition
          l m b c)
          (((SplitFamily.transport.{w, v, u} P F hF j).obj X).transition l m (a ≫ b) c)) ∧
      (∀ (j k l : J) (a : j ⟶ k) (b : k ⟶ l) {X Y : F.obj j} (t : X ⟶ Y),
        HEq (((SplitFamily.transport.{w, v, u} P F hF k).map ((F.map a).toFunctor.map t)).val l b)
          (((SplitFamily.transport.{w, v, u} P F hF j).map t).val l (a ≫ b))) ∧
      (∀ (j k : J) (a : j ⟶ k) (X : F.obj j),
        HEq ((κ a).app X)
          (((SplitFamily.transport.{w, v, u} P F hF j).obj X).transition j k (𝟙 j) a)) ∧
      (∀ j : J, HEq (κ (𝟙 j)) (Iso.refl (E j))) ∧
      (∀ (j k l : J) (a : j ⟶ k) (b : k ⟶ l) (X : F.obj j),
        HEq ((P.map b.toLoc).toFunctor.mapIso ((κ a).app X) ≪≫
          (κ b).app ((F.map a).toFunctor.obj X))
          ((Cat.Hom.toNatIso (P.mapComp a.toLoc b.toLoc)).symm.app ((E j).obj X) ≪≫
            (κ (a ≫ b)).app X)) ∧
      (∀ j : J, (αtilde.app j).toFunctor ⋙ E j = (α.app ⟨j⟩).toFunctor) ∧
      (∀ (j k : J) (a : j ⟶ k) (z : H.obj j),
        ((SplitFamily.transport.{w, v, u} P F hF j).obj ((αtilde.app j).toFunctor.obj z)).obj k a =
          (α.app ⟨k⟩).toFunctor.obj ((H.map a).toFunctor.obj z)) ∧
      (∀ (j k l : J) (a : j ⟶ k) (b : k ⟶ l) (z : H.obj j),
        HEq
          (((SplitFamily.transport.{w, v, u} P F hF j).obj
            ((αtilde.app j).toFunctor.obj z)).transition k l a b)
          ((Cat.Hom.toNatIso (α.naturality b.toLoc)).symm.app
            ((H.map a).toFunctor.obj z))) ∧
      (∀ (j k : J) (a : j ⟶ k) {z z' : H.obj j} (t : z ⟶ z'),
        HEq
          (((SplitFamily.transport.{w, v, u} P F hF j).map
            ((αtilde.app j).toFunctor.map t)).val k a)
          ((α.app ⟨k⟩).toFunctor.map ((H.map a).toFunctor.map t))) ∧
      (∀ (j k : J) (a : j ⟶ k) (z : H.obj j),
        HEq ((κ a).app ((αtilde.app j).toFunctor.obj z))
          ((Cat.Hom.toNatIso (α.naturality a.toLoc)).symm.app z)) ∧
      (∀ (I : Type (max w v u)) [SmallCategory I] (v : I ⥤ J) (R : I ⥤ Cat.{max w v u, max w v u})
        (_hR : v.toPseudofunctor.comp P = R.toPseudofunctor')
        (β : v ⋙ H ⟶ R)
        (_hβ : ∀ i : I, HEq (β.app i) (α.app ⟨v.obj i⟩))
        (_hθ : ∀ (i i' : I) (r : i ⟶ i'),
          HEq (α.naturality (v.map r).toLoc)
            (Iso.refl ((H.map (v.map r)) ≫ α.app ⟨v.obj i'⟩))),
        ∃ (K : I ⥤ Cat.{max w v u, max w v u}) (A : v ⋙ H ⟶ K)
          (q : K ⟶ v ⋙ F) (p : K ⟶ R),
          (∀ i : I, (q.app i).toFunctor.IsEquivalence) ∧
          (∀ i : I, (p.app i).toFunctor.IsEquivalence) ∧
          A ≫ q = Functor.whiskerLeft v αtilde ∧ A ≫ p = β) := by
  sorry

end Pseudofunctor

end CategoryTheory
