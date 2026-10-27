module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Over

/-! # Weighted central extensions of the additive group sheaf

Source: Conrad, Reductive group schemes, Proposition 4.3.1 and Lemma 4.3.2,
printed pp.127–128 (blueprint: def-sfb-weighted-additive-extension-datum).

The additive quotient is the actual global-sections functor, with its additive group
written multiplicatively. Universe lifts allow the middle sheaf to have larger section sets.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry

set_option autoImplicit false

/-- The additive group functor on all `S`-schemes, with its addition written multiplicatively.
Source: Conrad, Proposition 4.3.1, printed p.127
(blueprint: def-sfb-weighted-additive-extension-datum). -/
def fppfAdditiveGroup (S : Scheme.{u}) : (Over S)ᵒᵖ ⥤ GrpCat.{max u v} :=
  (Over.forget S).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat ⋙
    forget₂ RingCat AddCommGrpCat ⋙ AddCommGrpCat.toCommGrp ⋙
    forget₂ CommGrpCat GrpCat ⋙ GrpCat.uliftFunctor.{v, u}

set_option backward.isDefEq.respectTransparency false in
/-- Multiplication by the integer character `t ↦ t^k` on the additive quotient.
Source: Conrad, Lemma 4.3.2, printed p.128
(blueprint: def-sfb-weighted-additive-extension-datum). -/
def fppfAdditiveWeight (S : Scheme.{u}) (k : ℤ) (T : Over S)
    (t : Γ(T.left, ⊤)ˣ) (a : (fppfAdditiveGroup.{u, v} S).obj (op T)) :
    (fppfAdditiveGroup.{u, v} S).obj (op T) :=
  @ULift.up.{v, u} (Multiplicative Γ(T.left, ⊤))
    (@Multiplicative.ofAdd Γ(T.left, ⊤)
      ((↑(t ^ k) : Γ(T.left, ⊤)) * (@Multiplicative.toAdd Γ(T.left, ⊤) a.down)))

/-- A central exact extension of the additive fppf sheaf by the points of an `S`-group
scheme, equipped with a natural multiplicative-group action fixing the kernel and inducing
weight `k` on the quotient. Exactness includes injectivity of the first map, its identification
with the entire kernel, and fppf local surjectivity of the quotient map. No representability
of the middle sheaf is imposed.

Source: Conrad, Proposition 4.3.1 and Lemma 4.3.2, printed pp.127–128
(blueprint: def-sfb-weighted-additive-extension-datum). -/
structure WeightedAdditiveExtension (S : Scheme.{u}) (Z : Over S) [GrpObj Z] (k : ℤ) where
  /-- The middle group-valued functor. -/
  F : (Over S)ᵒᵖ ⥤ GrpCat.{max u v}
  /-- Unique gluing for the fppf topology. -/
  isSheaf : Presheaf.IsSheaf (Scheme.fppfTopology.over S) (F ⋙ forget GrpCat)
  /-- The kernel inclusion. -/
  i : yonedaGrpObj Z ⋙ GrpCat.uliftFunctor.{v, u} ⟶ F
  /-- The additive quotient map. -/
  q : F ⟶ fppfAdditiveGroup.{u, v} S
  /-- The first map identifies its source with a subgroup sheaf. -/
  injective_i : ∀ T : Over S, Function.Injective (i.app (op T))
  /-- Its image is exactly the kernel of the second map, on every test scheme. -/
  exact_i_q : ∀ (T : Over S) (x : F.obj (op T)),
    q.app (op T) x = 1 ↔ ∃ z, i.app (op T) z = x
  /-- Sections of the quotient lift fppf-locally. -/
  locallySurjective_q : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) q
  /-- The kernel commutes with every section. -/
  central : ∀ (T : Over S) (z : (yonedaGrpObj Z ⋙ GrpCat.uliftFunctor.{v, u}).obj (op T))
    (x : F.obj (op T)), i.app (op T) z * x = x * i.app (op T) z
  /-- An action by group automorphisms on every test scheme. -/
  action : ∀ T : Over S, Γ(T.left, ⊤)ˣ →* MulAut (F.obj (op T))
  /-- The action commutes with restriction, including restriction of the acting unit. -/
  action_natural : ∀ (T T' : Over S) (r : T' ⟶ T) (t : Γ(T.left, ⊤)ˣ)
    (x : F.obj (op T)),
    F.map r.op (action T t x) =
      action T' (Units.map r.left.appTop.hom.toMonoidHom t) (F.map r.op x)
  /-- The kernel is fixed pointwise. -/
  action_i : ∀ (T : Over S) (t : Γ(T.left, ⊤)ˣ)
    (z : (yonedaGrpObj Z ⋙ GrpCat.uliftFunctor.{v, u}).obj (op T)),
    action T t (i.app (op T) z) = i.app (op T) z
  /-- The induced action on the quotient is multiplication by `t^k`. -/
  action_q : ∀ (T : Over S) (t : Γ(T.left, ⊤)ˣ) (x : F.obj (op T)),
    q.app (op T) (action T t x) = fppfAdditiveWeight S k T t (q.app (op T) x)

end AlgebraicGeometry
