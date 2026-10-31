/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Geometric pullbacks detect isomorphisms in the unbounded derived category

Source: blueprint latest, sec-smooth-purity/sk-prop-sf-kunneth-ordinary,
lemma "Stalk faithfulness for derived objects"
(blueprint: lem-kun-stalk-faithful-derived).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- A morphism in the unbounded derived category of abelian étale sheaves is invertible
if and only if its pullback to every geometric point is invertible.

Source: blueprint latest, sec-smooth-purity/sk-prop-sf-kunneth-ordinary,
lemma "Stalk faithfulness for derived objects"
(blueprint: lem-kun-stalk-faithful-derived).

Proof:
1. Every functor preserves isomorphisms, giving the forward implication.
2. For the converse, apply the unbounded derived-category cohomology criterion
   `DerivedCategory.isIso_iff` and fix a degree `n`.
3. Exactness of inverse image gives its natural cohomology comparison
   `Functor.mapDerivedCategoryHomologyFunctorIso`. Thus every geometric pullback of
   the degree-`n` cohomology morphism is invertible.
4. Take the geometric point given by an algebraic closure of the residue field at
   each point of `T`. The pullback-stalk comparison
   `upperStarCompUliftSheafFiberIso` identifies its stalk with the stalk at the
   identity point of the pullback. The latter is invertible by functoriality.
5. The geometric sheaf-stalk criterion `Scheme.isIso_of_isIso_sheafFiber_map` makes
   the cohomology morphism invertible. This holds in every integer degree, with no
   boundedness assumption. -/
theorem isIso_iff_forall_isIso_geometricPullback_map {T : Scheme.{u}}
    {K L : _root_.DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (α : K ⟶ L) :
    IsIso α ↔ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
      IsIso ((upperStar AddCommGrpCat.{u + 1} t).mapDerivedCategory.map α) := by
  refine ⟨fun _ _ _ _ _ ↦ inferInstance, fun h ↦ ?_⟩
  rw [_root_.DerivedCategory.isIso_iff]
  intro n
  apply Scheme.isIso_of_isIso_sheafFiber_map
  intro s
  let t := T.algClosurePoint s
  have ht : IsIso ((upperStar AddCommGrpCat.{u + 1} t).mapDerivedCategory.map α) := h _ t
  have hH : IsIso ((upperStar AddCommGrpCat.{u + 1} t).map
      ((_root_.DerivedCategory.homologyFunctor _ n).map α)) :=
    (NatIso.isIso_map_iff
      ((upperStar AddCommGrpCat.{u + 1} t).mapDerivedCategoryHomologyFunctorIso n) α).2
        (Functor.map_isIso (_root_.DerivedCategory.homologyFunctor _ n) _)
  have hF : IsIso (((upperStar AddCommGrpCat.{u + 1} t) ⋙
      ((Scheme.pointSmallEtale
        (𝟙 (Spec (.of (AlgebraicClosure (T.residueField s)))))).ulift.{u + 1}).sheafFiber).map
          ((_root_.DerivedCategory.homologyFunctor _ n).map α)) := by
    dsimp only [Functor.comp_map]
    infer_instance
  let e := upperStarCompUliftSheafFiberIso AddCommGrpCat.{u + 1} t (𝟙 _)
  have e' : upperStar AddCommGrpCat.{u + 1} t ⋙
      ((Scheme.pointSmallEtale
        (𝟙 (Spec (.of (AlgebraicClosure (T.residueField s)))))).ulift.{u + 1}).sheafFiber ≅
      ((Scheme.pointSmallEtale t).ulift.{u + 1}).sheafFiber :=
    e ≪≫ eqToIso (by rw [Category.id_comp])
  exact (NatIso.isIso_map_iff e'
    ((_root_.DerivedCategory.homologyFunctor _ n).map α)).1 hF

end AlgebraicGeometry.Etale
