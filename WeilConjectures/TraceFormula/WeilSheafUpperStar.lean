/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Additivity
public import WeilConjectures.TraceFormula.ShriekTraceFunction
public import WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar

/-!

# The pullback of Weil sheaves

For `g : W ⟶ X` with `e_W ≫ g = g ≫ e_X`, the pullback `g^*` of module objects induces a pullback
of Weil sheaves (`ProEtale.CondensedRing.weilSheafUpperStar`). It is compatible with the homology
of Weil objects (`ProEtale.CondensedRing.nonempty_homologyFunctor_weilUpperStar_iso`) and with
the traces of the Frobenius on stalks
(`ProEtale.CondensedRing.weilSheafStalkTrace_weilSheafUpperStar`).

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Over

/-- An equation `a ≫ b = c ≫ d` in `Over T` holds for the underlying morphisms. -/
lemma left_comp_left_eq_of_comp_eq {S : Type*} [Category S] {T : S} {A B C D : Over T}
    {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ C} {d : C ⟶ D} (h : a ≫ b = c ≫ d) :
    a.left ≫ b.left = c.left ≫ d.left := by
  rw [← Over.comp_left, h, Over.comp_left]

end CategoryTheory.Over

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y W : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
  (eX : X ≅ X) (eY : Y ≅ Y) (eW : W ≅ W)



variable {g : W ⟶ X} (hg : eW.hom ≫ g = g ≫ eX.hom)

/-- The Frobenius comparison `g^* ⋙ e_W^* ≅ e_X^* ⋙ g^*` of the pullback of module objects along
`g` with `e_W ≫ g = g ≫ e_X`: the composite of the composition isomorphisms of the pullbacks and
the transport along `e_W ≫ g = g ≫ e_X`. -/
noncomputable def weilSheafUpperStarComparison :
    (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ⋙ (eW.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅
      (eX.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ⋙
        (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (upperStarComp _ eW.hom.left g.left).symm ≪≫
    eqToIso (congrArg (upperStar _) (Over.left_comp_left_eq_of_comp_eq hg)) ≪≫
    upperStarComp _ g.left eX.hom.left

/-- The pullback `g^*` of Weil sheaves along `g : W ⟶ X` with `e_W ≫ g = g ≫ e_X`: a Weil sheaf
`(F, φ_F)` for `e_X` is sent to `g^* F` with the structure isomorphism
`e_W^* g^* F ≅ g^* e_X^* F ≅ g^* F` given by `weilSheafUpperStarComparison` and `g^* φ_F`. -/
noncomputable def weilSheafUpperStar : WeilSheaf ℓ eX ⥤ WeilSheaf ℓ eW :=
  IsoAlgebra.mapOfNatIso (weilSheafUpperStarComparison ℓ eX eW hg)

/-- **The homology sheaves of a pullback of Weil objects** (standard input, still `sorry`): for
`g : W ⟶ X` with `e_W ≫ g = g ≫ e_X`, the Weil sheaf `Hʲ(Lg^* K)` is isomorphic to the pullback
`g^* Hʲ(K)` of the Weil sheaf `Hʲ(K)`. The underlying isomorphism is the commutation of the exact
functor `g^*` with homology (as in `weilHomologyComparison`, with the identification of the derived
pullback with the levelwise pullback); its compatibility with the Frobenius structures is the
compatibility of these commutation isomorphisms with the composition isomorphisms of the
pullbacks, along `e_W ≫ g = g ≫ e_X`. -/
theorem nonempty_homologyFunctor_weilUpperStar_iso (K : WeilBoundedConstructible ℓ eX.hom)
    (j : ℤ) :
    Nonempty ((WeilBoundedConstructible.homologyFunctor ℓ eW j).obj
        ((weilUpperStar ℓ eW.hom eX.hom g hg).obj K) ≅
      (weilSheafUpperStar ℓ eX eW hg).obj
        ((WeilBoundedConstructible.homologyFunctor ℓ eX j).obj K)) :=
  sorry

/-- **Stalks of a pullback of Weil sheaves** (standard input, still `sorry`): for `g : W ⟶ X`
with `e_W ≫ g = g ≫ e_X`, a Weil sheaf `F` for `e_X` and a point `w̄` of `W` of degree `n + 1`,
the trace of the `(n + 1)`-st Frobenius on the stalk of `g^* F` at `w̄` is its trace on the stalk
of `F` at `w̄ ≫ g`. The composition isomorphism `(w̄ ≫ g)^* F ≅ w̄^* g^* F` of the pullbacks
intertwines the two Frobenius operators: this is a coherence of the composition isomorphisms
`upperStarComp` (their associativity), applied to the iterated structure isomorphisms
`WeilSheaf.powSucc` and to the stalk comparison `weilStalkComparison`. -/
theorem weilSheafStalkTrace_weilSheafUpperStar (F : WeilSheaf ℓ eX) (n : ℕ)
    (w : frobeniusFixedPoints eW n) :
    weilSheafStalkTrace ℓ n w.1 w.2.2 ((weilSheafUpperStar ℓ eX eW hg).obj F) =
      weilSheafStalkTrace ℓ n (frobeniusFixedPointsMap eW eX hg n w).1
        (frobeniusFixedPointsMap eW eX hg n w).2.2 F :=
  sorry


end AlgebraicGeometry.ProEtale.CondensedRing
