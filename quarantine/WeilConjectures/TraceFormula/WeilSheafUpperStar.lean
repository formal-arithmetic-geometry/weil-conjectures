/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.PullbackFamily
public import WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar
public import WeilConjectures.WeilObject.BoundedConstructible.Homology

/-!

# The pullback of Weil sheaves

Let `g : W ⟶ X` be a morphism over a finite field `k` with automorphisms `e_W`, `e_X` such that
`e_W ≫ g = g ≫ e_X`. The pullback `g^*` of module objects sends a Weil sheaf `(F, φ_F)` for `e_X`
to the Weil sheaf `g^* F` for `e_W` (`ProEtale.CondensedRing.weilSheafUpperStar`). This file
proves the two inputs of the dévissage of the local trace along a pullback
(`ProEtale.CondensedRing.weilStalkSupertrace_weilUpperStar`):

- `ProEtale.CondensedRing.nonempty_homologyFunctor_weilUpperStar_iso`: for a Weil object `K` of
  `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, `Hʲ(Lg^* K) ≅ g^* Hʲ(K)` as Weil sheaves;
- `ProEtale.CondensedRing.weilSheafStalkTrace_weilSheafUpperStar`: the trace of the Frobenius on
  the stalk of `g^* F` at a point `w̄` of `W` is its trace on the stalk of `F` at `w̄ ≫ g`.

Both are instances of the coherence of the composition isomorphisms of pullbacks
(`WeilConjectures.TraceFormula.PullbackFamily`).

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### The pullbacks of module objects as a family of pullbacks -/

/-- The pullbacks of module objects over `ℚ̲̄_ℓ` satisfy the associativity law of a family of
pullbacks, along morphisms of schemes. -/
lemma pullbackAssoc_upperStar (ℓ : ℕ) [Fact ℓ.Prime] :
    PullbackAssoc (upperStar (Profinite.padicAlgClRingObj ℓ))
      (fun {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) ↦
        upperStarComp (Profinite.padicAlgClRingObj ℓ) f g) :=
  fun f g h ↦ upperStarComp_assoc _ f g h

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X W : Over (Spec (.of k))} (eX : X ≅ X) (eW : W ≅ W)

/-! ### The pullback of Weil sheaves -/

section WeilSheafPullback

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

omit [Finite k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- The pullback of Weil sheaves is the pullback of algebras for the family of pullbacks of
module objects. -/
lemma weilSheafUpperStar_eq :
    weilSheafUpperStar ℓ eX eW hg =
      Endofunctor.IsoAlgebra.overPullback (P := upperStar (Profinite.padicAlgClRingObj ℓ))
        (fun {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) ↦
          upperStarComp (Profinite.padicAlgClRingObj ℓ) f g) eX eW hg :=
  rfl

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- The stalk functor of Weil sheaves with the `(n + 1)`-st Frobenius operator is the Frobenius
stalk functor of algebras for the family of pullbacks of module objects. -/
lemma WeilSheaf.powSuccStalkFunctor_eq (n : ℕ) (x : Spec (.of (AlgebraicClosure k)) ⟶ W.left)
    (hx : x ≫ (eW.powSucc n).hom.left = ((geometricFrobeniusField k).powSucc n).hom ≫ x) :
    WeilSheaf.powSuccStalkFunctor ℓ n x hx =
      Endofunctor.IsoAlgebra.frobeniusStalkFunctor (P := upperStar (Profinite.padicAlgClRingObj ℓ))
        (fun {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) ↦
          upperStarComp (Profinite.padicAlgClRingObj ℓ) f g)
        (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ)
          ((geometricFrobeniusField k).powSucc n).hom) eW n x hx :=
  rfl

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- The trace of the Frobenius on the stalk only depends on the stalk with its Frobenius operator
up to isomorphism, for possibly different Weil sheaves and points. -/
lemma weilSheafStalkTrace_eq_of_iso (n : ℕ) {x : Spec (.of (AlgebraicClosure k)) ⟶ W.left}
    {hx : x ≫ (eW.powSucc n).hom.left = ((geometricFrobeniusField k).powSucc n).hom ≫ x}
    {x' : Spec (.of (AlgebraicClosure k)) ⟶ X.left}
    {hx' : x' ≫ (eX.powSucc n).hom.left = ((geometricFrobeniusField k).powSucc n).hom ≫ x'}
    {G : WeilSheaf ℓ eW} {F : WeilSheaf ℓ eX}
    (i : (WeilSheaf.powSuccStalkFunctor ℓ n x hx).obj G ≅
      (WeilSheaf.powSuccStalkFunctor ℓ n x' hx').obj F) :
    weilSheafStalkTrace ℓ n x hx G = weilSheafStalkTrace ℓ n x' hx' F :=
  (IsoAlgebra.categoricalTrace_str_congr i).symm
omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- **Stalks of a pullback of Weil sheaves**: for `g : W ⟶ X` with `e_W ≫ g = g ≫ e_X`, a Weil
sheaf `F` for `e_X` and a point `w̄` of `W` of degree `n + 1`, the trace of the `(n + 1)`-st
Frobenius on the stalk of `g^* F` at `w̄` is its trace on the stalk of `F` at `w̄ ≫ g`. The
composition isomorphism `(w̄ ≫ g)^* F ≅ w̄^* g^* F` of the pullbacks intertwines the two Frobenius
operators (`CategoryTheory.pullbackFamilyStalkComparison_pullbackFamilyComparison`), once the
iterated structure
isomorphism of `g^* F` is identified with the pullback of that of `F`
(`CategoryTheory.Iso.powSuccStr_pullbackFamilyComparison`). -/
theorem weilSheafStalkTrace_weilSheafUpperStar (F : WeilSheaf ℓ eX) (n : ℕ)
    (w : frobeniusFixedPoints eW n) :
    weilSheafStalkTrace ℓ n w.1 w.2.2 ((weilSheafUpperStar ℓ eX eW hg).obj F) =
      weilSheafStalkTrace ℓ n (frobeniusFixedPointsMap eW eX hg n w).1
        (frobeniusFixedPointsMap eW eX hg n w).2.2 F := by
  have I := Classical.choice
    (Endofunctor.IsoAlgebra.nonempty_obj_obj_iso_of_eq
      (c := fun {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) ↦
        upperStarComp (Profinite.padicAlgClRingObj ℓ) f g)
      (pullbackAssoc_upperStar ℓ) eX eW hg n
      (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ)
        ((geometricFrobeniusField k).powSucc n).hom) w.1 w.2.2
      (x := (frobeniusFixedPointsMap eW eX hg n w).1) rfl
      (frobeniusFixedPointsMap eW eX hg n w).2.2 (WeilSheaf ℓ eX) (WeilSheaf ℓ eW)
      (IsoAlgebra (𝟭 (GeometricPointMod ℓ (AlgebraicClosure k)))) F
      (weilSheafUpperStar ℓ eX eW hg) (WeilSheaf.powSuccStalkFunctor ℓ n w.1 w.2.2)
      (WeilSheaf.powSuccStalkFunctor ℓ n (frobeniusFixedPointsMap eW eX hg n w).1
        (frobeniusFixedPointsMap eW eX hg n w).2.2) rfl rfl rfl
      (heq_of_eq (weilSheafUpperStar_eq ℓ eX eW hg))
      (heq_of_eq (WeilSheaf.powSuccStalkFunctor_eq ℓ eW n _ _))
      (heq_of_eq (WeilSheaf.powSuccStalkFunctor_eq ℓ eX n _ _)))
  exact weilSheafStalkTrace_eq_of_iso ℓ eX eW n I

/-- **The homology sheaves of a pullback of Weil objects** (still `sorry`): for `g : W ⟶ X` with
`e_W ≫ g = g ≫ e_X`, the Weil sheaf `Hʲ(Lg^* K)` is isomorphic to the pullback `g^* Hʲ(K)` of the
Weil sheaf `Hʲ(K)`.

The isomorphism is the commutation `θ_g : Hʲ ⋙ g^* ≅ Lg^* ⋙ Hʲ` of the exact functor `g^*` with
homology. It is compatible with the Weil structures because `θ` is pseudonatural, and the
formal part of the argument is proved:
`Endofunctor.IsoAlgebra.nonempty_mapOfNatIso_pullback_iso` gives the isomorphism from
pseudonaturality (`CategoryTheory.PullbackPseudonatural`), and
`CategoryTheory.PullbackPseudonatural.lifted` reduces pseudonaturality on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` to
pseudonaturality on the derived categories of module objects. The latter is the composition
law of `CategoryTheory.Functor.leftDerivedFunctorHomologyFunctorIso`
(`Functor.leftDerivedFunctorHomologyFunctorIso_hom_app_comp_map_leftDerivedFunctorNatIso` and
`Functor.leftDerivedFunctorHomologyFunctorIso_hom_app_comp_map_leftDerivedFunctorCompIso`) applied
to the composition isomorphisms `upperStarComp`. What is missing is the instantiation of these
generic statements for the pullbacks of module objects. -/
theorem nonempty_homologyFunctor_weilUpperStar_iso [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    [IsSeparated W.hom] (K : WeilBoundedConstructible ℓ eX.hom) (j : ℤ) :
    Nonempty ((WeilBoundedConstructible.homologyFunctor ℓ eW j).obj
        ((weilUpperStar ℓ eW.hom eX.hom g hg).obj K) ≅
      (weilSheafUpperStar ℓ eX eW hg).obj
        ((WeilBoundedConstructible.homologyFunctor ℓ eX j).obj K)) :=
  sorry

end WeilSheafPullback

end AlgebraicGeometry.ProEtale.CondensedRing
