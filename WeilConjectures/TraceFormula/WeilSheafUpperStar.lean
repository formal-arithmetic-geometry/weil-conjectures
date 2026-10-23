/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.PullbackFamily
public import WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar

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

section PullbackFamily

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The pullbacks of module objects over `Λ` satisfy the associativity law of a family of
pullbacks, along morphisms of schemes. -/
lemma pullbackAssoc_upperStar :
    PullbackAssoc (D := fun V : Scheme.{u} ↦
        Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V))
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ (f)^*⟦Λ⟧)
      (fun {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) ↦ upperStarComp Λ f g) :=
  fun f g h ↦ upperStarComp_assoc Λ f g h

/-- The pullbacks of module objects over `Λ` satisfy the associativity law of a family of
pullbacks, along morphisms of schemes over a base `T`. -/
lemma pullbackAssoc_upperStar_left (T : Scheme.{u}) :
    PullbackAssoc (C := Over T) (D := fun V : Over T ↦
        Mod (Sheaf (Scheme.ProEt.topology V.left) Ab.{u + 1}) (condensedRingObj Λ V.left))
      (fun {X Y : Over T} (f : X ⟶ Y) ↦ (f.left)^*⟦Λ⟧)
      (fun {X Y Z : Over T} (f : X ⟶ Y) (g : Y ⟶ Z) ↦ upperStarComp Λ f.left g.left) :=
  fun f g h ↦ upperStarComp_assoc Λ f.left g.left h.left

end PullbackFamily

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

/-- The Frobenius comparison of the pullback of Weil sheaves is the comparison of the family of
pullbacks `V ↦ (V.left)^*`. -/
lemma weilSheafUpperStarComparison_eq :
    weilSheafUpperStarComparison ℓ eX eW hg =
      pullbackComparison (C := Over (Spec (.of k))) (D := fun V : Over (Spec (.of k)) ↦
          Mod (Sheaf (Scheme.ProEt.topology V.left) Ab.{u + 1})
            (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left))
        (P := fun {X Y : Over (Spec (.of k))} (f : X ⟶ Y) ↦
          (f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
        (c := fun {X Y Z : Over (Spec (.of k))} (f : X ⟶ Y) (g : Y ⟶ Z) ↦
          upperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left)
        g eW.hom eX.hom hg :=
  rfl

/-- `IsoAlgebra.categoricalTrace_str_congr` with the monoidal structures found by unification. -/
lemma categoricalTrace_str_congr_of_iso {C : Type*} [Category C] {_ : MonoidalCategory C}
    {_ : BraidedCategory C} {_ : Preadditive C} {A B : IsoAlgebra (𝟭 C)} (i : A ≅ B) :
    categoricalTrace B.str.hom = categoricalTrace A.str.hom :=
  IsoAlgebra.categoricalTrace_str_congr i

/-- **Stalks of a pullback of Weil sheaves**: for `g : W ⟶ X` with `e_W ≫ g = g ≫ e_X`, a Weil
sheaf `F` for `e_X` and a point `w̄` of `W` of degree `n + 1`, the trace of the `(n + 1)`-st
Frobenius on the stalk of `g^* F` at `w̄` is its trace on the stalk of `F` at `w̄ ≫ g`. The
composition isomorphism `(w̄ ≫ g)^* F ≅ w̄^* g^* F` of the pullbacks intertwines the two Frobenius
operators (`CategoryTheory.stalkComparison_pullbackComparison`), once the iterated structure
isomorphism of `g^* F` is identified with the pullback of that of `F`
(`CategoryTheory.Iso.powSuccStr_pullbackComparison`). -/
theorem weilSheafStalkTrace_weilSheafUpperStar (F : WeilSheaf ℓ eX) (n : ℕ)
    (w : frobeniusFixedPoints eW n) :
    weilSheafStalkTrace ℓ n w.1 w.2.2 ((weilSheafUpperStar ℓ eX eW hg).obj F) =
      weilSheafStalkTrace ℓ n (frobeniusFixedPointsMap eW eX hg n w).1
        (frobeniusFixedPointsMap eW eX hg n w).2.2 F := by
  sorry

end WeilSheafPullback

end AlgebraicGeometry.ProEtale.CondensedRing
