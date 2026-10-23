/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.FiniteEtaleStalkTrace
public import WeilConjectures.TraceFormula.HomologyWeilLowerShriek
public import WeilConjectures.TraceFormula.ShriekTraceFunction
public import WeilConjectures.TraceFormula.StalkDualizable

/-!

# The sheaf–function compatibility along a finite étale morphism

For a finite étale morphism `f : X ⟶ Y` with automorphisms `e_X`, `e_Y` such that
`e_X ≫ f = f ≫ e_Y`, the sheaf–function compatibility `ShriekTraceFunctionAt` holds
(`ProEtale.CondensedRing.shriekTraceFunctionAt_of_isFinite_of_etale'`): this is the
Grothendieck–Lefschetz formula in dimension zero. The proof:

1. `Hʲ(Rf_!^Weil K) ≅ f_* Hʲ(K)` as Weil sheaves
   (`ProEtale.CondensedRing.nonempty_homologyFunctor_weilLowerShriek_iso`);
2. the iterated Weil structure of `f_* Hʲ(K)` is the pushforward of the iterated structure of
   `Hʲ(K)` (`ProEtale.CondensedRing.nonempty_powSucc_weilSheafLowerStar_iso`);
3. the stalk of `f_* Hʲ(K)` at `ȳ` is the product of the stalks of `Hʲ(K)` at the points over `ȳ`,
   permuted by the Frobenius, so its trace is the sum of the traces at the fixed points
   (`ProEtale.CondensedRing.categoricalTrace_stalkFunctor_weilSheafLowerStar`), the stalks being
   dualizable (`ProEtale.CondensedRing.nonempty_hasRightDual_upperStar_homology`);
4. the sums over `j` and over the points are exchanged.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)

/-- The points of degree `n + 1` of `X` over a point `ȳ` of `Y` of degree `n + 1` are the
geometric points over `ȳ` fixed by the twisted Frobenius. -/
def frobeniusFixedPointsFiberEquivGeometricFibre (n : ℕ) (y : frobeniusFixedPoints eY n) :
    {x : frobeniusFixedPoints eX n // x.1 ≫ f.left = y.1} ≃
      {x : GeometricFibre f.left y.1 //
        x.1 ≫ (eX.powSucc n).hom.left = ((geometricFrobeniusField k).powSucc n).hom ≫ x.1} where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2.2⟩
  invFun x := ⟨⟨x.1.1, by rw [← Over.w f, ← Category.assoc, x.1.2, y.2.1], x.2⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The local trace through the explicit stalk Frobenius**: the trace `Tr(Fr_{x̄,n+1} | F_x̄)`
of a Weil sheaf `F` for `e` at a point of degree `n + 1` is the trace of the explicit Frobenius
`stalkFrobenius` of the stalk of the Weil sheaf `F^{(n+1)}` for `e^{n+1}`. -/
theorem weilSheafStalkTrace_eq_categoricalTrace_stalkFrobenius {Z : Over (Spec (.of k))}
    {e : Z ≅ Z} (n : ℕ) (x : Spec (.of (AlgebraicClosure k)) ⟶ Z.left)
    (hx : x ≫ (e.powSucc n).hom.left = ((geometricFrobeniusField k).powSucc n).hom ≫ x)
    (F : WeilSheaf ℓ e) :
    weilSheafStalkTrace ℓ n x hx F = categoricalTrace (stalkFrobenius ℓ
      ((geometricFrobeniusField k).powSucc n).hom (e.powSucc n) hx
      (WeilSheaf.powSucc ℓ F n).str.hom) :=
  sorry

/-- The trace of the Frobenius on the stalk of the pushforward `f_* F` of a Weil sheaf along a
finite étale morphism at a point `ȳ` of degree `n + 1` is the sum of the traces at the points of
degree `n + 1` over `ȳ`, provided the stalks of `F` over `ȳ` are dualizable. -/
theorem weilSheafStalkTrace_weilSheafLowerStar [IsFinite f.left] [Etale f.left] (n : ℕ)
    (y : frobeniusFixedPoints eY n) (F : WeilSheaf ℓ eX)
    (hF : ∀ x : GeometricFibre f.left y.1,
      Nonempty (HasRightDual ((x.1)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj F.carrier))) :
    weilSheafStalkTrace ℓ n y.1 y.2.2 ((weilSheafLowerStar ℓ eX eY hf).obj F) =
      ∑ᶠ x : {x : frobeniusFixedPoints eX n // x.1 ≫ f.left = y.1},
        weilSheafStalkTrace ℓ n x.1.1 x.1.2.2 F := by
  rw [weilSheafStalkTrace_eq_categoricalTrace_stalkFrobenius, powSucc_weilSheafLowerStar_obj,
    weilSheafLowerStar_obj_str, Iso.trans_hom, Functor.mapIso_hom,
    categoricalTrace_stalkFrobenius_lowerStar ℓ (eX.powSucc n) (eY.powSucc n) _ _ y.2.2 _ hF]
  refine (finsum_comp_equiv (frobeniusFixedPointsFiberEquivGeometricFibre eX eY n y)
    (f := fun x ↦ categoricalTrace (stalkFrobenius ℓ ((geometricFrobeniusField k).powSucc n).hom
      (eX.powSucc n) x.2 (WeilSheaf.powSucc ℓ F n).str.hom))).symm.trans ?_
  exact finsum_congr fun x ↦
    (weilSheafStalkTrace_eq_categoricalTrace_stalkFrobenius ℓ n x.1.1 x.1.2.2 F).symm

/-- **Dimension zero**: the sheaf–function compatibility holds along a finite étale morphism. -/
theorem shriekTraceFunctionAt_of_isFinite_of_etale' [IsFinite f.left] [Etale f.left] :
    ShriekTraceFunctionAt ℓ eX eY hf := by
  intro K n y
  classical
  have : Finite {x : frobeniusFixedPoints eX n // x.1 ≫ f.left = y.1} :=
    Finite.of_equiv _ (frobeniusFixedPointsFiberEquivGeometricFibre eX eY n y).symm
  let := Fintype.ofFinite {x : frobeniusFixedPoints eX n // x.1 ≫ f.left = y.1}
  have h : ∀ j : ℤ, weilSheafStalkTrace ℓ n y.1 y.2.2
      ((WeilBoundedConstructible.homologyFunctor ℓ eY j).obj ((weilLowerShriek ℓ eX eY hf).obj K)) =
      ∑ x : {x : frobeniusFixedPoints eX n // x.1 ≫ f.left = y.1},
        weilSheafStalkTrace ℓ n x.1.1 x.1.2.2 ((WeilBoundedConstructible.homologyFunctor ℓ eX j).obj K) := by
    intro j
    obtain ⟨i⟩ := nonempty_homologyFunctor_weilLowerShriek_iso ℓ eX eY hf K j
    rw [weilSheafStalkTrace_congr ℓ n y.1 y.2.2 i, weilSheafStalkTrace_weilSheafLowerStar ℓ eX eY hf
      n y _ fun x ↦ nonempty_hasRightDual_upperStar_homology ℓ K.carrier j x.1,
      finsum_eq_sum_of_fintype]
  rw [weilStalkSupertrace_eq, finsum_congr fun j ↦ by rw [h j, Finset.smul_sum],
    finsum_sum_comm _ _ fun x _ ↦ ?_, finsum_eq_sum_of_fintype]
  · exact Finset.sum_congr rfl fun x _ ↦ (weilStalkSupertrace_eq ℓ n x.1.1 x.1.2.2 K).symm
  · exact (finite_support_weilSheafStalkTrace_homology ℓ n x.1.1 x.1.2.2 K).subset
      fun j hj ↦ by
        contrapose! hj
        simp only [Function.mem_support, not_not] at hj ⊢
        rw [hj, smul_zero]

end AlgebraicGeometry.ProEtale.CondensedRing
