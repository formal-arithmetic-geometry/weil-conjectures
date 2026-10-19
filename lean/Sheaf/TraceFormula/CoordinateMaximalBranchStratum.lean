module

public import Sheaf.AlgebraicGeometry.NormalCrossingsBranchCount
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
import Sheaf.AlgebraicGeometry.IsRegularScheme
import Sheaf.AlgebraicGeometry.StrictHenselizationLocalPresentation
import Sheaf.RingTheory.Etale.LocalDimension
import Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence
import Sheaf.RingTheory.StrictHenselizationFaithfullyFlat
import Sheaf.RingTheory.StrictHenselizationRegular
import Sheaf.RingTheory.StrictHenselizationSurjectiveQuotient
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Coordinate description of the maximal branch stratum

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé VIII, 4.1.6 and 4.1.8,
printed pp. 118--119 (blueprint: lem-trf-nc-coordinate-max-stratum).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- In a regular locally Noetherian coordinate chart, the locus with the maximal number
of vanishing coordinates is the regular reduced coordinate intersection.  The branch count
is the intrinsic normal-crossings count. Geometric points are encoded by an underlying
point and a residue-field embedding into an algebraically closed field in any larger universe.
The final clause states every assertion after étale base change and compares any other
coordinate equations defining the same closed subscheme; taking the identity base change
gives coordinate-equation independence on the original chart.
Source: ILO VIII 4.1.6 and 4.1.8 (blueprint: lem-trf-nc-coordinate-max-stratum).

Proof:
1. Fix a point with local ring `A`. The vanishing coordinate germs are part of a
regular system of parameters. By `lem-weil-pbc-regular-local-generators-regular-sequence`,
their single-parameter quotients are regular local. The geometric local presentation
`lem-sbc-geometric-strict-henselization-local-presentation` and the quotient comparison
`lem-sbc-strict-henselization-surjective-quotient` identify their strict local quotients.
These are regular by `lem-sc-strict-henselization-regular` and domains by
`lem-sc-regular-local-domain`, so the corresponding coordinate ideals are prime.
2. Distinct parameter ideals are incomparable: quotienting by one leaves the other
nonzero. Faithful flatness (`lem-sc-strict-henselization-faithfully-flat`) and ideal
contraction (`lem-weil-pbc-faithfully-flat-ideal-contraction`) preserve this distinction
in the strict henselization. A prime containing the product contains one factor, so
these are exactly its minimal primes. Reduction preserves this prime poset. Unit factors
contribute nothing; off the divisor the branch count is zero. This proves the intrinsic
branch formula and independence of coordinate equations.
3. At a point of the full intersection, quotient by all the selected parameters.
The parameter-quotient theorem gives a regular local ring. Affine quotients of Noetherian
rings are Noetherian, hence the intersection is regular. Its local rings are domains and
therefore reduced. If the intersection is empty these local assertions are vacuous.
4. A finite set has at least `k` members exactly when it contains a `k`-element subset.
This proves the finite union formula, its extreme integer cases, the bound, the deepest
locus description, and the nonempty criterion. Evaluation through any residue-field
embedding preserves and reflects zero, so this also computes the geometric-point count.
5. For an étale map, `pqf-lem-locnoeth-lft` gives locally Noetherian source,
`lem-weil-pbc-etale-prime-generates-maximal` transports the maximal-ideal generators,
and `lem-sc-etale-local-dimension` preserves their required number. Residue-field maps
are injective, so precisely the same factors vanish. Thus the pulled functions satisfy
the coordinate hypothesis. Apply steps 1--4 on the source, with the pulled-back product
and ideal, to obtain every assertion there, including comparison with any alternative
coordinate equations defining that pulled-back divisor.
-/
theorem coordinate_maximal_branch_stratum
    {U : Scheme.{u}} [IsLocallyNoetherian U]
    (hregular : ∀ x : U, ∃ V : U.affineOpens, x ∈ V.1 ∧ IsRegularRing Γ(U, V))
    {s : ℕ} (hs : 1 ≤ s) (t : Fin s → Γ(U, ⊤))
    (hcoord : ∀ x : U,
      ∃ (hR : IsNoetherianRing (U.presheaf.stalk x))
        (q l : List (U.presheaf.stalk x)),
        @IsLocalRing.IsRegularSystemOfParameters (U.presheaf.stalk x) _ _ hR q ∧
          l.Sublist q ∧
          (∀ j : Fin s,
            U.presheaf.germ ⊤ x (by trivial) (t j) ∈ IsLocalRing.maximalIdeal _ ↔
              U.presheaf.germ ⊤ x (by trivial) (t j) ∈ l) ∧
          (∀ i j : Fin s,
            U.presheaf.germ ⊤ x (by trivial) (t i) ∈ IsLocalRing.maximalIdeal _ →
            U.presheaf.germ ⊤ x (by trivial) (t j) ∈ IsLocalRing.maximalIdeal _ →
            i ≠ j →
              U.presheaf.germ ⊤ x (by trivial) (t i) ≠
                U.presheaf.germ ⊤ x (by trivial) (t j))) :
    let D : U.IdealSheafData :=
      ofIdealTop (Ideal.span {∏ j : Fin s, t j})
    let C : U.IdealSheafData :=
      ofIdealTop (Ideal.span (Set.range t))
    let b : U → ℕ := fun x ↦
      Nat.card {j : Fin s //
        U.presheaf.germ ⊤ x (by trivial) (t j) ∈ IsLocalRing.maximalIdeal _}
    (∀ (Ω : Type (max u v)) [Field Ω] [IsAlgClosed Ω]
        (x : U) (ι : U.residueField x →+* Ω),
      D.ncBranchCount x = b x ∧
        Nat.card {j : Fin s // ι (U.Γevaluation x (t j)) = 0} = b x) ∧
    (∀ x : U, b x = 0 ↔ x ∉ (D.support : Set U)) ∧
    (∀ x : U, b x ≤ s) ∧
    (∀ (k : ℤ) (x : U),
      (k ≤ (b x : ℤ)) ↔
        k ≤ 0 ∨ ∃ J : Finset (Fin s),
          (k : ℤ) = J.card ∧
          x ∈ ((ofIdealTop (Ideal.span
            (Set.range (fun j : {j // j ∈ J} ↦ t j.1)))).support : Set U)) ∧
    (∀ x : U, b x = s ↔ x ∈ (C.support : Set U)) ∧
    (IsReduced C.subscheme ∧
      ∀ x : C.subscheme,
        ∃ V : C.subscheme.affineOpens, x ∈ V.1 ∧ IsRegularRing Γ(C.subscheme, V)) ∧
    ((∃ x : U, b x = s) ↔ Nonempty C.subscheme) ∧
    (∀ {W : Scheme.{u}} (e : W ⟶ U) [Etale e],
      let tW : Fin s → Γ(W, ⊤) := fun j ↦ e.appTop (t j)
      let bW : W → ℕ := fun w ↦
        Nat.card {j : Fin s //
          W.presheaf.germ ⊤ w (by trivial) (tW j) ∈ IsLocalRing.maximalIdeal _}
      IsLocallyNoetherian W ∧
      (∀ w : W, ∃ V : W.affineOpens, w ∈ V.1 ∧ IsRegularRing Γ(W, V)) ∧
      (∀ x : W,
        ∃ (hR : IsNoetherianRing (W.presheaf.stalk x))
          (q l : List (W.presheaf.stalk x)),
          @IsLocalRing.IsRegularSystemOfParameters (W.presheaf.stalk x) _ _ hR q ∧
            l.Sublist q ∧
            (∀ j : Fin s,
              W.presheaf.germ ⊤ x (by trivial) (tW j) ∈ IsLocalRing.maximalIdeal _ ↔
                W.presheaf.germ ⊤ x (by trivial) (tW j) ∈ l) ∧
            (∀ i j : Fin s,
              W.presheaf.germ ⊤ x (by trivial) (tW i) ∈ IsLocalRing.maximalIdeal _ →
              W.presheaf.germ ⊤ x (by trivial) (tW j) ∈ IsLocalRing.maximalIdeal _ →
              i ≠ j →
                W.presheaf.germ ⊤ x (by trivial) (tW i) ≠
                  W.presheaf.germ ⊤ x (by trivial) (tW j))) ∧
      D.comap e = ofIdealTop (Ideal.span {∏ j : Fin s, tW j}) ∧
      C.comap e = ofIdealTop (Ideal.span (Set.range tW)) ∧
      (∀ w : W, bW w = b (e w)) ∧
      (∀ (Ω : Type (max u v)) [Field Ω] [IsAlgClosed Ω]
          (w : W) (ι : W.residueField w →+* Ω),
        (D.comap e).ncBranchCount w = bW w ∧
          Nat.card {j : Fin s // ι (W.Γevaluation w (tW j)) = 0} = bW w) ∧
      (∀ w : W, bW w = 0 ↔ w ∉ ((D.comap e).support : Set W)) ∧
      (∀ w : W, bW w ≤ s) ∧
      (∀ (k : ℤ) (w : W),
        k ≤ (bW w : ℤ) ↔
          k ≤ 0 ∨ ∃ J : Finset (Fin s), (k : ℤ) = J.card ∧
            w ∈ ((ofIdealTop (Ideal.span
              (Set.range (fun j : {j // j ∈ J} ↦ tW j.1)))).support : Set W)) ∧
      (∀ w : W, bW w = s ↔ w ∈ ((C.comap e).support : Set W)) ∧
      IsReduced (C.comap e).subscheme ∧
      (∀ z : (C.comap e).subscheme,
        ∃ V : (C.comap e).subscheme.affineOpens,
          z ∈ V.1 ∧ IsRegularRing Γ((C.comap e).subscheme, V)) ∧
      ((∃ w : W, bW w = s) ↔ Nonempty (C.comap e).subscheme) ∧
      (∀ {r : ℕ} (hr : 1 ≤ r) (a : Fin r → Γ(W, ⊤)),
        (∀ x : W,
          ∃ (hR : IsNoetherianRing (W.presheaf.stalk x))
            (q l : List (W.presheaf.stalk x)),
            @IsLocalRing.IsRegularSystemOfParameters (W.presheaf.stalk x) _ _ hR q ∧
              l.Sublist q ∧
              (∀ j : Fin r,
                W.presheaf.germ ⊤ x (by trivial) (a j) ∈ IsLocalRing.maximalIdeal _ ↔
                  W.presheaf.germ ⊤ x (by trivial) (a j) ∈ l) ∧
              (∀ i j : Fin r,
                W.presheaf.germ ⊤ x (by trivial) (a i) ∈ IsLocalRing.maximalIdeal _ →
                W.presheaf.germ ⊤ x (by trivial) (a j) ∈ IsLocalRing.maximalIdeal _ →
                i ≠ j →
                  W.presheaf.germ ⊤ x (by trivial) (a i) ≠
                    W.presheaf.germ ⊤ x (by trivial) (a j))) →
        ofIdealTop (Ideal.span {∏ j : Fin r, a j}) = D.comap e →
        ∀ w : W,
          Nat.card {j : Fin r //
            W.presheaf.germ ⊤ w (by trivial) (a j) ∈ IsLocalRing.maximalIdeal _} = bW w)) := by
  sorry

end AlgebraicGeometry.Scheme.IdealSheafData
