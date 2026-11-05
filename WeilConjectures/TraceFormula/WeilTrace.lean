/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Ring.NegOnePow
public import WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology
public import WeilConjectures.TraceFormula.FrobeniusIterate
public import WeilConjectures.TraceFormula.HomologyUnit
public import WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek
public import WeilConjectures.WeilObject.Sheaf.StalkUnit

/-!

# Local and global Frobenius traces of Weil objects

Let `ℓ` be a prime, `k = 𝔽_q` a finite field of characteristic `p ≠ ℓ` with algebraic closure
`k̄`, `σ` the Frobenius of `Spec k̄` over `Spec k` (`geometricFrobeniusField k`) and
`s : Spec k̄ ⟶ Spec k` the geometric point of the base (`specAlgebraicClosure k`). Let `X` be a
separated scheme of finite type over `Spec k` with an automorphism `e : X ≅ X` over `Spec k`, and
let `(K, φ_K)` be a Weil object of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for `e`
(`ProEtale.CondensedRing.WeilBoundedConstructible`). This file defines the two sides of the
Grothendieck–Lefschetz trace formula from the existing Weil functors only: the Weil homology
sheaves (`WeilBoundedConstructible.homologyFunctor`), the Weil stalks
(`WeilSheaf.stalkFunctor`) and the Weil lower shriek (`weilLowerShriek`). No Frobenius
correspondence is introduced.

## Rational points

All Frobenius powers are indexed by `n : ℕ`, with `e⁰ = 𝟙` (`CategoryTheory.Iso.pow`). The points
of degree `n` (`ProEtale.CondensedRing.frobeniusFixedPoints e n`) are the geometric points
`x̄ : Spec k̄ ⟶ X` over `s` with `x̄ ≫ eⁿ = σⁿ ≫ x̄`. For `e = 𝟙` and `n ≠ 0` these are the
`k̄`-points of `X` with coordinates in the fixed field `𝔽_{qⁿ}` of `σⁿ`, that is the
`𝔽_{qⁿ}`-rational points of `X`; for a general `e` they are the fixed points of the Frobenius `σⁿ`
twisted by `eⁿ`. Each rational point is counted once: the geometric point is the rational point
itself, not a chosen geometric lift, so no independence of the lift is needed.

## The traces

All stalks live in the symmetric monoidal category `Mod_{Spec k̄}` of `ℚ̲̄_ℓ`-modules on the
pro-étale site of `Spec k̄` (`ProEtale.CondensedRing.GeometricPointMod`), and traces take values
in the ring `End (𝟙_ Mod_{Spec k̄})`, the categorical traces of
`WeilConjectures.TraceFormula.CategoricalTrace`. Through the equivalence of `Mod_{Spec k̄}` with
condensed `ℚ̲̄_ℓ`-modules (`isEquivalence_upperStarFromPointMod`) this ring is
`End(ℚ̲̄_ℓ) = ℚ̄_ℓ`, and the categorical trace of an endomorphism of a finite-dimensional
`ℚ̄_ℓ`-vector space is its usual trace.

* **Local trace.** For a Weil sheaf `F` and a point `x̄` of degree `n`, the stalk of the Weil
  sheaf `(F, φ_F^{(n)})` for `eⁿ` at `x̄` (`WeilSheaf.frobeniusStalk`) is `F_x̄` with its `n`-th
  Frobenius operator `Fr_{x̄,n}`. For a Weil complex `K`,
  ```
  tₙ(K; x̄) = ∑ⱼ (-1)ʲ Tr(Fr_{x̄,n} | Hʲ(K)_x̄)
  ```
  is `weilStalkTraceAlternatingSum`, the alternating sum of the traces on the stalks of the Weil
  homology sheaves. Since the stalk functor is exact, `Hʲ(K)_x̄ = Hʲ(K_x̄)`.
* **Global trace.** The compactly supported cohomology `RΓ_c(X, K) = Ra_! K` of a Weil object is
  the Weil object `Ra_!^Weil K` on the base `Spec k` (`ProEtale.CondensedRing.point k`) with the
  identity automorphism (`weilCompactSupportCohomology`), for `a : X ⟶ Spec k` the structure
  morphism (`toPoint X`). Its stalk at
  `s`, with the `n`-th Frobenius operator, is `RΓ_c(X_k̄, K)` with `Fr_{c,n}`, and
  ```
  Lₙ(X, K) = ∑ᵢ (-1)ⁱ Tr(Fr_{c,n} | Hⁱ_c(X_k̄, K))
  ```
  is the local trace of `Ra_!^Weil K` at the unique point `s` of the base
  (`weilStalkTraceAlternatingSum` at `specAlgebraicClosure k`), so the absolute trace formula is
  a special case of the relative one.

## Main definitions

- `ProEtale.CondensedRing.frobeniusFixedPoints`: the points of degree `n`.
- `ProEtale.CondensedRing.WeilSheaf.powStalkFunctor`: the stalk at a point of degree `n` with
  its `n`-th Frobenius operator, as a functor.
- `ProEtale.CondensedRing.weilSheafStalkTrace`: the trace of the `n`-th Frobenius on a stalk of
  a Weil sheaf.
- `ProEtale.CondensedRing.weilStalkTraceAlternatingSum`: the local trace `tₙ(K; x̄)`.
- `ProEtale.CondensedRing.weilCompactSupportCohomology`: `RΓ_c(X, K)` as a Weil object.
- `ProEtale.CondensedRing.weilUnit`: the unit `ℚ̲̄_ℓ,X` with its canonical Weil structure, that is
  `ProEtale.CondensedRing.WeilBoundedConstructible.unit` for `e`.

The base `Spec k` is `ProEtale.CondensedRing.point k`, from
`WeilConjectures.TraceFormula.Basic`.

## Main results

- `ProEtale.CondensedRing.weilSheafStalkTrace_congr`,
  `ProEtale.CondensedRing.categoricalTrace_frobeniusStalk_congr`: the local trace only depends on
  the Weil sheaf up to isomorphism.
- `ProEtale.CondensedRing.finite_support_weilSheafStalkTrace_homology`: only finitely many
  homology sheaves of a bounded complex contribute to the local trace.
- `ProEtale.CondensedRing.weilSheafStalkTrace_unit`: the unit Weil sheaf has trace `1` at every
  point of degree `n ≠ 0`.
- `ProEtale.CondensedRing.weilStalkTraceAlternatingSum_weilUnit`: the canonical Weil unit has
  local trace `1` at every point of degree `n ≠ 0`, the normalization test N1.

The points of degree `n ≠ 0` are finite
(`ProEtale.CondensedRing.finite_frobeniusFixedPoints`, in
`WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite`).

## Implementation notes

The `(n + 1)`-st iterated Weil structure of the unit is computed with `Iso.powSuccStr`
(`WeilSheaf.pow_succ`), which does not involve the identity isomorphism `𝟙^* ≅ 𝟭` of the
pullback; the unit results are stated for `n ≠ 0`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The category `Mod_{Spec Ω}` of `ℚ̲̄_ℓ`-modules on the pro-étale site of `Spec Ω`, in which the
stalks of Weil sheaves at geometric points with values in `Ω` live. -/
abbrev GeometricPointMod (Ω : Type u) [Field Ω] : Type _ :=
  CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of Ω)))

variable {k : Type u} [Field k]

/-! ### Rational points -/

section Points

variable [Finite k] {X : Over (Spec (.of k))} (e : X ≅ X) (n : ℕ)

/-- The points of degree `n` of `X` for the Frobenius twisted by `e`: the geometric points
`x̄ : Spec k̄ ⟶ X` over the geometric point `s : Spec k̄ ⟶ Spec k` of the base with
`x̄ ≫ eⁿ = σⁿ ≫ x̄`. For `e = 𝟙` and `n ≠ 0` these are the `𝔽_{qⁿ}`-rational points of `X`. -/
def frobeniusFixedPoints : Type u :=
  {x : Spec (.of (AlgebraicClosure k)) ⟶ X.left //
    x ≫ X.hom = specAlgebraicClosure k ∧
      x ≫ (e.pow n).hom.left = ((geometricFrobeniusField k).pow n).hom ≫ x}

end Points

/-! ### The local trace -/

/-- `traceOrZero` of the structure automorphism of an algebra for the identity functor only depends
on the algebra up to isomorphism. -/
lemma _root_.CategoryTheory.Endofunctor.IsoAlgebra.traceOrZero_str_congr {C : Type*}
    [Category C] [MonoidalCategory C] [BraidedCategory C] [Preadditive C]
    {A B : IsoAlgebra (𝟭 C)} (i : A ≅ B) :
    traceOrZero B.str.hom = traceOrZero A.str.hom := by
  let e : A.carrier ≅ B.carrier := (IsoAlgebra.forget _).mapIso i
  have h : B.str.hom = e.inv ≫ A.str.hom ≫ e.hom := (Iso.eq_inv_comp e).2 i.hom.hom.h
  exact (congrArg traceOrZero h).trans (traceOrZero_conj e _)

section Local

variable [Finite k] {X : Over (Spec (.of k))} {e : X ≅ X} (n : ℕ)
  (x : Spec (.of (AlgebraicClosure k)) ⟶ X.left)
  (hx : x ≫ (e.pow n).hom.left = ((geometricFrobeniusField k).pow n).hom ≫ x)

/-- The stalk at a geometric point `x̄` with `x̄ ≫ eⁿ = σⁿ ≫ x̄` of Weil sheaves for `e`, with the
`n`-th Frobenius operator: the stalk functor for `eⁿ` after `WeilSheaf.powFunctor`. -/
noncomputable def WeilSheaf.powStalkFunctor :
    WeilSheaf ℓ e ⥤ IsoAlgebra (𝟭 (GeometricPointMod ℓ (AlgebraicClosure k))) :=
  WeilSheaf.powFunctor ℓ e n ⋙
    WeilSheaf.stalkFunctor ℓ (e.pow n) ((geometricFrobeniusField k).pow n).hom x hx

/-- The stalk at a geometric point `x̄` with `x̄ ≫ eⁿ = σⁿ ≫ x̄` of a Weil sheaf `F` for `e`, with
its `n`-th Frobenius operator: the stalk of the Weil sheaf `(F, φ_F^{(n)})` for `eⁿ`. -/
noncomputable def WeilSheaf.frobeniusStalk (F : WeilSheaf ℓ e) :
    IsoAlgebra (𝟭 (GeometricPointMod ℓ (AlgebraicClosure k))) :=
  (WeilSheaf.powStalkFunctor ℓ n x hx).obj F

/-- The trace `Tr(Fr_{x̄,n} | F_x̄)` of the `n`-th Frobenius operator on the stalk of a Weil sheaf
at a geometric point `x̄` with `x̄ ≫ eⁿ = σⁿ ≫ x̄`: the categorical trace computed with a right
dual chosen from `Nonempty (HasRightDual F_x̄)` (`traceOrZero`, `weilSheafStalkTrace_eq`),
and `0` when the stalk has no right dual. The stalks of constructible sheaves are
finite-dimensional over `ℚ̄_ℓ`, hence dualizable, so the second case does not occur for the
homology sheaves of the trace formula. -/
noncomputable def weilSheafStalkTrace (F : WeilSheaf ℓ e) :
    End (𝟙_ (GeometricPointMod ℓ (AlgebraicClosure k))) :=
  traceOrZero (WeilSheaf.frobeniusStalk ℓ n x hx F).str.hom

/-- The trace of the Frobenius on the stalk only depends on the Weil sheaf up to isomorphism. -/
lemma weilSheafStalkTrace_congr {F G : WeilSheaf ℓ e} (i : F ≅ G) :
    weilSheafStalkTrace ℓ n x hx F = weilSheafStalkTrace ℓ n x hx G :=
  (IsoAlgebra.traceOrZero_str_congr ((WeilSheaf.powStalkFunctor ℓ n x hx).mapIso i)).symm

variable [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The local trace `tₙ(K; x̄) = ∑ⱼ (-1)ʲ Tr(Fr_{x̄,n} | Hʲ(K)_x̄)` of a Weil object `K` of
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧` at a geometric point `x̄` with `x̄ ≫ eⁿ = σⁿ ≫ x̄`: the alternating sum of the
traces of the `n`-th Frobenius on the stalks of the Weil homology sheaves. -/
noncomputable def weilStalkTraceAlternatingSum (K : WeilBoundedConstructible ℓ e.hom) :
    End (𝟙_ (GeometricPointMod ℓ (AlgebraicClosure k))) :=
  ∑ᶠ j : ℤ, (j.negOnePow : ℤ) •
    weilSheafStalkTrace ℓ n x hx ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj K)

/-- Only finitely many homology sheaves of a bounded complex contribute to the local trace, so
that the `finsum` defining it is a finite sum. -/
theorem finite_support_weilSheafStalkTrace_homology (K : WeilBoundedConstructible ℓ e.hom) :
    (Function.support fun j : ℤ ↦
      weilSheafStalkTrace ℓ n x hx
        ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj K)).Finite := by
  obtain ⟨⟨a, b, h⟩, -⟩ := (mem_boundedConstructible_iff _ _).1 K.carrier.property
  refine (Set.finite_Icc a b).subset fun j hj ↦ ?_
  by_contra hj'
  have hZ : Limits.IsZero (WeilSheaf.frobeniusStalk ℓ n x hx
      ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj K)).carrier := by
    rw [WeilSheaf.frobeniusStalk, WeilSheaf.powStalkFunctor, Functor.comp_obj,
      WeilSheaf.stalkFunctor_obj_carrier, WeilSheaf.powFunctor_obj,
      WeilSheaf.pow_carrier,
      WeilBoundedConstructible.homologyFunctor_obj_carrier]
    refine Functor.map_isZero _ (h j ?_)
    simpa only [Set.mem_Icc, not_and_or, not_le] using hj'
  refine hj ?_
  exact traceOrZero_eq_zero_of_isZero hZ _

end Local

/-! ### The unit Weil sheaf -/

section UnitSheaf

variable {X : Over (Spec (.of k))} (e : X ≅ X)

end UnitSheaf

/-! ### The canonical Weil unit -/

section Unit

variable [Finite k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (e : X ≅ X)

/-- The unit `ℚ̲̄_ℓ,X` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` with its canonical Weil structure
`Le^* ℚ̲̄_ℓ,X ≅ ℚ̲̄_ℓ,X`, the inverse of the unit isomorphism of the monoidal functor `Le^*`: the
constant Weil object `WeilBoundedConstructible.unit` for `e`. -/
noncomputable abbrev weilUnit : WeilBoundedConstructible ℓ e.hom :=
  WeilBoundedConstructible.unit ℓ e.hom

end Unit

/-! ### The global trace -/

section Global

variable [Finite k]

/-- The geometric point `s : Spec k̄ ⟶ Spec k` of the base is fixed by the Frobenius:
`s ≫ 𝟙 = σⁿ ≫ s`. -/
lemma specAlgebraicClosure_comp_pow (n : ℕ) :
    specAlgebraicClosure k ≫ ((Iso.refl (point k)).pow n).hom.left =
      ((geometricFrobeniusField k).pow n).hom ≫ specAlgebraicClosure k := by
  rw [Iso.pow_hom_comp_of_hom_comp _ (geometricFrobeniusField_hom_comp_specAlgebraicClosure k),
    Iso.pow_refl]
  exact Category.comp_id _

/-- The geometric point `s` of the base is its unique point of degree `n`. -/
noncomputable instance (n : ℕ) : Unique (frobeniusFixedPoints (Iso.refl (point k)) n) where
  default := ⟨specAlgebraicClosure k, Category.comp_id _, specAlgebraicClosure_comp_pow n⟩
  uniq x := Subtype.ext ((Category.comp_id _).symm.trans x.2.1)

variable [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (e : X ≅ X)

/-- The compactly supported cohomology `RΓ_c(X, K) = Ra_! K` of a Weil object `K` for `e`, as a
Weil object on the base `Spec k` for the identity: the Weil lower shriek along the structure
morphism `a` (`toPoint X`). -/
noncomputable def weilCompactSupportCohomology :
    WeilBoundedConstructible ℓ e.hom ⥤ WeilBoundedConstructible ℓ (Iso.refl (point k)).hom :=
  weilLowerShriek ℓ e (Iso.refl (point k)) (f := toPoint X) (toPoint_ext _ _)

end Global

end AlgebraicGeometry.ProEtale.CondensedRing
