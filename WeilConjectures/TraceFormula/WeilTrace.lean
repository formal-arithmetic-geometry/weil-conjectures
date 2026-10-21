/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Ring.NegOnePow
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.TraceFormula.CategoricalTrace
public import WeilConjectures.TraceFormula.FrobeniusIterate
public import WeilConjectures.WeilObject.BoundedConstructible.Homology
public import WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek

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
  the Weil object `Ra_!^Weil K` on the base `Spec k`, as the terminal object
  `Over.mk (𝟙 (Spec k))` of `Over (Spec k)`, with the identity automorphism
  (`weilCompactSupportCohomology`), for `a : X ⟶ Spec k` the structure morphism. Its stalk at
  `s`, with the `n`-th Frobenius operator, is `RΓ_c(X_k̄, K)` with `Fr_{c,n}`, and
  ```
  Lₙ(X, K) = ∑ᵢ (-1)ⁱ Tr(Fr_{c,n} | Hⁱ_c(X_k̄, K))
  ```
  is the local trace of `Ra_!^Weil K` at the unique point `s` of the base
  (`weilStalkTraceAlternatingSum` at `specAlgebraicClosure k`), so the absolute trace formula is
  a special case of the relative one.

## Main definitions

- `ProEtale.CondensedRing.frobeniusFixedPoints`: the points of degree `n`.
- `ProEtale.CondensedRing.weilStalkTraceAlternatingSum`: the local trace `tₙ(K; x̄)`.
- `ProEtale.CondensedRing.weilCompactSupportCohomology`: `RΓ_c(X, K)` as a Weil object.
- `ProEtale.CondensedRing.weilUnit`: the unit `ℚ̲̄_ℓ,X` with its canonical Weil structure.

## Sorried input

- `ProEtale.CondensedRing.finite_frobeniusFixedPoints`: there are finitely many points of degree
  `n ≠ 0`: they are the `k`-points of the fixed-point scheme of `σⁿ` twisted by `eⁿ`, which is of
  finite type and unramified over `k`. The resulting `Fintype` structure
  `ProEtale.CondensedRing.fintypeFrobeniusFixedPoints` is a local instance where sums over
  points are taken.
- `ProEtale.CondensedRing.hasRightDual_frobeniusStalk_homology`: the stalks of the homology
  sheaves of a bounded constructible complex are dualizable, that is finite-dimensional over
  `ℚ̄_ℓ`.
- `ProEtale.CondensedRing.finite_support_categoricalTrace_frobeniusStalk_homology`: only finitely
  many homology sheaves of a bounded complex contribute to the local trace.
- `ProEtale.CondensedRing.categoricalTrace_frobeniusStalk_add`: the trace of the Frobenius on the
  stalks is additive in short exact sequences of Weil sheaves.
- `ProEtale.CondensedRing.weilStalkTraceAlternatingSum_weilUnit`: the canonical Weil unit has
  local trace `1` at every point, the normalization test N1.

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

/-- A scheme of finite type over a finite field has finitely many points of degree `n ≠ 0`: they
are the `k`-points of the fixed-point scheme of `σⁿ` twisted by `eⁿ`, which is of finite type and
unramified over `k`, the differential of the Frobenius being zero. -/
theorem finite_frobeniusFixedPoints [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [NeZero n] : Finite (frobeniusFixedPoints e n) :=
  sorry

/-- The points of degree `n ≠ 0` form a finite type, with the `Fintype` structure chosen from
`finite_frobeniusFixedPoints`. It is not a global instance; enable it with
`attribute [local instance] fintypeFrobeniusFixedPoints` where sums over points are taken. -/
@[instance_reducible]
noncomputable def fintypeFrobeniusFixedPoints [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [NeZero n] : Fintype (frobeniusFixedPoints e n) :=
  have := finite_frobeniusFixedPoints e n
  Fintype.ofFinite _

end Points

/-! ### The local trace -/

section Local

variable [Finite k] {X : Over (Spec (.of k))} {e : X ≅ X} (n : ℕ)
  (x : Spec (.of (AlgebraicClosure k)) ⟶ X.left)
  (hx : x ≫ (e.pow n).hom.left = ((geometricFrobeniusField k).pow n).hom ≫ x)

/-- The stalk at a geometric point `x̄` with `x̄ ≫ eⁿ = σⁿ ≫ x̄` of a Weil sheaf `F` for `e`, with
its `n`-th Frobenius operator: the stalk of the Weil sheaf `(F, φ_F^{(n)})` for `eⁿ`. -/
noncomputable def WeilSheaf.frobeniusStalk (F : WeilSheaf ℓ e) :
    IsoAlgebra (𝟭 (GeometricPointMod ℓ (AlgebraicClosure k))) :=
  (WeilSheaf.stalkFunctor ℓ (e.pow n) ((geometricFrobeniusField k).pow n).hom x hx).obj
    (WeilSheaf.pow ℓ F n)

/-- The trace of the Frobenius on the stalk only depends on the Weil sheaf up to isomorphism. -/
lemma categoricalTrace_frobeniusStalk_congr {F G : WeilSheaf ℓ e} (i : F ≅ G)
    [HasRightDual (WeilSheaf.frobeniusStalk ℓ n x hx F).carrier]
    [HasRightDual (WeilSheaf.frobeniusStalk ℓ n x hx G).carrier] :
    categoricalTrace (V := (WeilSheaf.frobeniusStalk ℓ n x hx F).carrier)
        (WeilSheaf.frobeniusStalk ℓ n x hx F).str.hom =
      categoricalTrace (V := (WeilSheaf.frobeniusStalk ℓ n x hx G).carrier)
        (WeilSheaf.frobeniusStalk ℓ n x hx G).str.hom :=
  sorry

/-- The trace of the Frobenius on the stalks is additive in short exact sequences
`0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` of Weil sheaves:
`Tr(Fr_{x̄,n} | F_x̄) = Tr(Fr_{x̄,n} | F'_x̄) + Tr(Fr_{x̄,n} | F''_x̄)`. -/
theorem categoricalTrace_frobeniusStalk_add {F' F F'' : WeilSheaf ℓ e} (i : F' ⟶ F)
    (p : F ⟶ F'') (w : (IsoAlgebra.forget _).map i ≫ (IsoAlgebra.forget _).map p = 0)
    (hS : (ShortComplex.mk _ _ w).ShortExact)
    [HasRightDual (WeilSheaf.frobeniusStalk ℓ n x hx F').carrier]
    [HasRightDual (WeilSheaf.frobeniusStalk ℓ n x hx F).carrier]
    [HasRightDual (WeilSheaf.frobeniusStalk ℓ n x hx F'').carrier] :
    categoricalTrace (V := (WeilSheaf.frobeniusStalk ℓ n x hx F).carrier)
        (WeilSheaf.frobeniusStalk ℓ n x hx F).str.hom =
      categoricalTrace (V := (WeilSheaf.frobeniusStalk ℓ n x hx F').carrier)
          (WeilSheaf.frobeniusStalk ℓ n x hx F').str.hom +
        categoricalTrace (V := (WeilSheaf.frobeniusStalk ℓ n x hx F'').carrier)
          (WeilSheaf.frobeniusStalk ℓ n x hx F'').str.hom :=
  sorry

variable [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The stalks of the homology sheaves of a bounded constructible complex at a geometric point
are dualizable, that is finite-dimensional over `ℚ̄_ℓ`. -/
noncomputable instance hasRightDual_frobeniusStalk_homology (K : WeilBoundedConstructible ℓ e.hom)
    (j : ℤ) : HasRightDual (WeilSheaf.frobeniusStalk ℓ n x hx
      ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj K)).carrier :=
  sorry

/-- The local trace `tₙ(K; x̄) = ∑ⱼ (-1)ʲ Tr(Fr_{x̄,n} | Hʲ(K)_x̄)` of a Weil object `K` of
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧` at a geometric point `x̄` with `x̄ ≫ eⁿ = σⁿ ≫ x̄`: the alternating sum of the
traces of the `n`-th Frobenius on the stalks of the Weil homology sheaves. -/
noncomputable def weilStalkTraceAlternatingSum (K : WeilBoundedConstructible ℓ e.hom) :
    End (𝟙_ (GeometricPointMod ℓ (AlgebraicClosure k))) :=
  ∑ᶠ j : ℤ, (j.negOnePow : ℤ) •
    categoricalTrace (V := (WeilSheaf.frobeniusStalk ℓ n x hx
        ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj K)).carrier)
      (WeilSheaf.frobeniusStalk ℓ n x hx
        ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj K)).str.hom

/-- Only finitely many homology sheaves of a bounded complex contribute to the local trace, so
that the `finsum` defining it is a finite sum. -/
theorem finite_support_categoricalTrace_frobeniusStalk_homology
    (K : WeilBoundedConstructible ℓ e.hom) :
    (Function.support fun j : ℤ ↦
      categoricalTrace (V := (WeilSheaf.frobeniusStalk ℓ n x hx
          ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj K)).carrier)
        (WeilSheaf.frobeniusStalk ℓ n x hx
          ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj K)).str.hom).Finite :=
  sorry

end Local

/-! ### The canonical Weil unit -/

section Unit

variable [Finite k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (e : X ≅ X)

/-- The unit `ℚ̲̄_ℓ,X` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` with its canonical Weil structure
`Le^* ℚ̲̄_ℓ,X ≅ ℚ̲̄_ℓ,X`, the inverse of the unit isomorphism of the monoidal functor `Le^*`. -/
noncomputable def weilUnit : WeilBoundedConstructible ℓ e.hom :=
  IsoAlgebra.mk (𝟙_ _)
    (Functor.Monoidal.εIso
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ e.hom)).symm

/-- The canonical Weil unit has local trace `1` at every point: its stalk is `ℚ̄_ℓ` in degree `0`,
on which the Frobenius acts trivially (normalization test N1). -/
theorem weilStalkTraceAlternatingSum_weilUnit (n : ℕ) (x : Spec (.of (AlgebraicClosure k)) ⟶ X.left)
    (hx : x ≫ (e.pow n).hom.left = ((geometricFrobeniusField k).pow n).hom ≫ x) :
    weilStalkTraceAlternatingSum ℓ n x hx (weilUnit ℓ e) = 1 :=
  sorry

end Unit

/-! ### The global trace -/

section Global

instance (k : Type u) [Field k] : LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 _))

instance (k : Type u) [Field k] : QuasiCompact (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (QuasiCompact (𝟙 _))

instance (k : Type u) [Field k] : IsSeparated (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (IsSeparated (𝟙 _))

/-- The structure morphism `a : X ⟶ Spec k` is compatible with every automorphism `e` of `X` over
`Spec k` and the identity of the base. -/
lemma hom_comp_homMk_hom {X : Over (Spec (.of k))} (e : X ≅ X) :
    e.hom ≫ Over.homMk (V := Over.mk (𝟙 _)) X.hom (Category.comp_id _) =
      Over.homMk X.hom (Category.comp_id _) ≫ (Iso.refl (Over.mk (𝟙 _))).hom := by
  ext
  simp

variable [Finite k]

/-- The geometric point `s : Spec k̄ ⟶ Spec k` of the base is fixed by the Frobenius:
`s ≫ 𝟙 = σⁿ ≫ s`. -/
lemma specAlgebraicClosure_comp_pow (n : ℕ) :
    specAlgebraicClosure k ≫ ((Iso.refl (Over.mk (𝟙 (Spec (.of k))))).pow n).hom.left =
      ((geometricFrobeniusField k).pow n).hom ≫ specAlgebraicClosure k := by
  rw [Iso.pow_hom_comp_of_hom_comp _ (geometricFrobeniusField_hom_comp_specAlgebraicClosure k),
    Iso.pow_refl]
  exact Category.comp_id _

/-- The geometric point `s` of the base is its unique point of degree `n`. -/
noncomputable instance (n : ℕ) :
    Unique (frobeniusFixedPoints (Iso.refl (Over.mk (𝟙 (Spec (.of k))))) n) where
  default := ⟨specAlgebraicClosure k, Category.comp_id _, specAlgebraicClosure_comp_pow n⟩
  uniq x := Subtype.ext ((Category.comp_id _).symm.trans x.2.1)

variable [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (e : X ≅ X)

/-- The compactly supported cohomology `RΓ_c(X, K) = Ra_! K` of a Weil object `K` for `e`, as a
Weil object on the base `Spec k` for the identity: the Weil lower shriek along the structure
morphism `a`. -/
noncomputable def weilCompactSupportCohomology :
    WeilBoundedConstructible ℓ e.hom ⥤
      WeilBoundedConstructible ℓ (Iso.refl (Over.mk (𝟙 (Spec (.of k))))).hom :=
  weilLowerShriek ℓ e (Iso.refl (Over.mk (𝟙 _))) (hom_comp_homMk_hom e)

end Global

end AlgebraicGeometry.ProEtale.CondensedRing
