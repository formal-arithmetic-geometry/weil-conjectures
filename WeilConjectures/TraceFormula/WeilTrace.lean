/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.TraceFormula.CategoricalTrace
public import WeilConjectures.TraceFormula.FrobeniusIterate
public import WeilConjectures.TraceFormula.Main
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

All Frobenius powers are indexed by `n : ℕ`, the index `n` standing for the power `n + 1`. The
points of degree `n + 1` (`ProEtale.CondensedRing.frobeniusFixedPoints e n`) are the geometric
points `x̄ : Spec k̄ ⟶ X` over `s` with `x̄ ≫ e^{n+1} = σ^{n+1} ≫ x̄`. For `e = 𝟙` these are the
`k̄`-points of `X` with coordinates in the fixed field `𝔽_{q^{n+1}}` of `σ^{n+1}`, that is the
`𝔽_{q^{n+1}}`-rational points of `X`; for a general `e` they are the fixed points of the
Frobenius `σ^{n+1}` twisted by `e^{n+1}`. Each rational point is counted once: the geometric point
is the rational point itself, not a chosen geometric lift, so no independence of the lift is
needed.

## The traces

All stalks live in the symmetric monoidal category `Mod_{Spec k̄}` of `ℚ̲̄_ℓ`-modules on the
pro-étale site of `Spec k̄` (`ProEtale.CondensedRing.GeometricPointMod`), and traces take values
in the ring `End (𝟙_ Mod_{Spec k̄})`, the categorical traces of
`WeilConjectures.TraceFormula.CategoricalTrace`. Through the equivalence of `Mod_{Spec k̄}` with
condensed `ℚ̲̄_ℓ`-modules (`isEquivalence_upperStarFromPointMod`) this ring is
`End(ℚ̲̄_ℓ) = ℚ̄_ℓ`, and the categorical trace of an endomorphism of a finite-dimensional
`ℚ̄_ℓ`-vector space is its usual trace.

* **Local trace.** For a Weil sheaf `F` and a point `x̄` of degree `n + 1`, the stalk of the Weil
  sheaf `(F, φ_F^{(n+1)})` for `e^{n+1}` at `x̄` (`WeilSheaf.frobeniusStalk`) is `F_x̄` with its
  `(n + 1)`-st Frobenius operator `Fr_{x̄,n+1}`, and `weilSheafStalkTrace` is its trace. For a
  Weil complex `K`,
  ```
  t_{n+1}(K; x̄) = ∑ⱼ (-1)ʲ Tr(Fr_{x̄,n+1} | Hʲ(K)_x̄)
  ```
  is `weilStalkSupertrace`, the supertrace on the stalks of the Weil homology sheaves. Since the
  stalk functor is exact, `Hʲ(K)_x̄ = Hʲ(K_x̄)`.
* **Global trace.** The compactly supported cohomology `RΓ_c(X, K) = Ra_! K` of a Weil object is
  the Weil object `Ra_!^Weil K` on the base `Spec k` with the identity automorphism
  (`weilCompactSupportCohomology`), for `a : X ⟶ Spec k` the structure morphism
  (`toPoint X`). Its stalk at `s`, with the `(n + 1)`-st Frobenius operator, is
  `RΓ_c(X_k̄, K)` with `Fr_{c,n+1}`, and
  ```
  L_{n+1}(X, K) = ∑ᵢ (-1)ⁱ Tr(Fr_{c,n+1} | Hⁱ_c(X_k̄, K))
  ```
  is `weilGlobalSupertrace`. The global trace is the local trace of `Ra_!^Weil K` at the unique
  point `s` of the base, so the absolute trace formula is a special case of the relative one.

## Main definitions

- `ProEtale.CondensedRing.frobeniusFixedPoints`: the points of degree `n + 1`.
- `ProEtale.CondensedRing.WeilSheaf.powSuccStalkFunctor`: the stalk at a point of degree `n + 1`
  with its `(n + 1)`-st Frobenius operator, as a functor.
- `ProEtale.CondensedRing.weilSheafStalkTrace`: the trace of the `(n + 1)`-st Frobenius on a
  stalk of a Weil sheaf.
- `ProEtale.CondensedRing.weilStalkSupertrace`: the local trace `t_{n+1}(K; x̄)`.
- `ProEtale.CondensedRing.weilCompactSupportCohomology`: `RΓ_c(X, K)` as a Weil object.
- `ProEtale.CondensedRing.weilGlobalSupertrace`: the global trace `L_{n+1}(X, K)`.

The unit `ℚ̲̄_ℓ,X` with its canonical Weil structure is
`ProEtale.CondensedRing.WeilBoundedConstructible.unit`, and the base `Spec k` is
`ProEtale.CondensedRing.point k`, both from the model-Frobenius setting of
`WeilConjectures.TraceFormula.Main`.

## Main results

- `ProEtale.CondensedRing.weilSheafStalkTrace_congr`: the local trace only depends on the Weil
  sheaf up to isomorphism.
- `ProEtale.CondensedRing.finite_support_weilSheafStalkTrace_homology`: only finitely many
  homology sheaves of a bounded complex contribute to the local trace.

## Sorried input

- `ProEtale.CondensedRing.finite_frobeniusFixedPoints`: there are finitely many points of degree
  `n + 1`: they are the `k`-points of the fixed-point scheme of `σ^{n+1}` twisted by `e^{n+1}`,
  which is of finite type and unramified over `k`.
- `ProEtale.CondensedRing.weilStalkSupertrace_unit`: the canonical Weil unit has local trace
  `1` at every point, the normalization test N1.

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

/-- The points of degree `n + 1` of `X` for the Frobenius twisted by `e`: the geometric points
`x̄ : Spec k̄ ⟶ X` over the geometric point `s : Spec k̄ ⟶ Spec k` of the base with
`x̄ ≫ e^{n+1} = σ^{n+1} ≫ x̄`. For `e = 𝟙` these are the `𝔽_{q^{n+1}}`-rational points of `X`. -/
def frobeniusFixedPoints : Type u :=
  {x : Spec (.of (AlgebraicClosure k)) ⟶ X.left //
    x ≫ X.hom = specAlgebraicClosure k ∧
      x ≫ (e.powSucc n).hom.left = ((geometricFrobeniusField k).powSucc n).hom ≫ x}

/-- A scheme of finite type over a finite field has finitely many points of degree `n + 1`: they
are the `k`-points of the fixed-point scheme of `σ^{n+1}` twisted by `e^{n+1}`, which is of finite
type and unramified over `k`, the differential of the Frobenius being zero.

This is the twisted analogue of the finiteness part of blueprint `thm-trf-frobenius-fixed-points`,
which is stated for the model Frobenius
(`ProEtale.CondensedRing.IsModelFrobenius.finite_fixedPoint`). -/
theorem finite_frobeniusFixedPoints [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] : Finite (frobeniusFixedPoints e n) :=
  sorry

end Points

/-! ### The local trace -/

/-- The trace of the structure automorphism of an algebra for the identity functor only depends
on the algebra up to isomorphism. -/
lemma _root_.CategoryTheory.Endofunctor.IsoAlgebra.categoricalTrace_str_congr {C : Type*}
    [Category C] [MonoidalCategory C] [BraidedCategory C] [Preadditive C]
    {A B : IsoAlgebra (𝟭 C)} (i : A ≅ B) :
    categoricalTrace B.str.hom = categoricalTrace A.str.hom := by
  let e : A.carrier ≅ B.carrier := (IsoAlgebra.forget _).mapIso i
  have h : B.str.hom = e.inv ≫ A.str.hom ≫ e.hom := (Iso.eq_inv_comp e).2 i.hom.hom.h
  exact (congrArg categoricalTrace h).trans (categoricalTrace_conj e _)

section Local

variable [Finite k] {X : Over (Spec (.of k))} {e : X ≅ X} (n : ℕ)
  (x : Spec (.of (AlgebraicClosure k)) ⟶ X.left)
  (hx : x ≫ (e.powSucc n).hom.left = ((geometricFrobeniusField k).powSucc n).hom ≫ x)

/-- The stalk at a geometric point `x̄` with `x̄ ≫ e^{n+1} = σ^{n+1} ≫ x̄` of Weil sheaves for `e`,
with the `(n + 1)`-st Frobenius operator: the stalk functor for `e^{n+1}` after
`WeilSheaf.powSuccFunctor`. -/
noncomputable def WeilSheaf.powSuccStalkFunctor :
    WeilSheaf ℓ e ⥤ IsoAlgebra (𝟭 (GeometricPointMod ℓ (AlgebraicClosure k))) :=
  WeilSheaf.powSuccFunctor ℓ e n ⋙
    WeilSheaf.stalkFunctor ℓ (e.powSucc n) ((geometricFrobeniusField k).powSucc n).hom x hx

/-- The stalk at a geometric point `x̄` with `x̄ ≫ e^{n+1} = σ^{n+1} ≫ x̄` of a Weil sheaf `F` for
`e`, with its `(n + 1)`-st Frobenius operator: the stalk of the Weil sheaf `(F, φ_F^{(n+1)})` for
`e^{n+1}`. -/
noncomputable def WeilSheaf.frobeniusStalk (F : WeilSheaf ℓ e) :
    IsoAlgebra (𝟭 (GeometricPointMod ℓ (AlgebraicClosure k))) :=
  (WeilSheaf.powSuccStalkFunctor ℓ n x hx).obj F

/-- The trace `Tr(Fr_{x̄,n+1} | F_x̄)` of the `(n + 1)`-st Frobenius operator on the stalk of a
Weil sheaf at a geometric point `x̄` with `x̄ ≫ e^{n+1} = σ^{n+1} ≫ x̄`. -/
noncomputable def weilSheafStalkTrace (F : WeilSheaf ℓ e) :
    End (𝟙_ (GeometricPointMod ℓ (AlgebraicClosure k))) :=
  categoricalTrace (WeilSheaf.frobeniusStalk ℓ n x hx F).str.hom

/-- The trace of the Frobenius on the stalk only depends on the Weil sheaf up to isomorphism. -/
lemma weilSheafStalkTrace_congr {F G : WeilSheaf ℓ e} (i : F ≅ G) :
    weilSheafStalkTrace ℓ n x hx F = weilSheafStalkTrace ℓ n x hx G :=
  (IsoAlgebra.categoricalTrace_str_congr ((WeilSheaf.powSuccStalkFunctor ℓ n x hx).mapIso i)).symm

variable [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The local trace `t_{n+1}(K; x̄) = ∑ⱼ (-1)ʲ Tr(Fr_{x̄,n+1} | Hʲ(K)_x̄)` of a Weil object `K`
of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` at a geometric point `x̄` with `x̄ ≫ e^{n+1} = σ^{n+1} ≫ x̄`: the supertrace of
the `(n + 1)`-st Frobenius on the stalks of the Weil homology sheaves. -/
noncomputable def weilStalkSupertrace (K : WeilBoundedConstructible ℓ e.hom) :
    End (𝟙_ (GeometricPointMod ℓ (AlgebraicClosure k))) :=
  superTrace
    (fun j ↦ (WeilSheaf.frobeniusStalk ℓ n x hx
      ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj K)).carrier)
    (fun j ↦ (WeilSheaf.frobeniusStalk ℓ n x hx
      ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj K)).str.hom)

lemma weilStalkSupertrace_eq (K : WeilBoundedConstructible ℓ e.hom) :
    weilStalkSupertrace ℓ n x hx K =
      ∑ᶠ j : ℤ, (j.negOnePow : ℤ) •
        weilSheafStalkTrace ℓ n x hx ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj K) :=
  rfl

/-- Only finitely many homology sheaves of a bounded complex contribute to the local trace, so
that the `finsum` defining it is a finite sum. -/
theorem finite_support_weilSheafStalkTrace_homology (K : WeilBoundedConstructible ℓ e.hom) :
    (Function.support fun j : ℤ ↦
      weilSheafStalkTrace ℓ n x hx
        ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj K)).Finite := by
  obtain ⟨⟨a, b, h⟩, -⟩ := (mem_boundedConstructible_iff _ _).1 K.carrier.property
  refine (Set.finite_Icc a b).subset fun j hj ↦ ?_
  by_contra hj'
  refine hj (categoricalTrace_eq_zero_of_isZero ?_ _)
  rw [Functor.id_obj, WeilSheaf.frobeniusStalk, WeilSheaf.powSuccStalkFunctor, Functor.comp_obj,
    WeilSheaf.stalkFunctor_obj_carrier, WeilSheaf.powSuccFunctor_obj_carrier,
    WeilBoundedConstructible.homologyFunctor_obj_carrier]
  refine Functor.map_isZero _ (h j ?_)
  simpa only [Set.mem_Icc, not_and_or, not_le] using hj'

end Local

/-! ### The canonical Weil unit -/

section Unit

variable [Finite k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (e : X ≅ X)

/-- The canonical Weil unit `ℚ̲̄_ℓ,X` (`WeilBoundedConstructible.unit`) has local trace `1` at every
point: its stalk is `ℚ̄_ℓ` in degree `0`, on which the Frobenius acts trivially (normalization
test N1). This is the unit stalk trace used in the proof of blueprint `cor-trf-point-counting`. -/
theorem weilStalkSupertrace_unit (n : ℕ) (x : Spec (.of (AlgebraicClosure k)) ⟶ X.left)
    (hx : x ≫ (e.powSucc n).hom.left = ((geometricFrobeniusField k).powSucc n).hom ≫ x) :
    weilStalkSupertrace ℓ n x hx (WeilBoundedConstructible.unit ℓ e.hom) = 1 :=
  sorry

end Unit

/-! ### The global trace -/

section Global

variable [Finite k]

/-- The geometric point `s : Spec k̄ ⟶ Spec k` of the base is fixed by the Frobenius:
`s ≫ 𝟙 = σ^{n+1} ≫ s`. -/
lemma specAlgebraicClosure_comp_powSucc (n : ℕ) :
    specAlgebraicClosure k ≫ ((Iso.refl (point k)).powSucc n).hom.left =
      ((geometricFrobeniusField k).powSucc n).hom ≫ specAlgebraicClosure k := by
  rw [Iso.powSucc_hom_comp_of_hom_comp _ (geometricFrobeniusField_hom_comp_specAlgebraicClosure k),
    Iso.powSucc_refl]
  exact Category.comp_id _

/-- The geometric point `s` of the base, as the unique point of degree `n + 1` of the base. -/
noncomputable def pointFixedPoint (n : ℕ) :
    frobeniusFixedPoints (Iso.refl (point k)) n :=
  ⟨specAlgebraicClosure k, Category.comp_id _, specAlgebraicClosure_comp_powSucc n⟩

noncomputable instance (n : ℕ) : Unique (frobeniusFixedPoints (Iso.refl (point k)) n) where
  default := pointFixedPoint n
  uniq x := Subtype.ext ((Category.comp_id _).symm.trans x.2.1)

variable [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (e : X ≅ X)

/-- The compactly supported cohomology `RΓ_c(X, K) = Ra_! K` of a Weil object `K` for `e`, as a
Weil object on the base `Spec k` for the identity: the Weil lower shriek along the structure
morphism `a`. -/
noncomputable def weilCompactSupportCohomology :
    WeilBoundedConstructible ℓ e.hom ⥤ WeilBoundedConstructible ℓ (Iso.refl (point k)).hom :=
  weilLowerShriek ℓ e (Iso.refl (point k)) (f := toPoint X) (toPoint_ext _ _)

/-- The global trace `L_{n+1}(X, K) = ∑ᵢ (-1)ⁱ Tr(Fr_{c,n+1} | Hⁱ_c(X_k̄, K))` of a Weil object
`K` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`: the local trace of `RΓ_c(X, K)` at the geometric point `s` of the base. -/
noncomputable def weilGlobalSupertrace (K : WeilBoundedConstructible ℓ e.hom) (n : ℕ) :
    End (𝟙_ (GeometricPointMod ℓ (AlgebraicClosure k))) :=
  weilStalkSupertrace ℓ n (specAlgebraicClosure k) (specAlgebraicClosure_comp_powSucc n)
    ((weilCompactSupportCohomology ℓ e).obj K)

end Global

end AlgebraicGeometry.ProEtale.CondensedRing
