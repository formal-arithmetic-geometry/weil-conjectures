/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.Frobenius
public import WeilConjectures.AlgebraicGeometry.Morphisms.Frobenius
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperStarCompCoherence
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Correspondence
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.TopologicalInvariance

/-!
# Weil complexes, relative Frobenius and topological invariance

A *Weil datum* on the geometric base change `X` of a separated finite type
`𝐅_q`-scheme `X₀` is a complex `K ∈ Dᵇctf(X, A)` together with an isomorphism
`φ : Φ₁^* K ≃ K`, where `Φ₁` is the geometric `q`-power Frobenius. Its iterates give the
graph correspondences `c_m = (id, Φ_m)` and the global Frobenius operators.

## Main definitions

- `AlgebraicGeometry.ProEtale.WeilComplex`: a complex with a Frobenius coefficient
  morphism, together with its iterates `frobeniusIterate`, `coeffIterate` and its graph
  correspondences `WeilComplex.graph`.
- `AlgebraicGeometry.ProEtale.WeilComplex.IsModelFrobenius`: the Frobenius `Φ₁` is the base
  change of the `q`-power Frobenius of a model `X₀` over `𝐅_q`.
- `AlgebraicGeometry.ProEtale.WeilComplex.upperStarPullCoeff`: the Frobenius coefficient
  morphism `Lg^* Lf^* K ⟶ Lf^* K` of the pullback along a morphism `f` intertwining `g` and
  `Φ_m`.
- `AlgebraicGeometry.ProEtale.WeilComplex.upperStarPull`: the pullback `Lf^* K` of a Weil
  complex along a morphism `f` intertwining `g` and `Φ₁`.
- `AlgebraicGeometry.ProEtale.WeilComplex.stalkFrobenius`: the geometric-stalk Frobenius
  `F_{x,m} = (φ_m)_x̄` at a point fixed by `Φ_m`.
- `AlgebraicGeometry.ProEtale.relativeFrobenius`: the relative Frobenius `r_m` of a
  morphism compatible with the Frobenius morphisms of its source and target.
- `AlgebraicGeometry.ProEtale.GeometricOperations.lowerShriekExchange`: the compact-support
  exchange `Lg_Y^* Rf_! ⟶ Rf_! Lg_X^*` on `Dᵇctf` of a commutative square of geometric
  schemes with proper gap map.
- `AlgebraicGeometry.ProEtale.WeilComplex.lowerShriekPush`: the `!`-pushforward of a Weil
  complex.

## Main results

- `AlgebraicGeometry.ProEtale.comp_frobenius_pow_eq_of_isFrobenius`,
  `AlgebraicGeometry.ProEtale.isPullback_relativeFrobenius_of_isFrobenius`: for the base change
  `f` of a morphism `f₀` of schemes over a finite field, `Φ_Y ^ m ∘ f = f ∘ Φ_X ^ m`, and the
  relative Frobenius `r_m` is the base change of the relative `q ^ m`-power Frobenius of `f₀`.
- `AlgebraicGeometry.ProEtale.relativeFrobenius_specMap`: the relative Frobenius of an affine
  morphism `Spec S ⟶ Spec R` is `Spec` of `R ⊗_{φ, R} S ⟶ S`, `r ⊗ s ↦ r * φ s`.
- `AlgebraicGeometry.ProEtale.isFinite_relativeFrobenius`,
  `AlgebraicGeometry.ProEtale.isUniversalHomeomorphism_relativeFrobenius`: the relative
  Frobenius is a finite universal homeomorphism.
- `AlgebraicGeometry.ProEtale.isFinite_and_isUniversalHomeomorphism_relativeFrobenius`: the
  relative Frobenius for the base changes of the `#k`-power Frobenius of models locally of
  finite type over a finite field `k` is a finite universal homeomorphism.
- `AlgebraicGeometry.ProEtale.isEquivalence_leftDerivedUpperStar`,
  `AlgebraicGeometry.ProEtale.ctf_leftDerivedUpperStar_obj_iff`: topological invariance of
  the derived pro-étale category along a finite universal homeomorphism.

## Implementation notes

The `q^m`-power Frobenius of a scheme is not constructed anywhere in Mathlib or in this
project, so `AlgebraicGeometry.ProEtale.WeilComplex` carries it as data: an `s`-morphism
`Φ₁ : X ⟶ X`. Statements that are only true for the Frobenius, such as the trace formula,
add the hypothesis `WeilComplex.IsModelFrobenius`: `X = X₀ ×_{𝐅_q} s` for a model `X₀` and
`Φ₁` is the base change of the `q`-power Frobenius of `X₀`
(`AlgebraicGeometry.Scheme.Hom.IsFrobenius`). The properties of `Φ₁` that the formal parts of
the argument use — being finite and a universal homeomorphism — appear as hypotheses where
they are needed. The `coeff` field is a plain morphism rather than an isomorphism, so that a
`WeilComplex` covers both a Weil datum (add `IsIso W.coeff`) and the arbitrary *Frobenius
coefficient morphism* that the coefficient continuation of the argument needs.

`isFinite_relativeFrobenius` and `isUniversalHomeomorphism_relativeFrobenius` follow from
`r_m ≫ p_m = Φ_X` by the cancellation lemmas `AlgebraicGeometry.IsFinite.of_comp` and
`AlgebraicGeometry.IsUniversalHomeomorphism.of_comp`, since `p_m` is a base change of `Φ_Y`.
These two theorems assume that `Φ_X` and `Φ_Y` are finite universal homeomorphisms. For the
base changes of the `#k`-power Frobenius of models locally of finite type over `k`, these
hypotheses hold by `AlgebraicGeometry.Scheme.Hom.IsFrobenius.isFinite_of_isPullback` and
`AlgebraicGeometry.Scheme.Hom.IsFrobenius.isUniversalHomeomorphism_of_isPullback` (the absolute
Frobenius step of the blueprint proof), which gives
`isFinite_and_isUniversalHomeomorphism_relativeFrobenius`.

`isEquivalence_leftDerivedUpperStar` is stated on the whole unbounded `D(Y, A) ⥤ D(X, A)`,
whereas the blueprint states topological invariance on `Dᵇctf`; the generalisation is the
expected one on the pro-étale site, and `ctf_leftDerivedUpperStar_obj_iff` restricts it
back to the coefficient stage.

`WeilComplex.graph` takes the package `G` and the hypothesis `K ∈ Dᵇctf(X)` only for the
identification `GeometricOperations.upperShriekIdIso : K ≅ (𝟙 X)^! K` on `Dᵇctf`, which comes
from the field `lowerShriekId : R(𝟙 X)_! ≅ 𝟭` through the exceptional adjunction on `Dᵇctf`.
Constructing `R(𝟙 X)_! ≅ 𝟭` from the trivial compactification and the lower-star API would
remove that field, and `graph` would no longer depend on `G`.

`GeometricOperations.lowerShriekExchange`, and hence the coefficient map of
`WeilComplex.lowerShriekPush`, uses the fields `baseChange`, `properComparison` and
`lowerShriekComp` at non-identity morphisms. These are tied to each other by the coherence
axioms of the package, but `properComparison` is not pinned to the canonical map
`Rf_! ⟶ Rf_*` (see `WeilConjectures.SixFunctors.ProEtale.TraceFormula.Defs`).
-/

@[expose] public section

universe u' u

set_option linter.unusedVariables false

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {s X Y : Scheme.{u}}

/-- A *Weil complex* on a geometric scheme `a_X : X ⟶ s`: a geometric `q`-power Frobenius
`Φ₁ : X ⟶ X` over `s`, a complex `K` and a *Frobenius coefficient morphism*
`φ : Φ₁^* K ⟶ K`. A *Weil datum* in the strict sense of the blueprint is a `WeilComplex`
with `IsIso W.coeff` (blueprint: `sk-d-weil`). -/
structure WeilComplex (aX : X ⟶ s) where
  /-- the geometric `q`-power Frobenius `Φ₁ : X ⟶ X`. -/
  frobenius : X ⟶ X
  /-- `Φ₁` is a morphism over the base: it fixes the scalar field `k`. -/
  frobenius_comp : frobenius ≫ aX = aX
  /-- the coefficient complex `K`. -/
  obj : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)
  /-- the Frobenius coefficient morphism `φ : Φ₁^* K ⟶ K`. -/
  coeff : ((upperStar A frobenius).leftDerivedFunctor).obj obj ⟶ obj

namespace WeilComplex

variable {aX : X ⟶ s} (W : WeilComplex (A := A) aX)

/-- The `m`-th iterate `Φ_m = Φ₁^m : X ⟶ X` of the geometric Frobenius
(part of blueprint `sk-d-weil`). -/
noncomputable def frobeniusIterate (m : ℕ) : X ⟶ X :=
  let Φ : End X := W.frobenius
  Φ ^ m

@[simp]
lemma frobeniusIterate_zero : W.frobeniusIterate 0 = 𝟙 X := rfl

@[simp]
lemma frobeniusIterate_succ (m : ℕ) :
    W.frobeniusIterate (m + 1) = W.frobenius ≫ W.frobeniusIterate m :=
  (pow_succ (M := End X) W.frobenius m).trans (End.mul_def _ _)

/-- Every iterate of the Frobenius is a morphism over the base. -/
@[simp]
lemma frobeniusIterate_comp (m : ℕ) : W.frobeniusIterate m ≫ aX = aX := by
  induction m with
  | zero => simp
  | succ n ih => rw [frobeniusIterate_succ, Category.assoc, ih, W.frobenius_comp]

@[simp]
lemma frobeniusIterate_one : W.frobeniusIterate 1 = W.frobenius :=
  pow_one (M := End X) W.frobenius

/-- A point fixed by `Φ₁` is fixed by every iterate `Φ_m`. -/
lemma comp_frobeniusIterate_of_comp_frobenius {x : s ⟶ X} (hx : x ≫ W.frobenius = x)
    (m : ℕ) : x ≫ W.frobeniusIterate m = x := by
  induction m with
  | zero => simp
  | succ n ih => rw [frobeniusIterate_succ, ← Category.assoc, hx, ih]

/-- The Frobenius `Φ₁` of a Weil complex on `a_X : X ⟶ s` is the geometric `q`-power Frobenius
of a model `X₀` over the finite field `k` with `q = #k`: the square

```
     X ───p───▶ X₀
     │          │
  a_X│          │f₀
     ▼          ▼
     s ───σ───▶ Spec k
```

is Cartesian, and `Φ₁ = F₀ × 𝟙_s` for the `q`-power Frobenius `F₀` of `X₀`, that is,
`Φ₁ ≫ p = p ≫ F₀` (`Φ₁ ≫ a_X = a_X` is `WeilComplex.frobenius_comp`). Since the square is
Cartesian, these two equations determine `Φ₁` (blueprint: `sk-d-weil`). -/
structure IsModelFrobenius {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Spec (.of k)) (σ : s ⟶ Spec (.of k)) (p : X ⟶ X₀) : Prop where
  /-- `X` is the base change `X₀ ×_{Spec k} s`. -/
  isPullback : IsPullback p aX f₀ σ
  /-- `Φ₁` is the base change of the `q`-power Frobenius of `X₀`. -/
  exists_isFrobenius : ∃ F₀ : X₀ ⟶ X₀, F₀.IsFrobenius (Nat.card k) ∧ W.frobenius ≫ p = p ≫ F₀

/-- The geometric base change `X = X₀ ×_{Spec k} s` of a separated scheme of finite type `X₀`
over `k` is geometric over `s`. -/
lemma IsModelFrobenius.isGeometric {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}}
    {f₀ : X₀ ⟶ Spec (.of k)} {σ : s ⟶ Spec (.of k)} {p : X ⟶ X₀}
    (hΦ : W.IsModelFrobenius f₀ σ p) [IsSeparated f₀] [LocallyOfFiniteType f₀]
    [QuasiCompact f₀] : IsGeometric aX where
  isSeparated := MorphismProperty.of_isPullback hΦ.isPullback ‹_›
  locallyOfFiniteType := MorphismProperty.of_isPullback hΦ.isPullback ‹_›
  quasiCompact := MorphismProperty.of_isPullback hΦ.isPullback ‹_›

/-- The model Frobenius `Φ₁ = F₀ ×_{Spec k} 𝟙_s` and all its iterates `Φ_m` are universal
homeomorphisms (blueprint `i-relative-frob`, Step 2). -/
lemma IsModelFrobenius.isUniversalHomeomorphism_frobeniusIterate {k : Type u} [Field k]
    [Finite k] {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k)} {σ : s ⟶ Spec (.of k)}
    {p : X ⟶ X₀} (hΦ : W.IsModelFrobenius f₀ σ p) (m : ℕ) :
    IsUniversalHomeomorphism (W.frobeniusIterate m) := by
  obtain ⟨F₀, hF₀, hp⟩ := hΦ.exists_isFrobenius
  have := hF₀.isUniversalHomeomorphism_of_isPullback hΦ.isPullback W.frobenius_comp hp
  induction m with
  | zero => rw [frobeniusIterate_zero]; infer_instance
  | succ n ih => rw [frobeniusIterate_succ]; infer_instance

/-- The model Frobenius `Φ₁ = F₀ ×_{Spec k} 𝟙_s` of a scheme locally of finite type over `k`
and all its iterates `Φ_m` are finite (blueprint `i-relative-frob`, Step 1). -/
lemma IsModelFrobenius.isFinite_frobeniusIterate {k : Type u} [Field k] [Finite k]
    {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k)} {σ : s ⟶ Spec (.of k)} {p : X ⟶ X₀}
    (hΦ : W.IsModelFrobenius f₀ σ p) [LocallyOfFiniteType f₀] (m : ℕ) :
    IsFinite (W.frobeniusIterate m) := by
  obtain ⟨F₀, hF₀, hp⟩ := hΦ.exists_isFrobenius
  have := hF₀.isFinite_of_isPullback hΦ.isPullback W.frobenius_comp hp
  induction m with
  | zero => rw [frobeniusIterate_zero]; infer_instance
  | succ n ih => rw [frobeniusIterate_succ]; infer_instance

/-- The iterate `φ_m : Φ_m^* K ⟶ K` of the Frobenius coefficient morphism, obtained by
composing the pulled back copies of `φ` along the composition isomorphisms for `Φ^*`:
`φ_0` is the identification `L(𝟙 X)^* K ≃ K` and `φ_{m+1}` is the composite

```
  LΦ_{m+1}^* K ──leftDerivedUpperStarCongr (frobeniusIterate_succ m)──▶ L(Φ₁ ≫ Φ_m)^* K
    ──leftDerivedUpperStarComp Φ₁ Φ_m──▶ LΦ₁^* LΦ_m^* K ──LΦ₁^*.map φ_m──▶ LΦ₁^* K ──φ──▶ K
```

(part of blueprint `sk-d-weil`). -/
noncomputable def coeffIterate :
    (m : ℕ) → ((upperStar A (W.frobeniusIterate m)).leftDerivedFunctor).obj W.obj ⟶ W.obj
  | 0 => (leftDerivedUpperStarId A X).hom.app W.obj
  | m + 1 =>
    (leftDerivedUpperStarCongr A (W.frobeniusIterate_succ m)).hom.app W.obj ≫
      (leftDerivedUpperStarComp A W.frobenius (W.frobeniusIterate m)).hom.app W.obj ≫
      ((upperStar A W.frobenius).leftDerivedFunctor).map (coeffIterate m) ≫ W.coeff

/-- The defining equation of `coeffIterate` at `0`: `φ_0` is `L(𝟙 X)^* K ≃ K`. -/
@[simp]
lemma coeffIterate_zero : W.coeffIterate 0 = (leftDerivedUpperStarId A X).hom.app W.obj :=
  rfl

/-- The defining recursion of `coeffIterate`: `φ_{m+1} = φ ∘ LΦ₁^* φ_m ∘ comp`. It is not
`@[simp]`, since unfolding the successor would loop. -/
lemma coeffIterate_succ (m : ℕ) :
    W.coeffIterate (m + 1) =
      (leftDerivedUpperStarCongr A (W.frobeniusIterate_succ m)).hom.app W.obj ≫
        (leftDerivedUpperStarComp A W.frobenius (W.frobeniusIterate m)).hom.app W.obj ≫
        ((upperStar A W.frobenius).leftDerivedFunctor).map (W.coeffIterate m) ≫ W.coeff :=
  rfl

/-- `φ_1` is `φ`, read through `Φ_1 = Φ₁ ≫ 𝟙 X = Φ₁`. This needs the unit coherence of
`leftDerivedUpperStarComp` with `leftDerivedUpperStarId`. -/
lemma coeffIterate_one :
    W.coeffIterate 1 =
      (leftDerivedUpperStarCongr A W.frobeniusIterate_one).hom.app W.obj ≫ W.coeff := by
  have h := leftDerivedUpperStarComp_id_right_app (A := A) W.frobenius W.obj
  rw [coeffIterate_succ, coeffIterate_zero]
  erw [reassoc_of% h]
  rw [leftDerivedUpperStarCongr_hom_app_trans_assoc]

/-- `Φ_{m + n} = Φ_n ≫ Φ_m`. -/
lemma frobeniusIterate_add (m n : ℕ) :
    W.frobeniusIterate (m + n) = W.frobeniusIterate n ≫ W.frobeniusIterate m := by
  induction n with
  | zero => simp
  | succ n ih => rw [← Nat.add_assoc, frobeniusIterate_succ, ih, frobeniusIterate_succ,
      Category.assoc]

/-- The recursion of `coeffIterate` at `m + (n + 1)`, with the transport along
`Φ_{m + (n + 1)} = Φ₁ ≫ Φ_{m + n}`. -/
lemma coeffIterate_add_succ (m n : ℕ)
    (e : W.frobeniusIterate (m + (n + 1)) = W.frobenius ≫ W.frobeniusIterate (m + n)) :
    W.coeffIterate (m + (n + 1)) =
      (leftDerivedUpperStarCongr A e).hom.app W.obj ≫
        (leftDerivedUpperStarComp A W.frobenius (W.frobeniusIterate (m + n))).hom.app W.obj ≫
        ((upperStar A W.frobenius).leftDerivedFunctor).map (W.coeffIterate (m + n)) ≫
        W.coeff :=
  W.coeffIterate_succ (m + n)

/-- Blueprint `lem-trf-iterated-weil-cocycle`: the cocycle identity
`φ_{m + n} = φ_n ∘ LΦ_n^* φ_m` for the iterates of the Frobenius coefficient morphism, read
through the composition isomorphism `LΦ_{m + n}^* ≃ LΦ_n^* LΦ_m^*` of `Φ_{m + n} = Φ_n ≫ Φ_m`. -/
lemma coeffIterate_add (m n : ℕ) :
    W.coeffIterate (m + n) =
      (leftDerivedUpperStarCongr A (W.frobeniusIterate_add m n)).hom.app W.obj ≫
        (leftDerivedUpperStarComp A (W.frobeniusIterate n) (W.frobeniusIterate m)).hom.app
          W.obj ≫
        ((upperStar A (W.frobeniusIterate n)).leftDerivedFunctor).map (W.coeffIterate m) ≫
        W.coeffIterate n := by
  induction n with
  | zero =>
    have h := leftDerivedUpperStarComp_id_left_app (A := A) (W.frobeniusIterate m) W.obj
    have nat := (leftDerivedUpperStarId A X).hom.naturality (W.coeffIterate m)
    change W.coeffIterate m = (leftDerivedUpperStarCongr A _).hom.app W.obj ≫
      (leftDerivedUpperStarComp A (𝟙 X) (W.frobeniusIterate m)).hom.app W.obj ≫
      ((upperStar A (𝟙 X)).leftDerivedFunctor).map (W.coeffIterate m) ≫
      (leftDerivedUpperStarId A X).hom.app W.obj
    dsimp only [Functor.id_obj, Functor.id_map] at nat
    rw [nat, reassoc_of% h, leftDerivedUpperStarCongr_hom_app_trans_assoc]
    exact (Category.id_comp _).symm
  | succ n ih =>
    rw [coeffIterate_add_succ W m n (W.frobeniusIterate_succ (m + n)), ih,
      coeffIterate_succ W n]
    exact leftDerivedUpperStarComp_cocycle_aux _ _ _ _ _ _ _

/-- The iterates of an invertible Frobenius coefficient morphism are invertible. -/
instance isIso_coeffIterate [IsIso W.coeff] (m : ℕ) : IsIso (W.coeffIterate m) := by
  induction m with
  | zero => rw [coeffIterate_zero]; infer_instance
  | succ n ih => rw [coeffIterate_succ]; infer_instance

section Graph

variable [DerivedBraiding A] [Etale.HasBoundedBelowUpperShrieks A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- The graph correspondence `c_m = (id_X, Φ_m)` of a Weil complex with `K ∈ Dᵇctf(X)` on a
geometric scheme, with coefficient map `φ_m` read through the comparison `K ≃ 𝟙^! K`: the graph
correspondence `Correspondence.ofGraph` of `Φ_m`. Its ordinary-pullback leg is `Φ_m` and its
exceptional leg is the identity (part of blueprint `sk-d-weil`). -/
noncomputable abbrev graph (G : GeometricOperations A s) [IsGeometric aX] (hW : G.ctf X W.obj)
    (m : ℕ) : Correspondence aX aX W.obj W.obj :=
  Correspondence.ofGraph G aX W.obj hW (W.frobeniusIterate m) (W.frobeniusIterate_comp m)
    (W.coeffIterate m)

end Graph

/-- The geometric-stalk Frobenius `F_{x,m} = (φ_m)_x̄` of a Weil complex at a point
`x : s ⟶ X` fixed by `Φ_m`: the composite

```
  Lx^* K ──(leftDerivedUpperStarCongr hx).inv──▶ L(x ≫ Φ_m)^* K
    ──leftDerivedUpperStarComp x Φ_m──▶ Lx^* LΦ_m^* K ──Lx^*.map φ_m──▶ Lx^* K
```

(part of blueprint `sk-thm-trace-formula`). -/
noncomputable def stalkFrobenius (m : ℕ) (x : s ⟶ X) (hx : x ≫ W.frobeniusIterate m = x) :
    ((upperStar A x).leftDerivedFunctor).obj W.obj ⟶
      ((upperStar A x).leftDerivedFunctor).obj W.obj :=
  (leftDerivedUpperStarCongr A hx).inv.app W.obj ≫
    (leftDerivedUpperStarComp A x (W.frobeniusIterate m)).hom.app W.obj ≫
    ((upperStar A x).leftDerivedFunctor).map (W.coeffIterate m)

/-- At a point `x` fixed by `Φ₁` (a rational point of `X₀`), the stalk Frobenius of `φ_m`
is the `m`-th power of the stalk Frobenius of `φ`: `F_{x,m} = F_x^m`. This needs the
associativity and unit coherences of `leftDerivedUpperStarComp`. -/
lemma stalkFrobenius_eq_pow {x : s ⟶ X} (hx : x ≫ W.frobenius = x) (m : ℕ) :
    W.stalkFrobenius m x (W.comp_frobeniusIterate_of_comp_frobenius hx m) =
      let F : End (((upperStar A x).leftDerivedFunctor).obj W.obj) :=
        W.stalkFrobenius 1 x (W.comp_frobeniusIterate_of_comp_frobenius hx 1)
      F ^ m := by
  induction m with
  | zero =>
    have h := leftDerivedUpperStarComp_id_right_app (A := A) x W.obj
    change (leftDerivedUpperStarCongr A (Category.comp_id x)).inv.app W.obj ≫ (leftDerivedUpperStarComp A x (𝟙 X)).hom.app W.obj ≫
        ((upperStar A x).leftDerivedFunctor).map ((leftDerivedUpperStarId A X).hom.app W.obj) =
      𝟙 _
    rw [h, leftDerivedUpperStarCongr_inv_app, leftDerivedUpperStarCongr_hom_app_trans,
      leftDerivedUpperStarCongr_hom_app_self]
  | succ m ih =>
    simp only at ih ⊢
    rw [pow_succ', End.mul_def, ← ih]
    simp only [stalkFrobenius]
    rw [coeffIterate_succ W m, coeffIterate_one]
    exact leftDerivedUpperStarComp_stalk_aux (W.frobeniusIterate_succ m) W.frobeniusIterate_one
      _ _ _ _ _

/-- The Frobenius coefficient morphism of the pullback `Lf^* K` along a morphism
`f : Y ⟶ X` that intertwines an endomorphism `g : Y ⟶ Y` with `Φ_m`,

```
  Y ──f──▶ X
  │g       │Φ_m
  ▼        ▼
  Y ──f──▶ X
```

the composite

```
  Lg^* Lf^* K ≃ L(g ≫ f)^* K = L(f ≫ Φ_m)^* K ≃ Lf^* LΦ_m^* K ──Lf^* φ_m──▶ Lf^* K
```

whose first map is the inverse of `leftDerivedUpperStarSquareIso` for the square
(part of blueprint `sk-d-curve-pieces`). -/
noncomputable def upperStarPullCoeff (m : ℕ) {f : Y ⟶ X} {g : Y ⟶ Y}
    (sq : CommSq g f f (W.frobeniusIterate m)) :
    ((upperStar A g).leftDerivedFunctor).obj (((upperStar A f).leftDerivedFunctor).obj W.obj) ⟶
      ((upperStar A f).leftDerivedFunctor).obj W.obj :=
  (leftDerivedUpperStarSquareIso A sq).inv.app W.obj ≫
    ((upperStar A f).leftDerivedFunctor).map (W.coeffIterate m)

/-- The pullback of an invertible Frobenius coefficient morphism is invertible. -/
instance isIso_upperStarPullCoeff [IsIso W.coeff] (m : ℕ) {f : Y ⟶ X} {g : Y ⟶ Y}
    (sq : CommSq g f f (W.frobeniusIterate m)) :
    IsIso (W.upperStarPullCoeff m sq) := by
  dsimp [upperStarPullCoeff]
  infer_instance

/-- The pullback of a Weil complex along a morphism `f : Y ⟶ X` over `s` that intertwines an
endomorphism `g : Y ⟶ Y` with `Φ₁`: the Weil complex `Lf^* K` on `Y` with Frobenius `g` and
coefficient morphism `W.upperStarPullCoeff 1 sq` (part of blueprint `sk-d-curve-pieces`). -/
noncomputable def upperStarPull (f : Y ⟶ X) {aY : Y ⟶ s} (hf : f ≫ aX = aY) (g : Y ⟶ Y)
    (sq : CommSq g f f (W.frobeniusIterate 1)) : WeilComplex (A := A) aY where
  frobenius := g
  frobenius_comp := by
    rw [← hf, ← Category.assoc, sq.w, Category.assoc, W.frobeniusIterate_comp]
  obj := ((upperStar A f).leftDerivedFunctor).obj W.obj
  coeff := W.upperStarPullCoeff 1 sq

end WeilComplex

/-- The *relative Frobenius* `r_m = (f, Φ_{X,m}) : X ⟶ X'_m` of a morphism `f : X ⟶ Y`
compatible with Frobenius morphisms `Φ_X`, `Φ_Y`, where `X'_m = Y ×_{Φ_Y, Y, f} X`:

```
   X'_m ──f'_m──→ Y           r_m ≫ p_m = Φ_X
     │            │           r_m ≫ f'_m = f
  p_m│            │Φ_Y
     ↓            ↓
     X ────f────→ Y
```

Here `X'_m` is `CategoryTheory.Limits.pullback Φ_Y f`, with `f'_m = pullback.fst` and
`p_m = pullback.snd` (blueprint: `sk-d-relative-frob`, `d-relative-frob`). -/
noncomputable def relativeFrobenius (f : X ⟶ Y) (frobX : X ⟶ X) (frobY : Y ⟶ Y)
    (h : f ≫ frobY = frobX ≫ f) : X ⟶ pullback frobY f :=
  pullback.lift f frobX h

@[reassoc (attr := simp)]
lemma relativeFrobenius_comp_snd (f : X ⟶ Y) (frobX : X ⟶ X) (frobY : Y ⟶ Y)
    (h : f ≫ frobY = frobX ≫ f) :
    relativeFrobenius f frobX frobY h ≫ pullback.snd frobY f = frobX :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma relativeFrobenius_comp_fst (f : X ⟶ Y) (frobX : X ⟶ X) (frobY : Y ⟶ Y)
    (h : f ≫ frobY = frobX ≫ f) :
    relativeFrobenius f frobX frobY h ≫ pullback.fst frobY f = f :=
  pullback.lift_fst _ _ _

section BaseChange

variable {S s₀ X₀ Y₀ : Scheme.{u}} {gX : X₀ ⟶ S} {gY : Y₀ ⟶ S} {σ : s₀ ⟶ S} {pX : X ⟶ X₀}
  {aX : X ⟶ s₀} {pY : Y ⟶ Y₀} {aY : Y ⟶ s₀} {f₀ : X₀ ⟶ Y₀} {f : X ⟶ Y}

/-- Let `f : X ⟶ Y` be the base change of `f₀ : X₀ ⟶ Y₀`, and let `Φ_X`, `Φ_Y` be base changes
of endomorphisms `F_X`, `F_Y` of `X₀`, `Y₀` along `σ : s₀ ⟶ S`. If `f₀ ≫ F_Y = F_X ≫ f₀`, then
`f ≫ Φ_Y = Φ_X ≫ f` (blueprint: `d-relative-frob`). -/
lemma comp_eq_comp_of_isPullback (hY : IsPullback pY aY gY σ) {FX : X₀ ⟶ X₀} {FY : Y₀ ⟶ Y₀}
    (h₀ : f₀ ≫ FY = FX ≫ f₀) {ΦX : X ⟶ X} {ΦY : Y ⟶ Y} (hΦXa : ΦX ≫ aX = aX)
    (hΦYa : ΦY ≫ aY = aY) (hΦX : ΦX ≫ pX = pX ≫ FX) (hΦY : ΦY ≫ pY = pY ≫ FY)
    (hfp : f ≫ pY = pX ≫ f₀) (hfa : f ≫ aY = aX) : f ≫ ΦY = ΦX ≫ f := by
  apply hY.hom_ext
  · rw [Category.assoc, hΦY, reassoc_of% hfp, h₀, Category.assoc, hfp, reassoc_of% hΦX]
  · rw [Category.assoc, hΦYa, hfa, Category.assoc, hfa, hΦXa]

/-- The fibre product `X'_m = Y ×_{Φ_Y, Y, f} X` commutes with base change: if `f`, `Φ_Y` are
the base changes of `f₀ : X₀ ⟶ Y₀` and of `F_Y : Y₀ ⟶ Y₀` along `σ : s₀ ⟶ S`, then
`X'_m = X₀' ×_S s₀` for `X₀' = Y₀ ×_{F_Y, Y₀, f₀} X₀` (blueprint: `d-relative-frob`). -/
lemma isPullback_pullbackMap (hX : IsPullback pX aX gX σ) (hfp : f ≫ pY = pX ≫ f₀)
    {ΦY : Y ⟶ Y} {FY : Y₀ ⟶ Y₀} (hΦY : IsPullback ΦY pY pY FY) :
    IsPullback (pullback.map ΦY f FY f₀ pY pX pY hΦY.w hfp) (pullback.snd ΦY f ≫ aX)
      (pullback.snd FY f₀ ≫ gX) σ := by
  refine IsPullback.paste_vert ?_ hX
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (.of_hasPullback FY f₀)
  rw [pullback.lift_fst, ← hfp]
  exact (IsPullback.of_hasPullback ΦY f).paste_horiz hΦY.flip

/-- The relative Frobenius commutes with base change: in the situation of
`AlgebraicGeometry.ProEtale.isPullback_pullbackMap`, if moreover `Φ_X = F_X ×_S 𝟙_{s₀}` with
`F_X` an `S`-morphism, then `r = (f, Φ_X)` is the base change `(f₀, F_X) ×_S 𝟙_{s₀}` of the
relative Frobenius of `X₀` over `Y₀` (blueprint: `d-relative-frob`). -/
lemma isPullback_relativeFrobenius (hX : IsPullback pX aX gX σ) (hfp : f ≫ pY = pX ≫ f₀)
    {FX : X₀ ⟶ X₀} {FY : Y₀ ⟶ Y₀} (h₀ : f₀ ≫ FY = FX ≫ f₀) (hFX : FX ≫ gX = gX)
    {ΦX : X ⟶ X} {ΦY : Y ⟶ Y} (h : f ≫ ΦY = ΦX ≫ f) (hΦXa : ΦX ≫ aX = aX)
    (hΦX : ΦX ≫ pX = pX ≫ FX) (hΦY : IsPullback ΦY pY pY FY) :
    IsPullback (relativeFrobenius f ΦX ΦY h) pX (pullback.map ΦY f FY f₀ pY pX pY hΦY.w hfp)
      (relativeFrobenius f₀ FX FY h₀) := by
  refine (IsPullback.of_bot ?_ ?_ (isPullback_pullbackMap hX hfp hΦY)).flip
  · simpa [hΦXa, hFX] using hX
  · apply pullback.hom_ext <;> simp [relativeFrobenius, hfp, hΦX]

end BaseChange

section Model

variable {k : Type u} [Field k] [Finite k] {s₀ X₀ Y₀ : Scheme.{u}} {gX : X₀ ⟶ Spec (.of k)}
  {gY : Y₀ ⟶ Spec (.of k)} {σ : s₀ ⟶ Spec (.of k)} {pX : X ⟶ X₀} {aX : X ⟶ s₀} {pY : Y ⟶ Y₀}
  {aY : Y ⟶ s₀} {FX : X₀ ⟶ X₀} {FY : Y₀ ⟶ Y₀} {ΦX : X ⟶ X} {ΦY : Y ⟶ Y}

private lemma pow_comp_eq_comp_pow {Z W : Scheme.{u}} {F : Z ⟶ Z} {G : W ⟶ W} {g : Z ⟶ W}
    (hg : F ≫ g = g ≫ G) (m : ℕ) :
    End.asHom (End.of F ^ m) ≫ g = g ≫ End.asHom (End.of G ^ m) := by
  induction m with
  | zero => simp [End.one_def]
  | succ m ih =>
    rw [pow_succ, pow_succ, End.mul_def, End.mul_def]
    simp only [End.asHom, End.of, Category.assoc] at ih ⊢
    rw [ih, reassoc_of% hg]

private lemma pow_comp_eq_of_comp_eq {Z W : Scheme.{u}} {F : Z ⟶ Z} {g : Z ⟶ W} (hg : F ≫ g = g)
    (m : ℕ) : End.asHom (End.of F ^ m) ≫ g = g := by
  refine (pow_comp_eq_comp_pow (G := 𝟙 W) (hg.trans (Category.comp_id g).symm) m).trans ?_
  rw [show End.of (𝟙 W) ^ m = 1 from one_pow m]
  exact Category.comp_id g

/-- For the base change `f : X ⟶ Y` of a morphism `f₀ : X₀ ⟶ Y₀` of schemes over a finite
field `k`, and the base changes `Φ_X = F_X ×_k 𝟙`, `Φ_Y = F_Y ×_k 𝟙` of the `#k`-power
Frobenii, `Φ_Y ^ m ∘ f = f ∘ Φ_X ^ m` for every `m`: the absolute Frobenius commutes with every
morphism of `𝐅_p`-schemes. Hence the relative Frobenius `r_m = (f, Φ_X ^ m)` is defined
(blueprint: `sk-d-relative-frob`, `d-relative-frob`). -/
theorem comp_frobenius_pow_eq_of_isFrobenius (hX : IsPullback pX aX gX σ)
    (hY : IsPullback pY aY gY σ) (hFX : FX.IsFrobenius (Nat.card k))
    (hFY : FY.IsFrobenius (Nat.card k))
    (hΦXa : ΦX ≫ aX = aX) (hΦYa : ΦY ≫ aY = aY) (hΦX : ΦX ≫ pX = pX ≫ FX)
    (hΦY : ΦY ≫ pY = pY ≫ FY) (hfp : f ≫ pY = pX ≫ f₀) (hfa : f ≫ aY = aX) (m : ℕ) :
    f ≫ End.asHom (End.of ΦY ^ m) = End.asHom (End.of ΦX ^ m) ≫ f :=
  (pow_comp_eq_comp_pow (comp_eq_comp_of_isPullback hY (hFX.comp_eq_comp gX hFY f₀) hΦXa
    hΦYa hΦX hΦY hfp hfa).symm m).symm

/-- **The relative Frobenius factorization.** Let `f : X ⟶ Y` be the base change along
`σ : s₀ ⟶ Spec k` of a morphism `f₀ : X₀ ⟶ Y₀` of schemes over a finite field `k`, and let
`Φ_X = F_X ×_k 𝟙`, `Φ_Y = F_Y ×_k 𝟙` be the base changes of their `#k`-power Frobenii. Put
`Q = #k ^ m`. Then `F_X ^ m`, `F_Y ^ m` are the `Q`-power Frobenii of `X₀`, `Y₀`, the fibre
product `X'_m = Y ×_{Φ_Y ^ m, Y, f} X` is the base change `X₀^{(Q)} ×_k s₀` of
`X₀^{(Q)} = Y₀ ×_{F_Y ^ m, Y₀, f₀} X₀`, and `r_m = (f, Φ_X ^ m)` is the base change of the
relative `Q`-power Frobenius `F_{X₀/Y₀} = (f₀, F_X ^ m)`. The identities `p_m ∘ r_m = Φ_X ^ m`
and `f'_m ∘ r_m = f` are `relativeFrobenius_comp_snd` and `relativeFrobenius_comp_fst`
(blueprint: `sk-d-relative-frob`, `d-relative-frob`). -/
theorem isPullback_relativeFrobenius_of_isFrobenius (hX : IsPullback pX aX gX σ)
    (hY : IsPullback pY aY gY σ) (hFX : FX.IsFrobenius (Nat.card k))
    (hFY : FY.IsFrobenius (Nat.card k)) (hΦXa : ΦX ≫ aX = aX) (hΦYa : ΦY ≫ aY = aY)
    (hΦX : ΦX ≫ pX = pX ≫ FX) (hΦY : ΦY ≫ pY = pY ≫ FY) (hfp : f ≫ pY = pX ≫ f₀)
    (hfa : f ≫ aY = aX) (m : ℕ) :
    (End.asHom (End.of FX ^ m)).IsFrobenius (Nat.card k ^ m) ∧
      (End.asHom (End.of FY ^ m)).IsFrobenius (Nat.card k ^ m) ∧
      ∃ (h₀ : f₀ ≫ End.asHom (End.of FY ^ m) = End.asHom (End.of FX ^ m) ≫ f₀)
        (hm : End.asHom (End.of ΦY ^ m) ≫ pY = pY ≫ End.asHom (End.of FY ^ m)),
        IsPullback (pullback.map _ f _ f₀ pY pX pY hm hfp)
          (pullback.snd _ f ≫ aX) (pullback.snd _ f₀ ≫ gX) σ ∧
        IsPullback (relativeFrobenius f _ _ (comp_frobenius_pow_eq_of_isFrobenius hX hY hFX
          hFY hΦXa hΦYa hΦX hΦY hfp hfa m)) pX (pullback.map _ f _ f₀ pY pX pY hm hfp)
          (relativeFrobenius f₀ _ _ h₀) := by
  have h₀ := (pow_comp_eq_comp_pow (hFX.comp_eq_comp gX hFY f₀).symm m).symm
  have hm := pow_comp_eq_comp_pow hΦY m
  have hYm : IsPullback (End.asHom (End.of ΦY ^ m)) pY pY (End.asHom (End.of FY ^ m)) :=
    have h₁ := pow_comp_eq_of_comp_eq hΦYa m
    have h₂ := pow_comp_eq_of_comp_eq (hFY.comp_eq gY) m
    IsPullback.of_right (by rw [h₁, h₂]; exact hY.flip) hm hY.flip
  exact ⟨hFX.pow gX m, hFY.pow gY m, h₀, hm, isPullback_pullbackMap hX hfp hYm,
    isPullback_relativeFrobenius hX hfp h₀ (pow_comp_eq_of_comp_eq (hFX.comp_eq gX) m) _
      (pow_comp_eq_of_comp_eq hΦXa m) (pow_comp_eq_comp_pow hΦX m) hYm⟩

end Model

/-- The relative Frobenius of an affine morphism. Let `g : R ⟶ S` be a ring map and `φ_R`, `φ_S`
ring endomorphisms with `φ_R ≫ g = g ≫ φ_S` (for instance the `Q`-power maps `a ↦ a ^ Q` of
`𝐅_p`-algebras). Under the identification of `Spec R ×_{Spec φ_R, Spec R, Spec g} Spec S` with
`Spec (R ⊗_{φ_R, R} S)`, the relative Frobenius of `Spec g` is `Spec` of the map
`R ⊗_{φ_R, R} S ⟶ S`, `r' ⊗ s ↦ g r' * φ_S s` (blueprint: `d-relative-frob`). -/
lemma relativeFrobenius_specMap {R S : CommRingCat.{u}} (g : R ⟶ S) (φR : R ⟶ R) (φS : S ⟶ S)
    (w : φR ≫ g = g ≫ φS) :
    relativeFrobenius (Spec.map g) (Spec.map φS) (Spec.map φR)
        (by rw [← Spec.map_comp, ← Spec.map_comp, w]) =
      Spec.map (pushout.desc g φS w) ≫ (isPullback_SpecMap_pushout φR g).isoPullback.hom := by
  apply pullback.hom_ext <;> simp [← Spec.map_comp]

/-- The relative Frobenius of a morphism between schemes with finite Frobenius morphisms is
finite: it is a section of the projection `p_m`, a base change of `Φ_Y`, and its composite
with that projection is the finite morphism `Φ_X` (blueprint: `sk-i-relative-frob`). -/
instance isFinite_relativeFrobenius (f : X ⟶ Y) (frobX : X ⟶ X) (frobY : Y ⟶ Y)
    (h : f ≫ frobY = frobX ≫ f) [IsFinite frobX] [IsFinite frobY] :
    IsFinite (relativeFrobenius f frobX frobY h) := by
  have : IsFinite (relativeFrobenius f frobX frobY h ≫ pullback.snd frobY f) := by
    rw [relativeFrobenius_comp_snd]
    infer_instance
  exact .of_comp _ (pullback.snd frobY f)

/-- The relative Frobenius of a morphism between schemes whose Frobenius morphisms are
finite universal homeomorphisms is a universal homeomorphism: its composite with the
projection `p_m`, a base change of `Φ_Y`, is `Φ_X` (blueprint: `sk-i-relative-frob`). -/
theorem isUniversalHomeomorphism_relativeFrobenius (f : X ⟶ Y) (frobX : X ⟶ X)
    (frobY : Y ⟶ Y) (h : f ≫ frobY = frobX ≫ f) [IsFinite frobX] [IsFinite frobY]
    [IsUniversalHomeomorphism frobX] [IsUniversalHomeomorphism frobY] :
    IsUniversalHomeomorphism (relativeFrobenius f frobX frobY h) := by
  have : IsUniversalHomeomorphism
      (relativeFrobenius f frobX frobY h ≫ pullback.snd frobY f) := by
    rw [relativeFrobenius_comp_snd]
    infer_instance
  exact .of_comp _ (pullback.snd frobY f)

/-- **Relative Frobenius.** Let `X = X₀ ×_{Spec k} s` and `Y = Y₀ ×_{Spec k} s` be base changes
of schemes `X₀`, `Y₀` locally of finite type over a finite field `k`, and let `Φ_X`, `Φ_Y` be
the base changes `F ×_{Spec k} 𝟙_s` of their `#k`-power Frobenius morphisms. For a morphism
`f : X ⟶ Y` with `f ≫ Φ_Y ^ m = Φ_X ^ m ≫ f`, the relative Frobenius
`r_m = (f, Φ_X ^ m) : X ⟶ Y ×_{Φ_Y ^ m, Y, f} X` is finite and a universal homeomorphism
(blueprint: `sk-i-relative-frob`, `i-relative-frob`). -/
theorem isFinite_and_isUniversalHomeomorphism_relativeFrobenius {k : Type u} [Field k]
    [Finite k] {X₀ Y₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k)} {g₀ : Y₀ ⟶ Spec (.of k)}
    [LocallyOfFiniteType f₀] [LocallyOfFiniteType g₀] {σ : s ⟶ Spec (.of k)} {aX : X ⟶ s}
    {aY : Y ⟶ s} {pX : X ⟶ X₀} {pY : Y ⟶ Y₀} (hX : IsPullback pX aX f₀ σ)
    (hY : IsPullback pY aY g₀ σ) {FX : X₀ ⟶ X₀} {FY : Y₀ ⟶ Y₀}
    (hFX : FX.IsFrobenius (Nat.card k)) (hFY : FY.IsFrobenius (Nat.card k)) {ΦX : X ⟶ X}
    {ΦY : Y ⟶ Y} (hΦXa : ΦX ≫ aX = aX) (hΦYa : ΦY ≫ aY = aY) (hΦX : ΦX ≫ pX = pX ≫ FX)
    (hΦY : ΦY ≫ pY = pY ≫ FY) (f : X ⟶ Y) (m : ℕ)
    (h : f ≫ End.asHom (End.of ΦY ^ m) = End.asHom (End.of ΦX ^ m) ≫ f) :
    IsFinite (relativeFrobenius f _ _ h) ∧
      IsUniversalHomeomorphism (relativeFrobenius f _ _ h) := by
  have hpow {Z : Scheme.{u}} (Φ : End Z) [IsFinite Φ] [IsUniversalHomeomorphism Φ] (n : ℕ) :
      IsFinite (End.asHom (Φ ^ n)) ∧ IsUniversalHomeomorphism (End.asHom (Φ ^ n)) := by
    induction n with
    | zero =>
      exact ⟨inferInstanceAs (IsFinite (𝟙 Z)), inferInstanceAs (IsUniversalHomeomorphism (𝟙 Z))⟩
    | succ n ih =>
      obtain ⟨_, _⟩ := ih
      rw [pow_succ, End.mul_def]
      exact ⟨inferInstance, inferInstance⟩
  have := hFX.isFinite_of_isPullback hX hΦXa hΦX
  have := hFY.isFinite_of_isPullback hY hΦYa hΦY
  have := hFX.isUniversalHomeomorphism_of_isPullback hX hΦXa hΦX
  have := hFY.isUniversalHomeomorphism_of_isPullback hY hΦYa hΦY
  obtain ⟨_, _⟩ := hpow (End.of ΦX) m
  obtain ⟨_, _⟩ := hpow (End.of ΦY) m
  exact ⟨inferInstance, isUniversalHomeomorphism_relativeFrobenius ..⟩

/-- Topological invariance: for a finite universal homeomorphism `r : X ⟶ Y`, pullback is
an equivalence `Lr^* : D(Y, A) ≌ D(X, A)`, with inverse `Rr_* = Rr_!` and invertible unit
and counit. Reduction of a scheme is a finite universal homeomorphism, so the statement
covers it. It is the derived functor of the exact equivalence `r^*` of
`AlgebraicGeometry.ProEtale.isEquivalence_upperStar_of_isUniversalHomeomorphism`
(blueprint: `sk-i-topology`). -/
theorem isEquivalence_leftDerivedUpperStar (r : X ⟶ Y) [IsFinite r]
    [IsUniversalHomeomorphism r] : ((upperStar A r).leftDerivedFunctor).IsEquivalence :=
  have := isEquivalence_upperStar_of_isUniversalHomeomorphism A r
  inferInstance

/-- The unit `K ⟶ Rr_* Lr^* K` of the derived adjunction `Lr^* ⊣ Rr_*` is invertible for a
finite universal homeomorphism `r`, since `Lr^*` is an equivalence
(blueprint: `sk-i-topology`). -/
instance isIso_derivedUpperStarLowerStarAdjunction_unit (r : X ⟶ Y) [IsFinite r]
    [IsUniversalHomeomorphism r] : IsIso (derivedUpperStarLowerStarAdjunction A r).unit :=
  have := isEquivalence_leftDerivedUpperStar (A := A) r
  (derivedUpperStarLowerStarAdjunction A r).unit_isIso_of_L_fully_faithful

/-- The counit `Lr^* Rr_* K ⟶ K` of the derived adjunction `Lr^* ⊣ Rr_*` is invertible for a
finite universal homeomorphism `r`: `Rr_*` is right adjoint to an equivalence, hence an
equivalence itself (blueprint: `sk-i-topology`). -/
instance isIso_derivedUpperStarLowerStarAdjunction_counit (r : X ⟶ Y) [IsFinite r]
    [IsUniversalHomeomorphism r] : IsIso (derivedUpperStarLowerStarAdjunction A r).counit :=
  have := isEquivalence_leftDerivedUpperStar (A := A) r
  have := (derivedUpperStarLowerStarAdjunction A r).isEquivalence_right_of_isEquivalence_left
  (derivedUpperStarLowerStarAdjunction A r).counit_isIso_of_R_fully_faithful

section

variable [DerivedBraiding A] [Etale.HasBoundedBelowUpperShrieks A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- Topological invariance preserves the coefficient stage: `Lr^*` restricts to an
equivalence `Dᵇctf(Y, A) ≃ Dᵇctf(X, A)` along a finite universal homeomorphism. The
inverse `Rr_* = Rr_!` preserves `Dᵇctf` because `r` is finite, hence proper, and `Rr_!`
preserves `Dᵇctf` (blueprint: `sk-i-topology`). -/
theorem ctf_leftDerivedUpperStar_obj_iff (G : GeometricOperations A s) (r : X ⟶ Y)
    (hr : IsGeometricHom s r) [IsFinite r] [IsUniversalHomeomorphism r]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    G.ctf X (((upperStar A r).leftDerivedFunctor).obj K) ↔ G.ctf Y K :=
  ⟨fun hK ↦ (G.ctf Y).prop_of_iso
      (asIso ((derivedUpperStarLowerStarAdjunction A r).unit.app K)).symm
      (G.ctf_lowerStar r hr hK),
    G.ctf_upperStar r hr⟩

namespace GeometricOperations

/-- The *compact-support exchange* of a commutative square `f ≫ g_Y = g_X ≫ f` whose gap map
`r = relativeFrobenius f g_X g_Y h : X ⟶ X' = Y ×_{g_Y, Y, f} X` is proper:

```
   X ──r──→ X' ──f'──→ Y          r ≫ f' = f
            │          │          r ≫ p = g_X
           p│          │g_Y
            ↓          ↓
            X ───f───→ Y
```

with `f' = pullback.fst g_Y f` and `p = pullback.snd g_Y f`. It is the natural transformation
`θ : Lg_Y^* Rf_! ⟶ Rf_! Lg_X^*` with components

```
  Lg_Y^* Rf_! K ──baseChange sq──▶ Rf'_! Lp^* K
    ──Rf'_!(unit of Lr^* ⊣ Rr_*)──▶ Rf'_! Rr_* Lr^* Lp^* K
    ──Rf'_!(properComparison r).inv──▶ Rf'_! Rr_! Lr^* Lp^* K
    ──lowerShriekComp r f' ≪≫ rightDerivedLowerShriekCongr──▶ Rf_! Lr^* Lp^* K
    ──Rf_!(leftDerivedUpperStarComp r p ≪≫ leftDerivedUpperStarCongr)──▶ Rf_! Lg_X^* K.
```

For the Frobenius square of a Weil complex this is the Weil comparison `θ_{f,m}` with
`g_X = Φ_{X,m}`, `g_Y = Φ_{Y,m}` and `r = r_m`, and it is invertible when `r` is a finite
universal homeomorphism (`isIso_lowerShriekExchange`) (blueprint: `sk-d-weil-push`). -/
noncomputable def lowerShriekExchange (G : GeometricOperations A s) {aX : X ⟶ s} {aY : Y ⟶ s}
    [IsGeometric aX] [IsGeometric aY] (f : X ⟶ Y) (hf : f ≫ aY = aX) [HasCompactification f]
    (gX : X ⟶ X) (gY : Y ⟶ Y) (hgX : gX ≫ aX = aX) (hgY : gY ≫ aY = aY)
    (h : f ≫ gY = gX ≫ f) [IsGeometric (pullback.snd gY f ≫ aX)]
    [IsProper (relativeFrobenius f gX gY h)] :
    G.lowerShriekCtf f (.mk hf) ⋙ G.upperStarCtf gY (.mk hgY) ⟶
      G.upperStarCtf gX (.mk hgX) ⋙ G.lowerShriekCtf f (.mk hf) :=
  let f' := pullback.fst gY f
  let p := pullback.snd gY f
  let sq : IsPullback p f' f gY := (IsPullback.of_hasPullback gY f).flip
  let r := relativeFrobenius f gX gY h
  have : HasCompactification f' := HasCompactification.of_isPullback sq
  have : HasCompactification (r ≫ f') := by
    rw [relativeFrobenius_comp_fst]
    infer_instance
  have hf' : f' ≫ aY = p ≫ aX := by
    rw [← hgY, ← Category.assoc, pullback.condition, Category.assoc, hf]
  have hr : r ≫ p ≫ aX = aX := by
    rw [← Category.assoc, relativeFrobenius_comp_snd, hgX]
  (G.baseChange sq (.mk hf) (.mk hgY) (.mk hf') (.mk (aX := p ≫ aX) rfl)).hom ≫
    Functor.whiskerRight (Functor.whiskerLeft (G.upperStarCtf p (.mk (aX := p ≫ aX) rfl))
      (ctfHomMk (F := 𝟭 _) (G := G.upperStarCtf r (.mk hr) ⋙ G.lowerStarCtf r (.mk hr))
          (Functor.whiskerLeft (DerivedCategory.constructibleFiniteTor A _).ι
            (derivedUpperStarLowerStarAdjunction A r).unit) ≫
        Functor.whiskerLeft (G.upperStarCtf r (.mk hr)) (G.properComparison r (.mk hr)).inv))
      (G.lowerShriekCtf f' (.mk hf')) ≫
    Functor.whiskerLeft (G.upperStarCtf p (.mk (aX := p ≫ aX) rfl) ⋙ G.upperStarCtf r (.mk hr))
      (G.lowerShriekComp r f' (.mk hr) (.mk hf')
          (.mk (aX := aX) (aY := aY) (by rw [Category.assoc, hf', hr])) ≪≫
        ctfLowerShriekCongr (relativeFrobenius_comp_fst f gX gY h) _ _).hom ≫
    Functor.whiskerRight (ctfHomMk
      (F := G.upperStarCtf p (.mk (aX := p ≫ aX) rfl) ⋙ G.upperStarCtf r (.mk hr))
      (G := G.upperStarCtf gX (.mk hgX))
      (Functor.whiskerLeft (DerivedCategory.constructibleFiniteTor A _).ι
        ((leftDerivedUpperStarComp A r p).symm ≪≫
          leftDerivedUpperStarCongr A (relativeFrobenius_comp_snd f gX gY h)).hom))
      (G.lowerShriekCtf f (.mk hf))

/-- Topological invariance makes the compact-support exchange invertible when the gap map is
a finite universal homeomorphism: then the unit of `Lr^* ⊣ Rr_*` is an isomorphism
(blueprint: `sk-i-topology`). -/
instance isIso_lowerShriekExchange (G : GeometricOperations A s) {aX : X ⟶ s} {aY : Y ⟶ s}
    [IsGeometric aX] [IsGeometric aY] (f : X ⟶ Y) (hf : f ≫ aY = aX) [HasCompactification f]
    (gX : X ⟶ X) (gY : Y ⟶ Y) (hgX : gX ≫ aX = aX) (hgY : gY ≫ aY = aY)
    (h : f ≫ gY = gX ≫ f) [IsGeometric (pullback.snd gY f ≫ aX)]
    [IsFinite (relativeFrobenius f gX gY h)]
    [IsUniversalHomeomorphism (relativeFrobenius f gX gY h)] :
    IsIso (G.lowerShriekExchange f hf gX gY hgX hgY h) := by
  dsimp only [lowerShriekExchange]
  infer_instance

end GeometricOperations

/-- The coefficient map of `AlgebraicGeometry.ProEtale.WeilComplex.lowerShriekPush`: the
composite `ψ = Rf_! φ ∘ θ_{f,1}` of the compact-support exchange
`θ_{f,1} : LΦ_Y^* Rf_! K ⟶ Rf_! LΦ_X^* K` (`GeometricOperations.lowerShriekExchange` for the
square `f ≫ Φ_Y = Φ_X ≫ f`) with `Rf_! φ`. Only the case `m = 1` is constructed here. -/
noncomputable def WeilComplex.lowerShriekPushCoeff {aX : X ⟶ s} (W : WeilComplex (A := A) aX)
    (G : GeometricOperations A s) (hW : G.ctf X W.obj) {aY : Y ⟶ s} [IsGeometric aX]
    [IsGeometric aY] (f : X ⟶ Y) (hf : f ≫ aY = aX) [HasCompactification f] (frobY : Y ⟶ Y)
    (hY : frobY ≫ aY = aY) (h : f ≫ frobY = W.frobenius ≫ f)
    [IsGeometric (pullback.snd frobY f ≫ aX)]
    [IsProper (relativeFrobenius f W.frobenius frobY h)] :
    ((upperStar A frobY).leftDerivedFunctor).obj ((rightDerivedLowerShriek A f).obj W.obj) ⟶
      (rightDerivedLowerShriek A f).obj W.obj :=
  ((G.lowerShriekExchange f hf W.frobenius frobY W.frobenius_comp hY h).app ⟨W.obj, hW⟩).hom ≫
    (rightDerivedLowerShriek A f).map W.coeff

/-- The `!`-pushforward of a Weil complex `(K, φ)` with `K ∈ Dᵇctf(X)` along a morphism
`f : X ⟶ Y` of geometric schemes compatible with the Frobenius morphisms: the Weil complex
`L = Rf_! K` on `Y` with coefficient map `ψ = Rf_! φ ∘ θ_{f,1}` (blueprint: `sk-d-weil-push`). -/
noncomputable def WeilComplex.lowerShriekPush {aX : X ⟶ s} {aY : Y ⟶ s}
    (W : WeilComplex (A := A) aX) (G : GeometricOperations A s) (hW : G.ctf X W.obj)
    [IsGeometric aX] [IsGeometric aY] (f : X ⟶ Y) (hf : f ≫ aY = aX) [HasCompactification f]
    (frobY : Y ⟶ Y) (hY : frobY ≫ aY = aY) (h : f ≫ frobY = W.frobenius ≫ f)
    [IsGeometric (pullback.snd frobY f ≫ aX)]
    [IsProper (relativeFrobenius f W.frobenius frobY h)] :
    WeilComplex (A := A) aY where
  frobenius := frobY
  frobenius_comp := hY
  obj := (rightDerivedLowerShriek A f).obj W.obj
  coeff := W.lowerShriekPushCoeff G hW f hf frobY hY h

/-- The `!`-pushforward of a Weil datum is a Weil datum: when the relative Frobenius is a
finite universal homeomorphism, `θ_{f,1}` is invertible, so `ψ = Rf_! φ ∘ θ_{f,1}` is
invertible whenever `φ` is (blueprint: `sk-d-weil-push`). -/
instance WeilComplex.isIso_lowerShriekPush_coeff {aX : X ⟶ s} {aY : Y ⟶ s}
    (W : WeilComplex (A := A) aX) (G : GeometricOperations A s) (hW : G.ctf X W.obj)
    [IsGeometric aX] [IsGeometric aY] (f : X ⟶ Y) (hf : f ≫ aY = aX) [HasCompactification f]
    (frobY : Y ⟶ Y) (hY : frobY ≫ aY = aY) (h : f ≫ frobY = W.frobenius ≫ f)
    [IsGeometric (pullback.snd frobY f ≫ aX)]
    [IsFinite (relativeFrobenius f W.frobenius frobY h)]
    [IsUniversalHomeomorphism (relativeFrobenius f W.frobenius frobY h)] [IsIso W.coeff] :
    IsIso (W.lowerShriekPush G hW f hf frobY hY h).coeff := by
  have : IsIso ((G.lowerShriekExchange f hf W.frobenius frobY W.frobenius_comp hY h).app
      ⟨W.obj, hW⟩) := inferInstance
  have : IsIso ((G.lowerShriekExchange f hf W.frobenius frobY W.frobenius_comp hY h).app
      ⟨W.obj, hW⟩).hom :=
    inferInstanceAs (IsIso ((DerivedCategory.constructibleFiniteTor A Y).ι.map
      ((G.lowerShriekExchange f hf W.frobenius frobY W.frobenius_comp hY h).app ⟨W.obj, hW⟩)))
  dsimp [lowerShriekPush, lowerShriekPushCoeff]
  infer_instance

end

end AlgebraicGeometry.ProEtale
