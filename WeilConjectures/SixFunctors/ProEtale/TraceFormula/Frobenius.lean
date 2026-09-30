/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Correspondence

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
- `AlgebraicGeometry.ProEtale.WeilComplex.stalkFrobenius`: the geometric-stalk Frobenius
  `F_{x,m} = (φ_m)_x̄` at a point fixed by `Φ_m`.
- `AlgebraicGeometry.ProEtale.relativeFrobenius`: the relative Frobenius `r_m` of a
  morphism compatible with the Frobenius morphisms of its source and target.
- `AlgebraicGeometry.ProEtale.GeometricOperations.lowerShriekExchange`: the compact-support
  exchange `Lg_Y^* Rf_! ⟶ Rf_! Lg_X^*` of a commutative square with proper gap map.
- `AlgebraicGeometry.ProEtale.WeilComplex.lowerShriekPush`: the `!`-pushforward of a Weil
  complex.

## Main results

- `AlgebraicGeometry.ProEtale.isFinite_relativeFrobenius`,
  `AlgebraicGeometry.ProEtale.isUniversalHomeomorphism_relativeFrobenius`: the relative
  Frobenius is a finite universal homeomorphism.
- `AlgebraicGeometry.ProEtale.isEquivalence_leftDerivedUpperStar`,
  `AlgebraicGeometry.ProEtale.ctf_leftDerivedUpperStar_obj_iff`: topological invariance of
  the derived pro-étale category along a finite universal homeomorphism.

## Implementation notes

The `q^m`-power Frobenius of a scheme is not formalised anywhere in Mathlib or in this
project, so `AlgebraicGeometry.ProEtale.WeilComplex` carries it as data: an `s`-morphism
`Φ₁ : X ⟶ X`. The properties of it that the trace formula uses — being finite and a
universal homeomorphism — appear as hypotheses where they are needed. The `coeff` field is
a plain morphism rather than an isomorphism, so that a `WeilComplex` covers both a Weil
datum (add `IsIso W.coeff`) and the arbitrary *Frobenius coefficient morphism* that the
coefficient continuation of the argument needs.

`isUniversalHomeomorphism_relativeFrobenius` is not proved because the cancellation lemma
it needs — if `g ≫ f` and `f` are universal homeomorphisms then so is `g` — is missing;
the corresponding cancellation for finite morphisms is `AlgebraicGeometry.IsFinite.of_comp`
and makes `isFinite_relativeFrobenius` a theorem.

`isEquivalence_leftDerivedUpperStar` is stated on the whole unbounded `D(Y, A) ⥤ D(X, A)`,
whereas the blueprint states topological invariance on `Dᵇctf`; the generalisation is the
expected one on the pro-étale site, and `ctf_leftDerivedUpperStar_obj_iff` restricts it
back to the coefficient stage.

`WeilComplex.graph` takes the package `G` only for the identification
`GeometricOperations.upperShriekIdIso : 𝟭 ≅ (𝟙 X)^!`, which comes from the field
`lowerShriekId : R(𝟙 X)_! ≅ 𝟭`. Constructing `R(𝟙 X)_! ≅ 𝟭` from the trivial
compactification and the lower-star API would remove that field, and `graph` would no longer
depend on `G`.

`GeometricOperations.lowerShriekExchange`, and hence the coefficient map of
`WeilComplex.lowerShriekPush`, uses the fields `baseChange`, `properComparison` and
`lowerShriekComp` at non-identity morphisms. These are not pinned to the canonical maps nor
tied to each other (see `WeilConjectures.SixFunctors.ProEtale.TraceFormula.Defs`), so
rescaling `properComparison r` rescales the Frobenius coefficient of `Rf_! K`. Statements
about traces of Frobenius on `Rf_! K` need those coherence axioms first.
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
      (leftDerivedUpperStarCongr A W.frobeniusIterate_one).hom.app W.obj ≫ W.coeff :=
  sorry

/-- The iterates of an invertible Frobenius coefficient morphism are invertible. -/
instance isIso_coeffIterate [IsIso W.coeff] (m : ℕ) : IsIso (W.coeffIterate m) := by
  induction m with
  | zero => rw [coeffIterate_zero]; infer_instance
  | succ n ih => rw [coeffIterate_succ]; infer_instance

section Graph

variable [DerivedBraiding A]

/-- The coefficient map of the graph correspondence
`AlgebraicGeometry.ProEtale.WeilComplex.graph`: the iterate `φ_m` read through the
comparison `K ≃ 𝟙^! K`. -/
noncomputable def graphCoeff (G : GeometricOperations A s) (m : ℕ) :
    ((upperStar A (W.frobeniusIterate m)).leftDerivedFunctor).obj W.obj ⟶
      (rightDerivedUpperShriek A (𝟙 X)).obj W.obj :=
  W.coeffIterate m ≫ (G.upperShriekIdIso X).hom.app W.obj

/-- The graph correspondence `c_m = (id_X, Φ_m)` of a Weil complex, with coefficient map
`φ_m`. Its ordinary-pullback leg is `Φ_m` and its exceptional leg is the identity
(part of blueprint `sk-d-weil`). -/
noncomputable def graph (G : GeometricOperations A s) (m : ℕ) :
    Correspondence aX aX W.obj W.obj where
  supp := X
  str := aX
  fst := 𝟙 X
  snd := W.frobeniusIterate m
  fst_comp := Category.id_comp aX
  snd_comp := W.frobeniusIterate_comp m
  coeff := W.graphCoeff G m

/-- The structure morphism of the graph `W.graph G m` is `aX`, so it admits a
compactification when `aX` does. -/
instance hasCompactification_graph_str [HasCompactification aX] (G : GeometricOperations A s)
    (m : ℕ) : HasCompactification (W.graph G m).str :=
  inferInstanceAs (HasCompactification aX)

/-- The support map `(𝟙, Φ_m) : X ⟶ X ×_s X` of the graph `W.graph G m` is the graph
`X ⟶ X ×_s X` of `Φ_m`, a section of the first projection, followed by the identification
of `X ×_{Φ_m ≫ a_X, s, a_X} X` with `X ×_s X` along `Φ_m ≫ a_X = a_X`. -/
lemma graph_toProd_eq (G : GeometricOperations A s) (m : ℕ) :
    (W.graph G m).toProd =
      pullback.lift (𝟙 X) (W.frobeniusIterate m) (Category.id_comp (W.frobeniusIterate m ≫ aX)) ≫
        (pullback.congrHom (W.frobeniusIterate_comp m) rfl).hom := by
  apply pullback.hom_ext <;> simp [Correspondence.toProd, graph]

/-- The support map `(𝟙, Φ_m) : X ⟶ X ×_s X` of the graph `W.graph G m` is a section of the
first projection, hence a closed immersion when `aX` is separated. -/
instance isClosedImmersion_graph_toProd [IsSeparated aX] (G : GeometricOperations A s)
    (m : ℕ) : IsClosedImmersion (W.graph G m).toProd := by
  rw [graph_toProd_eq]
  -- instance search does not find this factor inside the composite, only when it is stated
  -- on its own
  have : IsClosedImmersion
      (pullback.lift (𝟙 X) (W.frobeniusIterate m) (Category.id_comp (W.frobeniusIterate m ≫ aX))) :=
    inferInstance
  infer_instance

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
      F ^ m :=
  sorry

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
`p_m = pullback.snd` (blueprint: `sk-d-relative-frob`). -/
noncomputable def relativeFrobenius (f : X ⟶ Y) (frobX : X ⟶ X) (frobY : Y ⟶ Y)
    (h : f ≫ frobY = frobX ≫ f) : X ⟶ pullback frobY f :=
  pullback.lift f frobX h

@[simp]
lemma relativeFrobenius_comp_snd (f : X ⟶ Y) (frobX : X ⟶ X) (frobY : Y ⟶ Y)
    (h : f ≫ frobY = frobX ≫ f) :
    relativeFrobenius f frobX frobY h ≫ pullback.snd frobY f = frobX :=
  pullback.lift_snd _ _ _

@[simp]
lemma relativeFrobenius_comp_fst (f : X ⟶ Y) (frobX : X ⟶ X) (frobY : Y ⟶ Y)
    (h : f ≫ frobY = frobX ≫ f) :
    relativeFrobenius f frobX frobY h ≫ pullback.fst frobY f = f :=
  pullback.lift_fst _ _ _

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
finite universal homeomorphisms is a universal homeomorphism
(blueprint: `sk-i-relative-frob`). -/
instance isUniversalHomeomorphism_relativeFrobenius (f : X ⟶ Y) (frobX : X ⟶ X)
    (frobY : Y ⟶ Y) (h : f ≫ frobY = frobX ≫ f) [IsFinite frobX] [IsFinite frobY]
    [IsUniversalHomeomorphism frobX] [IsUniversalHomeomorphism frobY] :
    IsUniversalHomeomorphism (relativeFrobenius f frobX frobY h) :=
  sorry

/-- Topological invariance: for a finite universal homeomorphism `r : X ⟶ Y`, pullback is
an equivalence `Lr^* : D(Y, A) ≌ D(X, A)`, with inverse `Rr_* = Rr_!` and invertible unit
and counit. Reduction of a scheme is a finite universal homeomorphism, so the statement
covers it (blueprint: `sk-i-topology`). -/
instance isEquivalence_leftDerivedUpperStar (r : X ⟶ Y) [IsFinite r]
    [IsUniversalHomeomorphism r] : ((upperStar A r).leftDerivedFunctor).IsEquivalence :=
  sorry

/-- Topological invariance preserves the coefficient stage: `Lr^*` restricts to an
equivalence `Dᵇctf(Y, A) ≃ Dᵇctf(X, A)` along a finite universal homeomorphism
(blueprint: `sk-i-topology`). -/
theorem ctf_leftDerivedUpperStar_obj_iff (G : GeometricCoefficients A) (r : X ⟶ Y)
    [IsFinite r] [IsUniversalHomeomorphism r]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    G.ctf X (((upperStar A r).leftDerivedFunctor).obj K) ↔ G.ctf Y K :=
  sorry

section

variable [DerivedBraiding A]

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
    ──lowerShriekComp r f' ≪≫ lowerShriekCongr──▶ Rf_! Lr^* Lp^* K
    ──Rf_!(leftDerivedUpperStarComp r p ≪≫ leftDerivedUpperStarCongr)──▶ Rf_! Lg_X^* K.
```

For the Frobenius square of a Weil complex this is the Weil comparison `θ_{f,m}` with
`g_X = Φ_{X,m}`, `g_Y = Φ_{Y,m}` and `r = r_m`, and it is invertible when `r` is a finite
universal homeomorphism (`isIso_lowerShriekExchange`) (blueprint: `sk-d-weil-push`). -/
noncomputable def lowerShriekExchange (G : GeometricOperations A s) (f : X ⟶ Y)
    [HasCompactification f] (gX : X ⟶ X) (gY : Y ⟶ Y) (h : f ≫ gY = gX ≫ f)
    [IsProper (relativeFrobenius f gX gY h)] :
    rightDerivedLowerShriek A f ⋙ (upperStar A gY).leftDerivedFunctor ⟶
      (upperStar A gX).leftDerivedFunctor ⋙ rightDerivedLowerShriek A f :=
  let f' := pullback.fst gY f
  let p := pullback.snd gY f
  let sq : IsPullback p f' f gY := (IsPullback.of_hasPullback gY f).flip
  let r := relativeFrobenius f gX gY h
  have : HasCompactification f' := HasCompactification.of_isPullback sq
  have : HasCompactification (r ≫ f') := by
    rw [relativeFrobenius_comp_fst]
    infer_instance
  (G.baseChange sq).hom ≫
    Functor.whiskerRight (Functor.whiskerLeft (upperStar A p).leftDerivedFunctor
      ((derivedUpperStarLowerStarAdjunction A r).unit ≫
        Functor.whiskerLeft (upperStar A r).leftDerivedFunctor (G.properComparison r).inv))
      (rightDerivedLowerShriek A f') ≫
    Functor.whiskerLeft ((upperStar A p).leftDerivedFunctor ⋙ (upperStar A r).leftDerivedFunctor)
      (G.lowerShriekComp r f' ≪≫ lowerShriekCongr (relativeFrobenius_comp_fst f gX gY h)).hom ≫
    Functor.whiskerRight ((leftDerivedUpperStarComp A r p).symm ≪≫
      leftDerivedUpperStarCongr A (relativeFrobenius_comp_snd f gX gY h)).hom
      (rightDerivedLowerShriek A f)

/-- Topological invariance makes the compact-support exchange invertible when the gap map is
a finite universal homeomorphism: then the unit of `Lr^* ⊣ Rr_*` is an isomorphism
(blueprint: `sk-i-topology`). -/
instance isIso_lowerShriekExchange (G : GeometricOperations A s) (f : X ⟶ Y)
    [HasCompactification f] (gX : X ⟶ X) (gY : Y ⟶ Y) (h : f ≫ gY = gX ≫ f)
    [IsFinite (relativeFrobenius f gX gY h)]
    [IsUniversalHomeomorphism (relativeFrobenius f gX gY h)] :
    IsIso (G.lowerShriekExchange f gX gY h) :=
  sorry

end GeometricOperations

/-- The coefficient map of `AlgebraicGeometry.ProEtale.WeilComplex.lowerShriekPush`: the
composite `ψ = Rf_! φ ∘ θ_{f,1}` of the compact-support exchange
`θ_{f,1} : LΦ_Y^* Rf_! K ⟶ Rf_! LΦ_X^* K` (`GeometricOperations.lowerShriekExchange` for the
square `f ≫ Φ_Y = Φ_X ≫ f`) with `Rf_! φ`. Only the case `m = 1` is constructed here. -/
noncomputable def WeilComplex.lowerShriekPushCoeff {aX : X ⟶ s} (W : WeilComplex (A := A) aX)
    (G : GeometricOperations A s) (f : X ⟶ Y) [HasCompactification f] (frobY : Y ⟶ Y)
    (h : f ≫ frobY = W.frobenius ≫ f) [IsProper (relativeFrobenius f W.frobenius frobY h)] :
    ((upperStar A frobY).leftDerivedFunctor).obj ((rightDerivedLowerShriek A f).obj W.obj) ⟶
      (rightDerivedLowerShriek A f).obj W.obj :=
  (G.lowerShriekExchange f W.frobenius frobY h).app W.obj ≫
    (rightDerivedLowerShriek A f).map W.coeff

/-- The `!`-pushforward of a Weil complex `(K, φ)` along `f : X ⟶ Y` compatible with the
Frobenius morphisms: the Weil complex `L = Rf_! K` on `Y` with coefficient map
`ψ = Rf_! φ ∘ θ_{f,1}` (blueprint: `sk-d-weil-push`). -/
noncomputable def WeilComplex.lowerShriekPush {aX : X ⟶ s} {aY : Y ⟶ s}
    (W : WeilComplex (A := A) aX) (G : GeometricOperations A s) (f : X ⟶ Y)
    [HasCompactification f] (frobY : Y ⟶ Y) (hY : frobY ≫ aY = aY)
    (h : f ≫ frobY = W.frobenius ≫ f) [IsProper (relativeFrobenius f W.frobenius frobY h)] :
    WeilComplex (A := A) aY where
  frobenius := frobY
  frobenius_comp := hY
  obj := (rightDerivedLowerShriek A f).obj W.obj
  coeff := W.lowerShriekPushCoeff G f frobY h

/-- The `!`-pushforward of a Weil datum is a Weil datum: when the relative Frobenius is a
finite universal homeomorphism, `θ_{f,1}` is invertible, so `ψ = Rf_! φ ∘ θ_{f,1}` is
invertible whenever `φ` is (blueprint: `sk-d-weil-push`). -/
instance WeilComplex.isIso_lowerShriekPush_coeff {aX : X ⟶ s} {aY : Y ⟶ s}
    (W : WeilComplex (A := A) aX) (G : GeometricOperations A s) (f : X ⟶ Y)
    [HasCompactification f] (frobY : Y ⟶ Y) (hY : frobY ≫ aY = aY)
    (h : f ≫ frobY = W.frobenius ≫ f) [IsFinite (relativeFrobenius f W.frobenius frobY h)]
    [IsUniversalHomeomorphism (relativeFrobenius f W.frobenius frobY h)] [IsIso W.coeff] :
    IsIso (W.lowerShriekPush G f frobY hY h).coeff := by
  dsimp [lowerShriekPush, lowerShriekPushCoeff]
  infer_instance

end

end AlgebraicGeometry.ProEtale
