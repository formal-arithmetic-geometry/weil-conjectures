/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
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
- `AlgebraicGeometry.ProEtale.relativeFrobenius`: the relative Frobenius `r_m` of a
  morphism compatible with the Frobenius morphisms of its source and target.
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

`coeffIterate` and the coefficient maps of `graph` and of `lowerShriekPush` are composites
of comparison maps that the package only postulates, so they are `opaque` for the reason
explained in `WeilConjectures.SixFunctors.ProEtale.TraceFormula.Correspondence`.

`isUniversalHomeomorphism_relativeFrobenius` is not proved because the cancellation lemma
it needs — if `g ≫ f` and `f` are universal homeomorphisms then so is `g` — is missing;
the corresponding cancellation for finite morphisms is `AlgebraicGeometry.IsFinite.of_comp`
and makes `isFinite_relativeFrobenius` a theorem.

`isEquivalence_leftDerivedUpperStar` is stated on the whole unbounded `D(Y, A) ⥤ D(X, A)`,
whereas the blueprint states topological invariance on `Dᵇctf`; the generalisation is the
expected one on the pro-étale site, and `ctf_leftDerivedUpperStar_obj_iff` restricts it
back to the coefficient stage.
-/

@[expose] public section

universe u' u

set_option linter.unusedVariables false

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [DerivedBraiding A] {s X Y : Scheme.{u}}

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

omit [DerivedBraiding A] in
@[simp]
lemma frobeniusIterate_zero : W.frobeniusIterate 0 = 𝟙 X := rfl

omit [DerivedBraiding A] in
@[simp]
lemma frobeniusIterate_succ (m : ℕ) :
    W.frobeniusIterate (m + 1) = W.frobenius ≫ W.frobeniusIterate m :=
  (pow_succ (M := End X) W.frobenius m).trans (End.mul_def _ _)

omit [DerivedBraiding A] in
/-- Every iterate of the Frobenius is a morphism over the base. -/
@[simp]
lemma frobeniusIterate_comp (m : ℕ) : W.frobeniusIterate m ≫ aX = aX := by
  induction m with
  | zero => simp
  | succ n ih => rw [frobeniusIterate_succ, Category.assoc, ih, W.frobenius_comp]

/-- The iterate `φ_m : Φ_m^* K ⟶ K` of the Frobenius coefficient morphism, obtained by
composing the pulled back copies of `φ` along the composition isomorphisms for `Φ^*`
(part of blueprint `sk-d-weil`). -/
noncomputable opaque coeffIterate (m : ℕ) :
    ((upperStar A (W.frobeniusIterate m)).leftDerivedFunctor).obj W.obj ⟶ W.obj := 0

/-- The coefficient map of the graph correspondence
`AlgebraicGeometry.ProEtale.WeilComplex.graph`: the iterate `φ_m` read through the
comparison `K ≃ 𝟙^! K`. -/
noncomputable opaque graphCoeff (m : ℕ) :
    ((upperStar A (W.frobeniusIterate m)).leftDerivedFunctor).obj W.obj ⟶
      (rightDerivedUpperShriek A (𝟙 X)).obj W.obj := 0

/-- The graph correspondence `c_m = (id_X, Φ_m)` of a Weil complex, with coefficient map
`φ_m`. Its ordinary-pullback leg is `Φ_m` and its exceptional leg is the identity
(part of blueprint `sk-d-weil`). -/
noncomputable def graph (m : ℕ) : Correspondence aX aX W.obj W.obj where
  supp := X
  str := aX
  fst := 𝟙 X
  snd := W.frobeniusIterate m
  fst_comp := Category.id_comp aX
  snd_comp := W.frobeniusIterate_comp m
  coeff := W.graphCoeff m

/-- The structure morphism of the graph `W.graph m` is `aX`, so it admits a compactification
when `aX` does. -/
instance hasCompactification_graph_str [HasCompactification aX] (m : ℕ) :
    HasCompactification (W.graph m).str :=
  inferInstanceAs (HasCompactification aX)

omit [DerivedBraiding A] in
/-- The support map `(𝟙, Φ_m) : X ⟶ X ×_s X` of the graph `W.graph m` is a section of the
first projection, hence a closed immersion when `aX` is separated. -/
instance isClosedImmersion_graph_toProd [IsSeparated aX] (m : ℕ) :
    IsClosedImmersion (W.graph m).toProd := by
  have : (W.graph m).toProd = pullback.lift (𝟙 X) (W.frobeniusIterate m) (Category.id_comp _) ≫
      (pullback.congrHom (W.frobeniusIterate_comp m) rfl).hom := by
    apply pullback.hom_ext <;> simp [Correspondence.toProd, graph]
  rw [this]
  have : IsClosedImmersion
      (pullback.lift (𝟙 X) (W.frobeniusIterate m) (Category.id_comp (W.frobeniusIterate m ≫ aX))) :=
    inferInstance
  infer_instance

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

/-- The coefficient map of `AlgebraicGeometry.ProEtale.WeilComplex.lowerShriekPush`: the
composite `ψ = Rf_! φ ∘ θ_{f,1}` of the Weil comparison

`θ_{f,m} : Φ_{Y,m}^* Rf_! K ≃ Rf'_{m!} p_m^* K ⟶ Rf'_{m!} Rr_{m!} r_m^* p_m^* K ≃
  Rf_! Φ_{X,m}^* K`,

built from Cartesian `!`-base change for `X'_m` and topological invariance for the relative
Frobenius `r_m`, with `Rf_! φ`. -/
noncomputable opaque WeilComplex.lowerShriekPushCoeff {aX : X ⟶ s} (W : WeilComplex (A := A) aX)
    (f : X ⟶ Y) [HasCompactification f] (frobY : Y ⟶ Y) :
    ((upperStar A frobY).leftDerivedFunctor).obj ((rightDerivedLowerShriek A f).obj W.obj) ⟶
      (rightDerivedLowerShriek A f).obj W.obj := 0

/-- The `!`-pushforward of a Weil complex `(K, φ)` along `f : X ⟶ Y` compatible with the
Frobenius morphisms: the Weil complex `L = Rf_! K` on `Y` with coefficient map
`ψ = Rf_! φ ∘ θ_{f,1}` (blueprint: `sk-d-weil-push`). -/
noncomputable def WeilComplex.lowerShriekPush {aX : X ⟶ s} {aY : Y ⟶ s}
    (W : WeilComplex (A := A) aX) (f : X ⟶ Y) [HasCompactification f] (frobY : Y ⟶ Y)
    (hY : frobY ≫ aY = aY) (h : f ≫ frobY = W.frobenius ≫ f) : WeilComplex (A := A) aY where
  frobenius := frobY
  frobenius_comp := hY
  obj := (rightDerivedLowerShriek A f).obj W.obj
  coeff := W.lowerShriekPushCoeff f frobY

end AlgebraicGeometry.ProEtale
