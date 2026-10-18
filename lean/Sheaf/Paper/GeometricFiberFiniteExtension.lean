/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.Paper.FiniteExtensionProperBaseChange
import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
import Sheaf.Paper.PbcRationalCategory

/-! # Finite-extension geometric-fiber formula

Source: Weil-conjectures blueprint, `sec-proper-base-change`,
`sk-thm-properbasechange` (blueprint: cor-weil-pbc-geometric-fiber-finite-extension).
The raw rational category below is the category `Dbc(T,E)` of the statement: it has
integral bounded constructible complete objects and the scalar-localized Hom modules.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The chosen Cartesian square defining the geometric fibre of `f` at `ybar`.
Source: the fibre-product construction in the blueprint
(blueprint: cor-weil-pbc-geometric-fiber-finite-extension). -/
def geometricFiberSquare
    {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω]
    (ybar : Spec (.of Ω) ⟶ Y) :
    ChosenCartesianSquare (pullback.fst f ybar) (pullback.snd f ybar) f ybar :=
  { toCommSq := CommSq.mk (pullback.condition (f := f) (g := ybar))
    isoPullback := Iso.refl (pullback f ybar)
    hom_fst := Category.comp_id (pullback.fst f ybar)
    hom_snd := Category.comp_id (pullback.snd f ybar) }

/-- For a proper morphism, the rational proper-base-change exchange at a geometric
point is invertible. The four existential witnesses in the conclusion express the
restrictions of direct images and completed pullbacks to the raw rational categories.
Specializing the finite-extension theorem to `geometricFiberSquare` gives the displayed
map `L ybar^* R f_* K ⟶ R a_ybar,* L i_ybar^* K`.
Source: Weil-conjectures blueprint, `sec-proper-base-change`,
`sk-thm-properbasechange` (blueprint: cor-weil-pbc-geometric-fiber-finite-extension).
Proof:
1. Set `P = Spec Ω`, `X_ybar = pullback f ybar`, with projections `pullback.fst f ybar`
   and `pullback.snd f ybar`; the defining pullback equality makes `geometricFiberSquare`
   a Cartesian square with the identity chosen pullback isomorphism.
2. The hypotheses put all four schemes in the raw rational categories and satisfy the
   finite-extension proper-base-change theorem, including properness of the two vertical
   maps and the geometric-fibre dimension bound.
3. Apply `finiteExtension_properBaseChange` to this square. Its specified component is
   exactly the rational exchange displayed in the statement, so every component is an
   isomorphism.
-/
theorem geometricFiber_finiteExtension_properBaseChange
    (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (ybar : Spec (.of Ω) ⟶ Y)
    [IsNoetherian X] [IsNoetherian Y]
    [IsNoetherian (pullback f ybar)] [IsNoetherian (Spec (.of Ω))]
    (_dimX : ∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))
    (_dimY : ∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))
    (_dimFiber : ∃ n : ℕ,
      topologicalKrullDim (pullback f ybar : Scheme.{u}) ≤ (n : WithBot ℕ∞))
    (_dimPoint : ∃ n : ℕ,
      topologicalKrullDim (Spec (.of Ω) : Scheme.{u}) ≤ (n : WithBot ℕ∞))
    [IsProper f] [IsProper (pullback.snd f ybar)]
    (_hlX : IsUnit (l : Γ(X, ⊤)))
    (_hlY : IsUnit (l : Γ(Y, ⊤)))
    (_hlFiber : IsUnit (l : Γ(pullback f ybar, ⊤)))
    (_hlPoint : IsUnit (l : Γ(Spec (.of Ω), ⊤)))
    (e : ℕ)
    (_hFibres : ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω']
      (y : Spec (.of Ω') ⟶ Y),
      topologicalKrullDim (pullback f y : Scheme.{u}) ≤ (e : WithBot ℕ∞)) :
    ∃ (hRf : ∀ K : PbcBoundedConstructibleComplete X
        (pbcPadicCoefficientDatum l E),
        IsPbcBoundedConstructibleComplete Y l E
          (((pbcPadicCoefficientDatum l E).push f).obj K.obj))
      (hRa : ∀ K : PbcBoundedConstructibleComplete (pullback f ybar)
          (pbcPadicCoefficientDatum l E),
        IsPbcBoundedConstructibleComplete (Spec (.of Ω)) l E
          (((pbcPadicCoefficientDatum l E).push (pullback.snd f ybar)).obj K.obj))
      (hLy : ∀ K : PbcBoundedConstructibleComplete Y
          (pbcPadicCoefficientDatum l E),
        IsPbcBoundedConstructibleComplete (Spec (.of Ω)) l E
          (((pbcPadicCoefficientDatum l E).completedPull ybar).obj K.obj))
      (hLi : ∀ K : PbcBoundedConstructibleComplete X
          (pbcPadicCoefficientDatum l E),
        IsPbcBoundedConstructibleComplete (pullback f ybar) l E
          (((pbcPadicCoefficientDatum l E).completedPull (pullback.fst f ybar)).obj K.obj)),
      ∀ K : PbcRationalCategory X (pbcPadicCoefficientDatum l E)
          (Padic.coefficientExtensionUniformizer l E),
        IsIso (finiteExtensionRationalExchangeComponent l E
          (geometricFiberSquare f ybar) K
          (hLy ⟨((pbcPadicCoefficientDatum l E).push f).obj K.obj.obj, hRf K.obj⟩)
          (hRa ⟨((pbcPadicCoefficientDatum l E).completedPull
              (pullback.fst f ybar)).obj K.obj.obj, hLi K.obj⟩)) := by
  sorry

end AlgebraicGeometry.Scheme
