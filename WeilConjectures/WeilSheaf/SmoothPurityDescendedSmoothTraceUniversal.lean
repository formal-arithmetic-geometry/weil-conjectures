/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityDescendedTraceEquivariance

/-!
# Universality of the descended smooth trace (A1', the remaining input)

For `f : X ⟶ Y` smooth separated of pure relative dimension `d` over the finite field `k₀`, the
descended smooth trace `Rf₀! ℚ̄_ℓ(d)[2d] ⟶ ℚ̄_ℓ` of Weil complexes
(`AlgebraicGeometry.WeilComplex.descendedSmoothTrace`) is universal on the geometric fibre
(`AlgebraicGeometry.WeilComplex.DescendedSmoothTraceUniversal`):
`AlgebraicGeometry.WeilComplex.descendedSmoothTraceUniversal`, stated with `sorry`.

The statement does not depend on the Tate encoding `α`: changing `α` precomposes the trace with
an isomorphism of its source. Its underlying geometric trace is the pullback along
`X̄ ⟶ X`, `Ȳ ⟶ Y` of the finite-field trace `Tr_f = counit ∘ Rf_!(γ_f)`, read through the
compact-support exchange `boundedConstructibleLowerShriekGeometricFiberWeilIso`. By
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_smoothUnitBaseChange_iff` this pulled-back trace
is universal iff the exceptional base change map at the unit
`AlgebraicGeometry.ProEtale.CondensedRing.smoothUnitBaseChange` is invertible, for `bc` the
`Dᵇc` part of that exchange. So the global exchange `Ex` of the gluing argument must be that
`Dᵇc` part (two exchanges for the same `f` cannot be compared).

With it, the statement of `exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso` needs
only the Tate encoding `α`
(`WeilComplex.exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_tateEncoding`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  {d : ℕ}

/-- **A1': the descended smooth trace is universal** (blueprint `sk-prop-sp-purity-bc` across
the field extension `k₀ ⟶ k̄`): for `f` smooth of pure relative dimension `d`, composing with
the underlying geometric trace of `descendedSmoothTrace f α` identifies
`Hom(For K[n], ℚ̄_ℓ(d)[2d])` with `Hom(Rf̄_! For K[n], ℚ̄_ℓ)`. Equivalently, the exceptional base
change map at the unit along `k₀ ⟶ k̄` is invertible, for the compact-support exchange
`boundedConstructibleLowerShriekGeometricFiberWeilIso`. -/
theorem descendedSmoothTraceUniversal [SmoothOfRelativeDimension d f]
    (α : TateEncoding (k₀ := k₀) (l := l) (X := X) d) :
    DescendedSmoothTraceUniversal f α :=
  sorry

variable [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] [HasUpperShriek k₀ l f]

/-- The statement of `exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso` from the
Tate encoding `α` alone (A3), through the universality of the descended trace (A1'). -/
theorem exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_tateEncoding
    [SmoothOfRelativeDimension d f] (α : TateEncoding (k₀ := k₀) (l := l) (X := X) d) :
    ∃ g : forget.obj ((upperShriek f).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))) ≅
      forget.obj (((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧),
      (Endofunctor.IsoAlgebra.derivedStrIso _).hom.app
          ((upperShriek f).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))).obj ≫
          g.hom =
        (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory.map g.hom ≫
          (Endofunctor.IsoAlgebra.derivedStrIso _).hom.app (((tateTwist k₀ l X d).obj
            (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧).obj :=
  exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_descendedTrace f α
    (descendedSmoothTraceUniversal f α)

end AlgebraicGeometry.WeilComplex
