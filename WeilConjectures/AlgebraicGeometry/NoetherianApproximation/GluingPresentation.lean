/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.SectionSubrings

/-!
# Finite affine gluing presentations and their finite-type stages

Let `S` be a quasi-compact quasi-separated scheme. A *finite affine gluing presentation* of `S`
(`AlgebraicGeometry.Scheme.FiniteAffineGluingPresentation`) consists of a finite affine open
cover `S = ⋃ₐ Uₐ` together with, for every pair of charts, finitely many sections
`f a b r ∈ Γ(S, Uₐ)` and `g a b r ∈ Γ(S, U_b)` with `D(f a b r) = D(g a b r)` whose basic opens
cover `Uₐ ⊓ U_b`.

A *stage* of such a presentation (`AlgebraicGeometry.Scheme.FiniteAffineGluingPresentation.Stage`)
is a family of finitely generated subrings `Aₐ ⊆ Γ(S, Uₐ)` containing the basic-open elements
and satisfying finitely many gluing conditions; the spectra `Spec Aₐ` then glue along the basic
opens of the `f a b r` to a scheme of finite type over `ℤ`.

## Main results

- `AlgebraicGeometry.Scheme.localizationSubring_range_appLE`: for `p : S ⟶ X` and an affine open
  `V` of `X`, the localization subring of the image of `Γ(X, V)` at (the image of) `s` is the
  image of `Γ(X, D(s))`.
- `AlgebraicGeometry.Scheme.FiniteAffineGluingPresentation.compactSpace`,
  `AlgebraicGeometry.Scheme.FiniteAffineGluingPresentation.quasiSeparatedSpace`: a scheme with a
  finite affine gluing presentation is quasi-compact and quasi-separated.
- `AlgebraicGeometry.Scheme.FiniteAffineGluingPresentation.witnesses`: finitely many sections of
  each chart such that every family of subrings containing them satisfies the unit conditions.
- `AlgebraicGeometry.Scheme.FiniteAffineGluingPresentation.exists_stage_of_model`: the images of
  the sections over affine opens of a scheme locally of finite type over `ℤ` through which the
  presentation factors form a stage.
- `AlgebraicGeometry.Scheme.FiniteAffineGluingPresentation.exists_stage_superset`: cofinality;
  any finitely many sections lie in the coefficient subrings of some stage. The proof uses a
  Noetherian approximation of `S` (`AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`).
- The stages form a join-semilattice (componentwise supremum); in particular they are directed,
  and they are nonempty.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

variable {S}

namespace FiniteAffineGluingPresentation

attribute [instance] fintype_ι fintype_κ

variable (G : S.FiniteAffineGluingPresentation)

end FiniteAffineGluingPresentation

/-! ### Localization subrings -/

namespace FiniteAffineGluingPresentation

variable (G : S.FiniteAffineGluingPresentation)

/-! ### Witnesses of the unit conditions -/

@[simp] lemma Stage.mk'_A (A) (fg) (hA) (h) : (Stage.mk' G A fg hA h).A = A := rfl

end FiniteAffineGluingPresentation

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.FiniteAffineGluingPresentation

variable {S : Scheme.{u}} (G : S.FiniteAffineGluingPresentation)

end AlgebraicGeometry.Scheme.FiniteAffineGluingPresentation

namespace AlgebraicGeometry.Scheme.FiniteAffineGluingPresentation

variable {S : Scheme.{u}} {G : S.FiniteAffineGluingPresentation}

end AlgebraicGeometry.Scheme.FiniteAffineGluingPresentation
