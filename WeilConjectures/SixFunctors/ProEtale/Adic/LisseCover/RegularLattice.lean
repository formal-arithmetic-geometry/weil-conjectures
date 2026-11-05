/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.CompactOpenLattice
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedFiniteEtale
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedPullback

/-!
# Lattices of lisse sheaves on regular schemes

Let `T` be a regular Noetherian scheme, `f : V ⟶ T` a single-morphism pro-étale cover and
`γ : V ×_T V → GL_n(E)` a cocycle acting on the lattices of `Eⁿ` by a descent cocycle (the
transition cocycle of a trivialisation of a lisse sheaf,
`AlgebraicGeometry.ProEtale.AdicSheaf.isDescentCocycle_smul_compactOpenLattice`). Then `γ` has a
twisted section with values in the lattices
(`AlgebraicGeometry.exists_isTwistedSection_compactOpenLattice`): a lisse sheaf on a regular
scheme has a lattice (blueprint `thm-lisse-qlbar-representations` (4), used in
`prop-zl-smooth-proper-relative-purity`).

On a connected `T`, the orbit of a lattice is contained in a finite invariant set of lattices
(`AlgebraicGeometry.exists_finite_invariant_subset`, Bhatt–Scholze, Lemma 7.4.10), whose sum is an
invariant lattice. In general the sections over the finitely many connected components glue.
-/

@[expose] public section

universe u

open CategoryTheory Limits PadicAlgCl

namespace AlgebraicGeometry

variable {l : ℕ} [Fact l.Prime] {E : IntermediateField ℚ_[l] (PadicAlgCl l)}
  [FiniteDimensional ℚ_[l] E] {n : ℕ} {T V : Scheme.{u}}

end AlgebraicGeometry
