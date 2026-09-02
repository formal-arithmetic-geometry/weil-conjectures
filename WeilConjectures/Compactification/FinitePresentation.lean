/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Compactification.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!

# Nagata compactification for a morphism of finite presentation

This file proves **Nagata's compactification theorem for a separated, quasi-compact morphism of
finite presentation over a quasi-compact quasi-separated base**
(`AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation`): such a morphism
factors as an open immersion followed by a proper morphism.

The Noetherian hypothesis on the base of
`AlgebraicGeometry.nagataCompactification_of_isNoetherian` is removed by absolute Noetherian
approximation. Writing the qcqs base `S` as a cofiltered limit `S = lim Dᵢ` of Noetherian
stages with affine transition maps (Stacks Tag 01ZA,
`AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`), a separated, quasi-compact
morphism `f : X ⟶ S` of finite presentation descends to a morphism `p : Y ⟶ Dᵢ` with the same
three properties over one of the stages (Stacks Tag 01ZQ,
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`). The stage
`Dᵢ` is Noetherian, so `p` has a compactification; base changing it back along `S ⟶ Dᵢ`
(`AlgebraicGeometry.HasCompactification.of_isPullback`) compactifies `f`.

The blueprint's compactification datum for `Rf_!` asks for more than mere existence: the
proper structure morphism `g` of the compactification must itself be *locally of finite
presentation*. Over a locally Noetherian base this is automatic, since `g` is proper, hence
locally of finite type (`AlgebraicGeometry.Compactification.locallyOfFinitePresentation_g`).
Over a general quasi-compact quasi-separated base we re-run the approximation argument above
while carrying this extra property: the compactification produced over the Noetherian stage
`Dᵢ` is of finite presentation, and its structure morphism stays so after base change to `S`,
because `AlgebraicGeometry.LocallyOfFinitePresentation` is stable under base change.

## Main results

- `AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation`: a separated,
  quasi-compact morphism of finite presentation to a quasi-compact quasi-separated scheme
  admits a compactification.
- `AlgebraicGeometry.Compactification.locallyOfFinitePresentation_g`: over a locally
  Noetherian base, the structure morphism of any compactification is locally of finite
  presentation.
- `AlgebraicGeometry.exists_compactification_locallyOfFinitePresentation`: such a morphism
  admits a compactification whose structure morphism is locally of finite presentation.
- `AlgebraicGeometry.finitelyPresentedCompactification`: a choice of such a compactification.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Nagata compactification for a morphism of finite presentation** (blueprint:
`lemma:nagata-final-basechanged-compactification`).

The base is written as a cofiltered limit of Noetherian stages by absolute Noetherian
approximation, `f` is descended to one of the stages, compactified there by
`AlgebraicGeometry.nagataCompactification_of_isNoetherian` and the compactification is base
changed back to `S`. -/
theorem nagataCompactification_of_locallyOfFinitePresentation {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFinitePresentation f]
    [QuasiCompact f] : HasCompactification f := by
  obtain ⟨N⟩ := S.nonempty_noetherianApproximation
  obtain ⟨i, Y, p, hp₁, hp₂, hp₃, h, H⟩ :=
    Scheme.exists_isPullback_of_finitePresentation_of_isSeparated N.isLimit f
  have := hp₁; have := hp₂; have := hp₃
  have : HasCompactification p := nagataCompactification_of_isNoetherian p
  exact HasCompactification.of_isPullback H

/-- **Over a locally Noetherian base the structure morphism of a compactification is locally
of finite presentation.**

It is proper, hence locally of finite type, and over a locally Noetherian base locally of
finite type implies locally of finite presentation. -/
theorem Compactification.locallyOfFinitePresentation_g {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] (c : Compactification f) : LocallyOfFinitePresentation c.g :=
  inferInstance

/-- **A compactification whose structure morphism is of finite presentation** (blueprint:
`proper_base_change.tex`, §A43, `BA43-RAW-DATA`).

This is `AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation` with the
finite presentation of the structure morphism carried along: `f` is descended to a Noetherian
stage `Dᵢ` of an absolute Noetherian approximation of `S`, compactified there — where the
structure morphism is automatically locally of finite presentation by
`AlgebraicGeometry.Compactification.locallyOfFinitePresentation_g` — and the result is base
changed back to `S`, which preserves finite presentation. -/
theorem exists_compactification_locallyOfFinitePresentation {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [LocallyOfFinitePresentation f] [QuasiCompact f] [CompactSpace S]
    [QuasiSeparatedSpace S] :
    ∃ c : Compactification f, LocallyOfFinitePresentation c.g := by
  obtain ⟨N⟩ := S.nonempty_noetherianApproximation
  obtain ⟨i, Y, p, hp₁, hp₂, hp₃, h, H⟩ :=
    Scheme.exists_isPullback_of_finitePresentation_of_isSeparated N.isLimit f
  have := hp₁; have := hp₂; have := hp₃
  obtain ⟨c⟩ := (nagataCompactification_of_isNoetherian p).nonempty_compactification
  have : LocallyOfFinitePresentation c.g := c.locallyOfFinitePresentation_g
  refine ⟨Compactification.ofIsPullback H c, ?_⟩
  rw [Compactification.ofIsPullback_g]
  infer_instance

/-- A choice of compactification with structure morphism locally of finite presentation, for a
separated, quasi-compact morphism of finite presentation over a quasi-compact quasi-separated
base. Its defining property is
`AlgebraicGeometry.locallyOfFinitePresentation_finitelyPresentedCompactification_g`. -/
noncomputable def finitelyPresentedCompactification {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [LocallyOfFinitePresentation f] [QuasiCompact f] [CompactSpace S]
    [QuasiSeparatedSpace S] : Compactification f :=
  (exists_compactification_locallyOfFinitePresentation f).choose

/-- The structure morphism of
`AlgebraicGeometry.finitelyPresentedCompactification` is locally of finite presentation. -/
instance locallyOfFinitePresentation_finitelyPresentedCompactification_g {X S : Scheme.{u}}
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    LocallyOfFinitePresentation (finitelyPresentedCompactification f).g :=
  (exists_compactification_locallyOfFinitePresentation f).choose_spec

/-! ### Axiom census

The existence of a compactification with structure morphism of finite presentation is
unconditional: the check below is run by the build, so a `sorry` reappearing anywhere beneath
Nagata's theorem or absolute Noetherian approximation breaks compilation rather than going
unnoticed. -/

/--
info: 'AlgebraicGeometry.exists_compactification_locallyOfFinitePresentation' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.exists_compactification_locallyOfFinitePresentation

end AlgebraicGeometry
