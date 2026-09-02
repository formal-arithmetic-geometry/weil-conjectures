/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.Constructions
public import WeilConjectures.Compactification.FinitePresentation

/-!

# Main Statements of Nagata Compactification

This file assembles **Nagata's compactification theorem** in its final form
(`AlgebraicGeometry.NagataCompactification`): a separated, quasi-compact morphism `f : X ⟶ Y`
locally of finite type over a quasi-compact quasi-separated base factors as an open immersion
followed by a proper morphism.

The assembly has three steps. The morphism `f` is only locally of finite *type*, while
`AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation` needs finite
*presentation*; the bridge is the finite-presentation envelope (Stacks Tag 01ZJ,
`AlgebraicGeometry.Scheme.Hom.exists_isClosedImmersion_isSeparated_locallyOfFinitePresentation`),
which writes `f` as `i ≫ f'` for a closed immersion `i : X ⟶ X'` and a separated, quasi-compact
`f' : X' ⟶ Y` of finite presentation. Compactifying `f'` and cutting back along `i` with
`AlgebraicGeometry.HasCompactification.of_isClosedImmersion` compactifies `f`.

## Main results

- `AlgebraicGeometry.NagataCompactification`: the compactification of a separated,
  quasi-compact morphism locally of finite type over a quasi-compact quasi-separated base.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Nagata compactification** (blueprint: `def:nagata-final-compactification`,
`thm:nagata-compactification`).

The morphism `f` is written as a closed immersion followed by a morphism of finite
presentation by the finite-presentation envelope (Stacks Tag 01ZJ), the latter is compactified
by `AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation` and the
compactification is cut back to the closed subscheme. -/
noncomputable def NagataCompactification [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] :
    Compactification f :=
  have : HasCompactification f := by
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    obtain ⟨X', i, f', hi, hf'fp, hf'qc, hf'sep, hcomm⟩ :=
      f.exists_isClosedImmersion_isSeparated_locallyOfFinitePresentation
    have := hi; have := hf'fp; have := hf'qc; have := hf'sep
    have : HasCompactification f' := nagataCompactification_of_locallyOfFinitePresentation f'
    rw [← hcomm]
    exact HasCompactification.of_isClosedImmersion i f'
  HasCompactification.compactification f

instance [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] : HasCompactification f :=
  (NagataCompactification f).hasCompactification

/-! ### Axiom census

Nagata's compactification theorem is unconditional: the checks below are run by the build, so a
`sorry` reappearing anywhere beneath the theorem or its two intermediate forms breaks compilation
rather than going unnoticed. -/

/--
info: 'AlgebraicGeometry.NagataCompactification' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.NagataCompactification

/--
info: 'AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation

/--
info: 'AlgebraicGeometry.nagataCompactification_of_isNoetherian' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.nagataCompactification_of_isNoetherian

end AlgebraicGeometry
