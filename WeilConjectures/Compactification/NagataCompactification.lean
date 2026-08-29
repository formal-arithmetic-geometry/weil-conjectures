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

/-- **Nagata compactification**: a separated, quasi-compact morphism `f : X ⟶ Y` locally of
finite type over a quasi-compact quasi-separated scheme `Y` factors as an open immersion
followed by a proper morphism.

The morphism `f` is written as a closed immersion followed by a morphism of finite
presentation by the finite-presentation envelope (Stacks Tag 01ZJ), the latter is compactified
by `AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation` and the
compactification is cut back to the closed subscheme.
(blueprint: `def:nagata-final-compactification`, `thm:nagata-compactification`) -/
noncomputable def NagataCompactification [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] :
    Compactification f :=
  have : HasCompactification f := by
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    obtain ⟨X', i, f', hi, hf'fp, hf'qc, hf'sep, hcomm⟩ :=
      f.exists_isClosedImmersion_isSeparated_locallyOfFinitePresentation
    haveI := hi; haveI := hf'fp; haveI := hf'qc; haveI := hf'sep
    haveI : HasCompactification f' := nagataCompactification_of_locallyOfFinitePresentation f'
    rw [← hcomm]
    exact HasCompactification.of_isClosedImmersion i f'
  HasCompactification.compactification f

instance [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] : HasCompactification f :=
  (NagataCompactification f).hasCompactification

end AlgebraicGeometry
