# ModuleCat.hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE

## Reason

Restore the quarantined Sheaf module without reintroducing the definitions and theorem
that now exist in the adopted upstream library. The rework row records a GlobalDimension
name collision. The original bridge is already proved verbatim in
WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension, and the current node
lem-weil-pbc-projective-resolution-ext-degree already attaches to that upstream declaration
following the reviewed A3 GlobalDimension retirement (20261020T144233-L-2257551).

Restore this import path as a public reexport of that source module. This is an actual
interface repair of the quarantined file: its duplicate theorem body and old direct imports
are replaced by the existing upstream theorem. Do not withdraw the absent quarantined
path, erase its archive, or change any upstream declaration. The bounded-resolution
construction, its splicing dependency, and every existing parent DAG edge remain needed
and preserved. No target statement or definition changes.

## Old

The quarantined module, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.RingTheory.GlobalDimension
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import WeilConjectures.RingTheory.ProjectiveResolutionSuccSplice

/-!
# Bounded projective resolutions and projective dimension

Mathlib defines projective dimension by Ext vanishing. This module constructs the
bounded projective resolution needed to compare it with the explicit resolution predicate.
Source: Stacks Project, Algebra, Lemma 065R.
-/

@[expose] public section
universe u v
open CategoryTheory
namespace ModuleCat
/-- The explicit bounded-resolution predicate agrees with Mathlib's projective-dimension
predicate. Unlike the Ext criteria already in Mathlib, the reverse implication constructs
an actual bounded projective resolution. Induct on the bound: at zero use the identity
resolution of a projective object; at a successor use Mathlib's dimension shifting for
the kernel of a projective epimorphism and augment its shorter resolution. Exactness,
projectivity and the support bound of the augmented complex give the required resolution.
The forward implication represents Ext classes by cocycles on the zero resolution terms
and applies Mathlib's `HasProjectiveDimensionLT.mk`.
Source: Stacks Project, Algebra, Lemma 065R, parts (1)--(3).
(blueprint: lem-weil-pbc-projective-resolution-ext-degree). -/
theorem hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE
    {R : Type u} [CommRing R] (X : ModuleCat.{max u v} R) (n : ℕ) :
    HasProjectiveResolutionLE X n ↔ HasProjectiveDimensionLE X n := by
  let := HasExt.standard (ModuleCat.{max u v} R)
  constructor
  · rintro ⟨P, hP⟩
    apply (hasProjectiveDimensionLT_iff X (n + 1)).mpr
    intro i hi Y a
    obtain ⟨f, _, rfl⟩ := P.extMk_surjective a (i + 1) rfl
    have hfzero : f = 0 := (hP i (by omega)).eq_of_src _ _
    simpa only [hfzero] using P.extMk_zero (i + 1) rfl
  · intro h
    induction n generalizing X with
    | zero =>
      have : Projective X := (projective_iff_hasProjectiveDimensionLE_zero X).mpr h
      refine ⟨ProjectiveResolution.self X, fun i hi ↦ ?_⟩
      exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
    | succ n ih =>
      let S := ShortComplex.mk _ _ (Limits.kernel.condition (Projective.π X))
      have hS : S.ShortExact := { exact := ShortComplex.exact_kernel (Projective.π X) }
      have hK : HasProjectiveDimensionLE S.X₁ n :=
        (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp h
      exact hasProjectiveResolutionLE_of_shortExact_projective_middle n S hS
        inferInstance (ih S.X₁ hK)
end ModuleCat
```

## New

The restored module, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension

/-!
# Bounded projective resolutions and projective dimension

The comparison between explicit bounded projective resolutions and Mathlib's projective
dimension is proved in the adopted source module, which this module reexports. Reusing that
module also keeps the bounded-resolution predicate and the splicing construction on the same
`WeilConjectures.RingTheory.GlobalDimension` definitions.

Source: Stacks Project, Algebra, Lemma 065R.
(blueprint: lem-weil-pbc-projective-resolution-ext-degree).
-/

@[expose] public section
```

The exported bridge has exactly the old name, universes, hypotheses and conclusion.
Its definition of HasProjectiveResolutionLE is now the same upstream definition that
the splicing construction uses. No alias or new public declaration is introduced.

## Users

The active-library downstream tool reports the item as unknown because it is quarantined.
Searching both lean/Sheaf and quarantine/Sheaf finds precisely the following direct
importers; neither has a current claim file. No consumer is edited in this packet.

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.BoundedProjectiveResolutionDimension | E2 | Restore quarantined path by publicly importing the already proved upstream bridge. |
| Sheaf.RingTheory.AuslanderBuchsbaum | unclaimed; quarantined | Import path restored; three .mp/.mpr bridge applications retain exactly their types. |
| Sheaf.RingTheory.UniformPerfectQuotientBound | unclaimed; quarantined | Import path restored; two .mp/.mpr bridge applications retain exactly their types. |
| Sheaf.Algebra.ProjectiveDimensionWellDefined | unclaimed | Already imports the upstream bridge directly; no change. |

A separate consumer probe compiles the exact universally quantified bridge signature
and both directions, importing both the Sheaf path and upstream path together. Both
original upstream proof modules were also compiled unchanged in the sandbox. The bridge
axiom check returns only propext, Classical.choice and Quot.sound. Quarantined consumers
are left to their own rework assignments; this delivery does not claim to repair their
other dependencies. The original archives and their node attachments are preserved.

## Status

landed 20261020T152957-L-2857871 2026-10-20 (merge of deliver/E2/Sheaf.RingTheory.BoundedProjectiveResolutionDimension)
