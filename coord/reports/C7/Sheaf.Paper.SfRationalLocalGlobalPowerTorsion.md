## What changed

Repair of the return at head `da5005885`: removed the inherited
`set_option warn.sorry false` line. The landing hole census treated the option's
`sorry` component as an unattributed hole at line 39. No warning suppression is
needed: the module contains no unfinished proof. The retained proof below is unchanged.
The fresh dry run required a change record for removal of that visible command;
`coord/changes/sf-rational-local-global-warning-option.md` records the exact command
change and all downstream modules. No downstream adaptation is needed.

Resumed verification on 2026-10-20: the repaired module compiles through `lcompile.py`
in 27.2 seconds with exit code 0 and no warnings. An initial compile timed out; a
profiled compile then succeeded in 54.3 seconds and the ordinary compile succeeded
in 27.2 seconds. Profiling found no persistent expensive definition to repair. A source comparison confirms
the theorem signature and every public import are unchanged, the module has no
hole tokens, and every line is at most 100 characters. The current downstream
check still lists exactly the three consumers recorded in the change record.

Proved `WeilConjectures.sfRationalLocalGlobalPowerTorsion` without changing its signature,
existing public declarations, or public imports. Added six proved private helpers:
`sfHomology_additive`, `sfScalarLocalization_power`,
`sfUniformizer_prime_factorization`, `sfPower_smul_zero_of_le`, `sfSheaf_map_zero_of_cover`, and
`sfModule_map_zero_of_cover`. Added proof imports of
`Mathlib.RingTheory.Localization.BaseChange` and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.

The tensor-localization zero criterion gives the local powers. Factor the prime as
`l = v * p^e`, with `v` a unit and `e > 0`, and take the finite supremum `M` of the
local exponents. Convert local annihilation to `l^M` annihilation, which is repeated
addition and hence is preserved by additive functors. Exact restriction commutes with
derived homology. Sheaf separatedness detects zero morphisms on the cover. Finally
cancel the unit factor inside the derived category and apply homology functoriality
to obtain the asserted uniformizer exponent `e * M`.

This explicitly handles arbitrary independent linear structures, independent scheme
and coefficient universes, unbounded cohomological degrees, and the empty covering
(`M = 0`). The proof does not assume coefficient-linearity of restriction or homology.
The existing node's proof, proof dependencies, and proof origin now follow this argument.

## Proved and sorry left

Closed 1 of 1 original holes: `WeilConjectures.sfRationalLocalGlobalPowerTorsion`
(node `lem-sf-rational-local-global-power-torsion`). Added 0 holes; split off 0 statements.
No `sorry` remains in the delivered module. All six new private helpers are proved.
Existing upstream theorem dependencies retain their own proof status; this delivery
adds no axiom or unproved declaration.

## No longer needed

Removed the proof import `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
Its node `lem-pur-site-restriction-module-adjunction-exact` is unnecessary for this
proof: the already imported `ringedOverFunctor_exactGeneral`, attached to
`def-weil-pbc-ringed-derived-restriction`, proves the exact restriction needed here.
The unused extension-by-zero and adjunction parts are never invoked.

The node `lem-sf-derived-homology-long-exact` is unnecessary: the proof uses the
exact-functor homology comparison, never a distinguished triangle or long exact sequence.
Its existing public Mathlib import is retained to preserve the public interface.

The node `lem-sfb-sheaf-cover-local-isomorphism` and its module
`Mathlib.CategoryTheory.Sites.LocalProperties` are unnecessary: sheaf separatedness
applies directly to the scalar morphism, so there is no image object, zero-to-image
map, or cover-local isomorphism argument. The experimental private import of that
Mathlib module was removed. No other original proof imports remain unused.
Existing public imports are retained as the module's public interface.
No unit statement or unit proof step is bypassed; this node is an internal finite-cover
supplement to the biduality unit.

## Where the brief, the DAG or earlier work was wrong

The earlier packet retained a warning option that the landing hole census interpreted
as an anonymous hole. Removing that option repairs the precise reported obstruction;
the Lean source has no hole tokens and no declarations or signatures change in this retry.

No statement defect was found. The original proof plan silently treated scalar
compatibility as canonical, although the Lean signature permits arbitrary independent
linear structures. The DVR conversion to natural-number scalar multiplication supplies
the missing justification without changing any hypothesis. Also, derived homology's
additivity was not available by instance inference in the pinned library; a proved
private helper descends it along `Qh` using `homologyFunctorFactorsh` and
`Localization.functor_additive_iff`.

The original image-sheaf argument is longer than necessary. Direct separatedness proves
the required zero equation, including on an empty cover. The node was updated accordingly.
No new nodes, definition repairs, or consumer adaptations are needed. The diagnostic
option removal is recorded in `coord/changes/sf-rational-local-global-warning-option.md`.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
