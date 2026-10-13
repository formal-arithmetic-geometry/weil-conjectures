## What changed

Proved `Module.exists_selected_basis_away_mul_of_split` in
`Sheaf.RingTheory.SelectedBasisOfLocalizedSplit`, with its original signature and visibility.
The existing proved private helper selects and spreads a basis over `A_b`.
The new argument extends the prime to `A_b`, clears the shrinking element's denominator,
verifies the iterated module localization by explicit power calculations, and transports
the basis to `LocalizedModule.Away (b * t) M`. The transport preserves each prescribed
basis value by `IsLocalizedModule.linearEquiv_apply`.

Added the proof-only import `Mathlib.Algebra.Module.LocalizedModule.Away` for the
localization constructor, denominator formulas, and associated-element transport.
All public imports and public signatures remain unchanged. Updated the existing node's
proof to record the completed argument; its dependency list remains empty.

Read the source passages online because the local Stacks source is absent here:
[07C6](https://stacks.math.columbia.edu/tag/07C6),
[00NX](https://stacks.math.columbia.edu/tag/00NX), and
[0GWM](https://stacks.math.columbia.edu/tag/0GWM).
The proof implements the selection-and-shrinking step of 07C6 using existing Mathlib
finite-projective and prescribed-isomorphism spreading results. No unit realization
is bypassed and no additional project statement is assumed.

## Proved and sorry left

Closed the only original hole:
`Module.exists_selected_basis_away_mul_of_split`
(node `lem-weil-pbc-selected-basis-of-localized-split`).
Holes closed: 1. Holes added: 0. Sorries left in the delivered module: none.
The existing private `Module.selected_basis_of_split` remains proved.

The module compiles with no warnings using `lcompile.py`. The delivery dry run checks
all declarations' axioms. The proof works with empty selected bases, with `m = 0` or
`n = 0`, and with denominator exponent zero: no nonempty-family or positive-rank
assumption was introduced. A zero ring cannot carry the specified prime ideal.
No new statements, definitions, or forced adaptations were needed.

## No longer needed

Removed these redundant proof-only imports:

- `Mathlib.LinearAlgebra.Dimension.Constructions`
- `Mathlib.LinearAlgebra.Dimension.StrongRankCondition`
- `Mathlib.LinearAlgebra.StdBasis`

The remaining imports already supply the rank and standard-basis declarations used
by the existing helper. Also removed the trial import
`Mathlib.RingTheory.Localization.Ideal`, whose declarations are already available
through the retained imports. This last import was not present in the original module.
No project node or `Sheaf`/`WeilConjectures` module is pruned: the original node has
no project proof dependencies, and the proof needs none.

## Where the brief, the DAG or earlier work was wrong

The node's short natural-language statement describes a globally split module;
the already-landed Lean signature and declaration docstring allow the splitting only
after localization at `b`. The proof handles that full existing signature without
assuming global finite presentation of `M` or changing the statement.
The missing step in earlier work was the denominator clearing and module/coefficient
transport from the globally split helper. These steps are now proved directly.

## Second reading by R3

1. Compared the delivered module with the repository version. The theorem signature and
   existing declarations are byte-for-byte unchanged; only the proof body and proof-only
   imports differ. Verdict: pass.
2. Compiled the module with `lcompile.py` and inspected the declarations for forbidden
   constructs or unlisted `sorry`s. The file compiles without warnings, contains no
   `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`, and the proof uses
   only the permitted localization and basis constructions. Verdict: pass.
3. Checked the completed theorem and its existing helper against the DAG and searched the
   local library for duplicate declarations. No new statement was introduced, and the
   theorem has the unchanged target statement. Verdict: pass.
4. Read the proof from the target downward. It uses the existing split-module helper,
   clears the localization denominator, proves the composite localization map directly,
   and transports the basis; the three removed dimension imports are unused. The unit's
   selection-and-shrinking route remains represented in the node. Verdict: pass.
5. Compared the node proof steps with the Lean proof. The node records the same five steps,
   has no stale project proof dependencies, and the report records the removed imports.
   Verdict: pass.

Changed only the report by adding this second-reading record; no proof or interface repair
was needed.
