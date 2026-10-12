## What changed

Replaced the sorry in `LocalizedModule.gradedModuleAwayRestriction` by a complete Lean
proof from two strictly smaller statements, imported with proof-only imports:
`Sheaf.Algebra.Module.GradedModuleAwayMaps` and
`Sheaf.Algebra.Module.GradedModuleAwayComparison`. The original theorem signature is unchanged.

The first statement constructs the degree-zero submodules and restriction maps, their fraction
formulas, semilinearity, and the distinguished units (parent steps 1–4 and 6). The second assumes
fixed restriction data and supplies only the principal-localization equivalences and their
formulas (parent steps 7–9). Each has its own module, node, source, and proof in words.

The original module now proves identity and composition from linear-map uniqueness and
`IsLocalization.ringHom_ext`, including the homogeneous composite relation. It constructs the
canonical map kappa by conjugating rho(g,h) with theta(f,g) and theta(f,h), proves its linearity
and extension formula, proves the needed unit property using the analogous ring conjugation,
and proves uniqueness by `IsLocalizedModule.ext`. The commuting square follows from the
construction. Thus none of the coherence argument is left in either new sorry.

Local compilation checks all three modules in import order. A local heartbeat increase is
needed to elaborate the nested scalar actions; the original declaration's unused dependent
binder is covered by a theorem-local unused-variable linter setting.

## Proved and sorry left

Closed: `LocalizedModule.gradedModuleAwayRestriction`
(node `lem-weil-pbc-graded-module-away-restriction`). Its body has no sorry.

Added and left as whole named public theorem proofs:

- `LocalizedModule.gradedModuleAwayMaps`
  (node `lem-weil-pbc-graded-module-away-maps`).
- `LocalizedModule.gradedModuleAwayComparison`
  (node `lem-weil-pbc-graded-module-away-comparison`).

This is a decomposition: one original hole closed and two lower holes added, net minus one.
It does not establish a sorry-free theorem or claim a net reduction in the closure ledger.
The identity, composition, transitive relation, and localization-square arguments are proved.
No definition, target statement, or existing statement was changed.

## No longer needed

None. Both existing public imports are needed for the original statement and remain.
All three original proof-dependency definition nodes remain needed, in addition to the two new
statement nodes. No unit statement or realized step was bypassed and no module is claimed pruned.
The second new node needs no identity/composition assumptions and asserts no commuting square:
those parts are handled in the original module.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found in the parent statement or plan. Its dependencies are localization
definitions, not ready-made lemmas for graded-module maps or comparisons; the two substantial
pieces are now explicit parallel proof items. Mathlib search found ring-level and ordinary
module localization APIs, but no exact graded-module result. LeanSearch returned an internal
server error, recorded as unavailable, not as a negative search.

The local file `literature/stacks-project/constructions.tex` is absent in this checkout.
Read the cited source at https://stacks.math.columbia.edu/tag/01M4, clauses (1)(c),(d),(e),(g),(h)
and the fraction-formula proof. The parent supplies the detailed degree and bijectivity
calculations expanding what Stacks calls clear from the formulas.

Edge cases checked for the new statements: zero modules and zero rings, nilpotent f or g,
zero relation multiplier, exponent 1, positive degree 1, and empty indexing type. In the
nilpotent-g case the target is zero; U is nilpotent in the source localization, so its further
localization is also zero. No nonzero-denominator or nonzero-numerator assumption was added.

## New nodes

`lem-weil-pbc-graded-module-away-maps`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-graded-module-away-maps.json`, carries the
construction of restriction data only, with no coherence or comparison assertion. Its module
is `lean/Sheaf/Algebra/Module/GradedModuleAwayMaps.lean`.

`lem-weil-pbc-graded-module-away-comparison`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-graded-module-away-comparison.json`, carries
principal-localization equivalences for fixed restriction data only. It does not construct
the input data or prove coherence. Its module is
`lean/Sheaf/Algebra/Module/GradedModuleAwayComparison.lean`.

Both nodes keep the parent's chapter, unit and blueprint ancestry. Searches and their actual
results are recorded. No change record is required because all existing statements and
interfaces are preserved; added imports are proof-only.

## Second reading by U1

1. Compared every delivered Lean module against the read-only repository. The only existing
   module is GradedModuleAwayRestriction; its declaration signature and docstring are byte for
   byte unchanged. Its additions are proof-only imports, theorem-local options, and the proof.
   The two other modules are new. No definition or target statement is changed. Verdict: pass.
2. Compiled all three modules locally in import order without errors or warnings. Scratch copies
   with `#print axioms` for each declaration showed exactly propext, Classical.choice, Quot.sound,
   and sorryAx. There are precisely the two reported named theorem holes; no forbidden declaration
   or hollow definition. Existential witnesses occur only inside a theorem proof, with submodules
   pinned by carriers, maps by extension or restriction formulas, and U by its injective value map.
   Verdict: pass as a decomposition, not a sorry-free proof.
3. Read both split statements and their docstring proofs against Stacks tag 01M4,
   https://stacks.math.columbia.edu/tag/01M4. Verified the degree equation when g is not nilpotent,
   the equal-degree inverse of rhoS(U), and both comparison bijectivity calculations. In particular,
   multiplying g^N*a^m*x=0 by f^m gives g^(N+e*m)*x=0, and d>0 permits K*d>=N+e*m.
   For nilpotent g, U is nilpotent in R_f, so the further localization is zero even when M_f
   is not zero. Zero rings, zero modules, f=g, exponent one, zero relation multipliers, and empty
   indexing types introduce no missing hypotheses. Neither split includes coherence or the final
   square, so neither restates the parent. Independent LeanFinder search for degree-zero homogeneous
   module fractions returned ring fraction constructors only; Loogle returned IsLocalizedModule.ext;
   grep and rg found ring awayMap APIs and other chart statements, no exact replacement. Neither
   substantial remaining statement can be closed by a short API application. Verdict: pass.
4. Read the parent proof from the top down: extension uniqueness gives identity/composition;
   comparison equivalences conjugate the restriction maps to construct kappa; ring conjugation
   establishes the unit needed for its uniqueness. Both original public imports appear in the
   unchanged signature, and both new plain imports are used in the proof. Compared the old three
   proof dependencies: all remain used. Reviewed sk-thm-reduction.json realized fields: this is
   below the unit steps and bypasses none. No prunable import or node found. Verdict: pass.
5. Checked node proof steps, dependency unions, origin, source, ancestry, created fields, Lean
   declarations, and search records against the actual modules. The parent node changes only
   proof, proof_deps, and proof_origin. New signatures agreed token for token but were flattened;
   repaired both new lean.statement fields to preserve the exact multiline Lean signature.
   Verdict: pass after this metadata repair.

Second reading changed only the two new nodes' signature formatting and added this review.
The Lean proof, interfaces, imports, and split remain as delivered by the first worker.
