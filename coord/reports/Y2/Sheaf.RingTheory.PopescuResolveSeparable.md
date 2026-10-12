## What changed

Replaced the sole `sorry` in `Algebra.canBePopescuResolved_of_regularLocalRing_separable`
with a compiling proof following the repaired Stacks 07FE route. Its signature and all
public imports are unchanged. Added four modules: two proved bridge lemmas and two
strictly smaller remaining parts of the argument. The main module proves the localized
minimal-prime power bound and both annihilator calculations, rather than putting these
into the new holes. Updated its node to the actual formal proof dependency graph.

`PopescuSeparableHeightZeroLocal` proves the dimension-zero localized case directly:
finite generators and directedness factor the map through one smooth subalgebra. It
handles universe size by a proved polynomial-surjection argument and `Shrink`.
`PopescuResolutionSmoothBase` proves transfer of a resolution across a smooth base,
including finite presentation, singular-ideal domination, and the composed maps.

## Proved and sorry left

Closed the original hole in
`Algebra.canBePopescuResolved_of_regularLocalRing_separable` (1 of 1).
This is a decomposition, not a complete sorry-free proof: two new holes remain:

- `Algebra.exists_popescu_separable_preparation`, node
  `lem-weil-pbc-popescu-separable-preparation`, constructs the positive-dimensional
  polynomial problem, maps and controlled parameters (repaired steps 3--6).
- `Algebra.exists_popescu_resolution_parameter_quotient`, node
  `lem-weil-pbc-popescu-separable-parameter-quotient`, resolves the powered parameter
  quotient by regular-local flatness and nilpotent lifting (steps 9--12).

The added public theorems `Algebra.popescu_separable_height_zero_local` and
`Algebra.canBePopescuResolved_of_smooth_base` are fully proved. All private helpers are
fully proved. No sorry remains in the main module; no definition or private lemma
contains a sorry. Net holes closed minus added is 1−2=−1, before closure accounting.
The new statements are genuine parts: preparation concludes no resolution, and the
quotient theorem concerns a different base and target with the parameters killed.

## No longer needed

Removed these direct proof imports from the main module:

- `Sheaf.Algebra.PopescuLiftNilpotent`
- `Sheaf.FieldTheory.SeparableSmoothColimit`
- `Sheaf.RingTheory.ExistsGeneratorsWithControlledAnnihilators`
- `Sheaf.RingTheory.FlatOverRegular`
- `Sheaf.RingTheory.ImprovePresentation`
- `Sheaf.RingTheory.PolynomialOriginRegularLocal`
- `Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence`
- `Sheaf.RingTheory.SingularIdeal`
- `Sheaf.RingTheory.SingularIdealLocalizationSmooth`
- `Sheaf.RingTheory.SmoothFreeDifferentialsStrictlyStandardPower`
- `Sheaf.RingTheory.StrictlyStandardElement`

Their uses move into the specific preparation, quotient, height-zero or smooth-base
modules. This is an import reorganization, not a claim that their modules are pruned
from the complete target closure. No whole module is claimed globally pruned.
The generic finite-presentation filtered-colimit factorization theorem is unnecessary
for the proved zero-dimensional branch: finite generators and directedness suffice;
it remains part of the parameter-quotient plan. The polynomial annihilator condition
and passage from first/square annihilators to powered annihilators need no new node or
unproved dependency: both are proved private helpers in the main module.


Second-reader audit of every old direct `proof_deps` entry absent from the new direct
proof follows. These are moved into the new bridges or remaining parts, supplied by
Mathlib, or used only in signatures/definitions; this list claims no global pruning:

- `lem-weil-pbc-finite-type-algebra-noetherian`
- `def-weil-pbc-localization-at-prime`
- `lem-weil-pbc-localization-noetherian`
- `lem-weil-pbc-zero-locus-eq-iff-radical-eq`
- `def-weil-pbc-noetherian-ring`
- `def-weil-pbc-separable-field-extension`
- `lem-kun-separable-smooth-colimit`
- `def-weil-pbc-filtered-colimit-smooth-algebras`
- `lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit`
- `lem-weil-pbc-singular-ideal-localization-smooth`
- `lem-weil-pbc-smooth-ring-map-base-change-composition`
- `lem-weil-pbc-smooth-ring-map-principal-localization`
- `lem-weil-pbc-smooth-ring-map-local-on-cover`
- `lem-weil-pbc-improve-presentation`
- `lem-weil-pbc-finite-type-noetherian-finite-presentation`
- `lem-weil-pbc-smooth-free-differentials-strictly-standard-power`
- `def-weil-pbc-strictly-standard-element`
- `lem-weil-pbc-popescu-find-sequence`
- `lem-weil-pbc-polynomial-ring-origin-regular-local`
- `lem-weil-pbc-regular-local-generators-regular-sequence`
- `def-weil-pbc-regular-sequence`
- `lem-weil-pbc-flat-over-regular`
- `lem-weil-pbc-flat-module-quotient-flat`
- `lem-weil-pbc-popescu-lift-nilpotent`

## Where the brief, the DAG or earlier work was wrong

No existing statement or definition changed. Preserved the DAG's repairs: use the
extended singular ideal itself for the power bound, handle dimension zero separately,
and explicitly transfer the polynomial-base resolution back to the field. Preparation
returns first/square annihilator equality; the powered condition is proved afterward.
The new quotient statement requires no minimal-singular-prime hypothesis: after
localization its parameter quotient has a unique prime; if the singular ideal escapes
the prime the identity works, otherwise height-zero delocalization applies.

Checked boundary cases: positive dimension and positive exponents are explicit in
preparation; the quotient statement also permits d=0 (zero parameter ideals, local
fields); the dimension-zero bridge needs no global minimality. All witness choices are
within theorem proofs, with no new data definition chosen from an unproved existence
statement. LeanSearch returned HTTP 500: node searches record it as unavailable, not
as absence of a Mathlib match. Loogle/LeanFinder and local grep supplied the usable
Mathlib ingredients. The unit route remains unchanged, and the already-approved
separable smooth-colimit tool is reused.

## New nodes

`lem-weil-pbc-popescu-separable-preparation`: remaining auxiliary-algebra construction
and controlled-parameter theorem; module `Sheaf.RingTheory.PopescuSeparablePreparation`.

`lem-weil-pbc-popescu-separable-parameter-quotient`: remaining nilpotent parameter-quotient
resolution theorem; module `Sheaf.RingTheory.PopescuSeparableParameterQuotient`.

`lem-weil-pbc-popescu-separable-height-zero-local`: proved local dimension-zero bridge;
module `Sheaf.RingTheory.PopescuSeparableHeightZeroLocal`.

`lem-weil-pbc-popescu-resolution-smooth-base`: proved smooth-base transfer bridge;
module `Sheaf.RingTheory.PopescuResolutionSmoothBase`.

No change records: no existing signature, definition or public import changed.

## Second reading by Y2

1. **Interfaces: PASS.** Compared every delivered module to the repository. Four modules
   are new; the existing theorem signature is byte-for-byte identical from `theorem`
   through the colon before its proof. Its docstring, definitions and public imports
   are unchanged. No target or existing declaration was altered; no change record needed.
2. **Proofs and axioms: PASS as a decomposition.** Independently compiled all five files
   in import order with `lcompile.py`. Exactly the two reported public theorems have
   `sorry`; no new definition, private helper, axiom or unsafe implementation does.
   An independent scratch axiom check of all five public theorems showed only
   `propext`, `Classical.choice`, `Quot.sound`, and expected `sorryAx` from open dependencies.
   Smooth-base transfer has only the three standard axioms. The height-zero proof has
   no direct hole but depends on the existing separable smooth-colimit hole. No data
   definition takes an arbitrary witness from an unproved existence theorem.
3. **New statements: PASS.** Read their full signatures, nodes, docstring arguments,
   controlled-generator, improve-presentation, nilpotent-lifting and delocalization
   statements, and checked the source at https://stacks.math.columbia.edu/tag/07FE.
   Preparation does not assume or conclude resolvability; its output is the explicit
   auxiliary lifting problem. Choosing c before the controlled parameters avoids a
   circular dependence on their annihilator quotients. The parameter-quotient theorem
   kills a full parameter system, has a zero-dimensional localized target, and does
   not restate the original problem. Contraction puts every parameter in q, so its
   quotient prime exists. Checked d=0, d=1, positive exponents, empty singular-generator
   families, and the branch where the singular ideal escapes the quotient prime.
   Zero target rings admit no q and give no counterexample. Universe bounds are
   justified by finite presentations, as required by CanBePopescuResolved.
   Independent LeanFinder searches for auxiliary polynomial preparation and flat
   nilpotent local maps, Loogle for Smooth/FinitePresentation, and targeted Mathlib
   grep found ingredients but no whole matching statement. Searched lean/Sheaf and
   the upstream RingTheory modules with parameter/quotient/annihilator terminology.
   Both remaining constructions require substantial work, not a short omitted tactic.
4. **Route and pruning: PASS after repair.** Read sk-thm-p1's realized statement and
   steps: this subsidiary argument bypasses none of them. The proof follows the
   repaired 07FE route and uses the already-approved separable smooth-colimit tool.
   Verified the monomial proof also works over rings with zero divisors: it shifts
   support with coefficient one and preserves every earlier-variable coordinate.
   The power-annihilator induction needs the explicit positive c and uses it.
   Audited every import and added the exhaustive old direct-dependency list above.
   Changed proof-only FiniteStability and Localization.Submodule imports in the new
   height-zero module from public imports to plain imports; recompiled all five files.
   No whole module is claimed pruned from the target closure.
5. **DAG: PASS.** The original node's only substantive changes are its actual proof,
   proof_deps and proof_origin. All new nodes have source, complete argument, search
   records, creation/blueprint/unit fields and matching Lean signatures. Their
   proof_deps are the union of their steps' uses. The main node records the proved
   local power bound and annihilators, the two remaining parts, height-zero
   delocalization and smooth-base transfer in the order the formal proof uses them.

Second reading changed two public proof-only imports to plain imports and completed
this report's dependency/pruning audit. Mathematical proofs and statements were kept.
One original hole is closed and two holes added: decomposition, net -1 before the
ledger's closure accounting; no claim of a complete axiom-clean original theorem.
