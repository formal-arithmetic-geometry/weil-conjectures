## What changed

Replaced the sorry in `Algebra.exists_popescu_unscaled_unit_basis` with explicit basis
construction. The statement, universes, public imports, and existing docstring are unchanged.
The geometric construction is separated into `Sheaf.RingTheory.PopescuUnitResidueExtension`,
which has no basis hypothesis or basis conclusion. Its output records a compatible residue
algebra and either a formally étale extension with m = 0 or a simple transcendental extension
with m = 1. The second new module,
`Sheaf.RingTheory.SimpleTranscendentalDifferentialDecomposition`, states the canonical
field differential decomposition without any admissibility or finite-basis hypotheses.
A proved private helper handles basis transport over abstract fields, keeping the large
quotient types out of its calculation. The main proof handles the étale case using Mathlib,
scalar-extends the input basis, forms
a product with the standard function-space basis, and transports it through the canonical
differential equivalence. The vector identities follow from its explicit formula and residue
compatibility. Both intermediate statements are strictly parts of the original argument.

Searches: LeanFinder returned polynomial/submersive-presentation bases; Loogle returned
`tensorKaehlerEquivOfFormallyEtale` and its formula, used directly in the étale branch;
grep found no geometric enlargement. LeanSearch returned Internal Server Error. The DAG
and library searches found no identical geometric certificate or rational differential
splitting. Source text was checked at Stacks Tags 07FH, 07FI, 00RS, 00RX, 00RT, 00S2, and 00RV.
The named local literature file is absent on this machine, so the official web versions were read.

## Proved and sorry left

Closed: `Algebra.exists_popescu_unscaled_unit_basis` (the module's sole original sorry),
by a complete Lean proof from the geometric intermediate statement, the proved differential
decomposition, and Mathlib.

Also proved: the new theorem
`KaehlerDifferential.exists_simple_transcendental_differential_decomposition`, node
`lem-weil-pbc-simple-transcendental-differential-decomposition`, entirely from Mathlib.
It uses the fraction-field construction patterned on the already-proved module
`Sheaf.FieldTheory.SeparablyGeneratedDifferentialsBasis`, with no import of that module.

Added and left: `Algebra.exists_popescu_unit_residue_extension`, node
`lem-weil-pbc-popescu-unit-residue-extension`.

This is a decomposition: one upper hole closed, one strictly smaller hole added, net zero
before the maintained ledger's import-closure calculation. No sorry remains in the original
module. No definition, axiom, or arbitrary chosen library data was added. Edge cases:
empty initial basis is retained; m = 0 is handled by the unique zero-coordinate module;
the transcendental lemma allows every characteristic and arbitrary base differential rank.
The certificate excludes duplicated generators and a nongenerating transcendental family.

## No longer needed

Removed proof imports from the original module:
`Sheaf.RingTheory.ArtinianLocalEssentiallyFiniteTypeResidue`,
`Sheaf.RingTheory.FlatAndFlatOfFlatFibreNoetherian`,
`Sheaf.RingTheory.HenselianEtaleRetraction`,
`Sheaf.RingTheory.HenselianFiniteEtaleEquivalence`,
`Sheaf.RingTheory.KaehlerDifferentialsPolynomialExtension`,
`Sheaf.RingTheory.HenselianOfNilMaximalIdeal`, and
`WeilConjectures.Mathlib.RingTheory.Etale.Field`.
All of these except the polynomial-extension module are relocated to the geometric module.
The proof now uses Mathlib's polynomial basis, localization, and differential exact sequences
directly. It no longer needs `Sheaf.RingTheory.KaehlerDifferentialsPolynomialExtension` or
its node `lem-weil-pbc-kahler-differentials-polynomial-extension`. This is pruning from this
route; other targets may still use that module. Mathlib's canonical étale differential
equivalence remains directly used. The original unit route is kept.

Complete old-node dependency accounting (removed from the original node’s direct
`proof_deps`, rather than all pruned from the target closure):

- `def-weil-pbc-localization-at-prime`
- `lem-weil-pbc-localization-noetherian`
- `lem-weil-pbc-noetherian-local-quotient-artinian-local`
- `lem-weil-pbc-artinian-local-noetherian-nilpotent`
- `lem-weil-pbc-artinian-local-unique-prime`
- `def-weil-pbc-popescu-admissible-subalgebra`
- `def-weil-pbc-kahler-differentials`
- `def-weil-algebraic-element`
- `lem-weil-pbc-separable-first-purely-inseparable`
- `lem-weil-pbc-finite-type-algebra-noetherian`
- `lem-weil-pbc-criterion-flatness-fibre-noetherian`
- `def-weil-pbc-flat-ring-map`
- `lem-weil-pbc-flat-local-hom-faithfully-flat`
- `lem-weil-pbc-faithfully-flat-ideal-contraction`
- `def-weil-pbc-essentially-finite-type-algebra`
- `def-weil-pbc-finite-type-algebra`
- `lem-weil-pbc-artinian-local-essentially-finite-type-residue`
- `lem-weil-pbc-kahler-differentials-polynomial-extension`
- `lem-weil-pbc-kahler-differentials-localization`
- `def-weil-pbc-separable-algebraic-extension`
- `lem-weil-pbc-finite-separable-extension-etale`
- `lem-weil-pbc-henselian-of-nil-maximal-ideal`
- `lem-weil-pbc-henselian-finite-etale-equivalence`
- `lem-weil-pbc-etale-ring-base-change`
- `lem-weil-pbc-henselian-etale-retraction`

The geometric entries are carried by the new geometric node; the differential
localization entry is carried by the proved decomposition node. Definition entries
remain statement dependencies or are available through the retained public imports.
Only the polynomial-extension node is no longer used by this route.

## Where the brief, the DAG or earlier work was wrong

No change to an existing statement or definition was needed. The existing plan requires
substantial missing geometric glue: its stated lower lemmas do not directly supply a
compatible residue algebra, the polynomial localization image, or its simple-extension
certificate. These are made explicit in the geometric node. Admissibility alone cannot
justify transport of the input differential basis; the residue-extension certificate is
essential. The generic transcendental node makes the polynomial/localization transport
and its canonical formula explicit rather than hiding it in the main proof.

## New nodes

`lem-weil-pbc-popescu-unit-residue-extension` is the basis-independent geometric portion
of the existing argument, in `Sheaf.RingTheory.PopescuUnitResidueExtension`. Its docstring
and node spell out the Artinian setup, polynomial branch, finite étale branch, admissibility,
residue algebra compatibility, and unit residue inverse.

`lem-weil-pbc-simple-transcendental-differential-decomposition` is the now-proved canonical
field splitting for a simple transcendental extension, in
`Sheaf.RingTheory.SimpleTranscendentalDifferentialDecomposition`. It constructs the relative
basis through the fraction-field localization and proves the canonical splitting using
formal smoothness and differential exactness, entirely from Mathlib.
No change record or forced adaptation is needed.

## Second reading by J4

1. Compared all delivered modules with the repository. The original theorem’s
   signature and docstring are byte-for-byte unchanged; its public imports are
   unchanged. The two other modules and their declarations are new. There are no
   changed definitions, statements, forced adaptations, or change records. PASS.
2. Compiled all three modules in import order, without errors or warnings. Scratch
   copies with `#print axioms` show only `propext`, `Classical.choice`, `Quot.sound`
   for the differential decomposition, and those plus `sorryAx` for the original
   theorem and the explicitly open geometric theorem. The only delivered sorry is
   `Algebra.exists_popescu_unit_residue_extension`; no forbidden declarations or
   hollow definitions occur. All basis constructions are explicit; existential
   geometric witnesses are used inside a proof, not to define library data. PASS.
3. Read the geometric certificate and its complete two-case proof against Stacks
   [07FI](https://stacks.math.columbia.edu/tag/07FI) and
   [07FH](https://stacks.math.columbia.edu/tag/07FH). The argument uses admissibility,
   without needing geometric regularity. The certificate removes every basis
   hypothesis and conclusion, and is a strict geometric part of the argument.
   Checked n=1, an already-contained residue (take the trivial etale extension),
   purely inseparable algebraic residue (a separable p-power), transcendental
   residue (one generator), and t₀=0. The generic decomposition is proved and
   permits arbitrary base differential rank and characteristic. Independent
   Loogle search for mapBaseChange, LeanFinder search for local Artinian residue
   enlargement, and grep for rational differential splitting found supporting
   results, not either complete new statement. Read the existing
   ArtinianTranscendentalLocalization, ArtinianCoefficientEnlargement, and
   SeparablyGeneratedDifferentialsBasis: these supply parts or a different
   certificate, not the required residue-algebra/differential certificate. Closing
   the remaining geometry needs those constructions and their residue-field
   identifications, and is not a short omitted proof. PASS.
4. Read the main proof from its geometric call through the two differential
   equivalences and the explicit product basis transport. The etale case uses
   Mathlib directly; the transcendental case is now entirely proved from Mathlib.
   Proof-only imports are plain imports. The geometric module retains the planned
   imports for its open proof. No shorter complete route was found. Checked
   dag/units/sk-thm-p1.json realized statement and steps: no realized unit node is
   bypassed or removed. Completed the report’s list of all old direct proof
   dependencies removed; distinguished relocation from pruning. PASS.
5. Checked all three node signatures against Lean and their dependency unions
   against their proof steps. The original node changes only proof, proof_deps,
   and proof_origin. New nodes have sources, searches, creation and blueprint
   records, matching Lean statements, and the original chapter and unit.
   Differential dependencies are proved Mathlib matches, not new holes. PASS.

Second-reading changes: completed dependency accounting and added this review;
no Lean proof or statement required repair. One original hole closed, one strictly
smaller geometric hole added, and the new differential theorem fully proved.
The delivery is a decomposition with net zero holes before the maintained ledger.
