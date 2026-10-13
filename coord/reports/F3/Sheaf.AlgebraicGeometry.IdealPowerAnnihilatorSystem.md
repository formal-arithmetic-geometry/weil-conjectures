## What changed

Added the explicit `idealAnnihilator` subsheaf construction and its inclusion in
`IdealPowerAnnihilatorQuasicoherent`. Proved `ideal_power_annihilator_system` by using
that construction, direct induction for annihilator monotonicity, stalk exactness,
and sectionwise stalk detection.
The quotient map is proved bijective on every open contained in `U`, and its restriction
along `overFunctor` is shown to be an isomorphism.

Repair of the returned delivery: removed the duplicate private `power_factor` theorem.
The existing theorem in `SectionsOverQuasiCompactOpen` is private, and that module
imports this item, so importing it here would introduce a cycle. Instead, the
annihilator-presheaf inclusion is proved directly by induction on `n ≤ m`; the
successor case tests annihilation through the defining ideal-product inclusion.
No duplicate power-factor theorem remains, no other module is adapted, and the
parent node now records this direct argument. The earlier second reading below
applies to the pre-repair delivery; the repaired delivery awaits a fresh reading.

## Proved and sorry left

Closed `ideal_power_annihilator_system` in
`lean/Sheaf/AlgebraicGeometry/IdealPowerAnnihilatorSystem.lean`.
This is a decomposition: 1 upper hole closed, 1 lower hole added, net 0 holes.
Left one strictly lower affine-local theorem, `ideal_power_annihilator_quasicoherent`,
with its node `lem-weil-pbc-ideal-power-annihilator-quasicoherent`.

## No longer needed

No existing imports were removed. The duplicate private `power_factor` helper
was removed; its general factorization statement is no longer needed here. The parent proof no longer directly uses these planned
nodes/modules: `lem-weil-pbc-sections-annihilated-by-ideal`
(`SectionsAnnihilatedByIdeal`), `lem-weil-pbc-quasi-coherent-finite-type-affine`
(`QuasicoherentFiniteTypeAffine`),
`lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`
(`Modules.IdealTimesQuasiCoherentAffineSections`), and
`lem-weil-pbc-module-restriction-open-immersion-colimits`. The first three arguments
are replaced by the direct construction plus the single quasi-coherence subproblem;
that subproblem may still need affine-local finiteness and power calculations. The
restriction-preserves-cokernels route is replaced by stalk exactness. Global pruning
depends on other users of these nodes and modules.

## Where the brief, the DAG or earlier work was wrong

The target's module inclusion is more general than the existing `IdealSheafData`
annihilator theorem, so that theorem cannot be applied directly. The delivery constructs
the annihilator from the module inclusion itself. The earlier delivery also
reproved the private `power_factor` theorem of `SectionsOverQuasiCompactOpen`;
the repair removes it and proves only the needed annihilator monotonicity directly.

## New nodes

`lem-weil-pbc-ideal-power-annihilator-quasicoherent` records the remaining affine-local
finite-generation and denominator-clearing argument.

Edge cases checked for the new statement: n = 0 gives the zero annihilator because
the power inclusion is the identity; I = 0 with n > 0 gives all of F; an empty
generator family uses denominator exponent zero. None requires extra hypotheses.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered target module with the repository by `diff`. The existing
   theorem's signature, hypotheses, conclusion and docstring are unchanged. Restored
   one extra space before `:=` so the signature is byte for byte identical. The other
   module is new; there are no changed existing definitions or undeclared interface
   changes.
2. Both delivered modules compile locally in import order. Inspected the entire
   construction, power-factor induction, monotonicity map, vanishing argument,
   stalk-exactness argument and restriction isomorphism. There is exactly one new
   named sorry, `ideal_power_annihilator_quasicoherent`; no definition has a hole
   or chooses arbitrary data from an unproved existence theorem. Scratch axiom
   checks of all six named declarations in the new module and the target show only
   `propext`, `Classical.choice`, `Quot.sound`, with `sorryAx` confined to the
   quasi-coherence theorem and its dependent target. Verdict: valid decomposition,
   not a completed axiom-free proof of the target.
3. Read the new theorem's complete denominator-clearing proof and checked it against
   Stacks https://stacks.math.columbia.edu/tag/01PO and the ideal-power setting of
   https://stacks.math.columbia.edu/tag/01PQ. Finite generation of powers follows
   from products of finite generating families. The n = 0, zero ideal with n > 0,
   unit ideal and empty-generator cases give respectively zero, all of F, zero and
   denominator exponent zero. The statement proves only quasi-coherence of the
   constructed annihilator, strictly one part of the target. Independent searches
   used LeanFinder ("kernel of multiplication by finitely generated ideal localization
   quasicoherent sheaf"), Loogle (`Submodule.localized, Module.Finite`), and grep
   (`IsQuasicoherent.*[Kk]er|[Kk]er.*IsQuasicoherent|annihilator.*localiz`). None
   supplied the missing sheaf result. Read `AnnihilatorSubsheaf`,
   `AnnihilatorAffineCriterion`, `AnnihilatorQuasicoherent`,
   `SectionsAnnihilatedByIdeal`, and upstream `IdealSheaf.Module`: their relevant
   results require `IdealSheafData`, with no direct inverse construction from this
   arbitrary module inclusion. Closing this hole needs further affine-local work.
4. Checked the proof from the top downward and all imports. The existing public
   imports provide the statement; the three added target imports are proof-only.
   The new module's public imports provide its constructions and statement, and its
   gluing import is proof-only. No redundant import or directly applicable shorter
   route was found. `No longer needed` lists all four old proof dependencies absent
   from the new route. These are planned dependency removals, not actual module
   pruning. The node is below the unit level and does not occur in the statement
   or steps of `dag/units/sk-thm-p1.json`'s `realized` record; that route is preserved.
5. Compared both DAG records to Lean. The parent steps describe the actual explicit
   construction, inductive power factor, vanishing and stalk proof; `proof_deps`
   is their union. The new node supplies the source, complete mathematical proof,
   searches, provenance, chapter/unit and Lean declarations, and records the only
   remaining hole. Verdict: the records agree with the delivery.

Second reading changed only the extra signature space and this report. No proof or
statement needed repair. One original hole is closed and one strictly lower hole
is added: net zero, with no actual import or module pruning.


## Second reading by F3

Fresh independent reading of the repaired delivery, 2026-10-13.

1. Compared the delivered target module with the repository using diff. The only
   differences are three plain proof imports and replacement of its proof. The
   existing declaration signature and docstring are byte for byte unchanged.
   The other module is new. No existing definition or statement changes, and
   no change record is required. Verdict: pass.
2. Compiled both modules in import order through lcompile.py: clean, 5.0 and
   7.8 seconds. Read every construction and proof. In particular the replacement
   induction on n <= m tests sections through the recursive power inclusion:
   at m = 0 it uses the original inclusion, and at m > 0 the image inclusion.
   No duplicate power-factor theorem remains. Gluing tests products on the
   intersections of the cover; vanishing lifts 1 on the open itself; stalk
   exactness gives the quotient bijection and the forgetful functor reflects
   the final isomorphism. Scratch-copy #print axioms checks of all six named
   declarations of the new module and the target show only propext,
   Classical.choice and Quot.sound, with sorryAx in the one split theorem and
   its dependent target. There is exactly one named sorry, in
   ideal_power_annihilator_quasicoherent; no hollow definition, arbitrary
   witness chosen from an unproved existence theorem, or prohibited command.
   Verdict: valid decomposition, not an axiom-free completed target.
3. Checked the split theorem against its explicit construction and its complete
   denominator-clearing docstring proof, and read the sources
   [01PO](https://stacks.math.columbia.edu/tag/01PO) and
   [01PQ](https://stacks.math.columbia.edu/tag/01PQ). Finite products of a finite
   generating family generate every power. The cases n = 0, zero ideal for
   positive n, unit ideal, and an empty generating family yield respectively
   the zero annihilator, all of F, the zero annihilator, and denominator
   exponent zero. This theorem supplies only quasi-coherence; the target's
   construction, image, monotonicity, vanishing and quotient claims are proved
   separately. Fresh LeanFinder search used "quasicoherent kernel of action
   finitely generated module ideal"; fresh Loogle search "Module.Finite,
   Submodule" found finite-generation tools, not the sheaf result (an initial
   IsQuasicoherent query was unavailable as an identifier). Fresh msearch grep
   and local rg searches checked kernel and annihilator formulations. Read
   AnnihilatorQuasicoherent, AnnihilatorAffineCriterion,
   SectionsAnnihilatedByIdeal, and the upstream IdealSheaf.Module bridge.
   Existing annihilator theorems require IdealSheafData; no direct reverse
   bridge from the arbitrary module inclusion was found. This hole requires
   substantial affine-local work rather than a short existing-lemma application.
   Verdict: true, needed, strictly smaller, no duplicate statement found.
4. Read from the target downward, checking the original planned dependencies,
   all imports, recursive power definitions, and sk-thm-p1's realized record.
   The added target imports are proof-only; the new module's public imports
   serve its definitions and statement and its gluing import is proof-only.
   No unused import or shorter direct route was found. The four discarded old
   proof dependencies are all listed under No longer needed. No actual module
   has been pruned. This node is below unit level and is not a realized unit
   statement or step, so the unit route is preserved. Verdict: pass.
5. Compared both node records to Lean and the original parent record. The parent
   records precisely the explicit construction, direct annihilator induction,
   vanishing, stalk exactness and sectionwise isomorphism argument; proof_deps
   is the union of the step uses. The new node has the matching statement,
   source, proof, searches, provenance, creation data, blueprint, unit, chapter
   and Lean record and identifies the only split hole. Verdict: pass.

Second reading changed this report only. No Lean proof, statement, definition,
import, or DAG repair was needed. Closed ideal_power_annihilator_system; added
ideal_power_annihilator_quasicoherent: one upper hole closed, one lower hole
added, net zero. This is a decomposition, with no actual module pruning.
