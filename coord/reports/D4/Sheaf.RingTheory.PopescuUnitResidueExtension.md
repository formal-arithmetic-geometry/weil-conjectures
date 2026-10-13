## What changed

`Algebra.exists_popescu_unit_residue_extension` now has a complete Lean proof from two strictly smaller geometric constructions. `Sheaf.RingTheory.PopescuAlgebraicResidueEnlargement` treats only an algebraic residue and returns a residue-power lift and a formally étale residue extension. `Sheaf.RingTheory.PopescuTranscendentalResidueEnlargement` treats only a transcendental residue and returns an element mapping to the unit, with rational residue extension. Neither theorem returns an inverse unit or a nilpotent inverse error.

The proved private helper `Algebra.exists_geometric_residue_power` establishes locality of the initial inclusion using nilpotence of Artinian-local nonunits, constructs the ambient residue algebra by `IsLocalRing.ResidueField.mapAlgHom`, proves the scalar tower and residue compatibility, and splits on algebraicity. It assembles the empty or singleton family and proves the singleton adjoin certificate matches the required range. The main theorem proves the prime-power quotient is nontrivial, local and Artinian with the specified maximal ideal, and proves that `s` maps to a unit. After applying the helper, it proves the captured residue-power lift is a unit: a nonunit would be nilpotent and have zero ambient residue, contradicting the residue of `x^Q`. Its inverse has the required nilpotent error by an explicit residue multiplication calculation.

No existing declaration signature or visibility changes. New imports are the two branch modules and Mathlib's minimal-prime Artinian criterion and dimension-zero lemmas. The item's node now follows the actual Lean proof.

## Proved and sorry left

Closed the original hole in `Algebra.exists_popescu_unit_residue_extension` (node `lem-weil-pbc-popescu-unit-residue-extension`). Its proof contains no `sorry`; the private helper is also completely proved.

Added two holes, each the whole proof `:= by sorry` of a public theorem in its own module:

- `Algebra.exists_popescu_algebraic_residue_enlargement`: node `lem-weil-pbc-popescu-algebraic-residue-enlargement`, module `Sheaf.RingTheory.PopescuAlgebraicResidueEnlargement`.
- `Algebra.exists_popescu_transcendental_residue_enlargement`: node `lem-weil-pbc-popescu-transcendental-residue-enlargement`, module `Sheaf.RingTheory.PopescuTranscendentalResidueEnlargement`.

This is a decomposition, with one upper hole closed and two lower holes added (net −1), not an unconditional proof of the geometric construction. The main theorem still transitively depends on `sorryAx` through these two theorems.

## No longer needed

Removed these original proof-only imports from the item:

- `Sheaf.RingTheory.FlatAndFlatOfFlatFibreNoetherian`
- `Sheaf.RingTheory.ArtinianLocalEssentiallyFiniteTypeResidue`
- `WeilConjectures.Mathlib.RingTheory.Etale.Field`
- `Sheaf.RingTheory.HenselianOfNilMaximalIdeal`
- `Sheaf.RingTheory.HenselianFiniteEtaleEquivalence`
- `Sheaf.RingTheory.HenselianEtaleRetraction`

The original nodes for the fibre criterion, essential finite type residue criterion, finite-separable étaleness, henselian nilpotent maximal ideals, finite étale equivalence and henselian retraction remain proof dependencies of the new branch nodes. They are not mathematically discarded; their modules are unnecessary for the proved combination and are not imported by the new statement modules while their construction proofs remain holes. Likewise localization, noetherianity, faithful flatness and ideal contraction still appear in the branch plans where needed. No original DAG node is declared globally unreachable, since other targets may still reach it.

Every original proof dependency removed from the item’s direct proof plan is listed here (the branch plans still retain the construction dependencies where needed):

- `lem-weil-pbc-artinian-local-unique-prime`
- `def-weil-pbc-popescu-admissible-subalgebra`
- `lem-weil-pbc-separable-first-purely-inseparable`
- `lem-weil-pbc-finite-type-algebra-noetherian`
- `lem-weil-pbc-criterion-flatness-fibre-noetherian`
- `def-weil-pbc-flat-ring-map`
- `lem-weil-pbc-flat-local-hom-faithfully-flat`
- `lem-weil-pbc-faithfully-flat-ideal-contraction`
- `def-weil-pbc-essentially-finite-type-algebra`
- `def-weil-pbc-finite-type-algebra`
- `lem-weil-pbc-artinian-local-essentially-finite-type-residue`
- `def-weil-pbc-separable-algebraic-extension`
- `lem-weil-pbc-finite-separable-extension-etale`
- `lem-weil-pbc-henselian-of-nil-maximal-ideal`
- `lem-weil-pbc-henselian-finite-etale-equivalence`
- `lem-weil-pbc-etale-ring-base-change`
- `lem-weil-pbc-henselian-etale-retraction`

The definition nodes remain in statement dependencies where appropriate. Removed unused public imports from the new modules: `Mathlib.FieldTheory.IntermediateField.Adjoin.Basic` in the algebraic branch and `Mathlib.RingTheory.Etale.Basic` in the transcendental branch.

## Where the brief, the DAG or earlier work was wrong

No disputed statement or source error was found. The existing proof plan does not give a single Lean lemma for the large polynomial localization or finite étale image constructions. The delivery isolates those two source cases and proves the quotient, residue algebra setup, case assembly and inverse-error glue directly in Lean.

The local copy does not contain `literature/stacks-project/smoothing.tex`. Read the actual Stacks Tags 07FI and 07FH on the official site; the new node sources retain the project's source path and identify the precise cases. LeanFinder returned supporting Artinian and formally unramified results, Loogle found the canonical residue maps, and grep found the nilpotence/maximal-ideal and residue-unit facts used. LeanSearch returned an Internal Server Error and is honestly recorded as unavailable.

Edge cases checked for the branch statements: when the residue already belongs to F₀, the algebraic construction permits A=A₀ and Q=1; an imperfect-field purely inseparable residue extension needs a positive p-power and is not incorrectly assumed separable itself. The transcendental statement allows no finite residue extension and uses one generator. The main proof also covers n=1, arbitrary positive characteristic, and the empty Fin 0 family. The trivial ambient ring is excluded by IsLocalRing, and the quotient is explicitly proved nontrivial from n≥1.

The unit `sk-thm-p1` does not list this auxiliary node as its own statement or proof step. Both new lemmas retain the geometric enlargement route of Tag 07FI and the initial admissibility of Tag 07FH. No unit-level route is bypassed. There are no forced adaptations and no change records.

## New nodes

`lem-weil-pbc-popescu-algebraic-residue-enlargement` is the algebraic case of Tag 07FI: separable Frobenius power, finite étale henselian lift, compatible local map into the ambient ring, admissible image and residue-power lift. Its source-derived steps retain the existing dependency nodes. It states only this case and leaves the inverse-unit and nilpotent-error proof to the item.

`lem-weil-pbc-popescu-transcendental-residue-enlargement` is the transcendental case of Tag 07FI: polynomial evaluation and localization, fibre flatness and an admissible image with simple rational residue extension. It states only this case and captures x itself, with no choice of inverse or nilpotent error. Both nodes have complete docstring proofs and recorded actual searches. No change records were needed.

## Second reading by D4

1. Compared the only existing delivered module against the repository version and
   mechanically compared its theorem signature before `:= by`: byte-identical.
   No definition, existing visibility, target statement, or other module was changed.
   Both new theorem signatures also match their node `lean.statement` verbatim.
2. Compiled all three modules through lcompile.py. Exactly two sorries remain, the
   named public branch theorems listed above; no prohibited declaration or hollow
   definition occurs. A scratch import and `#print axioms` for all three public
   theorems showed only propext, Classical.choice, Quot.sound and sorryAx. Read the
   quotient Artinian argument, canonical residue map, empty/singleton case assembly,
   unit reflection and inverse-error calculation. Verdict: genuine reduction, with
   one upper hole closed and two strictly smaller case holes added, not a net proof.
3. Checked both branch statements and their full docstring proofs against Stacks
   [07FI](https://stacks.math.columbia.edu/tag/07FI) and
   [07FH](https://stacks.math.columbia.edu/tag/07FH). Checked the field case, n=1,
   residue already in F₀, inseparable algebraic residue and transcendental residue.
   A residue already in F₀ permits A=A₀, Q=1; inseparability is handled by a p-power.
   Artinian locality excludes a trivial ambient ring. Each branch is only one case
   and omits the inverse-unit/nilpotent-error construction proved by the item.
   Repeated LeanFinder, Loogle and grep searches with different queries and searched
   lean/Sheaf and the upstream ring-theory library. Related existing declarations
   include exists_artinian_coefficient_enlargement,
   exists_finiteEtale_artinian_residue_lift and
   artinian_transcendental_polynomial_localization. They do not provide the required
   admissible subalgebra together with its specific residue-field certificate.
   No exact duplicate or immediately applicable shorter proof was found. Closing
   either branch still requires substantial image/admissibility and residue work.
4. Read the proof top down and inspected public versus proof-only imports. Removed
   two unused public imports from the new modules; the branch imports in the item
   are correctly private. Completed the list of every removed old proof dependency.
   Read dag/units/sk-thm-p1.json: the auxiliary item is not a realized unit statement
   or step; the source's geometric route is retained. No unit route is bypassed.
5. Checked the existing node's proof steps, their union proof_deps and proof_origin,
   and the new nodes' source, searches, created, blueprint, chapter, unit and Lean
   records. Corrected the item's nilpotence citation from the unique-prime node to
   lem-weil-pbc-artinian-local-noetherian-nilpotent, whose recorded Mathlib searches
   include the exact nilpotence/maximal-ideal equivalence used in Lean. New nodes
   describe the unproved construction plans, and their signatures match Lean.

Second reading changed only the two unused imports, the item's nilpotence dependency
citation, and this report (including the complete direct-dependency pruning list).
No proof body or declaration signature needed repair. No change record is required.
