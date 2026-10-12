## What changed

Added `AffineHomComplexEvaluation.lean` for the underived chain-level affine Hom calculation and `DerivedSingleHomEvaluation.lean` for the derived K-injective comparison. The item's theorem now combines these two interfaces with a real localization composition proof. Both intermediate theorems remain `sorry`. The second reading adds a local transparency setting to keep the combining proof within the file compilation limit.

## Proved and sorry left

Closed: `AlgebraicGeometry.affine_hom_kInjective_evaluation` (one original hole), by a genuine composition and functoriality proof using two strictly smaller statements.

Added and still open: `AlgebraicGeometry.affine_hom_complex_evaluation` (node `lem-sc-affine-hom-complex-evaluation`) and `AlgebraicGeometry.derived_single_hom_evaluation` (node `lem-sc-derived-single-hom-evaluation`). There are no other holes in the delivered sources. This is a decomposition, not a completed proof: one hole closed, two added, local net -1 before any closure pruning or shared dependency effects. A short attempt to finish the derived comparison exceeded the per-file compilation limit and was not retained.

## No longer needed

Removed direct proof-only import: `Sheaf.Algebra.Homology.HomComplex`; the new intermediate modules supply it transitively. No modules are pruned.

Old direct proof dependencies `def-pur-derived-internal-hom`, `def-pur-hom-complex`, and `def-sc-direct-image-algebra-derived-category` are replaced in the item's `proof_deps` by the two intermediate nodes. All three remain used transitively by those nodes; none is globally unnecessary or eligible for pruning.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan combines an underived chain calculation and a derived localization calculation without naming either as a separate Lean interface. These are strictly smaller statements and are now split off so the main theorem has a complete combining proof. The Stacks references used are Tags 0BUZ, 0BV0, and 0AX3; the source text confirms the affine Hom adjunction and its derived counterpart.

## New nodes

`lem-sc-affine-hom-complex-evaluation` records the underived chain-level calculation and evaluation-at-one identity. `lem-sc-derived-single-hom-evaluation` records the derived comparison and its naturality in maps from the unit. Both have corresponding modules under `lean/Sheaf/AlgebraicGeometry/`.

## Second reading by N2

1. Compared the delivered item to the repository with `diff`: its sole existing declaration's signature and docstring are unchanged; no definition or target changes. The only changes are private proof imports, local elaboration options, and the proof body. The two other modules are new.
2. Compiled all three modules in import order through `lcompile.py`. The only sorries are the two named intermediate theorems listed above. Scanned for forbidden declarations and hollow definitions: none. A scratch axiom check and the delivery probe check the trust basis; `sorryAx` is expected from the two open claims.
3. Read both split statements, their word proofs and their nodes. The underived lemma does not assume a derived category or K-injectivity; the derived lemma is independent of affine morphisms, the algebra-valued functor and its adjunction. Each is a strict part of the original argument, rather than a restatement. Checked zero complexes, zero module B, zero map k, the empty scheme, zero rings and arbitrary unbounded targets. The product calculation uses only one surviving factor, not exactness of products. Repeated searches using different queries via LeanFinder, Loogle, launcher grep and local rg. Existing homComplex_single_iso supplies an objectwise isomorphism only; homComplex_unit_iso and derivedInternalHom_unit_iso lack the required evaluation compatibility. None duplicates either new statement. Checked the cited Stacks tags online: [0BUZ](https://stacks.math.columbia.edu/tag/0BUZ), [0BV0](https://stacks.math.columbia.edu/tag/0BV0), [0AX3](https://stacks.math.columbia.edu/tag/0AX3), and [0A95](https://stacks.math.columbia.edu/tag/0A95). The unbounded chain identity is the elementary extension spelled out in the word proof, not an assertion that 0AX3 itself has that generality.
4. The combining proof uses associativity, localization functor composition and the two explicit equations. The imports of the new statements are proof-only. All old proof dependencies remain transitively needed, as detailed above. Read dag/units/sk-thm-picard-duality.json: its realized fields are empty; no recorded realization is removed, and this split preserves the existing finite-duality route within that unit.
5. Compared node fields with the proof: the item's two dependencies are precisely the two applications, followed by an elementary combining step. Each new node has its chapter, unit, source, statement dependencies, proof steps and their union, origin, searches, status, creation record, blueprint lineage and Lean record. Repaired the two new Lean records to contain their signatures verbatim.

Changes made: preserved signature whitespace; added a local transparency option so the item compiles within the file limit; corrected the hole accounting and pruning report; recorded independent searches and verbatim new-node signatures. The attempted closure of the derived lemma was discarded rather than delivering a partial proof.
