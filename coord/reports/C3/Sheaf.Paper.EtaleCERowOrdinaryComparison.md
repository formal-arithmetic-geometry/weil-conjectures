## What changed

`Sheaf.Paper.EtaleCERowOrdinaryComparison` proves its original
`AlgebraicGeometry.Etale.ceRowOrdinaryIso_naturality` by extending the supplied augmented
row comparison, composing the integer-indexed evaluation square with the degreewise
extension square, and applying `extendHomologyIso_hom_naturality`.
All four existing declaration signatures and all three existing definition bodies are
byte-for-byte unchanged. The sole added import is the proof-only
`import Sheaf.Paper.EtaleRowSectionsExtend`.

Three new auxiliary modules contain genuine smaller parts of the argument:
`Sheaf.CategoryTheory.ExtCoefficientCocycle` computes exact-functor and coefficient
transport on one cocycle; `Sheaf.Paper.EtaleRowIntegerSections` descends that formula to
homology and evaluates at 1; `Sheaf.Paper.EtaleRowSectionsExtend` proves the extension
square for arbitrary complexes, without augmentation or injectivity hypotheses.
The integer-indexed theorem remains a named lower hole with its source, full docstring argument
and matching node. Its augmentation-extension and nonnegative homology transport steps are
independently proved in the other modules.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.Etale.ceRowOrdinaryIso_naturality`
(node `lem-weil-pbc-ce-row-ordinary-naturality`), the only original hole in the item.

Two new auxiliary theorems are proved:

- `CategoryTheory.InjectiveResolution.ext_mapExactFunctor_coefficient_cocycle`
  (`lem-weil-pbc-ext-coefficient-cocycle`);
- `AlgebraicGeometry.Etale.ceRowSectionsMap_extend`
  (`lem-weil-pbc-row-sections-extend`).

Hole added and still open: `AlgebraicGeometry.Etale.ceIntegerSectionsIso_naturality`
(`lem-weil-pbc-row-integer-sections`) in `Sheaf.Paper.EtaleRowIntegerSections`.
This is the sole sorry in the delivery, written exactly as `:= by sorry` in a named
theorem with a complete source-based docstring proof and matching node.

One original hole closed, one lower hole added: this is a decomposition with net zero
holes closed, not a completed proof of the target's import closure. The upper theorem
has no direct sorry, but its axioms still include sorryAx through this lower theorem.
The two new proved auxiliary theorems and all definitions have only the allowed axioms.
The maintainer's pinned-baseline ledger determines library-wide closure and pruning counts.

## No longer needed

No source import was removed, and no module is claimed globally pruned.
Every original direct proof dependency was compared with the actual argument:

- `def-sp-injective-resolutions`: retained for the extended augmentation calculation;
- `def-weil-pbc-ext-resolution-sections-iso`: retained for the explicit comparison;
- `lem-weil-pbc-ext-pullback-resolution-sections`: no longer used by this proof.
  Its chosen-resolution, coefficient-free theorem is replaced by the proved generic
  coefficient-cocycle calculation and the integer-indexed evaluation square;
- `lem-weil-pbc-constant-sheaf-pullback-transpose`: no longer a direct dependency of
  the top theorem; still needed inside `EtaleRowIntegerSections`, where its node and
  proof-only import are retained.

The earlier rejected comparison-map restatement is absent from this delivery.

## Where the brief, the DAG or earlier work was wrong

The previous attempt moved the whole target equation into a new theorem defined using
its desired right-hand side. The delivered replacement genuinely proves the augmentation
extension and homology transport, and keeps only the smaller integer-indexed evaluation square open.
The worker report also omitted the old direct proof dependencies no longer used by the
new top-level proof; the complete accounting is above.

The inherited unit `sk-prop-h2` has `realized.statement = []` and `realized.steps = [[]]`.
This delivery changes neither that record nor the unit's Kummer/Brauer route. The comparison
lemmas remain tools below the unit level in the existing hypercohomology lineage.

## New nodes

`lem-weil-pbc-ext-coefficient-cocycle` is a new proved node, not an existing repository
node. Its derived-category roof formula adds the coefficient morphism to exact-functor
transport.

`lem-weil-pbc-row-integer-sections` is a new open node for the evaluation
square on integer-indexed complexes, with complete proof instructions.

`lem-weil-pbc-row-sections-extend` is a new proved node for the independent chain-level
extension square.

Each node records the source,
verbatim Lean theorem signature, proof steps and their dependency union, creation and
blueprint lineage, and Mathlib searches. No statement-change record is needed.

## Second reading by C3

1. **Visible interface — pass.** Diffed the item against the repository and compared
   the declaration table's exact statement strings for `ceRowOrdinaryIso`,
   `ceRowSectionsMap`, `cePresentationRow`, and `ceRowOrdinaryIso_naturality`.
   All are byte-identical; the three definition bodies are identical. The other three
   modules and their nodes are new. All proof-only imports are plain `import`;
   public imports provide names used in signatures or public definition bodies.

2. **Proof and data — pass.** Read every delivered proof and every definition.
   The coefficient lemma cancels the mapped augmentation in the derived category
   using the supplied homotopy; it does not assume inverse image preserves injectives.
   The top proof tests the extended augmentation in degree zero, applies the two
   smaller comparison squares, and transports homology through the canonical isos.
   The sole lower hole remains named and fully documented. All maps are explicit constructions;
   no arbitrary witness is selected from an unproved existence statement. Checked
   compilation of the four modules and `#print axioms` for every public theorem and
   definition; the final delivery gate additionally probes every declaration.
   No forbidden declaration or sorry in a definition occurs.

3. **Auxiliary statements and alternatives — pass.** Checked the sources
   [06XR](https://stacks.math.columbia.edu/tag/06XR),
   [01F8](https://stacks.math.columbia.edu/tag/01F8),
   [01F9](https://stacks.math.columbia.edu/tag/01F9),
   [01FA](https://stacks.math.columbia.edu/tag/01FA),
   [08J6](https://stacks.math.columbia.edu/tag/08J6),
   [015J](https://stacks.math.columbia.edu/tag/015J), and
   [015K](https://stacks.math.columbia.edu/tag/015K).
   These supply the Ext, functoriality and CE-row framework. The extension and cocycle
   squares have checked Lean proofs; the integer square has the complete argument in
   its docstring and remains explicitly open. The cocycle lemma concerns
   a single representative without quotient descent or sections. The integer theorem
   handles evaluation without nonnegative homology. The extension theorem applies
   to arbitrary complexes, without any resolution assumptions. None defines a map
   to make the target equality tautological. Checked p = 0 (no positive-degree-only
   assumption), zero cocycles and coefficients (all maps are additive), identity
   comparisons, and empty schemes (no nonemptiness assumption). The extension proof
   explicitly handles every degree outside the embedding image with a zero source.
   Repeated LeanFinder, Loogle and grep searches with different wording: Mathlib's
   `extMk_comp_mk₀`, `mapExactFunctor_hom`, and embedding naturality are component
   tools; there is no duplicate combined statement. Read the existing
   `ExtPullbackResolutionSections` proof and checked the remaining evaluation argument
   against its calculation; its chosen-resolution theorem is not restated. Search results are added to each node.

4. **Route, imports and pruning — pass.** All original direct proof dependencies
   are accounted for under `No longer needed`. `ExtCoefficientCocycle`,
   `ExtPullbackHomComplex` (for the concrete Hom-complex map), and
   `ConstantSheafPullbackTranspose` are proof-only imports of the integer module.
   The extension module's public import is needed for its signature's explicit maps.
   The item's existing public imports remain needed by its unchanged definitions.
   Read `dag/units/sk-prop-h2.json`; its realized fields and its sole Kummer exactness
   step are untouched. No unit step or chapter route is bypassed.

5. **DAG agreement — pass.** Checked each recorded Lean signature against its module
   and each `proof_deps` against the union of `proof[].uses`. The top node records
   augmentation extension, the two smaller squares and canonical homology transport.
   The integer node records its complete remaining argument, including the proved private
   quotient-descent helper, Γ/terminal-sections naturality and inverse-oriented cancellation.
   The coefficient node records the
   actual localized denominator and numerator calculations. The extension node has
   only degreewise and zero-source steps; its statement dependencies now name the
   explicit integer-map definitions and omit unrelated injective/Ext/cohomology data.

Second reading changed: supplied source/blueprint references to the two new map docstrings;
corrected pruning and hole accounting; added independent searches; clarified the integer
node's remaining argument; trimmed the extension node's statement dependencies.
No existing mathematical statement or definition changed.

A bounded attempt to close the integer square reached explicit Γ/terminal-sections
naturality and categorical cancellation, but its full proof exceeded the required
60-second compilation limit. It was restored to the worker's single named hole; no
unverified proof, diagnostic option or partial-proof sorry is delivered. Experiments
remain only in the sandbox scratchpad and are excluded from the delivery.
