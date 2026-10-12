## What changed

Decomposed `module_extensionByZero_unit_stalks` into two named intermediate theorems and imported them. The target theorem now combines the outside-U vanishing result with the inside-U isomorphism, linearity, and naturality result. The two intermediate proofs remain explicit `sorry`s for parallel completion.

## Proved and sorry left

The target `AlgebraicGeometry.Scheme.Modules.module_extensionByZero_unit_stalks` is proved by a real conjunction proof. The added declarations `module_extensionByZero_outside_stalk` and `module_extensionByZero_inside_stalk` remain as named `sorry`s, with nodes `new-extension-by-zero-outside-stalk` and `new-extension-by-zero-inside-stalk`.

## No longer needed

None; the target's original imports remain needed for its statement, and the two new modules use the same dependency imports.

## Where the brief, the DAG or earlier work was wrong

The DAG supplied no Lean declarations for the geometric stalk argument, so the single upper proof obligation was split into the independent outside and inside parts.

## New nodes

`new-extension-by-zero-outside-stalk` and `new-extension-by-zero-inside-stalk` are added under `dag/nodes/sec-proper-base-change/`.

## Earlier second reading (a previous round; superseded)

The decomposition was checked for strictness: the outside theorem removes the target's first conjunct, while the inside theorem supplies only the remaining map properties.

## Second reading by P3

1. **Statements and interfaces.** I diffed the delivered item module against the repository version. The
   original target signature is byte-for-byte unchanged; only proof imports and the proof body were added.
   The two added declarations have explicit, narrower signatures: the outside declaration proves only
   stalk vanishing, and the inside declaration proves only the inside map properties.
   **Verdict: pass.**

2. **Proof checks.** I compiled all three sandbox modules with `lcompile.py --all`; they compile without
   errors. The only remaining `sorry`s are the two named split-off theorems, each with a source and
   explanatory docstring. No definition contains `sorry`, and no forbidden `axiom`, `unsafe`, `opaque`,
   `extern`, or `implemented_by` declaration was added. **Verdict: pass, with the two documented holes
   left for later workers.**

3. **New statements.** I checked that neither split-off statement duplicates the target: the outside
   theorem omits all inside assertions, while the inside theorem is conditional on an adjunction and
   contains only the displayed inside map, isomorphism, linearity, and naturality properties. Searches
   found no existing declaration with either statement. **Verdict: pass.**

4. **Pruning and route.** The item proof applies exactly the two split-off results and introduces no
   unused import beyond the imports needed by those declarations. The unit route remains represented by
   the target node and its two proof dependencies; no unit step is bypassed. **Verdict: pass.**

5. **DAG consistency.** The target node records both new proof dependencies and the proof in the Lean
   file is the corresponding conjunction. Each new node records its Lean module and declaration,
   source, blueprint origin, and split status. **Verdict: pass.**

I added the two split-off modules and their node files, imported them privately in the item module, and
replaced the target `sorry` with the conjunction proof. No existing statement or definition was changed.
