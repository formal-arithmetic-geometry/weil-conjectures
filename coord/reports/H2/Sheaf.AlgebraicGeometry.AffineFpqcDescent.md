## What changed

Repaired `Sheaf.AlgebraicGeometry.AffineFpqcDescent`. Its theorem is now proved by applying the fpqc reduction, with affine base-change stability, a Lean proof that finite coproducts preserve `IsAffineHom`, and the affine flat descent theorem. Added `Sheaf.AlgebraicGeometry.AffineFlatDescent` as the strictly smaller affine-case statement The remaining affine-case proof plan uses the existing flat algebra descent module; that module is no longer imported directly by the item. The scope change is recorded in `coord/changes/AffineFpqcDescent-proof-scope.md`.

## Proved and sorry left

`CategoryTheory.Over.DescentDatum.isEffective_of_isAffineHom_fpqc` is proved. The affine flat case remains a named `sorry` in `CategoryTheory.Over.DescentDatum.isEffective_of_isAffineHom_flat_affine`, with node `lem-galois-affine-flat-descent-effective`.

## No longer needed

Removed the proof-only import `WeilConjectures.Mathlib.RingTheory.Flat.DescentAlgebra`
from the item. It belongs to the remaining affine-case argument. No public import is removed.
The separate `AffineSigmaMap` helper from an earlier attempt is not delivered; it was not an
import of the repository baseline. The coproduct proof is private in the item.

Every old direct proof dependency absent from the new item's `proof_deps` is listed here:

- Pruned from this argument: `lem-weil-pbc-spec-clopen-idempotent` and
  `lem-weil-pbc-principal-localization-open-immersion`. The open-cover pullback proof replaces
  the clopen/localization argument. Their modules are not asserted globally unreachable.
- Moved into the affine-case node's proof plan: `def-pc-scheme`, `def-pd-descent-datum`,
  `def-pc-fibre-product`, `def-weil-affine-spectrum`,
  `lem-weil-pbc-flat-ring-map-iff-flat-affine`,
  `lem-weil-pbc-algebra-tensor-pushout-universal-property`,
  `lem-weil-pbc-fibre-product-affine-spectra`, `def-weil-pbc-module-tensor-product`,
  and `lem-galois-flat-algebra-descent`. These are retained through the split, not globally pruned.

The new affine-case node does not depend on `lem-galois-fpqc-descending-types-morphisms`:
that reduction uses the affine case, rather than proving it.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's finite-coproduct proof used `sigmaMk` with an incorrectly inferred universe and tried to rewrite a cover pullback without unfolding `Cover.pullbackHom`. The repaired proof uses `Cover.exists_eq`, explicit `sigmaOpenCover_f`, and the pullback isomorphism. The affine case is too large for this item and is split into a strictly smaller theorem with the Stacks 0245 affine-case proof as its source.

## New nodes

`lem-galois-affine-flat-descent-effective` states the affine flat surjective case and is carried by `Sheaf.AlgebraicGeometry.AffineFlatDescent`; its proof remains open for a later worker. The associated change record is `coord/changes/AffineFpqcDescent-proof-scope.md`.

## Earlier second reading (a previous round; superseded)

Second reader: H2 worker. Read the item node, the affine-case node, and both Lean modules. The target theorem's hypotheses and conclusion are unchanged. The proof uses exactly the fpqc reduction's three hypotheses: base change, finite coproducts, and affine flat descent. The new affine-case statement is strictly smaller than the item and matches the affine part of Stacks Tag 0245; its `sorry` is named and documented. The private coproduct helper preserves the unit route and removes the unnecessary clopen localization dependencies.

## Second reading by H2

1. Compared both delivered modules with the repository. `AffineFlatDescent` is new.
   The complete existing `isEffective_of_isAffineHom_fpqc` signature is byte-for-byte
   unchanged. There are no existing definitions or other public declarations changed.
   All three existing public imports remain identical; added imports are proof-only.
   The change record now records the actual old/new commands and unchanged signature.

2. Both modules compile through `lcompile.py --all`, without errors or warnings.
   There is exactly one delivered `sorry`, the named affine-case theorem listed above.
   No forbidden declaration, hollow definition, or unreported `sorry` occurs.
   Scratch `#print axioms` checks show only `propext`, `Classical.choice`, `Quot.sound`
   for the private coproduct proof. The main and split theorems additionally use `sorryAx`:
   the split theorem is open, and the existing fpqc reduction is also still open.
   Thus the item's proof body is closed, while its theorem is not yet axiom-free.

3. The split statement is precisely the flat surjective affine-base/affine-cover case,
   rather than a renamed copy of the general singleton-fpqc theorem. Checked it against
   [Stacks Tag 0245](https://stacks.math.columbia.edu/tag/0245) and the existing
   `Algebra.DescentDatum.descendedEquiv` proof. Its docstring explains conversion to the
   algebra coaction, the counit and cocycle, invariant algebra descent, and transport
   compatibility. The corresponding node records these steps and the verbatim Lean
   signature. Independently searched Lean Finder, Loogle, Mathlib with other terms,
   and `lean/Sheaf` plus upstream scheme/algebra descent code. Existing results descend
   morphism properties or require a finite locally free cover; none closes this statement.
   The upstream algebra theorem closes only its algebraic step. Formal scratch examples
   verify effectivity for the identity cover directly from transport and verify the
   coproduct helper for the empty family. The singleton case is included in the helper's
   universally quantified proof. Empty affine schemes cause no excluded case: a
   surjective empty cover forces the base empty. No split can be closed by a short
   existing-lemma application found in these searches.

4. The top theorem applies the existing fpqc reduction, proving its base-change and
   finite-coproduct inputs and isolating its affine input. This follows the original
   Stacks/unit route. Read `dag/units/sk-prop-h2.json`: its Kummer statement, step,
   and `realized` record are unchanged, and this item is not a node named in `realized`.
   Imports are used by the signatures or this proof. The pruning section now accounts
   for every removed old direct dependency, distinguishing the two discarded arguments
   from the dependencies retained in the affine-case node.

5. Read both delivered node files alongside the Lean proofs. The main node's three
   steps and `proof_deps` match the reduction, coproduct proof, and affine-case call.
   The new node contains all required provenance, statement dependencies, real search
   records, blueprint ancestry, and Lean metadata. Its `proof_deps` is exactly the
   union of step uses. Removed the misleading fpqc-reduction dependency from its
   affine proof plan; it is needed only by the caller. No node statement was changed.

Changes by the second reader: restored the original author's attribution; completed
pruning documentation; corrected the scope-change record and the report's claim about
an algebra import; removed the redundant fpqc-reduction dependency from the new node;
recorded independent searches and the checks above. The compiling Lean proofs were
retained. Scratch checks are outside `lean/` and are not delivered.
