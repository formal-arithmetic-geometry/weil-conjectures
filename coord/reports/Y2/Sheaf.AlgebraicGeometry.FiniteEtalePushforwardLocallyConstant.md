## What changed

Proved `AlgebraicGeometry.Scheme.finiteLocallyConstant_lowerStar_of_finite_etale` in
`Sheaf.AlgebraicGeometry.FiniteEtalePushforwardLocallyConstant`, keeping its signature,
public imports, and existing docstring unchanged. Two proved private helpers implement
finite-product closure and the split-cover case. The main proof chooses a splitting
neighbourhood at every point, applies the split-cover product theorem, uses the existing
étale base-change isomorphism, and descends local constancy and finitely generated stalks.
The empty product is covered by the zero-sheaf case. No surjectivity hypothesis on `f`
is used; an empty target and zero-sheet neighbourhoods are allowed.

Added proof imports `WeilConjectures.SixFunctors.BaseChange.Etale`,
`WeilConjectures.ConstructibleSheaf.OpenClosed` (its proved zero-sheaf lemma), and
`Mathlib.CategoryTheory.ObjectProperty.FiniteProducts`. Both source imports pass
`tools/import_direction.py may`. Updated only the item's DAG proof, proof dependencies,
and proof origin to record the Lean argument. The item's unit is `sk-thm-p1`; none of
its realized statement or proof-step nodes is bypassed.

Local compilation passes without errors or warnings. The delivery dry run supplies
local and server compilation, the declaration/axiom probe, and preflight validation.

## Proved and sorry left

Proved the module's sole original sorry:
`AlgebraicGeometry.Scheme.finiteLocallyConstant_lowerStar_of_finite_etale`
(node `lem-weil-pbc-etale-finite-pushforward-locally-constant`).
The private helpers `finiteLocallyConstant_product` and
`finiteLocallyConstant_lowerStar_split` are also fully proved.
There are no sorries in the delivered module and no new modules or sorries.

The proof still uses the existing named theorem
`AlgebraicGeometry.directImage_splitCover_product`, node
`lem-weil-pbc-direct-image-split-cover-product`, whose proof is sorry in the base
library. This is the intended next proof dependency, not a new gap in this delivery.
The theorem is therefore reduced from its original sorry, not claimed to be free
of all transitive sorry dependencies.

## No longer needed

Removed explicit proof imports:

- `Sheaf.Paper.InverseImageStalkGerm`: germ compatibility is not needed; the proved
  module-valued `Etale.upperStarCompSheafFiberIso` suffices.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`: supplied transitively
  by the existing pullback/restriction APIs.
- `WeilConjectures.ConstructibleSheaf.Defs`: supplied transitively by Biproduct.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`: supplied
  transitively by the étale base-change module and split-cover product module.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: supplied transitively.

Removed proof-plan dependencies:
- `def-weil-sheaf-of-modules-category`.
- `lem-weil-pbc-cartesian-square-pasting`.
- `lem-weil-pbc-etale-base-change-finite-limits`.
- `lem-weil-pbc-finite-locally-constant-module-values`.
- `lem-weil-pbc-inverse-image-stalk-germ`.

The finite-module-values equivalence remains a statement dependency and its public
import is preserved. It is not used as a proof step because the goal already uses
the finite-local-constancy class. The removed germ module can still be reached
transitively through that public import; this report does not claim it is globally
unreachable from all targets. Cartesian pasting and étale base-change of schemes
are now encapsulated in the existing étale exchange theorem, rather than re-proved
in this module. No splitting/product/biproduct step is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The planned step 3 already has
a closed source-library implementation:
`Etale.isIso_baseChangeMap_flip_of_isPullback`, in
`WeilConjectures.SixFunctors.BaseChange.Etale`. It works directly for module sheaves,
so there is no need to construct componentwise linearity or a new base-change lemma.
Likewise the pullback, zero-sheaf, isomorphism-invariance and étale local-constancy
APIs are already proved. The finiteness descent step is implemented explicitly,
since the source's named finite-sheaf cover descent theorem is for open covers.

The literature files and blueprint section source named in the node are not copied
onto this worker machine; the supplied node's complete proof and the unit JSON were
read. No new sourced statement or node was needed. Three prescribed searches ran:
LeanFinder returned unrelated condensed-sheaf facts, Loogle did not know the project's
class name, and the grep service found no direct theorem. Local source search found
the APIs used above.

## Second reading by Y2

1. **Unchanged statements.** Compared the delivered module with the repository version. The target theorem signature and docstring are byte-for-byte unchanged; only proof imports and proof bodies changed. Verdict: pass.
2. **Proof and axioms.** Compiled the module with `lcompile.py`; it compiles cleanly with no warnings or sorries. The proof introduces no axioms, unsafe declarations, hollow definitions, or split-off theorems. Its only transitive open dependency is the existing named split-cover theorem recorded in the report. Verdict: pass.
3. **Statement strength and searches.** No new public statements or DAG nodes were added. The two private helpers are strict proof-local reductions (finite product closure and the split-cover case), and existing APIs were searched before use. Verdict: pass.
4. **Pruning and imports.** Removed proof-only imports and stale proof dependencies listed above. The proof follows the existing unit route: local splitting, split-cover product, etale base change, and descent. Verdict: pass.
5. **DAG agreement.** Updated the item's proof, proof dependencies, and proof origin to match the Lean proof; the unit `sk-thm-p1` and its realized route remain intact. Verdict: pass.

I changed only this report section after the first reading; no Lean declarations or statements required repair.
