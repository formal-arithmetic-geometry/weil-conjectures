## What changed

Proved `AlgebraicGeometry.Scheme.Modules.finite_affine_pushforward_ideal_devissage`
without changing its signature or public imports. Three fully proved private helpers
construct the coherent ideal-product subobject, identify terminal-open and constant-integer
Ext cohomology, and prove first-cohomology vanishing of the ideal product. The target
combines these via the canonical underlying isomorphism and functorial transport of IsZero.
No definitions or statements used by other modules changed.

The construction uses finite-pushforward coherence, quasi-coherent tensor products and
images, coherent submodules, and the ideal-product stalk range formula. The vanishing
uses the affine projection formula, affine edge-map comparison, affine vanishing, and
module/abelian cohomology comparison. The terminal-open Ext identification follows the
already proved private construction in ModuleAbelianZariskiCohomology; it is repeated
locally because that helper is private. Empty schemes, zero modules, and the unit ideal
require no additional cases.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.finite_affine_pushforward_ideal_devissage`
(node `lem-weil-pbc-finite-affine-pushforward-ideal-devissage`), the module's only direct
sorry. All private helpers are proved. Holes added: none. Holes left in delivered
modules: none. The proof still uses existing stated dependencies with sorry, including
the ideal-product stalk calculation, coherent-submodule theorem, affine projection
formula, and affine cohomology edge theorem; this delivery does not claim these are proved.

## No longer needed

Removed proof-only imports `Sheaf.Paper.PQFCohomology` and
`Sheaf.Paper.ZariskiModuleAbelianCohomologyNatural`: the proof uses the component
comparison `module_cohomology_iso_underlying_abelian` from
`Sheaf.AlgebraicGeometry.ModuleAbelianZariskiCohomology`, without naturality or a
delta-functor structure. Removed the direct proof dependency `pqf-def-cohomology` from
the node. Its cohomology definitions remain through the unchanged statement imports.
The natural comparison module and its component node
`new-zariski-module-abelian-cohomology-components` are not needed by this proof.
No other planned dependency is pruned. This does not assert these modules are unreached
from every other target.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the stated result or its five-step route was found.
The terminal-open Ext-to-constant-integer Ext conversion is essential: affine vanishing
is stated for `Scheme.Modules.H`, whereas module cohomology comparison targets `Sheaf.H'`.
The proof supplies that conversion explicitly. A mere factorization through the ideal
product would not suffice to transport vanishing; the constructed subobject is actually
isomorphic to the whole ideal product, which the proof records and uses.

## Second reading by C2

1. **Statements and interfaces.** Compared the delivered module with the repository version. The target theorem signature and all existing declaration signatures are byte-for-byte unchanged; only proof code and proof-only imports differ. The DAG node statement and Lean declaration agree.

2. **Proof validity.** Compiled the module with `python3 /home/ubuntu/weil-launcher/lcompile.py`; it succeeds with no errors. The target contains no `sorry`, and the private helper proofs contain no axioms or prohibited constructs. The helper constructions are genuine image/subobject constructions rather than data selected from an unproved existence theorem.

3. **Split statements.** No new public or split-off theorem was added; hence no additional node or docstring proof is required. The existing node is proved directly using its stated dependencies.

4. **Pruning and route.** The proof follows the unit route through coherent ideal products, affine projection, affine vanishing, and the cohomology edge comparison. The removed imports `Sheaf.Paper.PQFCohomology` and `Sheaf.Paper.ZariskiModuleAbelianCohomologyNatural` are unused by the proof; the remaining imports are needed. The node's `proof_deps` and `## No longer needed` report match this route.

5. **DAG and unit agreement.** The node's proof, dependencies, and origin describe the implemented argument, and no unit step is bypassed. The terminal-open Ext identification and module/abelian comparison are explicitly present, so the affine vanishing step is transported correctly.

I changed only this report section; no Lean statements or definitions were altered during second reading.
