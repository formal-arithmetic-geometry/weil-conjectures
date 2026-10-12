## What changed

Proved `AlgebraicGeometry.Scheme.closedImmersion_idealPower_image` without changing its
signature or public imports. The proof computes both inclusion ranges on affine opens,
compares their pure-product generators using the surjective structure map and
`Ideal.map_pow`, and constructs both subobject inequalities by lifting through kernels
of cokernel projections. Four fully proved private helpers implement the image-range,
pure-product-range, affine separatedness and kernel-lift arguments; their proofs follow
the already proved private helpers in `Sheaf.AlgebraicGeometry.AffinePushforwardIdealProduct`.

Added proof-only imports of
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine`,
`Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`,
`Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections`, and
`WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion`.
Updated the item's DAG proof and proof dependencies to match the Lean; the existing proof origin stays.
The item does not realize a unit-level step of `sk-thm-p1`; its unit's realized route stays.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.closedImmersion_idealPower_image`
(node `lem-weil-pbc-closed-immersion-ideal-power-image`), one of one original holes.
Added holes: none. Sorries left in delivered modules: none.
This is a proof from existing stated dependencies, not a new decomposition.
The existing dependency
`AlgebraicGeometry.Scheme.Modules.ideal_times_quasiCoherent_affine_sections`
(node `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`) remains sorry in the
library; this delivery uses its positive-power quasi-coherence and affine range clauses.
No claim is made that the resulting theorem has a sorry-free transitive axiom closure.

Local compilation passed with no warnings. The argument works unchanged for n = 1,
the zero and unit ideals, the zero module and empty affine opens: it never chooses a
point or a nonzero section. No finite-generation or Noetherian assumption was added.

## No longer needed

Removed direct proof imports:
`Sheaf.AlgebraicGeometry.ModulePullbackIdealQuotient` and
`WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism`.

Pruned the proof dependencies `lem-weil-pbc-module-pullback-ideal-quotient` and
`lem-weil-pbc-closed-immersion-affine-cover-criterion`: the bundled
pullback quotient theorem, quotient isomorphisms, kernel claims and naturality are
unnecessary here. The needed affine ideal-extension computation is the existing proved
source lemma `Scheme.IdealSheafData.ideal_comap_appLE`.
This also avoids directly importing
`Sheaf.AlgebraicGeometry.ModulePullbackIdealProductImage` through that quotient module. The
affine-cover criterion is unnecessary because the proof constructs the inverse-image affine
open directly and uses the existing ideal comap section formula.
No claim is made that these modules leave every other target's import closure.

Retained `lem-pc-closed-immersion-coherent-cohomology` for its recorded declaration
`isQuasicoherent_pushforward_of_isClosedImmersion`, imported from its actual narrower
module `WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion`.
Retained `lem-weil-pbc-affine-opens-basis`: the local helper uses its recorded Mathlib
match `Scheme.isBasis_affineOpens` directly. Thus all three retained old dependencies
and both removed old dependencies are accounted for.

## Where the brief, the DAG or earlier work was wrong

The proof plan is mathematically correct. It asks for the bundled
`modulePullbackIdealQuotient` only to obtain its first clause, although the underlying
source lemma is already proved and available directly; the proof uses that shorter route.
The cohomology node records the needed pushforward quasi-coherence theorem among its
additional declarations, but its primary module is the larger cohomology module;
this proof imports the actual module of the quasi-coherence theorem.
The local literature files cited by the node are absent on this machine; the node's
source was checked against https://stacks.math.columbia.edu/tag/088A and the existing
Lean dependency docstrings. No source, definition, public signature or unit route changed.

The first worker reported an import-cycle-checker API mismatch. The second reader's
ordinary `deliver3.py --no-push` invocation reached preflight without that error;
no alternate checker, preload, or tool modification was used by the second reader.

## Second reading by C2

1. **Interface: pass.** Read the complete repository/sandbox diff. The existing
`closedImmersion_idealPower_image` signature is byte-for-byte identical (also checked
by extracting the text before `:= by`); its visibility, docstring and both public
imports are unchanged. No definition or target statement changes; no change record
is needed. Only the proof, four private proved helpers, proof imports and author line
change in Lean.

2. **Proof and axioms: pass with the reported existing dependency.** Compiled the
item locally without errors or warnings through `lcompile.py`. A scratch copy printed
axioms for all five theorems: each private helper uses only `propext`,
`Classical.choice`, `Quot.sound`; the main theorem additionally uses `sorryAx` from
existing dependencies. No delivered `sorry`, forbidden declaration or attribute, or
hollow definition occurs. The proof constructs image objects and kernel lifts using
the categorical operations; it chooses no arbitrary data from an unproved existence
statement. Section lifts in the proof are propositional witnesses only.

3. **Split statements: pass (none).** No new hole or public statement is split off.
Read each helper: tensor pure products generate their additive subgroup, affine
separatedness detects zero, and vanishing against a monomorphism's cokernel gives
its kernel/image factorization. These statements require no nonempty affine, nonzero
ideal or module, finite generation or Noetherian hypotheses. Checked n = 1, zero/unit
ideals, zero modules, and empty affine opens mathematically. Independent repository
searches for ideal powers, affine ranges and subobject ranges found the related affine
pushforward theorem; its relevant helpers are private and cannot be imported as API.
A Loogle search confirmed `Ideal.map_pow`, already used by the proof.

4. **Route and pruning: pass after repair.** Read the existing affine-pushforward
proof and the imported section formulas. A direct application of that affine
pushforward theorem would additionally require identifying tensor pullback with the
chosen ideal-power object; the current direct range comparison avoids that step.
All proof imports have concrete uses: ideal comap sections, positive powers, affine
image ranges, tensor sections, and closed pushforward quasi-coherence. Both removed
imports are proof-only. The two pruned old nodes are fully listed above. Restored
`lem-weil-pbc-affine-opens-basis` to the DAG because its Mathlib match is used, rather
than claiming its pruning. The item's node is absent from the unit's `realized` route,
which is unchanged.

5. **DAG: pass after repair.** Read the original and delivered node, each dependency's
record and `dag/units/sk-thm-p1.json`. Only `proof` and `proof_deps` differ; the statement,
source, Lean signature record and unit stay identical. The union of the proof steps'
`uses` equals `proof_deps`. The comap node records the actual proved lemma, and the
cohomology node records the pushforward quasi-coherence declaration among its
additional declarations. The restored basis node records the exact Mathlib theorem
called in the helper. There are no new nodes.

**Second-reader changes:** restored the used affine-basis dependency in the final DAG
step and dependency list; clarified retained dependencies and the unchanged proof
origin in this report; recorded the successful ordinary tool invocation. No Lean proof
repair was necessary.
