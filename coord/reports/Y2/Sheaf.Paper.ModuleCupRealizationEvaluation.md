## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.Modules.moduleCup_realization_evaluation`
with a compiling proof, preserving its complete signature and public imports. Added private
helpers for surjectivity of resolution class maps, constructing paired cycles from Leibniz,
bilinearity on cycles, and descent through two surjective linear maps. The descent helpers
reuse the existing argument of `ModuleCohomologyCupProduct`, whose module cannot be imported
here because it depends on this item through `ModuleCupResolutionInvariance`.

Added `Sheaf.Paper.ModuleCupEqualDerivedMapsClass`, containing the single intermediate
statement that equal realized derived maps send equal input classes to equal output classes.
The main module first proves equality of the chosen derived maps using the existing
realization theorem, derived tensor connectivity, and injectivity of H-zero on morphisms
from a nonpositive object to a degree-zero object. It then constructs the bilinear map by
quotient descent and uses a constant evaluation family. This satisfies the unchanged
existential signature, which places no condition on evaluation at unrealized morphisms.
The supplied realization t is therefore unnecessary for the final descent step.

The new lemma isolates the diagram/class-identification part of the argument; it neither
asserts existence of any bilinear cohomology map nor performs quotient descent. Updated the
existing DAG proof and dependencies to follow this route. No existing definition or
statement changed, and no other existing module was adapted.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.moduleCup_realization_evaluation`
(node `lem-sc-module-cup-realization-evaluation`), one of one original holes.

Added and still sorry:
`AlgebraicGeometry.Scheme.Modules.moduleCup_equal_derived_maps_class`
(node `lem-sc-module-cup-equal-derived-maps-class`). Its proof is exactly `by sorry`,
in its own new module, with source and a complete natural-language diagram argument.

This is a decomposition: one upper hole closed and one strictly more primitive hole added,
net zero new mathematical closures. All private helpers in the main module are proved.
No sorry occurs in any definition. The product cycle chosen in a private definition is
uniquely determined by its prescribed underlying section; the surjective representative
choices occur only in a proved existential construction.

## No longer needed

Removed the direct proof import of `Sheaf.Paper.ModuleCupNaiveDerivedCompatibility`
from the main module. Its node `lem-sc-module-cup-naive-derived-compatibility` remains
needed by the new intermediate lemma, so its module is not pruned from the closure.
The old proof dependency `def-pc-scheme-derived-tensor-structure` is no longer a
direct proof dependency: no shifted-unit evaluation is constructed. Its definitions
remain necessary in the signature and are supplied transitively by the unchanged
public realization import. No original dependency module or node is completely pruned. The shifted-unit construction
of an evaluation varying with every derived morphism is unnecessary for this existential
statement; no existing module was identified as solely implementing that construction.

The original resolution data, module cohomology, tensor structure and realization nodes
remain needed. Added proof imports of the new intermediate module, pairing existence,
derived tensor connectivity. The latter already publicly imports the upstream
derived-category t-structure API through FlatModel and TorAmplitude; the second
reader removed its redundant direct proof import.

## Where the brief, the DAG or earlier work was wrong

The original proof plan specifies more structure on evaluation than the Lean signature
requires: no formula or naturality is required at arbitrary unrealized morphisms. A constant
family built by representative descent suffices, while the naive/derived compatibility
still supplies the crucial cocycle-class comparison. The unit record has no realized
statement or step attached to this node, and the route above the unit is unchanged.

The open lemma was checked at p=0 or q=0, zero coefficient sheaves and zero input cycles:
there is no positivity or flatness hypothesis hidden in it, and equality of realized maps
makes the conclusion true by functoriality of the derived cup diagram. It assumes equality
of the derived maps rather than trying to derive that equality; the latter is proved in
the main module from existing declarations. No reliance on the downstream resolution
invariance or cup-product theorem is introduced.

## New nodes

`lem-sc-module-cup-equal-derived-maps-class` in
`dag/nodes/sec-abelian-varieties/lem-sc-module-cup-equal-derived-maps-class.json`, realized
by `Sheaf.Paper.ModuleCupEqualDerivedMapsClass`. This is the cocycle-class equality
consequence of Stacks Lemma 20.31.3 under equality of supplied realized derived maps.
It carries the original comparison-to-injective-resolution and extension-by-zero work,
while existence and bilinear descent are performed in the main module.

No change record is required: existing signatures, definitions and public imports are
unchanged.

## Second reading by Y2

1. Compared the delivered main module with the repository using a textual diff and
checked the existing theorem signature byte for byte. Its signature, all existing
definitions, instances and public imports are unchanged. Only private helpers,
proof imports, and the theorem proof were added or changed. Verdict: pass.

2. Inspected both complete modules: the only explicit sorry is
`moduleCup_equal_derived_maps_class`, exactly the named hole listed above. No
forbidden declarations or hollow definitions occur. `cupPairCycle` chooses the
unique subtype element with a prescribed value from a proved existence theorem;
representatives and reference pairings are chosen only within proved existential
proofs. Local compilation and axiom results are recorded below. Verdict: pass; compilation and axiom checks succeeded.

3. Read the split lemma against the naive/derived compatibility theorem and the
Stacks global cup diagram (Section 20.31, Lemma 20.31.3). Equal transported derived
maps yield identical operations on classes; the comparisons over augmentations
identify those classes with the stated class maps. Degree zero needs no positivity
assumption; zero sheaves and zero representatives give zero by linearity. The
lemma assumes equality of supplied derived maps and does not construct any
bilinear descent or evaluation family, so it is strictly one part of the argument.
Its source, full diagram proof docstring and matching node are present. Repeated
LeanFinder, Loogle and grep searches with different queries: Ext representative
identifications are related infrastructure, not this theorem. Local searches find
resolution invariance and cup-product existence only downstream of this item;
importing them would create a cycle. Verdict: pass; the split remains open.

4. Read the proof from the final existential construction through descent and
class invariance. The constant family satisfies the unchanged existential
specification, whose restriction is only on realized maps. Each remaining added main-module
import supplies an actual proof dependency; removed the redundant direct upstream
t-structure import, already exported by the connectivity module. The new lemma retains its intended
proof dependency on the naive/derived diagram. The unit
`dag/units/sk-prop-av-cube.json` has empty realized statement and step lists; no
unit-level step is bypassed. Expanded No longer needed to account explicitly for
the removed direct derived-tensor-structure proof dependency. Verdict: pass.

5. Checked both nodes' Lean records and proof steps against their modules. The
existing node now records connectivity, equality of H-zero maps, class invariance,
cycle descent and the constant family, with proof_deps equal to the union of uses.
The new node has the required source, searches, creation, blueprint, unit, chapter
and verbatim Lean statement fields. No existing node statement changes. Verdict:
pass.

Second reading changes: clarified the removed direct DAG dependency in this
report and removed the redundant direct t-structure proof import; retained the
correct Lean proofs and split statement. This delivery closes
one original hole and adds one smaller hole: a decomposition, with net zero.

Compilation and axioms: both modules compiled locally without warnings. Scratch
copies with `#print axioms` for both public theorems printed exactly `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx`, the last coming from the explicitly
open intermediate and imported statements. The final delivery dry run also runs
the all-declaration axiom probe.
