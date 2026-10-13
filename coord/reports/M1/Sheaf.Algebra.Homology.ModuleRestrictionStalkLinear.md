## What changed

The existing target module adds two plain proof imports and assembles its natural
transformation from linear components and their germ formula. The original target
signature, definitions, and public imports are unchanged. Two new modules state the
component construction and naturality. The second reader proved naturality directly
using Mathlib's germ representatives and stalk-map germ formula.

## Proved and sorry left

Hole closed in the original module:
`AlgebraicGeometry.exists_moduleRestrictionStalk_morphism`.
Its body constructs the natural transformation; it still depends on the open component
construction and is not yet a proof with only the three permitted axioms.

Hole added:
`AlgebraicGeometry.exists_moduleRestrictionStalk_components`
(node `new-module-restriction-stalk-components`). This is the only remaining `sorry`
in the delivery. Its statement is the component and scalar-compatibility part of the
original argument, without naturality or natural-transformation assembly.

The first worker also left `AlgebraicGeometry.moduleRestrictionStalk_components_natural`
(node `new-module-restriction-stalk-naturality`) open. The second reader closed this
hole. Thus the final delivery closes one original hole and adds one lower hole: a
net-zero decomposition, not completion of the target. Naturality itself is fully proved
using only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

No imports or modules from the original target module are pruned.
The original target's direct proof dependency `def-pc-module-stalk-functor` is replaced
by the two intermediate nodes; its module stays publicly imported because the target
statement uses its definitions. It remains a dependency of the intermediate nodes.

The naturality module no longer imports
`Sheaf.Algebra.Homology.ModuleRestrictionStalkComponents`: it needs the component
family and germ formula as hypotheses, not the component-existence theorem. Its
statement dependencies are imported directly, and its node no longer has
`new-module-restriction-stalk-components` as a proof dependency.

## Where the brief, the DAG or earlier work was wrong

The first report described two open intermediate lemmas as progress without explicitly
counting the resulting decomposition. The existing target node was missing from the
sandbox, leaving its proof route inconsistent with the new assembly. Both are repaired.
The new-node search records originally included queries/digests not substantiated by
this sandbox's search log, and the naturality node's recorded signature had different
line wrapping. The records now contain actual searches and verbatim Lean signatures.

## New nodes

`new-module-restriction-stalk-components` records the componentwise linear maps and germ
formula. It is true by the additive restriction-stalk comparison and compatibility of
germ scalar multiplication after inverse ring transport; its complete argument is in
its docstring. It remains open.

`new-module-restriction-stalk-naturality` records the naturality of any family satisfying
the germ formula. It is proved by representing an arbitrary stalk element as a germ,
rewriting both induced stalk maps, and using the assumed formulas. No existence theorem
is used to choose data for a definition. There are no change records or interface changes.

## Second reading by M1

1. PASS. Compared the target module with the repository using `diff`; its existing
   theorem signature is byte-for-byte identical, and its public imports and definitions
   are unchanged. The only original-module changes are two plain proof imports and the
   theorem body. The two additional modules contain new statements only.
2. PASS with the declared component hole. All three modules compile locally without
   warnings. No forbidden declarations or hollow definitions occur. Explicit
   `#print axioms` probes show only the permitted three axioms for naturality, and
   `sorryAx` for the component theorem and target, exactly as reported.
3. PASS. Both intermediate statements are true and separate scalar-compatible
   component construction from naturality. For W = X the component map is the usual
   identity comparison; the zero sheaf gives zero maps; W empty admits no hx, so adds
   no exceptional obligation. Naturality follows for every morphism, including zero
   and identity morphisms, because every source stalk element has a germ representative.
   Searched the library with restriction/stalk variants and Mathlib with different
   natural-language, Loogle, and grep queries; found the generic germ lemmas, no exact
   duplicate. LeanSearch was unavailable and is recorded as such. Checked Stacks
   [Lemma 6.31.1](https://stacks.math.columbia.edu/tag/009Z) and
   [Definition 6.31.2](https://stacks.math.columbia.edu/tag/00A1): they supply the
   restriction-stalk comparison and restricted module action.
4. PASS. The target opens its original hole and assembles the result from the two
   subarguments. Naturality now takes the shorter Mathlib germ route. Original target
   imports remain needed by its statement; the new naturality file's unnecessary
   component-existence import is removed. The unit sk-thm-picard-duality's realized
   record is unchanged (its statement/step lists were already empty); this is a local
   subargument and does not replace any unit or chapter step.
5. PASS after repair. The existing target node now describes the component/naturality
   assembly with the corresponding proof_deps and proof_origin. New nodes contain
   the required fields, real search records, and signatures copied verbatim from Lean.
   The naturality node describes the proved germ calculation and no longer depends on
   the component-existence theorem.

Second-reading changes: proved naturality; removed its unnecessary component-existence
import and node dependency; repaired the target's DAG proof route, new-node signature
and search records, and hole accounting. Component construction remains the sole split.
