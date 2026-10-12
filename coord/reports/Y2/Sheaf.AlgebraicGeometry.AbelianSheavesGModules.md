## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.abelianSheaves_equiv_discreteGModules`
with a compiling composition of two independent parts of Stacks 04JQ. Its signature is
unchanged. The proof obtains the canonical set-valued equivalence, lifts it by a generic
abelian group-object theorem, applies the set-valued action formula to the forgotten
abelian sheaf, and transfers the resulting equality to the additive stalk.

Added `Sheaf.AlgebraicGeometry.AbelianSheavesGModulesAction` (canonical set equivalence
for an arbitrary algebraically closed extension) and
`Sheaf.AlgebraicGeometry.AbelianSheavesGModulesData` (generic lifting over any site and
point of the indicated universes). These are genuinely separate steps: the former contains
no abelian sheaves or integer representations, and the latter contains no fields or Galois
actions and only transfers an already supplied equality of germs. Neither restates the item.

The original public imports and declaration signature remain unchanged. New imports in the
item are proof-only. Suppressed the unused-binder linter locally on the original theorem:
its action hypotheses are deliberately preserved verbatim, including their binder names.

## Proved and sorry left

The item's sole sorry is reduced by the complete Lean proof of
`AlgebraicGeometry.Scheme.abelianSheaves_equiv_discreteGModules`. This is a reduction,
not an axiom-free closure of the target's dependency tree. Exactly two sorries are added:

- `AlgebraicGeometry.Scheme.abelianSheaves_equiv_discreteGModules_action`, node
  `lem-exc-abelian-sheaves-gmodules-action`: the canonical set-valued equivalence for
  arbitrary algebraically closed Omega, with its action-on-germs formula.
- `AlgebraicGeometry.Scheme.abelianSheaves_equiv_discreteGModules_core`, node
  `lem-exc-abelian-sheaves-gmodules-core`: the generic categorical abelian lifting and
  compatibility implication for germs.

Both are public named theorems with their whole proof `by sorry`. Both have a source,
a complete natural-language argument, and a matching new node. Small cases checked:
trivial G, separably closed K, zero abelian sheaf, empty section sets, and nonalgebraic
Omega. The generic lifting works for any comparison j, since natural isomorphisms of
cartesian functors preserve the transported group operations. It does not assert canonical
Galois-action formulas for arbitrary comparison isomorphisms.

## No longer needed

Removed the item's direct proof imports of `Sheaf.AlgebraicGeometry.EtaleSheaves`,
`Sheaf.AlgebraicGeometry.Sites.EtaleSheavesGsetsPoint`, and
`Sheaf.CategoryTheory.EquivalenceInternalModule`. The latter two are not globally pruned:
their underlying arguments remain in the new nodes' plans. The internal-module theorem
alone does not provide the identifications with concrete abelian sheaves and integer
representations; the generic lifting node records that missing categorical step.

The new canonical set theorem omits the original set theorem's representable-stalk
comparison and its naturality formula, which the abelian enhancement does not need as
conclusions. Their use inside the proof of the set equivalence is retained. No unit statement
or realized unit step is bypassed. There is no claim that an entire existing module has
become unreachable from all other targets.

For the parent's old `proof_deps`, all four direct edges are replaced by the two
new nodes: `lem-exc-etale-sheaves-gsets-point`, `def-weil-pbc-geometric-stalks`,
`def-weil-pbc-etale-sheaves`, and `lem-pod-equivalence-induces-module-objects`.
The point definition remains used in the new set-valued statement; the internal-module
transport remains in the generic lifting plan. The set-valued node's original geometric
and invariant-section substeps also remain. Their modules are imported privately by the
new open lemmas so that the proof plans remain visible to the import-based queue.
`Sheaf.AlgebraicGeometry.EtaleSheaves` supplies locally constant sheaf definitions that
this argument never uses. No assertion of global unreachability is made.

## Where the brief, the DAG or earlier work was wrong

The stated proof dependencies do not directly compose at the Lean interface. The existing
`AlgebraicGeometry.etaleSheavesGsetsPoint` assumes `[IsAlgClosure K Omega]`; this item
correctly permits arbitrary algebraically closed Omega. Its carrier universe also has a
different shape. The new set-valued statement isolates exactly the needed version of
Stacks 03QT/03QW, which explicitly permits nonalgebraic geometric points.

`equivalence_induces_internalModules` transports internal modules, but does not identify
internal integer modules with abelian sheaves or arbitrary discrete integer representations.
Its second theorem addresses finite actions only. The general abelian lifting is therefore
not an application of either existing declaration alone.

LeanFinder returned condensed-module equivalences; Loogle returned sheaf congruences
induced by equivalences of sites. Neither supplies the needed value-category lifting or
Galois action. Grep found the useful `GrothendieckTopology.Point.sheafFiberCompIso` for
the future proof of generic lifting. LeanSearch returned Internal Server Error, recorded as
unavailable rather than as a negative search. Source text was checked at the official Stacks
tags 04JQ, 03QT and 03QW; the cited local literature file is absent on this clone.

## New nodes

`lem-exc-abelian-sheaves-gmodules-action`, in
`lean/Sheaf/AlgebraicGeometry/AbelianSheavesGModulesAction.lean`, isolates the set-valued
part of Stacks 03QT/03QW in the universes and geometric-point generality needed by the item.
Its proof plan retains the original set-valued node's four steps and dependencies.

`lem-exc-abelian-sheaves-gmodules-core`, in
`lean/Sheaf/AlgebraicGeometry/AbelianSheavesGModulesData.lean`, isolates the formal
abelian group-object lifting from Stacks 04JQ, with the stalk and germ comparisons needed
for action compatibility. No existing statement or definition was changed, so no change
record is needed. Both new nodes remain in the parent's chapter and unit. Neither node
has a dependency on its parent; the resulting graph has no new circular proof.

## Second reading by Y2

1. Compared the item with the repository using `diff -u`, then checked its declaration
   signature byte for byte with a script: identical. Its original public imports are
   identical. The only existing-node fields changed are `proof`, `proof_deps`, and
   `proof_origin`. No existing definition, statement, target, or change record is altered.
2. Compiled all three delivered modules locally in import order without errors or
   warnings. Compiled scratch copies with `#print axioms` for each of the three theorems:
   only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The item has no direct
   sorry; precisely the two reported public split lemmas have `by sorry`. No forbidden
   declaration or hollow definition occurs. This is a reduction, not an axiom-free proof.
3. Read both new statements, their proofs in words, their nodes, and Stacks
   [04JQ](https://stacks.math.columbia.edu/tag/04JQ),
   [03QT](https://stacks.math.columbia.edu/tag/03QT), and
   [03QW](https://stacks.math.columbia.edu/tag/03QW). The action lemma is the set-valued
   step, without abelian data; the core assumes that step and supplies the categorical
   lifting for any site and group. Neither is a renamed copy of the item. Checked trivial
   G, separably closed and imperfect K, nonalgebraic Omega, zero abelian sheaf, empty
   set-valued sheaf, and sets whose cardinality exceeds the site universe. Naturality of
   an arbitrary comparison j with group operations makes the core valid even when j is
   not the canonical comparison. Fresh LeanFinder queries about commutative group objects
   in sheaves and nonalgebraic geometric points returned no matching theorem. Loogle on
   `CategoryTheory.GrothendieckTopology.Point.sheafFiberCompIso` returned the useful
   comparison and its component formulas, which alone do not prove the lifting. A second
   Loogle query using `CategoryTheory.Action` was invalid (unknown identifier), so is not
   evidence of absence. Grep of Mathlib and both library roots found the existing
   algebraic-point theorem and internal-module transport, whose signatures were read;
   neither closes either split lemma in a few minutes.
4. Read the original dependency modules and `dag/units/sk-prop-h2.json`: the original
   set-equivalence/abelian-transport route is retained. Its unit has empty `realized`
   lists, and no unit record is changed. The parent's four removed direct dependency
   edges are now all listed above; retained substeps have proof-only imports in the new
   open modules. Trimmed public imports used by neither new signature: integer
   representations from the action module, and the explicit Krull-topology imports;
   replaced EtalePoint by Point.Basic in the generic core. The public EtaleFieldGsets
   import remains needed for its discrete topology instance on Type.
5. Checked each node's recorded Lean signature against the file (whitespace normalized),
   each `proof_deps` against the union of the proof steps' `uses`, and both new nodes'
   source, creation, blueprint, chapter/unit, search, and Lean records. The parent proof
   now describes exactly the two obtain steps, the forgotten sheaf, and the transferred
   equality in the Lean proof. No circular edge is introduced.

Second reading changed the action lemma's natural-language proof and DAG plan in two
places: compare through the algebraic subfield of Omega before applying the existing
invariant-section lemma (it assumes an algebraic point), and use a coproduct of finite-orbit
representable sheaves rather than an oversized coproduct scheme for essential surjectivity.
Also made the core's compatibility proof explicit using the equation
`gamma ∘ forget(i) = j ∘ forget(beta)`, equivariance of beta, and injectivity of gamma;
trimmed unused new public imports, restored private imports for the open proof plans,
and completed the pruning record. No Lean statement or proof term needed repair.
