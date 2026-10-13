## What changed

Completed `AlgebraicGeometry.Scheme.isPseudoCoherent_of_bounded_coherent` in
`Sheaf.AlgebraicGeometry.NoetherianBoundedCoherentPseudoCoherent` with the existing
lower-truncation triangle, coherent-sheaf pseudo-coherence, and distinguished-triangle
closure declarations. Added three proved private helpers: invariance under isomorphisms,
closure under shifts, and pseudo-coherence of zero objects. The zero helper constructs the
zero complex and proves its terms are free of rank zero; it chooses no arbitrary model
from an unproved existence theorem.

The proof inducts on a natural number k to show that truncation at b+1-k is pseudo-coherent.
Its base case is the zero truncation above the cohomological upper bound. Each induction
step applies `DerivedCategory.exists_lowerTruncationStepTriangle` with n equal to the
negative of the truncation degree and combines its outer terms using
`isPseudoCoherent_of_distinguished_triangle`. Taking k=(b+1-a).toNat gives a truncation
cutoff at most a, so its canonical projection from E is an isomorphism. This also handles
a>b, negative endpoints, and the empty scheme. All existing public signatures and imports
are preserved. Added two proof-only Mathlib imports for the t-structure and truncation API;
the triangle dependency's private imports do not export these APIs.

## Proved and sorry left

Closed the only original hole:
`AlgebraicGeometry.Scheme.isPseudoCoherent_of_bounded_coherent`
(node `lem-pc-noetherian-bounded-coherent-pseudo-coherent`).

Validation: the module compiles without warnings through `lcompile.py`. Explicit
`#print axioms` checks give only `propext`, `Classical.choice`, and `Quot.sound`
for all three private helpers. The main theorem additionally uses the existing
`sorryAx` through its imported, unfinished dependencies.

No sorry remains in this module, and no new sorry or node is added. The three private
helpers are fully proved. This is a proof from existing stated dependencies, not a claim
that its transitive dependencies are all sorry-free: the existing theorem
`AlgebraicGeometry.Scheme.isPseudoCoherent_of_distinguished_triangle` still has its
original sorry in its own module. Its proof is outside this item's scope.

## No longer needed

None. Every existing proof-dependency import is used: coherent sheaves supply the first
triangle term, the lower-truncation triangle supplies each step, and triangle closure
supplies the middle term. The standard t-structure and the definition of pseudo-coherence
are also used. No node or module of the existing plan is bypassed. Existing public imports
are retained to preserve this module's exported interface.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface correction was necessary. The DAG proof route is implemented
unchanged and therefore needs no node edit. The unit's realized statement/step list is not
bypassed. The proof does not need the informal preliminary assumption a≤b: choosing a
truncation cutoff at most a handles the empty interval directly.

The cited local Stacks TeX files are absent on this machine. Checked the cited results at
[Tag 08E8](https://stacks.math.columbia.edu/tag/08E8) and
[Tag 08CD](https://stacks.math.columbia.edu/tag/08CD). Searches through the prescribed
leanfinder, loogle, and grep interfaces and the two library roots found no direct theorem
that avoids the planned dependencies. The upstream generic bounded dévissage lemma would
require establishing a triangulated object property first, so the direct truncation
induction is shorter here.

## Second reading by D2

1. Interface: PASS. Compared the delivered module against the repository with `diff -u`
   and separately compared the complete existing theorem signature byte for byte. The
   signature, docstring, definitions, and existing public imports are unchanged. Only two
   private proof imports, three proved private helpers, and the theorem proof are added.
   No change record or forced adaptation is needed.
2. Proof: PASS. Independently compiled the delivered file and a scratch copy containing
   `#print axioms` for all four declarations with the required `lcompile.py`. Both compile
   without warnings. Each private helper uses only `propext`, `Classical.choice`, and
   `Quot.sound`; the main theorem additionally uses the permitted existing `sorryAx` from
   unfinished imported dependencies. There is no local sorry, forbidden declaration,
   hollow definition, or arbitrary object chosen from unproved existence. The zero model
   is the actual zero complex, with its terms proved free of rank zero.
3. Split statements: PASS (none). No hole, public statement, module, or node was split off.
   Checked the proved helpers directly: restriction transports isomorphisms; a shift by n
   changes the upper bound to b-n; the rank-zero free sheaf and zero complex are zero.
   Tested the induction's edge cases in the argument: k=0, a=b, a>b (k=0 and b+1<=a),
   arbitrary negative endpoints, and the empty scheme. The final cutoff inequality
   eliminates any need to assume a<=b.
4. Route and pruning: PASS. Independently searched with leanfinder for finite Postnikov
   towers and extension-closed properties, loogle for t-structures/object properties, and
   grep/rg in Mathlib and both library roots. Read the upstream
   `DerivedCategory.prop_of_bounded`; it requires triangulated-property and isomorphism
   instances not available here and does not improve this direct induction. All five
   existing proof dependencies are used. The HomologySequence public import provides
   `homologyFunctor` in the public signature; both added Mathlib imports are private and
   supply proof APIs no longer exported by the triangle dependency (also checked
   `coord/changes/LowerTruncationStepTriangleProofImports.md`). No import or dependency is
   newly dispensable. Read `dag/units/sk-thm-picard-duality.json`: its realized lists are
   empty and this node is not a realized unit statement or step. No unit route is bypassed.
5. DAG: PASS. Read the complete original node and all three imported theorem statements.
   The Lean proof implements its coherent-single-object, shift, successive-truncation,
   triangle-closure, and final-isomorphism route. Its `proof`, `proof_deps`, and
   `proof_origin` remain accurate; no new node is required.

Second reading changed only this report by adding the independent review and its evidence.
The Lean proof required no repair. Closed holes: one, named above. Added holes: none.
