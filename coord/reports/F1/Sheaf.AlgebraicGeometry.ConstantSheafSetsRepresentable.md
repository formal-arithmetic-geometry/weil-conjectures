## What changed

Proved `AlgebraicGeometry.Scheme.constantSheaf_sets_representable` with its original
signature and unchanged `constantSetCoproductPresheaf` definition. Added one proof-only
import, `Mathlib.CategoryTheory.Sites.LocallyBijective`; all original imports remain used.
No other Lean module changed.

The canonical map sends a constant to the structure morphism followed by its coprojection;
its over-base equation and naturality are proved directly. The represented presheaf is a
sheaf by `AlgebraicGeometry.smallEtaleRepresentablePresheaf_isSheaf`, then Mathlib's
universe-lifting sheaf criterion. Part (c) of
`AlgebraicGeometry.coproductCopiesMorphismsClopen` proves local injectivity: distinct
constants with equal images force the domain to be empty, and the empty family covers it.
Part (a) gives the covering by open component preimages and their constant restrictions,
which proves local surjectivity.

`sheafifyLift` constructs the comparison. Its factorization and the local bijectivity of
the sheafification unit transfer the two local conditions to that comparison; Mathlib's
sheaf local-bijection criterion proves it is an isomorphism. `sheafifyLift_unique` proves
the required uniqueness. No separate gluing construction of the inverse is needed.

Updated the item's DAG proof, proof dependencies, and proof origin to follow these steps.
Recorded the set-valued Mathlib local-bijection criterion as a new node referencing an
existing declaration, without adding a Lean module. The older analogous DAG leaf
`lem-weil-pbc-site-sheafification-iso-locally-bijective` states the abelian-group case,
so it cannot serve as the set-valued statement unchanged.

Local compilation passed without warnings. The Lean statement handles arbitrary `E`,
including the empty index set, and empty schemes; it adds no nonemptiness, connectedness,
or finiteness hypothesis. The unit record `dag/units/sk-prop-h2.json` has no realized
statement or proof step in this module, and no unit route is bypassed.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.constantSheaf_sets_representable`
(node `lem-galois-constant-sheaf-sets-representable`): 1 of 1 original sorries removed.
No sorry remains in the item's module. No new sorry or split-off theorem was introduced.

The proof uses the existing stated geometric dependencies
`AlgebraicGeometry.coproductCopiesMorphismsClopen`
(node `lem-galois-coproduct-copies-morphisms-clopen`) and
`AlgebraicGeometry.smallEtaleRepresentablePresheaf_isSheaf`
(node `lem-weil-pbc-small-etale-representable-presheaf-sheaf`). Their proofs still contain
sorry in the repository; they are unchanged and remain the next work items. Thus this
is a stage-3 proof from the existing stated dependencies, not a claim that the entire
axiom closure is already sorry-free. The new node references a proved Mathlib lemma.

## No longer needed

No imports removed. No original dependency node or module is pruned: the two geometric
modules are both used, and the original Mathlib leaves supply coproducts, the site,
open-immersion/etale instances, sheaves, constants, and sheafification.

The manual second universal-property argument of old Steps 3–4 is unnecessary, including
the overlap-empty gluing calculation and construction/checking of a second inverse.
Mathlib's local-bijection and sheafification APIs supply that categorical comparison.
Those arguments had no separate outstanding DAG nodes to remove. Parts (b), the two
bijections, and the explicit empty-coproduct clause of the clopen theorem are not used;
parts (a) and (c) suffice, so its module remains required.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or signature correction was needed. The original DAG plan
works but duplicates general sheafification theory already proved in Mathlib. The
source library's analogous continuous-map comparison is restricted to abelian groups;
its local-bijection proof pattern applies here without introducing a group structure.

The local `literature/stacks-project/` files named by the node are absent on this machine.
Read the sources online instead: [03P5](https://stacks.math.columbia.edu/tag/03P5),
[03YW](https://stacks.math.columbia.edu/tag/03YW), and
[03O3](https://stacks.math.columbia.edu/tag/03O3). The group structures in 03P5 and 03YW
are unused in the underlying set-valued representability and local-cover arguments.
LeanSearch returned Internal Server Error for the new categorical leaf; this is recorded
as an unavailable search. Loogle and the pinned Mathlib sources confirm the exact lemma.

## New nodes

`lem-galois-set-sheaf-local-bijection-isomorphism`, in
`dag/nodes/sec-curve-estimates/lem-galois-set-sheaf-local-bijection-isomorphism.json`,
records the set-valued specialization of the existing proved Mathlib declaration
`CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`, with its complete gluing proof,
three recorded kinds of search, and its Mathlib match. It introduces no Lean file or
sorry and is a dependency of the item's final comparison step. No change record is
needed: no definition, statement, public import, or public declaration set changed.


## Second reading by F1

1. **Visible declarations: pass.** Read the entire module and its repository diff.
   Both existing declaration signatures are byte for byte unchanged, as is the body
   of `constantSetCoproductPresheaf`. The declaration comparison reports no statement
   change, no new declaration and no new sorry. The only added import is the plain,
   proof-only `Mathlib.CategoryTheory.Sites.LocallyBijective`. The local transparency
   option affects elaboration, not the kernel or the theorem statement. No change
   record is needed.

2. **Proof and axioms: pass as a stage-3 reduction.** Local compilation succeeds
   without warnings. No sorry or forbidden declaration occurs in the delivered
   module, and there is no hollow definition. Compiled a scratch copy with
   `#print axioms` for both declarations and the Mathlib comparison criterion.
   The presheaf abbreviation and Mathlib criterion use only `propext`,
   `Classical.choice`, `Quot.sound`; the proved theorem additionally uses `sorryAx`
   through the existing open geometric dependencies listed above. Read their actual
   signatures: part (a) of `coproductCopiesMorphismsClopen` supplies the component
   restrictions and covering union; part (c) supplies the constant-component
   preimages. `smallEtaleRepresentablePresheaf_isSheaf` applies with the codiagonal
   as the structure morphism and the covering sieve's arrows. The proof constructs
   the canonical map, establishes both local conditions, and obtains the unique
   isomorphism from Mathlib's sheafification API; it does not restate the item.

3. **Split statements and new node: pass after metadata repair.** No new Lean
   statement or split-off sorry was introduced. Read the new set-valued Mathlib
   node against `Sites/LocallyBijective.lean` lines 43-93: its two directions are
   exactly the type-valued specialization, including the implicit forgetful-functor
   instances. Its written gluing argument uses separatedness on overlaps, then
   existence and uniqueness of the amalgamation. On an empty object, covering by
   the empty sieve forces a sheaf of sets to have exactly one section, so this
   criterion still applies. Searched with a different LeanFinder query about
   sheafification via disjoint unions, repeated the Loogle criterion query, and
   searched the library for constant-sheaf representability and the DAG/blueprint
   records for local bijectivity. No shorter exact theorem was found; the existing
   DAG leaf concerns presheaves of abelian groups. Corrected the new node's grep
   query to the actual logged query and added its missing `blueprint.same_as: []`.

4. **Route and pruning: pass.** Checked all imports against their uses: Limits
   supplies scheme coproducts, Etale supplies the site, ConstantSheaf supplies
   the constant-sheaf statement, and LeftExact supplies the sheafification instance
   needed to elaborate that statement. Both geometric imports are proof-only and
   used; the new local-bijection import supplies the final comparison. Read the
   upstream abelian-group continuous-map comparison; it is not the set-valued
   representability statement. The Mathlib route already avoids a redundant
   inverse/gluing construction. Compared old and new `proof_deps`: none is removed,
   so `## No longer needed` is complete. Read `dag/units/sk-prop-h2.json`: its
   `realized.statement` and only `realized.steps` entry are empty, so this change
   bypasses no realized unit statement or step. Checked arbitrary and empty `E`,
   empty base/domain, and disconnected domains: no connectedness, finiteness or
   nonemptiness is assumed. In particular the local-injectivity empty covering
   and the local-surjectivity possibly empty indexed cover are explicit.

5. **DAG agreement: pass after metadata repair.** Only `proof`, `proof_deps` and
   `proof_origin` change in the existing node. The union of the steps' `uses` is
   exactly `proof_deps`. Followed the four steps against the actual Lean code:
   representable sheaf/canonical map, local injectivity, component-cover local
   surjectivity, and unique sheafification comparison. Read Stacks
   [03P5](https://stacks.math.columbia.edu/tag/03P5),
   [03YW](https://stacks.math.columbia.edu/tag/03YW), and
   [03O3](https://stacks.math.columbia.edu/tag/03O3) online: the underlying
   component and representability arguments do not use the group law. The new
   node references an already proved Mathlib declaration, carries the item's
   chapter/unit and provenance, and adds no Lean module or outstanding proof.

**Changes made by the second reader:** repaired the new node's missing
`blueprint.same_as` field and its grep query to match the recorded search; added
this reading and its independent verification. The Lean proof is unchanged.
