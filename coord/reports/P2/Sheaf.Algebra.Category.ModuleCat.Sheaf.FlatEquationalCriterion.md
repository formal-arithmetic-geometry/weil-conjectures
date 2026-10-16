## What changed

Proved `SheafOfModules.isFlat_iff_local_equationalCriterion` with its signature unchanged.
The forward implication uses the coefficient ideal on the slice site and Mathlib's
finite-generator tensor criterion. The converse proves the finite-matrix criterion by
induction, proves finite witnesses for a zero tensor image using a free presentation,
and proves preservation of monomorphisms. Closed monoidality and the additive exact-functor
API then prove flatness. All auxiliary results are private and proved in the same module;
there are no new statement modules or changes to existing definitions.

Added proof imports for presheaf submodules, the closed symmetric monoidal and additive APIs,
Mathlib's finite tensor-vanishing criterion, and the categorical exact-functor API. Updated the
existing DAG node's proof, proof_deps and proof_origin to follow this route. Public imports
and the theorem signature are unchanged. The conservative command-interface check is
documented in `coord/changes/flat-equational-criterion-private-proof-setup.md`; it concerns
local proof setup only, with no dependent adaptation.

## Proved and sorry left

Closed the sole original hole:
`SheafOfModules.isFlat_iff_local_equationalCriterion`
(node `lem-weil-pbc-site-flat-equational-criterion`). Proved 1 of 1; added 0 holes.
No `sorry` remains in the delivered module, and no new module is added.

The proof still uses the existing `SheafOfModules.isFlat_over`
(node `lem-weil-pbc-slice-restriction-flat`), which is a separate existing obligation.
Thus this is a proof from that stated dependency, not a claim that the target's full
axiom closure is already closed. Single-file compilation passes without warnings. The downstream scan found 504 transitive
importers and no textual use of the theorem outside its declaring module; no downstream
adaptation is needed.
The finite-matrix induction handles zero columns by the identity covering and identity
matrix; the algebraic argument also allows empty supports and empty index sets.

## No longer needed

Removed these direct proof imports (the second reader also removed the redundant
`Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`, already public through
`SliceRestrictionFlat`, and `Mathlib.CategoryTheory.Abelian.Exact`, already public through
`ShortComplex.ExactFunctor`):

- `Sheaf.Paper.SiteSheafificationSectionsLocal`
  (`lem-weil-pbc-site-sheafification-sections-local`): Mathlib's additive sheafification
  unit is locally injective and supplies exactly the local-zero fact used here.
- `Mathlib.Algebra.Homology.ExactSequence`
  (`def-weil-pbc-exact-sequence`): the proof uses the homology-preservation criterion
  directly, without constructing the planned explicit exact complex of sheaves.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: the unchanged statement and proof
  use `IsFlat` from the existing `Flat` module, not the alternate site-flatness API.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
  (`def-pur-sheaf-tensor-product`'s currently recorded generalized-universe attachment):
  the theorem has one universe and uses the already-public monoidal tensor/sheafification
  comparisons from `Flat` and `TensorProduct`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
  (`def-weil-pbc-sites-and-cohomology`'s current attachment): the statement's existing
  Mathlib precoverage hypotheses already provide every covering operation used.

The first two node ids and the generalized tensor node are removed from proof_deps;
the site node is also removed from proof_deps, while its statement-dependency entry stays.
The original planned kernel-of-a-row sheaf construction and local lifts through that
kernel are unnecessary: the ideal argument replaces them. The explicit sheaf-cokernel
descent argument at the end is replaced by the existing closed monoidal and exact-functor
APIs. No claim is made that these modules are globally unreachable from other items;
`FlatOnSite` in particular remains a dependency of the existing slice-flatness item.

## Where the brief, the DAG or earlier work was wrong

No false statement was found and no statement was changed. The DAG's forward presentation
kernel route is longer than the source's ideal argument combined with Mathlib's existing
finite-generator tensor lemma. Its final manual proof of tensor right exactness is
unnecessary because the library already has a closed symmetric monoidal structure.
The generalized-universe tensor and alternate site-covering attachments are not needed
for this unchanged same-universe statement. The new private lemmas implement the existing
node's proof steps rather than introducing any further obligations.

The shared delivery cache repeatedly re-entered `load` as the shared repository revision
advanced, leaving the downstream scan waiting for about sixteen minutes and the second
dry run waiting in preflight. The interrupted scan's stack showed repeated
`delivery_cache._load -> load` recursion ending at `library-builder.lock`. Validation was
rerun using the tooling's built-in `WEIL_DELIVERY_CACHE_DISABLE=1` source-scanning mode;
this changes caching only and retains every delivery/preflight check. No tool was edited.

## Second reading by P2

1. **Interfaces — pass.** Diffed the complete module and node against the shared repository.
The existing theorem signature is byte-for-byte identical; its public imports are identical.
All new helpers and the coefficient-ideal construction are private. The change record
accounts for local proof setup, with no public definition or global instance change.
Only `proof`, `proof_deps`, and `proof_origin` differ in the node.

2. **Proof — pass.** Read every helper and the final proof, then compiled the delivered
module with `lcompile.py` without warnings. A scratch copy appending `#print axioms` for
the target, `isFlat_over`, and all eight named helpers also compiled. All helpers except
`flat_equational_forward` use only `propext`, `Classical.choice`, and `Quot.sound`.
The forward helper and target additionally use `sorryAx` through the existing
`SheafOfModules.isFlat_over` obligation. No prohibited declaration, local hole, or hollow
definition is present: `coefficientIdeal` is the actual sectionwise span with proved
restriction stability. No arbitrary witness is chosen from an unproved existence theorem.

3. **Split statements and edge cases — pass.** No holes or split-off statements were added.
The free-presentation witness uses surjectivity of the explicitly defined evaluation map,
right exactness, and finite supports; it does not assume injectivity of the input map.
The finite-matrix base case uses the identity covering and identity matrix and covers
zero rows/columns, empty supports, and the zero ring. In the induction step the substituted
relations are pulled back before matrix multiplication, and composition of coverings is
explicit. In the local-kernel argument, sectionwise injectivity is used only after applying
the original presheaf monomorphism. No extra flatness hypothesis enters the converse.

4. **Shortest route, imports, and units — pass after import cleanup.** A fresh LeanFinder
query, "Flatness criterion for sheaves of modules via locally trivial finite linear
relations", found ordinary-module flatness and finite-presentation sheaf APIs, but no
replacement arbitrary-site theorem. A source search under both Lean roots found no other
local equational criterion. The forward ideal argument uses Mathlib's existing finite
tensor-vanishing lemma directly. The converse retains the finite-matrix reduction and
uses the existing closed monoidal and exact-functor APIs. Checked
`dag/units/sk-thm-properbasechange.json`: this auxiliary node is not a unit statement or
realized unit step, so these internal reductions preserve the unit route. The four old
proof dependency nodes removed are all listed under No longer needed; no global pruning
claim is made for modules that other items still import.

5. **DAG — pass.** Checked all six revised proof steps against the helpers and final proof.
The union of their `uses` is exactly `proof_deps`. `isFlat_over` is the existing slice
flatness declaration; `SheafOfModules.over` is the localized-ringed-site Mathlib match;
`lTensor_exact` is the ordinary tensor right-exactness match. The node statement,
statement dependencies, source, and unit metadata are unchanged.

Second reading changed only proof imports and this report: removed the two redundant
imports above and replaced `Mathlib.RingTheory.Flat.EquationalCriterion` by the narrower
`Mathlib.LinearAlgebra.TensorProduct.Vanishing`, which defines both tensor-vanishing lemmas
used. Recompiled successfully after these changes. No proof-body repair was necessary.
