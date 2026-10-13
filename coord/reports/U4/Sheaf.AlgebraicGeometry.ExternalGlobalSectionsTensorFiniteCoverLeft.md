## What changed

Proved `AlgebraicGeometry.Scheme.Modules.externalGlobalSectionsTensor_bijective_of_finite_cover_left`
from a first-factor restriction comparison, without changing its signature or existing docstring.
The proof uses the same categorical finite-limit argument as the already proved second-factor
module `Sheaf.AlgebraicGeometry.ExternalGlobalSectionsTensorFiniteCover`: a private proved
limit-comparison helper, pairwise sheaf limits, flatness of vector spaces and componentwise
isomorphism detection. No second-factor module is imported.

Added `Sheaf.AlgebraicGeometry.ExternalGlobalSectionsRestrictionComparisonLeft` with the concrete
pushforward presheaf and preimage-top section isomorphism, plus one residual theorem. It has no
cover or local-bijectivity assumptions: it isolates precisely the restriction compatibility,
not finite-cover descent. Its definitions are actual constructions and choose no witness from
an unproved theorem. The comparison witness is eliminated only within the main theorem proof.
Both modules compile locally (8.2 and 10.4 seconds in the first complete run).

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.Modules.externalGlobalSectionsTensor_bijective_of_finite_cover_left`
(node `lem-sc-external-global-sections-tensor-finite-cover-left`). The item's module has no sorry.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.exists_externalSectionsRestrictionComparisonLeft`
(node `lem-sc-external-global-sections-restriction-comparison-left`). Its proof is exactly
`:= by sorry` and its docstring spells out the construction, naturality, normalization and
open-subscheme coefficient comparison. This is a decomposition, with zero net holes closed,
not a sorry-free proof of the full theorem. The finite-cover/flat-limit part is fully proved.

The empty-index case needs no special hypothesis: Pairwise has a finite empty diagram and
both sheaf-limit arguments still apply. Empty opens, empty Y, and zero coefficients likewise
satisfy the new comparison statement by the same units and tensor equations.

## No longer needed

No existing import was removed: the original module only publicly imported its statement API.
No module is claimed pruned from the targets' closure. The adjunction, restriction and tensor
comparison nodes formerly cited directly now belong to the residual comparison's proof,
so they remain needed transitively. Explicitly, the old direct proof dependencies removed
from the item's `proof_deps` are:
- `lem-weil-pbc-open-immersion-module-pullback-restriction`;
- `lem-weil-pbc-module-restriction-open-immersion-colimits`;
- `def-weil-pbc-composite-adjunction`;
- `lem-weil-pbc-conjugate-iso-unit-equation`;
- `lem-weil-pbc-module-pullback-tensor`.

The first, third, fourth and fifth are direct proof dependencies of the residual comparison.
The second is retained through the open-immersion comparison's `stmt_deps`: the
restriction adjunction it defines is used by that comparison. Its colimit-preservation
and quasi-coherence conclusions are not used here. These are changes of direct edges,
not claims of pruning nodes from the targets' closure.

The second-factor finite-cover and restriction-comparison
modules were read as templates but are not dependencies of this delivery. The three new
proof-only imports of the item are all used.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed. The node's proposed equalizer argument lacked an
assembled first-factor restriction comparison, so that step is now a named residual item.
Some of its planned adjunction/open-restriction nodes have no `lean` record in this checkout;
this does not prevent making the finite-limit part into a complete Lean proof.

The local checkout has no `literature/stacks-project/varieties.tex`. Read the source directly
at https://stacks.math.columbia.edu/tag/0BED: the maps before equation-kunneth-on-cech and the
omitted degree-zero canonical-cup identification. The strengthened generality of the descent
lemma uses only restriction and finite sheaf limits, not the source theorem's quasi-coherent
or affine-diagonal hypotheses. The cube unit and its route are unchanged.

LeanFinder, Loogle, and Mathlib/source-library grep found tensor and restriction tools but
no first-factor assembled comparison. LeanSearch returned Internal Server Error and is recorded
as unavailable. Blueprint searches for external section restriction and Kunneth did not find
this first-factor comparison; the existing residual comparison is only for the second factor.

## New nodes

`lem-sc-external-global-sections-restriction-comparison-left` in
`dag/nodes/sec-abelian-varieties/` states the natural comparison of presheaves on X, with
normalization at top and component squares for all opens. It realizes step 1 of the original
node's plan, has no cover or bijectivity hypotheses, and leaves the finite-limit chase to
the main proof. The node contains the complete proof in words and the actual search records.
No change records or forced adaptations are needed.


## Second reading by U4

1. **Unchanged interface — pass.** Read the complete diff against the repository item:
   only three plain proof imports, a private proved limit helper and the theorem body
   were added. The existing theorem signature and docstring are byte-for-byte unchanged.
   The comparison module is new; there are no adapted modules or change records.
2. **Proof and constructions — pass with the declared residual hole.** Compiled both
   delivered modules together through `lcompile.py --all`. Scratch-copy `#print axioms`
   probes of the main theorem and all three public declarations of the new module show
   only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for the two theorems.
   The pushforward abbreviation and top isomorphism do not depend on `sorryAx`.
   The only literal sorry is the named residual theorem, with its complete docstring
   argument and node. There are no prohibited declarations or anonymous proof holes.
   The existential witnesses are eliminated inside a theorem proof; no definition
   selects data from this mere existence theorem.
3. **Residual statement — pass.** Read `scalarPresheaf`, `scalarObj`,
   `tensorPullbackTopSection`, `externalGlobalSectionsBilinear` and the tensor lift.
   The residual domain tensors F-sections on X with the unchanged G global sections;
   its codomain is the first-projection pushforward of the actual external coefficient.
   Its top equation normalizes to the existing canonical map. For each open the
   source and target isomorphisms have exactly the local types used by `hU` and `hUU`.
   Read Stacks Tag 0BED (maps preceding equation the project server and its final omitted
   degree-zero verification), and the existing open-immersion comparison node:
   restriction is left adjoint to pushforward and uniqueness compares its unit with
   the chosen tensor-pullback unit. Naturality and the pure tensor formulas give the
   asserted squares without quasi-coherence or an affine diagonal. At V=top the
   square and normalization concern the same global external map; at V=empty both
   section modules are zero. Empty X, empty Y and zero coefficients also give zero
   maps between zero modules. The residual has no cover or bijectivity assumptions,
   and leaves all finite-cover descent to the proved categorical argument: it does
   not restate the original item.
   Independently searched LeanFinder for naturality under open restriction, Loogle
   for `pushforwardSections`, and Mathlib grep for restriction/tensor combinations.
   Hits were open-immersion section naturality, `restrict_map`, `restrictFunctorComp`,
   and generic pushforward-section tools, not the assembled external comparison.
   Repository searches also found `exists_restriction_tensor_comparison` and
   `tensorPullback_unit_restriction_isIso`, which are coefficient/unit tools rather
   than the asserted scalar-linear presheaf comparison. The second-factor residual
   would additionally require a swap compatibility and is not a shorter ready proof.
4. **Shortest route and pruning — pass.** The local IsIso argument cancels genuine
   section isomorphisms; flat tensor preserves the finite Pairwise limit; continuous
   pushforward preserves the other sheaf limit. Componentwise isomorphisms then give
   the global one, including the empty finite diagram. All three added plain imports
   serve these steps; the public scalar comparison import is needed by the statement.
   No unused public API imports were introduced. Listed every removed old direct
   dependency explicitly above, distinguishing transitive use from module pruning.
   The cube unit and chapter route are unchanged. Its `realized` lists are already
   empty in the repository (an existing bookkeeping gap, not introduced here); this
   delivery changes neither that record nor any unit step and bypasses no unit.
5. **DAG agrees — pass.** The existing node's two new proof steps describe the
   comparison reduction and the exact finite-limit argument in Lean; `proof_deps`
   is their union. The new node has its self-contained statement, source, full
   construction argument, dependency union, searches, creation/blueprint metadata,
   chapter/unit and verbatim Lean theorem signature. The proof origin explicitly
   identifies the agent-written degree-zero compatibility omitted by Tag 0BED.

Second reading changed the pruning report to name all old direct dependencies and
explain the transitive restriction-adjunction dependency, added independent search
records to the new node, and recorded this review. No Lean proof or statement needed
repair. One original hole closed and one strictly smaller hole added: decomposition,
zero net holes closed; no modules pruned.
