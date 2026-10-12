## What changed

Proved `TopCat.Sheaf.constantSubsheaf_peel_layer` in
`Sheaf.Topology.ConstantSubsheafPeelLayer` without changing its signature. The proof
constructs the short complex, proves its composite vanishes by stalk detection using
Mathlib's `TopCat.Presheaf.section_ext`, and checks short exactness in the three regions
V, U minus V, and outside U. It uses `exact_iff_epi`, `exact_iff_mono`, and
`exact_of_isZero_X₂` for those cases, with the existing extension-stalk and stalkwise
short-exactness declarations. The final object isomorphisms are identities.

Split the finite-generator construction and the independent nested-open inclusion into
two public intermediate theorems in new modules. These are separate parts of the
argument: neither asserts the parent's short exact complex, and the nested-open lemma
has no subsheaf, generation, bound, compactness, or quotient hypotheses. The quotient
construction supplies a morphism and local stalk data; the parent actually proves its
compatibility with the first arrow and the exactness assertions.

Updated the parent DAG proof to match the Lean assembly. Sources 0A38 and 00A5 were read
at https://stacks.math.columbia.edu/tag/0A38 and
https://stacks.math.columbia.edu/tag/00A5 because this clone lacks the cited TeX files.
No existing definition or statement was changed. No unit or chapter route was bypassed.
All three sandbox modules compile cleanly with the required local compiler.

## Proved and sorry left

Proved `TopCat.Sheaf.constantSubsheaf_peel_layer`
(node `lem-sc-constant-subsheaf-peel-layer`): no `sorry` remains in the item's module.
The private stalk-zero detection helper is also fully proved.

Hole accounting: one existing hole closed and two new holes added. This is a
decomposition, not an axiom-free proof of the parent: its axiom print still includes
`sorryAx` through the two new theorems and the existing stalkwise criterion. The
delivery alone has net -1 holes closed; target-closure pruning is for the ledger to
measure.

Every new `sorry` is the entire proof of one public theorem:

- `TopCat.Sheaf.constantSubsheaf_lower_layer_generator`, module
  `Sheaf.Topology.ConstantSubsheafLowerLayerGenerator`, node
  `lem-sc-constant-subsheaf-lower-layer-generator`.
- `TopCat.Sheaf.abelianIntegerOpen_exists_inclusion`, module
  `Sheaf.Topology.AbelianIntegerOpenInclusion`, node
  `lem-sc-abelian-integer-open-inclusion`.

The existing `TopCat.shortExact_iff_stalkFunctor_map_shortExact` remains an imported
open dependency; it is not modified or delivered. The extension-stalk theorem is
already proved in the repository and is used as stated.

Edge cases checked before stating the intermediates: if the finite generating family
is empty, K is zero and U=V may be empty. If no maximal layer occurs, U=V and the
quotient is zero. For b=0 the lower layer is zero. For V empty the nested inclusion
stalk condition is vacuous; for V=U the inclusion can be identity. Sign reversals in
the arbitrary stalk identifications preserve the integer subgroup aZ and its positive
generator. Neither intermediate asserts a strict inclusion of opens or sheaves.

## No longer needed

Removed the proof-only import `Sheaf.Topology.PresheafModuleStalkFunctor` from the parent.
The proof uses Mathlib's abelian presheaf stalks, not the module-specific declarations
`stalkObj`, `stalkMap`, or `moduleStalkFunctor` from that module. The corresponding node
`def-weil-pbc-module-stalk` is no longer a direct parent proof dependency; the statement
still refers to the stalk notion, so its statement dependency is retained.

The other old direct proof dependencies removed from the parent are
`def-sc-abelian-open-extension-by-zero` and `def-weil-pbc-constant-sheaf`. Their
public imports stay because the signature uses those definitions; their construction
steps now belong to the lower-layer node. Thus all three removed old direct
proof-dependency nodes are accounted for, and none is asserted globally unreachable.

No other existing module is pruned. In particular,
`Sheaf.Topology.AbelianOpenExtensionByZeroStalks` and
`Sheaf.Topology.AbelianSheafShortExactStalkwise` are both genuinely used. The public
imports of the parent are retained. The constant-sheaf and extension-by-zero definitions
are now used in the lower-layer construction rather than as direct parent proof steps;
they remain necessary and are not claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The parent node's first two steps cited only definitions for the substantial
normalization, gcd closure, image-subobject construction, and quotient gluing. None of
its original imported declarations states those construction conclusions. This delivery
makes that gap a separate named item with a complete proof in words. The original final
step also assumed the nested-open integer inclusion without a stated declaration; it
now has its own independent item.

No mathematical error in the original statement was found. The source's quotient
section must be glued on the union of the opens labelled b+1 and on V, rather than
being described as a section on the potentially nonopen difference U minus V. The
parent docstring already included this corrected gluing, and the new construction
lemma preserves it. A direct implementation of the nested inclusion by direct-sum
index maps was explored but not completed; no unfinished helper is delivered.

LeanSearch returned Internal Server Error. LeanFinder, Loogle, Mathlib/source grep,
and blueprint duplicate searches found no exact result for the new interfaces.

## New nodes

`lem-sc-constant-subsheaf-lower-layer-generator`, at
`dag/nodes/sec-curve-estimates/lem-sc-constant-subsheaf-lower-layer-generator.json`,
states the finite lower-layer construction together with a quotient-generator morphism
and its zero/isomorphism stalk regions. Its docstring and node expand the normalization,
Bezout, image, and corrected gluing steps of Stacks 0A38.

`lem-sc-abelian-integer-open-inclusion`, at
`dag/nodes/sec-curve-estimates/lem-sc-abelian-integer-open-inclusion.json`, states the
nested-open extension morphism and interior stalk isomorphisms. Its proof plan uses the
existing constant-integer open-extension comparison, sends each direct-sum summand to
its composite inclusion index, and uses cofinal interior neighborhoods and
sheafification's stalk isomorphisms. No change record is needed.

## Second reading by A2

1. Compared every delivered module with the repository. The two intermediate modules
   are new. The parent's existing theorem signature and docstring are byte-identical;
   only its proof, a proved private helper, and plain proof imports differ. No existing
   data definition, hypothesis, conclusion, or public import changed. Verdict: pass.
2. Compiled all three modules in import order with lcompile.py: no errors or warnings.
   Scanned declaration hygiene: exactly the two reported public theorem bodies contain
   `sorry`, with no forbidden declaration or hollow definition. Axiom prints from
   scratch copies show only propext, Classical.choice, Quot.sound and sorryAx for the
   public theorems; the private helper has only the three permitted axioms. The parent
   remains conditional on open dependencies. Verdict: valid decomposition.
3. Read the two new statements, their complete docstring arguments, their nodes, and
   Stacks 0A38/00A5. Checked empty space, empty family, zero sheaf, b=0, V empty, V=U,
   absent top layer, and sign changes. Gcd closure forces the full and lower images to
   coincide on V; quotient sections glue on the union of the top-label opens and V.
   Neither split theorem is the parent restated: the parent proves the composite-zero
   and three-region exactness assertions. Independent LeanFinder, Loogle, Mathlib grep
   and local source searches found no identical interface. The module-stalk nested-open
   theorem uses ringed spaces and different extension objects, so it is not an immediate
   replacement. Closing either construction requires substantial work beyond a short
   review repair. Verdict: true, needed intermediate parts.
4. Read the parent proof from its target downward, the original dependency declarations,
   the constant-integer comparison, and the proved integer-extension mono. The three
   stalk cases and stalk detection are direct; no shorter existing declaration was
   found for this assembly. All retained public imports serve signatures; each added
   plain import supplies a used theorem. The removed module-stalk import is not used
   directly (and remains transitively reachable). Checked sk-thm-curveestimate's
   realized record: no unit statement or step is replaced or bypassed. Expanded
   No longer needed to account explicitly for every removed old direct dependency.
   Verdict: pass, with no claim of globally pruning a module.
5. Checked all three node signatures against Lean (the parent retains its existing
   whitespace-normalized record); proof_deps equal the unions of step uses, and all
   referenced nodes exist. The new nodes have source, complete proof plan, searches,
   split status, created, blueprint, chapter/unit and verbatim Lean records. The parent
   proof and proof_origin match the assembly. No existing node statement changes.
   Verdict: pass.

Second-reading changes: clarified decomposition and net-hole accounting, and completed
the list of removed direct proof dependencies in this report. No Lean repair was needed.
