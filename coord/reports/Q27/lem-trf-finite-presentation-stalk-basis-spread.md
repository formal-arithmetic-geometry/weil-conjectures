## Worker report

Files written: `dag/nodes/sec-trace-formula/lem-trf-finite-presentation-stalk-basis-spread.json` (item, split), `citations.json` (one verbatim statement witness per step/dependency), and this report. `searches.jsonl` is the search command's unmodified log. No Lean, repository, or launcher files were written.

## New nodes

None: 0 new nodes and 0 Mathlib leaves. In particular, do not create separate lemmas for a finite tuple of germs, a zero finite-type stalk, restriction of local finite presentations, or the sectionwise kernel calculation: these have short arguments from the cited definitions/statements. Existing nodes already state both substantial inputs.

## Attachments

None. Searched `lean/WeilConjectures/` by the exact blueprint tag and by stalk/basis/free/finite-presentation terminology. The scheme-specific finite-free stalk equivalence and coherent generic-free neighbourhood declarations do not cover arbitrary ringed spaces and arbitrary prescribed stalk bases. The topology basis-stalk theorem concerns extension from a topological basis, not the asserted module basis spreading.

## WANTED

None. All mathematical sources were present and read locally.

## Findings and changes

The item was unsplit, with no proof. Its existing statement is correct, including rank zero, and is unchanged. Stacks `modules.tex`, Tag 0B8J (`lemma-finite-presentation-stalk-free`, lines 1537 onward), proves the version with an unspecified trivialization; its proof explicitly begins with any basis and retains its section representatives through shrinking, so it gives the prescribed-basis version in this item. I also read the concluding paragraph of `more-morphisms.tex`, Tag 080Q (`lemma-flat-and-free-at-point-fibre`, lines 4791 onward). We need neither relative flatness nor locally ringedness here: those are inputs to the parent's acquisition of a basis, not to spreading a supplied basis.

The proof follows that source: represent germs, obtain a surjection near the point, take its finite-type kernel, kill that kernel near the point, and glue the inverse. The kernel germ computation is written coordinatewise rather than invoking an uncited exact-stalks theorem. Rank-zero arguments use empty tuples and the same surjectivity theorem.

Whole-DAG searches by 0B8J, the precise source labels, 01B8/01B9, and finite-type kernel/stalk/free/generator terminology located the two existing input nodes. Blueprint searches using `tools/blueprint_refs.py search` for `stalk free`, `finite presentation stalk`, `finite type stalk`, `0B8J`, `stalk basis`, `kernel surjection finite free`, `finite presentation stalk free`, and `surjective on stalk` found no equivalent blueprint theorem; the broader basis/finite-type searches were used to inspect possible neighbours. No duplicate node is created.

The inherited blueprint ancestor is `lem-trf-local-term-locality`, through the recorded flattening/free-neighbourhood chain. I read its current files under `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/`, as well as the chapter and unit records. The current ancestor uses Varshavsky's contracting-correspondence theorem and no longer explicitly displays this auxiliary flattening chain. That is an ancestry/history issue, not a false statement here; I preserve the assigned ancestry and record the precise 0B8J/080Q auxiliary place without changing the unit or ancestor. No SGA source is used.

## Mathlib searches

Preserved the item's original recorded searches. Ran the required search command anew for this item in all four modes. The unmodified log contains the exact queries and returned names. Two semantic phrasings were tried. LeanFinder returned local-generators and presentation data; Loogle returned `SheafOfModules.IsFinitePresentation` and its finite-type/quasicoherent instances; LeanSearch also suggested free sheaves and `Module.FinitePresentation.exists_free_localizedModule_powers`. The grep over `Algebra/Category/ModuleCat` found no free/basis stalk assertion. A targeted grep located the localized-module basis/free lemmas at `Mathlib/RingTheory/Localization/Free.lean:41,78`, whose declarations and proofs I read. They assume localization from a single ring/module and do not prove this theorem for arbitrary ringed spaces. I read the relevant presentation and generator instances in `Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`, including the finite-presentation-to-finite-type instance around line 281. These are ingredients, not a one-line specialization proving the entire item. No service failure occurred in the new searches.

## Tool uses

`lem-weil-pbc-module-finite-type-surjective-on-stalk` (01B8) and `lem-weil-pbc-finite-presentation-kernel-surjection-finite-type` (01BP(1)) belong to another unit. Both are generic ringed-space tools used exactly as in 0B8J, not alternative routes for a trace-formula unit step. Their proposed uses are recorded in `split_report.tool_uses` for maintainer review; no maintainer-owned `tool_uses` field was set.

## Review by Q27

I opened the item, its four statement-definition nodes, both substantive input nodes, and all source passages used. The statement-definition nodes really supply ringed spaces, module sheaves with sectionwise kernels and sheafified cokernels, finite presentation/type and finite-free maps specified by sections, and germs with representatives and the neighbourhood equality criterion. In particular the ringed-space definition node does not force locally ringedness: its first sentence defines a general ringed space. Every cited node statement is copied verbatim into the corresponding entry of `citations.json`.

Step 1 uses the module-stalk definition for representation, common restrictions, germ scalar multiplication, and the equality criterion, and the finite-type/presentation definition for the free-module map specified by sections. Its finite-free stalk coordinate identification is proved in the step, not taken from the existing scheme-only stalk equivalence. Surjectivity and injectivity follow from the supplied basis, over a general stalk ring, with no use of Nakayama or nontriviality.

Step 2 uses the finite-type/presentation definition and the module-category statement's description of cokernels. It explains why the same local presentation restricts, and why the images of the finite basis generate its cokernel locally; it does not infer finite type just from an uncited slogan. These are elementary consequences of the stated local definitions.

Step 3 uses exactly the conclusion of the 01B8 node: a map into a finite-type target that is surjective at the specified stalk is surjective after shrinking. The node states a sheaf surjection by local preimages, not surjectivity on every section space. The target satisfies finite type by Step 2 and the stalk map is surjective by Step 1. Restriction preserves the specified germs by the stalk definition, also cited.

Step 4 uses exactly 01BP(1), whose statement is for ringed spaces, a finite-free source of any nonnegative rank, a finitely presented target, and a surjection. Step 2 supplies presentation after restriction, Step 3 supplies the sheaf surjection, and the source is the constructed finite-free sheaf. Its conclusion is the finite type of the sectionwise kernel. I checked the actual node statement, not its proof, and read `lemma-kernel-surjection-finite-free-onto-finite-presentation` in `modules.tex` at lines 1457 onward.

Step 5 uses the stalk definition's representative/equality criterion and the kernel node's explicit sectionwise description. A kernel section maps to a zero linear combination in the prescribed basis, hence each coordinate germ vanishes. There are finitely many coordinates, so there is one neighbourhood on which the entire kernel section vanishes. This proves vanishing of the kernel stalk without a hidden exactness or restriction-stalk-comparison lemma.

Step 6 reapplies the same 01B8 node to the morphism from the zero sheaf into the finite-type kernel. The zero kernel stalk makes this stalk map surjective, so no separate new statement for 01B9 is needed. A locally surjective map from zero forces every kernel section to vanish by uniqueness in the sheaf axiom. The original local preimages glue uniquely because their differences are kernel sections; the text spells out why they form an inverse compatible with restrictions and module operations. It uses the module-sheaf definition for these operations and gluing. This verifies a genuine isomorphism and the original prescribed germs, rather than merely injectivity or a stalkwise assertion.

I checked the edge cases: when r=0, take the whole space for the empty intersection, the free sheaf and its stalk are zero, and 01B8 gives the zero neighbourhood; when the stalk ring is the zero ring, the same tuple argument works without invariant basis number or a positive-rank assumption; on a one-point space, the result is the given module basis; an empty space has no specified point and contributes no additional case. For arbitrary non-Noetherian ringed spaces, finite presentation is used precisely in 01BP(1), so no coherence, affine, quasi-compactness, or Noetherian hypothesis has entered. There are no new statements needing independent small-case tests.

Checked B--E: self-contained unchanged TeX statement and correct source tags; no new statement-only-node violation or duplicate; all non-elementary inputs cited and verbatim witnesses supplied; no use of cited proofs in place of statements; no circular argument; genuine assembly rather than moving the conclusion into a new node; no added hypothesis or substituted object. All six steps are below 2000 characters. The main corrections to the initially contemplated proof were to avoid the scheme-only free-stalk node and an uncited exactness-of-stalks assertion, using the explicit finite-coordinate arguments instead.

## Unfinished work

None in the split. Independent maintainer review and subsequent formalization remain the project's later work.
