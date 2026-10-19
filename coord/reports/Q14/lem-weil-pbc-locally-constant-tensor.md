# Q14 — lem-weil-pbc-locally-constant-tensor

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-locally-constant-tensor.json`: statement, split; same arbitrary-small-site assertion, repaired proof dependencies and nine complete proof steps; retained the inherited statement, Lean records, blueprint ancestry, and earlier searches.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-derived-tensor-truncation-window.json`: statement, unsplit; no Mathlib match. This is the fixed-degree comparison for good lower truncations of two bounded-above derived objects on any ringed site. Its statement does not assume finite generation, local constancy, or a Noetherian coefficient ring.
- `citations.json`: one entry for every step/node citation, quoting the actual cited statement verbatim.
- `searches.jsonl`: actual msearch.py records; inherited searches were not invented or overwritten.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the blueprint tag, `locallyConstantFiniteType_derivedTensor`, locally constant tensor terminology, and tensor/truncation terminology. `ConstructibleSheaf/Monoidal.lean:101` only states the underived finite-locally-constant sheaf tensor assertion on an etale site, and its proof is `sorry`. The adjacent constructible tensor theorem invokes it and does not state our derived arbitrary-site assertion. The inherited `Sheaf.Paper.LocallyConstantTensor` statement is not a finished declaration under this source checkout's `WeilConjectures/`. The item's slopmaster2 audit is `none`.

## WANTED

None. The source needed for the item and child is present in `literature/stacks-project/`.

## What was wrong and what changed

The imported item was marked unsplit despite carrying an earlier reviewed proof. I preserved its correct statement and its logged historical searches. Its first step unnecessarily rederived reflection of exactness through extension by zero; the existing `lem-weil-pbc-slice-restriction-flat` already states the needed flat-restriction conclusion. Its second step was a long inline general truncation comparison, including cone and local cycle arguments. I isolated that general fact as a statement-only child instead of retaining a hidden lemma. The finite-generation argument now cites the existing Mathlib leaf `lem-weil-pbc-noetherian-submodule-finite`. Exact constant realization now cites `def-sfb-site-derived-constant-module-functor`, whose statement actually supplies the functor on derived categories and exactness, rather than requiring an implicit identification of two module-sheaf presentations.

The inherited Lean statement is a representative-based version with explicit K-flat complexes, whereas the natural statement uses the derived tensor bifunctor. No Lean record was changed and no compiler was run. No target, chapter, or unit statement was changed. The unit's proper-base-change route and the current main-20261015 amplification-proper proof (c) remain the ancestry: this is the tensor reduction needed below the nilpotent-reduction/lisse-cohomology branch, not a replacement proof of a unit. No SGA source is used.

## Source error

STATEMENT-DISPUTED (source proof equality, not the item's theorem): Stacks Tag 094H, `sites-cohomology.tex`, `lemma-locally-constant-tensor-product`, says the degree-i cohomology is unchanged when both factors are truncated below i-1. Without normalizing both upper bounds this is false. On the one-point site over a nonzero field B, take i=0, K=B[2] concentrated in degree -2 and L=B[-2] concentrated in degree 2. Their tensor has H^0=B, whereas tau_ge(-1) K=0 and the claimed truncated tensor has H^0=0. All source theorem hypotheses hold in this example.

The previous node had already corrected the cutoffs. I retained that correction, stating it independently and generally in the new child: if H^q(K)=0 for q>b_K and H^q(L)=0 for q>b_L, cut K at a<=i-b_L and L at c<=i-b_K. The item uses the equality cutoffs. This changes no hypothesis or conclusion of the item.

The child follows the first reduction in Tag 094H with that correction. Its argument, for the next worker, is as follows. Good upper truncations and bounded-above flat replacements (Tag 06YS, whose proof uses Tag 077J) show that objects with upper bounds u,v have derived tensor bounded above by u+v: the flat representatives have exactly those term bounds and every total summand above u+v is zero. The truncation triangle tau_<a K -> K -> tau_ge a K is the one in Derived Categories Tag 08J5. Derived tensor is an exact functor on an arbitrary ringed site by Tag 06YU; tensor that triangle with L. Its first term has upper bound a-1+b_L<=i-1. The cohomology exact sequence (Derived Categories Tag 05RS) therefore has zero adjacent terms in degrees i and i+1, so H^i(K tensor^L L) -> H^i(tau_ge a K tensor^L L) is an isomorphism. Next tensor the corresponding truncation triangle for L with tau_ge a K, whose upper bound is still b_K. The first term now has upper bound c-1+b_K<=i-1. The same exact-sequence argument gives the second comparison. Their composite is the canonical map in the child's statement. Good truncation gives the two claimed finite cohomology windows. This argument requires the general tensor upper-bound and triangulated-computation facts and is not merely the item's local-constancy conclusion under another name.

## Searches and reuse

Before creating the child I searched the whole DAG by its proposed id, by tensor/truncation and finite-window terminology, by source tag 094H, and by parsing node titles and statements for tensor cohomological bounds and cutoffs. `tools/blueprint_refs.py search` was run for `locally constant tensor`, `locally constant`, `derived tensor`, `truncation comparison`, `truncation tensor`, `tensor truncation`, `finite window`, `094H`, and `tensor cohomological`; ancestor is `thm-weil-pbc-amplification-proper`. The finite-window blueprint hit `det-finite-window-reduction` is about Hom from a constructible object and does not concern a derived tensor. `lem-weil-pbc-ringed-tensor-cohomological-bounds` treats extension of scalars by a ring sheaf, not two arbitrary complexes. The etale-only tensor and scheme/open-only comparisons were not used as arbitrary-site assertions.

The child's Mathlib records contain both semantic phrasings, Loogle's tensor/truncation name search, LeanSearch, and two greps. LeanSearch/LeanFinder find `CochainComplex.truncGE`, `quasiIso_truncGEMap_iff`, `shortComplexTruncLEX₃ToTruncGE`, and individual derived-category cohomological-bound lemmas. I read the truncation declarations in `Mathlib/Algebra/Homology/Embedding/CochainComplex.lean:277-300`; they concern truncations alone, with no derived tensor comparison. Loogle finds truncated simplicial-set tensors. Grep produces no homological tensor/truncation theorem; the broader search's `equivFinsuppOfBasisLeft` hits are lexical false positives, not a derived comparison. None is an exact or one-line specialized match.

For the item, fresh semantic searches in two phrasings, LeanSearch, Loogle, and grep were run. The hits give ordinary locally constant functions, condensed-module monoidal structures, exact sheafification, or flat-module tensor functors. I read the light-condensed monoidal source to verify that it supplies ordinary monoidal structures, not the arbitrary-site theorem. No fresh search service was reported unavailable. All new-node query texts agree with searches.jsonl; earlier item records remain intact.

## Not duplicates

lem-weil-pbc-derived-tensor-truncation-window vs lem-weil-pbc-locally-constant-tensor: the child compares a fixed cohomology degree after good truncation for arbitrary ring sheaves and arbitrary bounded-above factors; the item proves local constancy and finite generation over a Noetherian constant coefficient ring. The child neither states nor implies that local-constancy assertion on its own.

lem-weil-pbc-derived-tensor-truncation-window vs lem-weil-pbc-nilpotent-reduction-lissity: the existing node propagates local constancy from B/J to B/J^m; the child has no ideal or coefficient reduction and proves a tensor truncation comparison.

lem-weil-pbc-derived-tensor-truncation-window vs def-weil-pbc-site-locally-constant-finite-type: the existing node defines a local finite-type module property; the child compares cohomology of two derived tensor objects without that property.

lem-weil-pbc-derived-tensor-truncation-window vs def-weil-pbc-locally-constant-finite-type-modules: the existing node is another definition of local finite-type constancy; the child is a truncation theorem for general ringed sites, not that definition.

## What remains

The item is split by one level. The new child deliberately has only a self-contained statement, empty proof/proof_deps, and unsplit status; its proof route and source correction are recorded above for its later worker. No unresolved statement dispute concerns the item's theorem. Delivery validation results are recorded below when available.

## Review by Q14

I read the full Stacks Tag 094H statement and proof in `sites-cohomology.tex`, the preceding Tag 094G constant-model induction, the Tag 06YU construction, Tag 06YS bounded-above flat-resolution route, Tag 0E8J flat-restriction proof in `sites-modules.tex`, and the Tag 066E Noetherian pseudo-coherence criterion in `more-algebra.tex`. The child uses the first equality of 094H only after correcting it as above; it is not attributed to the source verbatim. I read the current amplification-proper proof (c) and the chapter/unit records to check the route.

For Step 1, I opened the statements of the exact module-restriction lemma, the localized-ringed-site definition, the sheaf tensor definition, and local sections/equality after sheafification. They give exactly the exactness, identical slice covering families, presheaf tensor formula, and local equality used. The argument does not identify a sheaf tensor's sections with the raw presheaf tensor. It identifies the sheafifications using their local representatives and relations.

For Step 2, the standard-t-structure statement gives representatives zero above the chosen bound; the bounded-flat-replacement statement explicitly preserves that bound. The existing flat-restriction theorem applies to any ringed site and object, and the bounded-above-flat criterion then gives K-flatness on each slice. The tensor-descent statement explicitly computes the bifunctor from such representatives. The total-tensor definition supplies the finite diagonal sum and the signed differential. None of these references is being used outside its statement or specialized from an etale-only theorem.

For Step 3, the child's hypotheses are satisfied by the selected upper bounds, and the good-truncation definition gives both preserved cohomology and zero cohomology in the omitted degrees. Its canonical direction is K -> tau_ge a K. I checked the shift counterexample and corrected cutoffs explicitly. If a window is empty the truncated factor is zero in the derived category and so is its tensor; zero is the constant finite module used for the conclusion.

For Step 4, the bounded-constant-model statement really supplies termwise constant complexes of finite modules with constant differentials, not merely complexes of unrelated locally constant terms. Each slice has a final object and retains the Noetherian ring B and bounded cohomology. The two covers are composed, rather than claiming a simultaneous refinement over infinitely many cohomological degrees. Relocalization is explicitly included in the localized-site statement.

For Step 5, the submodule theorem applies to cycles in finite modules over B; quotient finiteness is the elementary image-of-generators argument. The pseudo-coherence criterion has precisely the upper bound and finite cohomology that were just proved. Its definition then supplies bounded-above finite free models, with no unjustified finite lower bound.

For Step 6, exact constant realization explicitly descends termwise to unbounded derived categories, so it carries the derived isomorphisms of free models. Its finite-sum preservation identifies constants of finite free modules. Tensor with a finite free sheaf is a finite sum of the identity, by the two written basis maps; that proves flatness from the cited definition, rather than assuming constants are flat. The general K-flat criterion and tensor-descent statement then apply.

For Step 7, I checked the finite diagonal index range n-s<=p<=r, including an empty range. The free tensor-basis map and its inverse respect matrices of differentials, including the (-1)^p sign, so this is a comparison of whole complexes. For Step 8, exactness preserves kernels, images, and their quotient, and the submodule theorem proves finite generation of cycles. For Step 9, the local finite-type-constancy definition is explicitly objectwise; a covering family generates a covering sieve and further restriction preserves the displayed constant models. These three steps are elementary deductions from the quoted statements, with no uncited spectral sequence or stalk argument.

I tested B=0, K=0 or L=0, shifts in either direction, a window with its lower endpoint above its upper endpoint, and arbitrary sites without points. I also checked the nonregular case B=Z/4 with the finite module Z/2: its unbounded free resolution causes no problem because each fixed total degree has only finitely many summands; the conclusion does not assert a bounded tensor or finite Tor amplitude. The site can have no global final object because all constant-model applications take place on slices. Every cited node's statement was opened and copied into citations.json. No proof step exceeds 2000 characters; the old long truncation argument has become an independent, non-duplicate statement-only child. I checked B1--B10, C1--C8, D1--D5 and E1--E7 against the files; the repairs above address hidden infrastructure, definition-only citations, and the source's false cutoff. Only the authorized sandbox was written, and no Lean, Lake, build, agent, or git command was run by me.
