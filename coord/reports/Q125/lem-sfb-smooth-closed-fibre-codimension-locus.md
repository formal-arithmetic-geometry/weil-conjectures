## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-closed-fibre-codimension-locus.json`: item, statement, split into nine steps; not a Mathlib leaf.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-presentation-fibre-dimension-levels.json`: new statement-only general theorem, unsplit; no Mathlib match after LeanFinder, LeanSearch, Loogle and source grep, including two semantic phrasings.
- `citations.json`: verbatim statement quotations for every citation in every item step.

## Attachments

None. Searched the live read-only `lean/WeilConjectures` for the item identifier, fibre codimension, and constructible-dimension language, and read `AlgebraicGeometry/FiberDimension.lean`. Its dimension inequalities do not state the closed-pair theorem. Nothing was compiled. Existing sorry declarations were not treated as proofs.

## WANTED

None for this split. The proof uses the available Stacks sources. I also read EGA IV2 Corollary 6.1.4, printed p.136 (PDF page 133): it states codimension preservation for surjective quasi-flat maps. The ambient EGA IV4 reference in the item's source is context for the parent arithmetic-approximation argument, not an additional premise of this proof.

## Corrections and scope

No change to the item's statement, hypotheses or conclusions. The original node was unsplit, with no proof or Lean attachment. Its source suggested finitely many smooth dimension pieces, but the construction, dimension comparison, emptiness case and arbitrary-base-change argument still needed to be supplied. These are now written out.

The assembly deliberately distinguishes local topological dimension from local-ring dimension. The former is preserved at every lifted point by 02FY; the latter need not be. The equality of minimum codimensions is proved from the dimensions of the entire closed subsets. The finite nonnegative level sets in 05F9 do not themselves include empty fibres; those are treated as the complement of the constructible image using Chevalley. No infinite union of constructible sets is used.

Read the current `literature/blueprint/latest` snapshot (COMMITS: main-20261024, ef6f9619fdbffa59e88528fb56483d76c70258c8), its six-functor stability unit and direct-images proof (3). The inherited ancestry ends in null; `tools/blueprint_refs.py ancestor` confirms null, so it is retained and the full inherited via chain is carried into the new node. This lower geometric input does not change the unit's proper/open compactification route. The old `dag/units` record is historical and differs from latest; I did not edit it or the fixed chapter.

## Unfinished work

The general fibre-dimension-level theorem remains statement-only, as required for a one-level split. No argument of the item remains unwritten. Independent maintainer review is still required after delivery.

## Not duplicates

lem-sfb-finite-presentation-fibre-dimension-levels vs lem-sfb-smooth-closed-fibre-codimension-locus: both cite 05F9, but the new theorem concerns dimensions of fibres of an arbitrary finitely presented morphism, without a smooth ambient scheme, a closed pair, codimension bounds, field-extension invariance, base-change equality, or the component criterion. It is the standard dimension input, not a restatement of a clause about the smooth pair.

Searched the entire DAG by tag 05F9, lemma label, fibre-dimension and constructibility keywords, and used `blueprint_refs.py search` with codimension, 05F9, fibres constructible, constructible fibre, dimension of fibres and fibre-dimension. No blueprint node states the new theorem. The dimension-formula search found `lem-kun-dimension-formula`, which is reused rather than duplicated. The smooth dimension-strata search found the scheme result `sbc-lem-smooth-relative-dimension-locally-constant`; the algebraic-space stratum theorem has extra atlas infrastructure and an unnecessary separatedness clause, so the scheme result is used directly. Field-extension dimension is assembled in three lines from the existing scheme local-dimension theorem, surjectivity, and supremum theorem; it is not a new node.

## Review by Q125

I read coord/delivery-errors.md B--E in full and checked the actual node statements against what every step takes from them. I read Stacks more-morphisms.tex around `lemma-base-change-dimension-fibres` and `lemma-dimension-fibres-constructible` (05F9), morphisms.tex around `lemma-smooth-omega-finite-locally-free` (02G1) and `definition-smooth-relative-dimension` (02G2), varieties.tex `lemma-dimension-locally-algebraic` (0A21), especially the generic-point transcendence-degree and dimension-formula clauses, and topology.tex `definition-Krull` (0055). I read EGA IV2 6.1.4 as a cross-check of the intended minimum-codimension invariance. The new node follows precisely 05F9, globalized on a Noetherian base; its objects and finite-presentation convention are stated without relying on the source for meaning.

Step 1 uses the finite-type-over-Noetherian theorem for X, the actual closed-subscheme existence theorem for Z, the scheme smooth-relative-dimension theorem for local constancy, the smooth definition for what its integer means, and closed-immersion base change for C_d. The finite set of integers comes from compactness of X and the clopen covering, not a finite-dimensionality hypothesis on S. C_d is constructed by a fibre product, never by inferring factorization from set containment.

Step 2 uses the Noetherian-open/closed finite-presentation theorem with ambient X, and the local-finite-presentation composition theorem twice. Quasi-compactness of C_d is shown by the elementary closed-subset covering argument. The locally-Noetherian quasi-separatedness theorem applies separately to S and C_d. The actual qcqs permanence statement then gives both morphism properties of C_d -> S. Its hypotheses are now all established; no separatedness of S, X, or f is added.

Step 3 checks every fibre is finite type over its residue field, hence Noetherian; a field is Noetherian because its only ideals are zero and the whole field. The smooth-relative-dimension permanence statement supplies the precise d after base change. The finite closed-component theorem and scheme sobriety give W_j and eta_j. The scheme dimension formula gives d = dim O_(M,eta_j) + trdeg_k kappa(eta_j), and the closed-irreducible dimension theorem gives dim W_j equal to the last term. The chain-of-generalizations statement really gives the required monotonicity from eta_j to any z in W_j; I did not cite the unrelated topological dimension monotonicity. All these statements were opened and their complete statements were copied verbatim into citations.json.

Step 4 is elementary from that calculation: a chain in a finite closed union lies in one component, by irreducibility of its largest member. This establishes the dimension maximum with its argument, so no lemma is hidden behind 'codimension calculation'. The arithmetic treats d < c separately; a nonempty component has dimension at least zero.

Step 5 applies the new node only after step 2 proved finite presentation and with the given Noetherian S. Chevalley is applied to the constructible whole source C_d; its qc/lpf hypotheses hold and S is qcqs by the previous steps. The fibre definition gives exactly the nonempty-fibre image. Finite Boolean operations are supplied explicitly by the constructible-subset definition node. The range n=0,...,d-c is finite and only appears when d >= c.

Step 6 uses the field-extension-surjectivity statement and the scheme base-change-surjectivity statement, which applies to every morphism, with no flatness or finiteness needed. The scheme fibre-dimension statement assumes only local finite type and gives equality of local topological dimensions. Its fibres over spectra of fields are Y and Y_K. The supremum-local-dimensions statement then gives equality of the total dimensions, including empty schemes. This general few-line argument stays in the item's proof.

Step 7 applies smooth-relative-dimension permanence and closed-immersion base change again; the closed subset after extension is the actual fibre product. It then applies the already proved dimension criterion and step 6, so both preservation and reflection follow, even for transcendental or inseparable extensions. Step 8 uses the fibre-identification clause in the scheme fibre-dimension theorem, and the fibre-product universal property to match the inverse images. No Noetherian assumption on S' is used: the comparison is over kappa(s) and kappa(s').

Step 9 is elementary from the chain-of-generalizations and sobriety statements: dimension zero is absence of a strict generalization, hence being a component's generic point; closedness then gives the entire component. This also checks c=0 and the empty cases explicitly. No regularity assertion is needed for this clause.

I tested the statements on empty schemes and Z=empty, Z=X, c=0, a point in affine d-space (good exactly up to c=d), and a disjoint union of smooth pieces of different dimensions. The new theorem allows non-flat finite-presentation maps: for a closed point into a trait its E_0 is that closed point, while all other finite nonnegative levels are empty. An open immersion of a quasi-compact open into a Noetherian base gives its open image as E_0. These confirm that openness or proper upper semicontinuity must not be claimed. For transcendental extension, the generic point of A^1_k can acquire closed lifts in A^1_{k(t)} (u-t); their local-ring dimensions differ, which is why the proof only compares the bound over the entire inverse image of a closed subset.

The new node has statement only, all notions cited or explicitly defined, and no proof sketch in its statement. Its searches were actually run with msearch.py and are recorded from searches.jsonl; no unavailable service was represented as a negative search. The hits for constructible images in FinitePresentation.lean (lines 121 and 165), height versus ring dimension in Ideal/Height.lean, and the polynomial-fibre estimate at KrullDimension/Polynomial.lean line 38 were read and do not state the new theorem. Existing Mathlib-backed Chevalley and topology nodes are reused rather than recreated. Every proof step is under 2000 characters; none conceals an additional independent lemma. Off-unit generic tool uses are declared only in split_report.tool_uses for maintainer review. No SGA, Lean writing, compiler, git command in the repository, or repository mutation was used.
