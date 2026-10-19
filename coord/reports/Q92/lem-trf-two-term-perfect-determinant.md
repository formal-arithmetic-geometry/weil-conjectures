# Stage-1 report: lem-trf-two-term-perfect-determinant

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-two-term-perfect-determinant.json`: statement item, split in ten steps; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-surjective-two-term-determinant-calculus.json`: one new statement-only, unsplit supporting lemma; no Mathlib match.
- `citations.json`: verbatim statement quotations for every node cited by each proof step.

There are one new node and zero new Mathlib leaves. Preliminary affine-functor, scalar-extension, and gluing children were discarded before delivery: those were clauses of the item. Their arguments now appear in the item itself. The retained lemma concerns only the explicitly kernel-normalized maps for degreewise surjective chain maps. It makes no assertion about arbitrary derived morphisms, model independence, sheaf gluing, or pullback.

## Attachments

None. Searches for the item tag and determinant-complex notions in the project declarations of both supplied Lean checkouts found no exact finished declaration. In particular an upstream sorry declaration would not count. Existing K-projective and derived-Hom results are reused through their existing DAG Mathlib leaves, not re-created.

## WANTED

None. All sources used here are available locally.

## Statement and source audit

I read the chapter/unit records and kept the imported item's statement. The scheme-level source is `literature/stacks-project/perfect.tex`, Tag 0FJX, label `lemma-determinant-two-term-complexes`, and Tag 0FJY, label `remark-functorial-det`. I read their affine restriction/gluing argument and the pullback remark. The affine argument is `literature/stacks-project/more-algebra.tex`, Tag 0FJM, label `lemma-determinant-two-term-complexes`: good diagrams exist by adjoining an identity complex, compose through a degreewise fibre product, and become independent of choices by composing with a homotopy inverse. Those constructions are written out in the item rather than hidden in a child.

For the new supporting lemma I read the construction in Tag 0FJI immediately before Tag 0FJJ, the kernel-normalized determinant isomorphism, and the complete statements and proofs of Tag 0FJK (`lemma-homotopic-surjections`) and Tag 0FJL (`lemma-compose-surjections`). The new statement defines the determinant of a finite projective module using local top wedges, specifies the wedge-with-lifts maps, the acyclic kernel's determinant trivialization, and the normalization determining each map. Its assertions are only the identity, homotopy and composition calculus. It remains unsplit, with no proof sketch or proof dependencies in its JSON. The localization cover, exterior powers, projectivity and quasi-isomorphism notions are linked to nodes that actually state/define them; finite projective is also defined inline as a finite-free summand.

I searched the whole DAG for the source tags and determinant/homotopic-surjection notions, the whole imported blueprint through `blueprint_refs.py search`, and the Lean project for these notions before introducing the new lemma. No existing node states this calculus. The item retains its original blueprint ancestry; the child prepends the item to that ancestry and identifies the determinant input to the local complete-intersection adjunction, within the marked dualizing construction used by the semistable-modification branch. No unit route is replaced and no unit record is changed.

## Source error

The displayed concluding type in More on Algebra Tag 0FJL is printed as maps from `det(M)` to `det(K)`, although its maps and composition are defined in the preceding text from `det(K)` to `det(M)`. The latter direction is forced by the declared types of `det(a)` and `det(b)`. The new lemma gives the correctly typed equation `T_ba = T_b composed with T_a`, from `D(P)` to `D(S)`. This is a typographical source error, not a change to the imported item's hypotheses or conclusion.

## Not duplicates

- lem-trf-surjective-two-term-determinant-calculus vs lem-trf-two-term-perfect-determinant: the shared source Tag 0FJI contains the lower kernel construction, but the new node covers only degreewise surjective chain maps and their homotopy/composition calculus. The item constructs maps for arbitrary derived isomorphisms using good diagrams, proves independence, glues on schemes, and proves pullback compatibility. None of those clauses is moved into the child.
- lem-trf-surjective-two-term-determinant-calculus vs lem-sc-determinant-short-exact: the existing statement gives a determinant isomorphism for a short exact sequence of finite locally free sheaves. It does not state homotopy invariance or composition for acyclic-kernel-normalized maps of two-term module complexes.
- lem-trf-surjective-two-term-determinant-calculus vs lem-sc-determinant-wedge-morphism: the existing statement constructs one wedge-with-lifts morphism for a sequence of sheaves; it has neither the acyclic kernel normalization nor the homotopy and composition conclusions.
- lem-trf-surjective-two-term-determinant-calculus vs lem-trf-completed-conormal-determinant-comparison: the existing node concerns completed local complete-intersection presentations and uses the item as an input. The new node has no completion or conormal hypotheses and supplies lower chain-map calculus; citing the completed comparison here would be circular.

## Review by Q92

I rechecked delivery-errors B through E against the actual statements and the sources, not just the schema. I replaced the preliminary clause-shaped children with the single lower-level calculus lemma described above, corrected a scheme-sheaf definition previously being used for ring projectivity, specified the local-rank interpretation of determinants, and restored the inherited blueprint chain. Every retained proof citation was opened and read; `citations.json` copies its actual statement verbatim.

Step 1 uses the bounded-above-flat K-flat lemma for a two-term locally free sheaf complex, and the site-perfect Tor-window theorem with exactly `a=-1,b=0` on the small Zariski site. Its conclusion supplies summands of finite free sheaves in those degrees. The finite-projective standard-free-cover theorem is applied to their affine idempotent image modules; taking a common refinement makes both terms free without changing bounds. This verifies the equivalence in the item rather than adding it as an unsupported assumption.

Step 2 uses the two existing K-projective statements for bounded complexes of projective modules over a ring, where their hypotheses hold. The Hom bijection gives representatives and homotopy inverses for derived isomorphisms. The free-localization node supplies the covers for invertibility of top wedges. The new calculus lemma supplies only the maps on surjective quasi-isomorphisms.

Step 3 constructs its own good diagram. I checked both differentials and the homotopy formula, and explicitly verified degree-zero surjectivity from surjectivity on H^0. No cited lemma is being asked for a non-surjective map. Step 4 uses exactly the child's homotopy and composition clauses. Its fibre product terms are finite projective because the surjections split degreewise; its projection kernels have invertible differential. The cycle/boundary lifting argument establishing that projections are quasi-isomorphisms is included. Step 5 uses the K-projective Hom bijection only for a homotopy inverse; the fixed-inverse argument then proves good-diagram independence and descends the maps to the derived groupoid.

Step 6 checks scalar extension directly on basis wedges and duals. The kernel sequences are split, so arbitrary ring maps preserve them; no hidden flat-base-change hypothesis occurs. The child's normalization formula specifies exactly the gamma maps and kernel element used in the naturality check. Identities and iterated scalar extensions agree on the displayed pure-wedge generators. Step 7 uses the module version of bounded-flat K-flatness to identify ordinary with derived tensor, and computes the projection of an identity complex to zero from the child's normalization. Its normalized unit element gives exactly evaluation under the ordinary symmetry of the two line factors.

Step 8 uses the affine derived equivalence for complexes with quasi-coherent cohomology (our finite locally free models satisfy this), and uses the explicit restriction and affine derived-tensor clauses of the affine pullback/tensor node. I cover overlaps by affine opens; an intersection of affines is never assumed affine. Cocycle identities follow from the already proved ring functor's composition law. Step 9 checks the fpqc-covering definition, using the quoted quasi-compactness of each affine spectrum. It applies the actual descent equivalence for quasi-coherent modules and the explicit invertible-module descent clause, with no assumption of quasi-compactness of the whole scheme. Full faithfulness glues maps and gives independence under refinement.

Step 10 uses the bounded-flat-complex pullback statement on the actual two-term flat models and the affine tensor comparison for every ring map. The full faithfulness of descent glues the compatible local wedge comparisons. The composition lemma supplies precisely the unital associative identification of derived pullbacks; the equality of determinant comparisons is checked on pure wedge tensors, not asserted merely from that identification. I declared the off-unit generic tools in `split_report.tool_uses`, explaining the exact use of each; no maintainer-owned `tool_uses` field is set.

For the child's small cases I checked the zero complex, a projection `[V --1--> V]` to zero, and homotopic automorphisms of a contractible rank-one complex (the two determinants cancel). I also checked composition of projections after adjoining identity summands. Variable ranks are interpreted locally on their rank loci, never as a single global integer. For a nonflat scalar change, such as integers to F_2, only split term sequences and invertible kernel differentials are preserved; no nonsplit exact sequence is incorrectly tensored. The model `[Z --2--> Z]` tensors to `[F_2 --0--> F_2]`, so the construction does not mistake ordinary tensor cohomology for flat-base-change cohomology. No characteristic, separatedness, regularity or constant-global-rank assumption was added.

Mathlib searches for the new node used LeanFinder, LeanSearch, Loogle and source grep, with two semantic phrasings and the exact queries/results recorded in the node and the command log. I read the returned types and relevant source locations: the derived-category hits identify homotopies in a localization, and the determinant hits concern endomorphisms, so neither states the normalized determinant-line calculus. The zero-hit Loogle query succeeded and is recorded as no match, not unavailable. The item retains its earlier searches; discarded-child searches remain only as historical search logs. No service outage is treated as evidence of absence.

All ten proof steps are shorter than 2000 characters. Each non-elementary input has a node citation, and explicit constructions, finite-basis checks and diagram chases are kept in the item's proof. The child's statements are strictly lower-level and no child depends on the item. No Lean was written or compiled.

## Unfinished work

None for stage 1. The new statement-only lemma is deliberately left in the queue for its own later split. Delivery still requires the final server dry run and push, which will be performed after this report is written.
