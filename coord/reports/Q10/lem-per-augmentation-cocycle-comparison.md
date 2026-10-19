# Stage-1 delivery: lem-per-augmentation-cocycle-comparison

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-augmentation-cocycle-comparison.json`: existing statement node, now split into ten explicit proof steps; statement unchanged. No exact Mathlib match.
- `citations.json`: verbatim statement quotes for every cited node at each proof step.
- `searches.jsonl`: actual searches made with the prescribed command. Inherited searches in the item were retained as inherited evidence, not represented as new searches by Q10.

No new DAG nodes, no new Mathlib leaves, no unit or chapter edits, no Lean files or builds. The sandbox initially contained only the dispatcher marker files and had no previous split/report/search results to resume.

## Attachments

None. Searched the read-only project `WeilConjectures/` for the exact blueprint tag and for augmentation, crossed homomorphisms and continuous/group cohomology. The augmentation hits concern Amitsur complexes, Hopf algebras and unrelated scheme constructions. No project declaration supplies this item. Upstream master is not used as evidence of a completed proof.

## WANTED

None: the needed ILO PDF, Stacks sources and pinned Mathlib bar-complex source are present.

## Corrections and scope

The imported statement is retained verbatim, including the conditional topological isomorphism and its negative sign at `1-sigma`. It is mathematically sound. Its source explicitly calls the general comparison an agent refinement, rather than a quotation of ILO. Accordingly the proof origin is agent-written, with exact source places for the completed algebra and signed cochain conventions.

ILO Expose XVII 1.2.1.1 defines the completed ring as natural endomorphisms and identifies it with the inverse limit, while the item begins with the inverse limit. Step 2 constructs its action directly so that this difference is not hidden behind a source citation. ILO 1.2.1.2 states freeness for the tame procyclic situation, whereas the present item assumes a topological isomorphism. We use that hypothesis and never assert it for general profinite groups. Nor do we assert that `I` is projective for arbitrary `G`, or that abstract group cohomology equals continuous cohomology.

No clause is moved into a new node. A candidate finite-data helper was investigated, then avoided: the existing arbitrary-discrete-target coset-factorization lemma supplies the genuine topological input, and the finite spans, intersections, finite sums and density arguments are written in the item.

The item's existing blueprint ancestry was checked against `tools/blueprint_refs.py ancestor`, the current `main-20261015` ancestor text and the chapter/unit records. The general augmentation comparison occurs in this descendant of the trait orientation refinement; the current ancestor does not itself state it. Whole-blueprint searches for augmentation, continuous cohomology, cocycles, crossed homomorphisms, finite stable submodules and finite quotients found no blueprint node with this statement. The chapter and unit routes are unchanged. `blueprint.same_as` remains empty, and `from.place` already precisely identifies the relevant orientation step.

## Tool uses

`lem-exc-coinduced-functions-open-stabilizer` is an off-unit general group-topology tool: for a continuous map to any discrete target it supplies an open normal subgroup on whose right cosets the map is constant. It is applied to the cocycle and orbit maps. The perverse unit contains no replacement for this topological fact.

`def-exc-continuous-cohomology` supplies both the coefficient category and its continuous inhomogeneous-cochain model. It was already a statement dependency and is now cited exactly where that model is used.

`lem-sfb-bar-resolution-cochains` is an existing Mathlib leaf supplying the signed integral bar differential and the basis-evaluation cochain formula. It is used only to compute the comparison map, with an explicit restriction to continuous degree-one cochains.

## Not duplicates

No new nodes. In particular the prospective finite-data lemma would unnecessarily package the existing `lem-exc-coinduced-functions-open-stabilizer` plus elementary finite spans and intersections. The existing `lem-sc-group-cohomology-filtered-union` has an ell-primary hypothesis and a cohomology/colimit conclusion, so it is not silently applied to an arbitrary finite commutative coefficient ring. The finite-orbit coproduct node and the profinite-limit-function-factorization node were also read; their more elaborate interfaces are unnecessary here.

## Review by Q10

I read ILO Expose XVII 1.2.1 through 1.2.3, printed pages 259–260, including the completed-ring definition, the generator `1-sigma` and the supported-cohomology differential. I read Stacks `etale-cohomology.tex`, `definition-G-module-continuous` (04JP) and `section-continuous-group-cohomology` (0DVG), including both displayed differentials, and `topology.tex`, `lemma-profinite-group` (0BR1), for the finite quotient topology. I read the statements of all three cited nodes. The bar node supplies exactly its displayed signed formula; the coset lemma supplies exactly right-coset factorization for any discrete target; and the cohomology definition explicitly supplies the continuous inhomogeneous model. The corresponding sentences/formulas are copied verbatim into citations.json, with no use of a node's proof as its public statement.

In Step 1 the coset lemma is applied only to continuous maps from the profinite group to discrete sets. Compactness gives finite index by the open coset cover. The finite ring hypothesis makes the span of finitely many finite orbits finite; no finite generation of M is assumed. Intersecting the finitely many normal subgroups for the elements of that finite submodule makes its entire action factor through one quotient. This is a few-line finite construction from the cited factorization statement, not an uncited stable-lattice theorem.

Step 2 writes the completed action and its choice independence using common finite submodules and quotient refinements. Its continuity follows from a finite discrete intermediary. Step 3 cites the same coset lemma on c and explicitly refines the quotient so it also acts on the entire finite stable submodule containing c(G). This checks the hypothesis that the finite cocycle is a cocycle for the descended action, not merely a locally constant function.

Step 4 is the finite-sum computation L(qx)=qL(x)+epsilon(x)c(q). Restriction to the augmentation ideal kills the correction term and proves linearity for all elements of the finite group ring, hence for A. Step 5 proves density by matching every finite set of quotient coordinates, using a common refinement and an augmentation-zero finite lift. Uniqueness uses discreteness of M. Neither step invokes a completed-free-module universal property or an unproved extension theorem.

Step 6 checks the inverse using gh-1=(g-1)+g(h-1), and checks each principal map on g-1. Step 7 cites the continuous-cohomology node only for what it actually states, expands the usual differential, then uses the explicit bijection and boundary calculation to pass to the quotient. Naturality follows by agreement on g-1.

Step 8 cites the bar node for d1[g]=g-1 and d2[g|h]=g[h]-[gh]+[g]. I checked the R-linear maps to A and I and the cancellation on d2. Evaluation gives f(g-1), so the inverse sends c to f_c with the positive g-1 convention. This uses neither the exactness of a hypothetical completed bar complex nor equality of abstract and continuous cohomology. It simply computes the chain comparison and then uses the explicit continuous degree-one bijection already proved. This is the meaning of the item's conditional augmentation-resolution comparison.

Step 9 uses only the additional *topological* A-module isomorphism assumed in the item. Evaluation at 1-sigma identifies any algebraic map with an orbit map A to M, making it continuous; restriction is precisely m maps to (a maps to am). Step 10 computes the negative sign directly. All ten steps are shorter than 2000 characters, and no longer step hides an independent lemma.

I checked small and limiting cases: the trivial group has I=0 and zero degree one; M=0 and the zero coefficient ring give zero on both sides; finite G is covered by the same finite sums without assuming its augmentation ideal free; for trivial action crossed homomorphisms become ordinary continuous homomorphisms and principal maps vanish; in characteristic two the two signs coincide. For G=Z_ell with F_ell coefficients and a nonzero homomorphism to the trivial F_ell module, f(sigma-1)=c(sigma) and f(1-sigma)=-c(sigma), so the sign is detectably negative when ell is odd. For a nontrivial action the principal-cocycle test gives (1-sigma)m=-(sigma m-m). None of these tests requires strengthening a hypothesis.

Against delivery-errors B–E: there are no new incomplete statements, duplicate nodes or fabricated searches; the item introduces its completed algebra and action; each non-elementary external input is one of the three cited statements; there is no cycle through a child or parent; the steps carry the construction rather than restating clauses via helper nodes. No statement dispute, no coefficient-category substitution, and no prohibited SGA route are introduced. No unfinished mathematics remains in this one-level split; downstream cited statements retain their own independent status.

## Validation

The required server dry run exited successfully: `OK (not pushed) deliver/Q10/lem-per-augmentation-cocycle-comparison at 4fbce313c0: preflight passed`. The statement was checked unchanged against the current repository; all four step citations quote the actual cited statements. A final dry run validates this report update before the authorized push.
