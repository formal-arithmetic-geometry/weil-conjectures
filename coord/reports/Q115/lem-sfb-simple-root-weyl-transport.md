# Stage-1 report: lem-sfb-simple-root-weyl-transport

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-simple-root-weyl-transport.json: item, statement unchanged, split into twelve proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-root-marked-parabolic-connectivity.json: statement, unsplit; no Mathlib match. A finite reduced based root datum, without a realization, has a marked-root presentation connected by standard rank-two parabolic moves, with positivity-preserving paths inside each dihedral subgroup.
- dag/nodes/sec-six-functors-basics/lem-sfb-sl2-cubic-gauss-identity.json: statement, unsplit; no Mathlib match. An additive root map, diagonal map and Weyl element satisfying the rank-one identities obey the polynomial Gauss interchange formulas.
- citations.json: twenty-three entries, one per cited node per step, using verbatim statements.
- report.md; sandbox-only edge_cases.py, write_split.py and searches.jsonl support the work.

## Attachments

None. Searches in lean/WeilConjectures for the blueprint id and Weyl/root transport, rank-one centralizer and Tits terminology found no declaration of the item. Abstract Mathlib root pairings and Lie-algebra triples do not supply a project attachment.

## WANTED

WANTED: Brian Conrad, Reductive Group Schemes, local archival copy of https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, Theorem 6.2.4 proof, printed pp.202--203, for the item and both new nodes. I read these pages online. No document was downloaded or written to the shared repository. No Stacks tag states either of these specialized reductive-group/root-system inputs. No SGA source was consulted or cited as a proof source.

## What was wrong or incomplete

The item was statement-only. Its source honestly identified the omitted Weyl-word compatibility obligation, but did not expose the actual input or explain the rank-one construction. I kept its full statement, all hypotheses, arbitrary-ring scope, restrictions on all root groups and the entire normalizer of each simple centralizer. There is no statement dispute and no change to a target.

Conrad's proof explicitly leaves the Tits combinatorics and the matrix calculation as inputs. I formulated these as two strictly smaller obligations, not as new nodes asserting the item's conclusions: the first has no group scheme, target or homomorphism at all; the second is an identity inside an arbitrary affine target, with no root datum or extension homomorphism in its conclusion. The assembly argument gives the all-root maps and rank-one maps itself. The proof is marked agent-written because these precise intermediate formulations and their assembly are mine.

The inherited blueprint ancestor is null: tools/blueprint_refs.py ancestor reports None. I preserved it, the inherited via chain, and its precise long provenance, and added this item to each new node's via list. The current blueprint is literature/blueprint/latest (main-20261024); I read the actual unit and direct-images proof (3), not an old snapshot. This continues the inherited supporting branch below direct images and does not change the unit route or its realized fields.

## Not duplicates

lem-sfb-root-marked-parabolic-connectivity vs lem-sfb-normalizer-torus-weyl-presentation: the latter extends a map on the normalizer from torus and Weyl values; it does not identify the fibers of W times the simple roots under rank-two moves.

lem-sfb-root-marked-parabolic-connectivity vs lem-sfb-exchange-reduced-subword-extension: that conditional strong-exchange statement extends a reduced subword by one position; it gives neither marked-root connectivity nor positive dihedral paths.

lem-sfb-root-marked-parabolic-connectivity vs lem-sfb-rank-two-pinned-braid: the latter is an equality of representatives inside a pinned group, not a presentation of all marked roots of an arbitrary-rank abstract root datum.

lem-sfb-sl2-cubic-gauss-identity vs lem-sfb-sl2-lifted-root-gauss-relations: the existing node assumes a central extension of SL2 with root lifts and a commutative inverse-image diagonal. Here there is no map H to SL2, central extension, or lifting hypothesis; the input is instead a cubic relation in an arbitrary affine group. It cannot be applied to the present H.

lem-sfb-sl2-cubic-gauss-identity vs lem-sfb-rank-one-normalized-gauss-chart: the existing node gives identities inside a reductive source with specified root lines. It does not show the corresponding identities for arbitrary homomorphic images of a positive root and a torus in H.

lem-sfb-sl2-cubic-gauss-identity vs lem-sfb-sl2-open-cell-sheaf-extension: the existing node extends an already locally multiplicative cell map. The new node supplies the identities needed to prove that local multiplicativity.

lem-sfb-sl2-cubic-gauss-identity vs lem-sfb-pinned-root-hom-extension-criterion: that node concludes existence of a homomorphism for rank at most two and depends on the general relation criterion above this item. Citing it here would be circular. The new node is only the preceding rank-one polynomial identity.

Whole-DAG searches for Tits, Weyl, root transport, gallery, Exercise 21, cubic/Gauss, as well as blueprint_refs searches Weyl, root, Gauss and cubic, found no equivalent imported blueprint statement. The new identifiers did not exist. Relevant Mathlib hits were read: WeylGroup.lean definition at 56 and root action at 197, Chain.lean indices at 366/377, GeckConstruction/Relations.lean isSl2Triple at 189, GeckConstruction/Basic.lean comment at 44, SpecialLinearGroup.lean definition near 70. They give actions, root strings, matrix groups and Lie triples, not either new assertion. All recorded queries were actually run with msearch.py and their original output summaries are retained in searches.jsonl; each concept was searched with a second phrasing. Both new nodes have LeanFinder, Loogle, LeanSearch and source-grep records.

## Review by Q115

I read coord/delivery-errors.md sections B--E in full, the worker brief and stage-1 contract, SETUP's three levels, GOAL, the chapter/unit records and the current blueprint passage. For the item and each new node I read Conrad's online Theorem 6.2.4 proof on printed pp.202--203. The combinatorial node makes precise the root-system input he names; the Gauss node isolates the SL2 calculation he leaves implicit. These are statement-only future obligations, each independently searchable and testable.

For step 1 I checked the statement of split-root-subgroup-weyl-calculus: it gives conjugation between the root subgroups. Torus ambiguity is canceled explicitly using the item's own hypothesis, with no hidden assertion of word independence. Step 2 uses precisely the new positive-dihedral path assertion; every intermediate root is positive and differs from the reflection's simple root, so the stated conjugation hypothesis applies at every step. The recurrence is written out, including its initial condition and endpoint. Step 3 uses precisely the new equivalence relation and surjectivity assertion. Each generating move is converted into equality of maps by step 2, after which transitivity proves independence. It does not assume the desired family in order to construct it. Step 4 uses the normalizer quotient and open-and-closed cosets of the calculus node, whose statement gives both; it explicitly treats locally constant Weyl images and the zero algebra.

For step 5 I opened relative-root-rank-one-centralizer, framed-noetherian-descent and relative-rank-one-local-matrix-model. The first permits arbitrary rings and has the exact centralizer of the primitive character; it gives the roots and root lines. The descent statement gives a nonzero Noetherian model retaining those lines and their weights. Thus the Noetherian hypothesis of the matrix-model node is met there, not imposed on A. The matrix-model node gives actual affine-open pair isomorphisms, which are pulled back. The calculus node explicitly says root maps, coroots and pinned representatives agree with those of a reductive subgroup containing the relevant roots. Unit scaling of the matrix coordinate normalizes the positive pinning. No descent of H, which is not assumed of finite presentation, occurs.

Step 6 checks all four hypotheses of the new Gauss identity: the square action is the coroot pairing 2, inversion and the square of h follow from the already supplied homomorphism f_N, and the cubic relation is an explicit assumption. Step 7 uses the existing open-cell extension statement, not its proof: it applies to any fppf group sheaf, once local multiplicativity on its specified bottom-right-unit cell is checked. The exact inner pair y(v)x(u_2), the denominator w and the bottom-right entry of the product are displayed. Its second Gauss identity has the correct inverse diagonal for this cell convention. Representable descent makes H a sheaf and the natural map a scheme morphism. No geometric-point density argument replaces a scheme identity.

Step 8 restores a central factor using its commutation with each generator and uniqueness of the existing SL2 extension; this is an elementary consequence of the cited theorem. Steps 9 and 10 explicitly construct the fppf square-root cover, which remains finite free in characteristic 2, and kill their actual scheme-theoretic kernels with the prescribed torus values. The PGL2 quotient meaning and the GL2 matrix model are in the matrix-model statement. For GL2 the kernel consists of (s^{-1}I,s), s^2=1, and the displayed image is diag(1,s^2). These arguments do not assume surjectivity on R-points. I checked representable-descent's exact statement: it glues compatible morphisms along fpqc covers, so all uses concern genuine such covers. This generic tool is declared in split_report.tool_uses.

Step 11 uses the calculus statement on the rank-one reductive pair, whose two-open-cell multiplication is faithfully flat. Hence equality on T, the positive root and n forces equality on the negative root and on the group, allowing overlap descent. The opposite-root restriction is identified by the same lift formula used to define g, rather than asserting an unexplained transport. Step 12 uses exactly the rank-one normalizer quotient from the calculus statement: its two cosets are T and n_aT. Thus the full N intersection K restriction follows from the verified torus and Weyl value, not just equality on A-points. Every cited statement was opened and every citation entry is a literal substring of it.

I tested the combinatorial node by exact finite Weyl-group enumeration in edge_cases.py: empty roots, A1, A1 times A1, A2, B2, G2, A3, B3 and A4 all satisfy both the marked-root fiber connectivity and the positivity-preserving path assertion. These checks are examples, not proofs of the unsplit general theorem. The lattice is allowed a central complement; none of the combinatorics uses a root-span-equals-lattice assumption. Rank one has no rank-two moves, and its two marked pairs map to the two distinct roots, as required. The rank-one matrix equations have the standard SL2 signs n=x(1)y(-1)x(1), y(v)=n x(-v)n^{-1}; I checked the cell conventions and kernels above. Empty roots give vacuous conclusions. Nonreduced bases and bad residue characteristics are retained through universal identities and flat covers; no division by 2, 3 or a nonunit root parameter occurs. Every proof step is shorter than 2000 characters. The two non-elementary omitted inputs are separate nodes, and the other steps cite existing exact statements rather than source labels or definition nodes for theorems.

## Unfinished work

The two new nodes remain unsplit, as required for a one-level split. No Lean was written, and no compiler, Lake, local DAG checker or build was run. Delivery validation is through the prescribed server tools.
