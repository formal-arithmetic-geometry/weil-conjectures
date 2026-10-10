# Stage-1 split: lem-exc-cochains-derived-invariants

## Files written

- dag/nodes/sec-curve-estimates/lem-exc-cochains-derived-invariants.json: split in four steps; no Mathlib match.
- dag/nodes/sec-curve-estimates/lem-exc-continuous-cochains-short-exact.json: new unsplit statement; abstract-group Mathlib analogue is not a continuous-cochain match.
- dag/nodes/sec-curve-estimates/lem-exc-coinduced-discrete-embedding.json: new unsplit statement; no Mathlib match for a discrete coinduced object.
- dag/nodes/sec-curve-estimates/lem-exc-coinduced-continuous-acyclic.json: new unsplit statement; no Mathlib match for its acyclicity.

## Attachments

None. Search of the read-only slopmaster2 source for the blueprint tag, derived invariants, continuous cohomology, and coinduction found no declaration stating this item or these new statements.

## Wanted

WANTED: Stephen S. Shatz, *Profinite Groups, Arithmetic, and Geometry*, II.2, Proposition 5 and Theorem 8, for lem-exc-coinduced-continuous-acyclic and the missing comparison proof of lem-exc-cochains-derived-invariants. The source is named in the comment on Stacks 0DVG but is absent from literature/. The split uses the explicit coinduced contraction described below.

## Corrections and limits

Stacks 0DVG, label section-continuous-group-cohomology, defines the inhomogeneous differential, proves/records short exactness for discrete modules, constructs canonical maps from derived invariants, then asserts the maps are isomorphisms for profinite groups with "insert future reference here." Thus its last paragraph was an assertion, not a proof to copy. The imported item had no steps. I supplied a proof route via effaceability; the two coinduced facts are agent-written obligations, and their source fields say explicitly that 0DVG does not state them. I kept the item's mathematical statement unchanged.

The local literature/stacks-project/ source tree is absent on this machine. I read the Stacks pages for Tags 0DVG, 04JP, 04JF, 010T, and 015B directly; no literature file was downloaded or modified. Mathlib's LeanSearch service returned HTTP 500 on all three new-node queries. LeanFinder and the pinned Mathlib source were checked, including GroupCohomology/LongExactSequence.lean:50, the abstract-group analogue.

The first dry run found two off-unit delta-functor citations. I declared both generic tools in `split_report.tool_uses`, as the current brief requires. They provide universal properties used as black boxes and do not replace the H^2-via-Kummer unit's route. The launcher accepts the command without the trailing dot shown in the brief.

## Review by E1

I checked the item against Stacks 0DVG: the formula, discreteness, direction of the canonical map, and the profinite restriction all agree. Stacks 04JP defines the discrete continuous $A$-$G$ modules, and 04JF supplies enough injectives; these are exactly the hypotheses in the existing lem-exc-discrete-modules-abelian statement. The finite-ring assumption is stronger than needed for the coinduced argument but is retained from the item. The unit sk-prop-h2 and chapter sec-curve-estimates were read; this auxiliary comparison changes neither the unit's statement nor its route.

For lem-exc-continuous-cochains-short-exact I checked 0DVG's paragraph beginning "However, a short exact sequence of discrete G-modules". Its claim is degreewise exactness plus the induced cochain maps. A continuous map from compact $G^n$ to discrete $M''$ has finite image and clopen fibres; choosing a lift of each value gives a continuous lift. Kernels are pointwise. Equivariance makes the displayed differentials commute with the module maps. This verifies the $A$-linear version as well. I found no blueprint node for this narrower claim: blueprint_refs search for "cochains", "continuous", and the DAG search for Tag 0DVG only found the parent definition and this item.

For lem-exc-coinduced-discrete-embedding I read 04JP for the open-stabilizer criterion and 0DVG for the comparison it serves. The node does not pretend 0DVG states coinduction. Every continuous $f:G\to M$ into discrete $M$ is uniformly locally constant on compact profinite $G$, so it factors through $G/U$ for an open normal $U$ and right translation by $U$ fixes $f$. The formula $(h\cdot f)(x)=f(xh)$ is a left action, and $(h\cdot\iota(m))(x)=\iota(hm)(x)$. Evaluation at $1$ proves injectivity. This is an agent proof ingredient. A DAG keyword search and blueprint_refs search for "coinduced" found no duplicate; Mathlib's abstract coinduction and compact-open TopRep coinduction do not state this discrete version.

For lem-exc-coinduced-continuous-acyclic I checked the inhomogeneous differential against 0DVG and the module $D(M)$ against the preceding new node. The omitted comparison is the only Stacks source for which this is an ingredient. On an $n$-cochain $F:G^n\to D(M)$ define $(hF)(g_1,\ldots,g_{n-1})(x)=F(x,g_1,\ldots,g_{n-1})(1)$. Compactness of $G$ makes this a continuous map into the *discrete* $D(M)$, not merely a jointly continuous function of $(x,g_i)$. Substituting the right-translation action into the differential gives $dh+hd=1$ for $n>0$; in degree one the calculation reads $F(g)(x)=(dF)(x,g)(1)+F(xg)(1)-F(x)(1)$. This proves the intended vanishing once the continuity and cancellation are formalized. I checked the whole DAG and blueprint for coinduction/acyclicity and found no statement of it.

Step 1 of the item uses the exact-complex statement, the existing Mathlib-leaf nodes lem-weil-pbc-complex-ses-homology-long-exact and lem-weil-pbc-complex-ses-long-exact-naturality, and def-weil-pbc-delta-functor; each cited statement supplies precisely the assertion used. The degree-zero equality is the kernel of $d^0$, and left exactness uses underlying exactness from lem-exc-discrete-modules-abelian. Step 2 uses the new embedding and acyclicity statements, whose monomorphism and positive-degree vanishing are explicit; the zero induced map follows because its target is zero. Step 3 applies the exact hypotheses in lem-weil-pbc-effaceable-delta-functor-universal (Stacks 010T) and lem-weil-pbc-right-derived-universal-delta-functor (Stacks 015B): abelian source with enough injectives, abelian target $A$-modules, left exact additive invariants, and a positive-degree effacement for every object. These two nodes are generic tools from another unit, needed because this unit has no delta-functor theorem. Step 4 uses their universal properties in both directions; uniqueness makes the composites identities. Its remaining calculation is categorical identity composition.

I tested the new statements at $G=1$ (then $D(M)=M$ and positive cochain cohomology vanishes), $M=0$, and finite $G$ (every map is continuous, the right-translation coinduction is the ordinary acyclic coinduced module). For $G=C_2$ and $A=\mathbf F_2$ the degree-one contraction formula still works despite signs collapsing in characteristic two. I checked that no step assumes $M$ finite: only compactness of $G$ and discreteness of $M$ are used. I also checked that a continuous $G^n\to D(M)$ means continuity for the discrete topology on $D(M)$; the contraction's uniform continuity argument is the nontrivial point and is explicitly identified above. New nodes have statements only, with no proof sketches in those statements, no cycles, correct blueprint ancestry and places, and no Mathlib leaf asserted without an exact declaration and line.
