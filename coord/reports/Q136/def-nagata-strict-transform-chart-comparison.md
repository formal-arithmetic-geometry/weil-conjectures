# Worker report

## Files written

- `dag/nodes/sec-nagata-compactification/def-nagata-strict-transform-chart-comparison.json`: definition, status split; no exact Mathlib match. Statement unchanged. Added two existing well-definedness dependencies.
- `citations.json`: empty list, since this is a definition and its `proof` is empty as required by the stage-1 definition convention. The construction and exact statements used are reviewed below.
- `report.md`: this report. `searches.jsonl` is the unmodified log written by the required search command.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None requested. The earlier attachment was rejected for absence of the file. The current read clone now contains `AlgebraicGeometry.AffineBlowup.strictChartComparison` at `lean/WeilConjectures/Blowup/Affine/StrictTransformChart.lean:250`, with its quotient formula at 257. I read this as construction evidence, and obey the explicit instruction not to answer ATTACH again. No transitive sorry-free claim is made.

## WANTED

None. The current blueprint and the relevant Mathlib source are present locally.

## Problems found and changes

The imported definition named the raw chart map and the quotient ring, but did not record the justification that the map descends. Added existing `lemma-nagata-strict-chart-to-extended-blowup-chart` and `lemma-nagata-strict-chart-map-kernel` as statement dependencies: the definition needs their named proofs to construct its data. No theorem is hidden as a new definition and no new node simply repeats the item. The statement, source metadata, import flags, blueprint update and historical bypass note are preserved. No statement dispute arose.

The generic Mathlib quotient lift is available, but it requires a map of algebras and a proof of vanishing on the ideal. Those are supplied by two separate project nodes, so Mathlib alone does not furnish the whole item by specialization under its written data. The exact live source lines are `Ideal.Quotient.liftₐ` in `Mathlib/RingTheory/Ideal/Quotient/Operations.lean:471`, `liftₐ_apply` at 484 and `liftₐ_comp` at 489; the representative formula also uses `Ideal.Quotient.lift_mk` in `Defs.lean:150`. The single-file msearch grep output capped at early hits and misparsed line numbers as files; its actual output is recorded as such, and I read the declarations directly to resolve this.

## Construction

Here A and B are commutative rings, A maps to B, I is an ideal of A, and a belongs to I, as in the original chart data. Put b equal to the image of a in B, C equal to the base-change chart, alpha equal to the structural image of a in C, and T equal to Gamma_(alpha)(C), its power-torsion ideal. The current chart-ring definition makes this structural image and ideal explicit. These are the existing chart notions, not extra hypotheses on the item.

1. The original definition `def-nagata-strict-chart-to-extended-blowup-chart` supplies sigma from C to B[IB/b], and `lemma-nagata-strict-chart-to-extended-blowup-chart` states exactly: “Consequently $\sigma_a$ is a well-defined $B$-algebra homomorphism.” Thus the input map preserves all the operations needed here.
2. The revised `def-nagata-strict-transform-chart-ring` defines the source as C/T, where T is Gamma_(alpha)(C), and explicitly says that its final occurrence of a means alpha. Thus the ideal used in the construction is exactly the current definition's ideal, rather than torsion for an unspecified action. `lemma-nagata-strict-chart-map-kernel` states verbatim: “The kernel of $\sigma_a$ is exactly
$\Gamma_{(a)}(C_a(A,B,I))$.” In particular sigma vanishes on T. This uses only the theorem's statement, not its imported proof or an implicit identification of two localizations.
3. Set sigma-bar([z]) = sigma(z). If [z]=[z'], then z-z' belongs to T, so sigma(z)-sigma(z') = sigma(z-z') = 0 by step 2. This proves independence of representatives. On representatives, preservation of 0, 1, sums, products and B-scalars is exactly the corresponding property of sigma from step 1. Every quotient element has a representative, so these identities hold on the quotient, and the displayed formula determines the map uniquely. This is the elementary quotient construction implemented by Mathlib's lift; it is not a further non-elementary lemma needing a new node.

The item remains a definition, with no theorem proof steps. Its four statement dependencies expose its data and the named well-definedness proofs. No claim of injectivity, surjectivity, isomorphism, localization compatibility or cocycle compatibility is made here.

## Review by Q136

I read the current main-20261015 blueprint definition (order 158), the current blow-up unit section, the DAG chapter and unit records, the raw-map definition, the strict-chart quotient definition, the power-torsion definition, and both cited theorem statements. I also read `StrictTransformChart.lean` through the construction at lines 249–259, and the Mathlib quotient lift declarations and representative formula at the lines listed above. This follows the unit's strict-chart quotient construction and does not invoke SGA or change the chapter route.

For construction step 1, the raw-map definition has precisely the target B[IB/b] and the formula on pure tensors. The well-definedness theorem explicitly supplies a B-algebra homomorphism; I do not infer that assertion merely from a definition. For step 2, the quotient definition supplies precisely C/T and the kernel theorem supplies exactly T=ker(sigma), so vanishing follows by membership in the kernel without extra hypotheses. Neither theorem depends on this comparison definition. For step 3, I wrote the representative calculation out instead of saying only “descend”; it uses no facts beyond these statements and the elementary meaning of a quotient ring. The quotient is by an ideal, and all rings here are commutative, so no two-sidedness issue or domain assumption is hidden. No finite-generation, Noetherian, reducedness, flatness or nonzerodivisor hypothesis is needed.

I tested the cases a=0 (both localized chart target and torsion quotient are zero rings), a a unit (the torsion ideal is zero and the map is the ordinary base-change chart map), and a nilpotent image b, for example A=Z, I=(2), a=2, B=Z/4Z. In the latter case the target localization is zero, and a is nilpotent on C, so T=C and its quotient is also zero. These checks show why one must not assume a or b is a nonzerodivisor, and they are compatible with the construction even for zero rings. With identity base change the construction reduces to the quotient map induced by the chart map, as expected.

I checked delivery-errors B through E: no new statement-only nodes, duplicate nodes or new Mathlib leaves are introduced; all needed existing notions and both well-definedness statements are named; the representative argument is elementary and written out; no circular dependency or off-unit proof citation is added; no theorem is moved into a new node; and all the original statement clauses are retained. The blueprint searches for strict-chart and power-torsion quotient return the existing map, kernel and quotient notions; localized comparisons and comparison isomorphisms have additional data or assertions and do not state this definition. Therefore `same_as` is empty. No proof step is longer than 2000 characters because this is a definition with an empty proof list. The review is my check of the construction, not an independent second reading.

### Repair of the returned delivery (2026-10-21)

The sole return in `coord/returns/Q136.md` concerns reviewed branch head `8f6cf6cef31`: landing refused the changed statement of `def-nagata-strict-transform-chart-ring`. I retained the sandbox's approved construction, citations and six logged Mathlib searches, compared the item against the current read repository, and reread every one of its four statement dependencies. The delivery command rebases the sandbox-owned fields onto current `origin/sheaf-dag`; I do not copy an older dependency into the delivery.

The substantive citation check is the source quotient. The current chart-ring statement now introduces a homomorphism of commutative rings A to B, an ideal I and a in I, defines C as B tensor_A A[I/a], and specifies alpha as the structural image of a. It makes Gamma_(alpha)(C) an ideal using the existing power-torsion-submodule node and defines C^st=C/T using the existing quotient node. These are exactly the ring, action and ideal used in construction step 2; I updated that step to use alpha explicitly. The original blueprint formula and the current expanded definition have the same quotient, with no new finiteness, injectivity or regularity assumption. No supplementary lemma about ideals is silently inferred from a definition: that well-definedness is already exposed by the chart-ring node's named dependency.

I also checked the current raw-map definition: it now explicitly constructs sigma by localization extension, restriction to the chart subalgebra, and the tensor map, with target B[J/b], J=IB. Its B-algebra structure is stated there and in the cited well-definedness theorem. The kernel theorem still says precisely that its kernel equals Gamma_(a)(C); here a acts through alpha as just specified. Thus step 1 uses the same map as step 2, and step 3's calculation sigma(z-z')=0 applies to exactly the ideal defining the current source quotient. The four statements checked are reproduced below so the citation validation is reviewable.

`def-nagata-strict-chart-to-extended-blowup-chart` (current statement):

> Let $f:A\to B$ be a homomorphism of commutative rings, $I\subseteq A$ an ideal and $a\in I$. Put $J=IB=(f(x):x\in I)\subseteq B$ and $b=f(a)\in J$. Use the chart algebras $A[I/a]\subseteq A_a$ and $B[J/b]\subseteq B_b$ of [def-nagata-blowup-chart-ring], and put $C_a(A,B,I)=B\otimes_A A[I/a]$ as in [def-nagata-strict-transform-basechange-chart-ring]. Define $\sigma_a:C_a(A,B,I)\to B[J/b]$ as follows: extend $A\xrightarrow{f}B\to B_b$ to $A_a\to B_b$, restrict this map to $A[I/a]\to B[J/b]$, and take the tensor-product homomorphism with the structural map $B\to B[J/b]$. Thus $\sigma_a$ is a homomorphism of $B$-algebras and on pure tensors of chart generators it satisfies
> $$\sigma_a\bigl(y\otimes(x/a)\bigr)=y\,f(x)/b\qquad(y\in B,\ x\in I).$$
> The localization and tensor-product maps used in this construction are those of [lem-weil-pbc-localization-away-universal-property] and [lem-weil-pbc-algebra-tensor-pushout-universal-property].

Statement SHA-256: `f8b953f76550c76491a6e317468c2239c798742470c70c20d2b161ef8023c84b`.

`def-nagata-strict-transform-chart-ring` (current statement):

> Let $A\to B$ be a homomorphism of commutative rings, let $I\subseteq A$ be an ideal, and let $a\in I$. Put $C=C_a(A,B,I)=B\otimes_A A[I/a]$ as in [def-nagata-strict-transform-basechange-chart-ring], and write $\alpha\in C$ for the image of $a$ under the structural map $A\to C$. Let
> 
> $$
> T=\Gamma_{(\alpha)}(C)=\{c\in C\mid \exists n\geq0,\ \alpha^nc=0\}
> $$
> be the power-torsion submodule of the regular $C$-module $C$ [def-nagata-power-torsion], viewed as an ideal using [lemma-nagata-power-torsion-submodule]. Define the affine strict-transform chart ring to be the quotient ring [def-weil-pbc-algebra-hom-quotient]
> 
> $$
> C_a^{\mathrm{st}}(A,B,I)
> =C/T
> =C_a(A,B,I)/\Gamma_{(a)}(C_a(A,B,I)),
> $$
> where the last occurrence of $a$ means its image $\alpha$ in $C$.

Statement SHA-256: `ab1125d0c6d0b0cae5953b1270b68e08389a6a828490cc142cc898b1ef1d9d25`.

`lemma-nagata-strict-chart-to-extended-blowup-chart` (current statement):

> The assignment defining $\sigma_a$ respects addition, multiplication, the
> localization relations in $A[I/a]$, and the two $A$-algebra structures.
> Consequently $\sigma_a$ is a well-defined $B$-algebra homomorphism.

Statement SHA-256: `4ded4deb77917129eef4e941189de7b9c6bdc987e02b228f393f1e96a273a834`.

`lemma-nagata-strict-chart-map-kernel` (current statement):

> The kernel of $\sigma_a$ is exactly
> $\Gamma_{(a)}(C_a(A,B,I))$.

Statement SHA-256: `e01a4c1243bbcbb7274b4c280e31e21a719cb24e0a218aa42226a36e3fec1187`.

The item remains a definition: `proof=[]`, `proof_deps=[]` and `citations.json=[]` are intentional. The construction above is the elementary representative argument; all four needed construction dependencies are in `stmt_deps`. Its source clause, target and meaning are preserved. There are no new nodes or new Mathlib searches in this repair, because neither the item statement nor the earlier search question changed. I reread the recorded results: they supply generic quotient lifts, not the chart map's vanishing theorem. The repaired `split_report.summary` now records the structural-image check, so this delivery contains a mathematical revalidation in addition to the automatic rebase. This addresses the return's one point without changing another worker's node.

## Not duplicates

No new nodes. All relevant existing map, quotient and kernel nodes are reused.

## Earlier delivery-tool failure (resolved on retry)

The previous attempt completed the citation repair but was blocked by server storage. Both required dry-run invocations exited 1 before verifying the DAG baseline. The first reported `[Errno 28] No space left on device` at `/tmp/sheaf-dag-base-k63i0aqt/dag/nodes/sec-smooth-purity/lem-sp-comparison-constant-generator.json`; the retry reported the same error at `/tmp/sheaf-dag-base-a_8qny9z/dag/nodes/sec-picard-framework/lem-pc-localization-preserves-nonzerodivisor.json`. These are the server's baseline extraction paths, not files in this delivery. No push was attempted, no check was bypassed, and no launcher or repository file was changed. The retry below passed the dry run, so this storage failure no longer blocks delivery. The existing dependency nodes retain their own queue states; this delivery does not claim to have proved them.


### Retry validation by Q136 (2026-10-21)

On this retry I opened the sole return entry in `coord/returns/Q136.md`, compared every field of the sandbox item with the current read clone, and reread all four cited node statements. The only item differences are the intended split fields: `blueprint.same_as`, `stmt_deps`, `mathlib_searches`, `status`, and `split_report`. The statement and all imported source metadata are unchanged. All four current statement hashes equal the hashes recorded in the repair above, including `ab1125d0c6d0b0cae5953b1270b68e08389a6a828490cc142cc898b1ef1d9d25` for the returned chart-ring citation. Thus no additional citation change has occurred since the saved repair.

I reopened the main-20261015 definition at order 158, its current unit section and the DAG chapter/unit records. The definition still asks for exactly the map induced on the power-torsion quotient. For the three construction steps above I checked, respectively, the raw map's explicit tensor construction and B-algebra property; the current quotient by the ideal of elements killed by a power of the structural image alpha, together with the kernel statement for that same action; and the representative calculation proving independence and preservation of operations. In particular, the definition uses the kernel theorem's statement, not a result hidden in its proof. The revised ideal description imposes no regularity or finiteness condition, including when alpha is nilpotent or zero. The elementary descent calculation therefore covers the zero-ring and nilpotent cases already recorded.

I reread the six saved search results and the generic Mathlib quotient lift at `Operations.lean:471`, its application and composition formulas at 484 and 489, and `Defs.lean:150`. The item and search questions have not changed, so I reused those searches rather than recording unrun replacements. No new nodes or leaves are created, and the definition's empty proof and citation lists are retained. I rechecked delivery-errors B through E with these statements open: no missing theorem is hidden behind the descent, no statement is replaced by its own clause as a new node, and the source and target rings are exactly the ones supplied by the cited definitions.

The required initial retry dry run exited successfully: `OK (not pushed) deliver/Q136/def-nagata-strict-transform-chart-comparison at ef155b3e610: preflight passed`. This confirms that the earlier server baseline extraction failure is resolved. After this report update the final dry run and push are performed by the prescribed delivery command; no repository or launcher file is edited, no compiler is run, and no check is bypassed.

## Unfinished work

No mathematical repair remains. The existing dependencies retain their own queue states; this item only defines the induced comparison map and does not assert their proofs are complete.
