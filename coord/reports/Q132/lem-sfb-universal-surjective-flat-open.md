# Q132 stage-1 repair: lem-sfb-universal-surjective-flat-open

## Files written
- dag/nodes/sec-six-functors-basics/lem-sfb-universal-surjective-flat-open.json: statement unchanged; four assembly steps, 2351 characters in total.
- dag/nodes/sec-six-functors-basics/lem-sfb-relative-universal-flat-open.json: statement, unsplit, no Mathlib match; source Stacks 05XB.
- dag/nodes/sec-six-functors-basics/lem-sfb-open-image-universal-surjectivity.json: statement, unsplit, no Mathlib match; source the open-image part of the proof of Stacks 05XC.
- citations.json: one literal statement quote per citation of every current parent step.
- report.md and repair.py (sandbox-only repair/report generation); searches.jsonl is the actual search tool log.

## Attachments
None. I searched the current WeilConjectures source by the exact blueprint tag and by universal flat/surjective-locus terminology. The source has no completed declaration of the item. I read Sheaf.AlgebraicGeometry.UniversalSurjectiveFlatOpen:62--72, whose exact statement has a `sorry` at line 72. Its docstring retains the seven returned arguments; it cannot be an attachment. No Lean file was changed and no compiler was run.

## WANTED
None: Stacks sources needed here are available locally.

## What was wrong and repaired
The return requires redistribution of the 5106-character proof, at least two independently claimable statement-only nodes of comparable size, and at most 3000 characters in the parent assembly. I copied the returned live version because the designated sandbox contained only dispatcher marker files: there was no earlier report, node copy or searches.jsonl to overwrite. The current main node contains the exact seven returned steps and the maintainer's earlier repair of the algebraic-space citation, which I preserved as the starting point. There is no statement dispute and no target statement change.

The new flatness theorem is the independent standard lemma 05XB, with its explicit complement formula. It is not a clause of the parent's existential statement: an open representing flatness alone is generally larger than the open representing flatness AND surjectivity; the parent does not give it. It drops closedness of q, says nothing about surjectivity, and needs the existing non-elementary 05VK source-flat-locus lemma. The new surjectivity theorem works for an arbitrary S-morphism with open image: it has neither flatness nor finite-type hypotheses. It isolates the two cartesian-square point-lifting arguments and the closed-image complement. Neither new node restates the parent, and neither receives a proof or proof dependencies. Their argument sizes are original Steps 1--3 versus Steps 5--7 (the latter includes two different point lifts); original Step 4 remains explicit in the parent. This is the human-requested re-split, not a shortened proof without new work items.

## Review by Q132
I read spaces-more-morphisms.tex, Tag 05XC, label spaces-more-morphisms-lemma-where-surjective-flat, statement and entire proof (lines 11729 onwards); Tag 05XB, label spaces-more-morphisms-lemma-where-flat, entire statement and proof (11687 onwards); and more-morphisms.tex, Tag 05VK, label more-morphisms-lemma-base-change-flatness-fibres (4759 onwards). The new flatness node is exactly 05XB for schemes, including its explicit F formula; 05VK supplies the formation of U after arbitrary base change. For the new surjectivity node I read the displayed W formula and both final directions in 05XC: after the source has proved that the image is open, flatness and finite presentation are unused. Thus the extracted node states precisely the hypotheses that this argument actually needs. Closed means a closed underlying map; no universal closedness, properness, Noetherianity, reducedness or finiteness restriction on test schemes has been added.

For current Step 1 I opened the new flatness node and checked that its hypotheses match p,q,f and that its conclusion quantifies over every h:T→B. It supplies F and the full equivalence, so evaluation on F gives flatness of f_F. The open-immersion definition identifies an open subscheme with its restricted structure sheaf, which justifies the notation A_F,C_F.

For current Step 2 I opened def-weil-finite-type-morphism and def-sbc-locally-finite-presentation: they provide exactly the affine finite-type and finite-presentation conditions used on compatible neighbourhoods. I opened lem-weil-pbc-finite-presentation-over-finite-type-algebra and read its matched Mathlib theorem in RingTheory/FinitePresentation.lean:208--211. With R→D→E, D is finite type over R, E is finitely presented over R and the map D→E is R-linear; these are exactly its hypotheses. I opened lem-weil-pbc-flat-lfp-open and read UniversallyOpen.of_flat in Morphisms/UniversallyOpen.lean:147--149. Step 1 gives the flatness it needs, and the affine argument gives local finite presentation. Hence the cited statement really gives the openness of I. This is the original finite-presentation and open-image argument, retained rather than hidden in a new statement.

For current Step 3 I checked the elementary restriction of closedness on actual closed subsets D∩q⁻¹(F); its image is q(D)∩F. The new surjectivity node assumes only that q_F is closed and I is open, both now established. Its formula is exactly V and its equivalence is over arbitrary F-schemes. The open-immersion definition supplies the restricted structure sheaf, and an open subset of an open is open in B.

For current Step 4 I opened def-pc-fibre-product and checked its test-object universal property and induced-map clause. Factorization through the inverse-image opens gives the two pullback identifications; the two projections determine the induced map, so it is the same f_T, not a different comparison. The open-immersion definition makes the inclusions monomorphisms (a restricted map of spaces and sheaves has at most one such factorization). The flatness equivalence in the first new node and the surjectivity equivalence in the second then give the two implications. No claim about point sets commuting with fibre products is assumed. The non-elementary point existence used in the extracted arguments is the exact statement of the existing scheme Mathlib leaf lem-weil-pbc-base-change-image, whose source I read at PullbackCarrier.lean:420--430. I preserved its role in the full argument allocations below, including singleton applications and both cartesian identifications.

I reviewed B--E of delivery-errors in full. New objects and hypotheses are introduced in each statement, with exact definition dependencies; sources use tags and tex labels, no SGA; new nodes have empty proof and proof_deps, and single-escaped TeX. Every parent citation is checked from the statement, with a literal quote in citations.json, rather than from a cited proof. I checked that neither new node cites the parent, so no cycle is introduced. No off-unit proof tool is used. No parent step exceeds 2000 characters, and the parent's complete assembly is below 3000. I read the chapter and the inherited unit record; this is a descendant through the existing alteration/Hilbert chain, not its key statement, so no unit record is changed. The null blueprint ancestor and inherited via chain are retained and extended by the parent for each new node; all same_as searches were negative.

## Edge cases
- Empty T: both universal predicates are vacuous and the unique map from the empty scheme factors through any open, even the empty open.
- Empty X: U is empty and F=S because p has empty image; every base change is flat. In the surjectivity node I is empty and V=S\q(Y); precisely tests disjoint from q(Y) make Y_T empty. This illustrates why the flatness open cannot replace the parent's simultaneous open.
- Empty Y: existence of f forces X empty. Both predicates hold over every test and V=S. Empty S forces all schemes over it empty.
- f an isomorphism: U=X, F=S and I=Y, so V=S; arbitrary tests work.
- Nonreduced field test: S=Spec(k), X=Spec(k), Y=Spec(k[ε]/(ε²)), f the quotient point. p is flat, lfp and closed; q is lft and closed. The flatness locus U is empty, so F is empty, while I=Y is open and the separate surjectivity node gives V=S. This checks that the two new statements separate real arguments and are not either equivalent to the original item.
- Parameter degeneration: p:A²→A¹ is not closed, so it is NOT an example satisfying the universal-flatness node; I did not assume a projection is closed merely because it is flat/lfp. The hypotheses remain the exact closedness required by 05XB.

## Mathlib search audit
All new-node searches were actually run with batch2/msearch.py Q132 lem-sfb-universal-surjective-flat-open; exact tool/query records and returned digests are in searches.jsonl and in the respective mathlib_searches. Two LeanFinder phrasings were tried for each actual new statement. Loogle and grep were also run for each, as was LeanSearch. LeanSearch for the flatness node was rate-limited and is recorded as unavailable, never as a negative hit. For the surjectivity node LeanSearch returned closed-dominant criteria and range_eq_univ, which do not represent a parameter locus. The initial generic-open-fibre searches remain logged; they led to choosing the actual source's separate flatness lemma rather than adding a new topological helper. Existing item searches and their recorded results were preserved, since its statement and the search question did not change.

Read hits include Flat, flat_iff, Flat.of_stalkMap (local/affine predicates only), UniversallyOpen.of_flat (already the existing open-map leaf), IsOpenImmersion.of_flat_of_mono (needs a monomorphism and constructs no parameter locus), Scheme.image_preimage_eq_of_isPullback (the existing point/image leaf), Surjective.instIsStableUnderBaseChangeScheme (permanence, not a universal locus), range_eq_range_of_surjective (an image equality under a surjective map), UniversallyClosed.of_comp_surjective (descent of universal closedness) and coborderRange (requires an immersion and is a target open of a different kind). None is either new statement or a one-line specialization of it.

## Not duplicates
lem-sfb-relative-universal-flat-open vs lem-sfb-relative-flat-locus-base-change: the existing node is a source flat locus with base-change compatibility; this node descends it through a closed source-family map to an open in the parameter base representing global flatness.

lem-sfb-relative-universal-flat-open vs lem-sfb-universal-surjective-flat-open: the parent represents simultaneous flatness and surjectivity; this separate lemma represents flatness alone without q closed, with the explicit F formula.

lem-sfb-open-image-universal-surjectivity vs lem-sfb-universal-isomorphism-open: the existing node represents isomorphisms under stronger separatedness/universal closedness hypotheses; this node only represents surjectivity from an open image.

lem-sfb-open-image-universal-surjectivity vs lem-sfb-relative-flat-locus-base-change: the existing node is a source flat locus with base-change compatibility; this node concerns the open image, a closed target-family map and universal surjectivity, with no flatness hypothesis.

lem-sfb-open-image-universal-surjectivity vs lem-sfb-fibrewise-flatness-criterion: the existing node is a local-at-a-point flatness criterion for a map and its fibre, not an open-image universal surjectivity theorem.

lem-sfb-open-image-universal-surjectivity vs lem-sfb-pointwise-flatness-base-change: the existing node proves pointwise flatness ascent/descent along a cartesian square; it neither assumes an open image nor constructs a surjectivity parameter open.

lem-sfb-open-image-universal-surjectivity vs lem-sfb-finite-type-local-closed-fibre-approximation: the existing node factors a local essentially finite-type ring homomorphism through a finite-presentation local model; it is not a parameter open or a surjectivity assertion.

lem-sfb-open-image-universal-surjectivity vs lem-sfb-universal-surjective-flat-open: the parent represents simultaneous flatness and surjectivity; this separate lemma represents surjectivity alone under only an open-image hypothesis, without flatness or finiteness.

I also compared the flatness node to lem-weil-pbc-openness-of-flatness (a finitely presented module's source flat locus over a fixed ring), lem-sbc-finite-flat-target-locus (a finite morphism to a locally Noetherian target), and lem-trf-free-subtraction-flatness (a generic basis subtraction criterion over integral fibres). None represents arbitrary base changes of the map of families. Blueprint search terms: 'surjective flat', 'open image', '05XB', '05XC', 'whole fibre', 'closed map', 'surjectivity locus', 'flat base change', 'where-flat', and 'surjectivity'; no equivalent blueprint statement was found. DAG searches included tags and full-statement keyword filtering, and source searches included both notion and exact blueprint tag.

## Complete allocation of the returned proof
These are the returned steps verbatim, retained so that every argument is accounted for. They are not proof fields in the two unsplit nodes: subsequent workers supply their proofs independently. Nothing is discarded by shortening the parent assembly.

### Returned Step 1 → lem-sfb-relative-universal-flat-open

Apply [lem-sfb-relative-flat-locus-base-change] to $p,q,f$. Its hypotheses are the assumed flatness and local finite presentation of $p$ and local finite type of $q$. Obtain the open subset $U\subseteq |A|$ of points where $f$ is flat, and, for every $h:T\to B$, the equality between the flat locus of $f_T$ and $\pi_A^{-1}(U)$.

Cited nodes: lem-sfb-relative-flat-locus-base-change.

### Returned Step 2 → lem-sfb-relative-universal-flat-open

Define $F=|B|\setminus p(|A|\setminus U)$. The complement of $U$ is closed, so $F$ is open because $p$ is a closed map. Give $F$ its restricted structure sheaf, hence its open subscheme structure [def-weil-open-immersion]. If $h:T\to B$ has image in $F$, every point of $A\times_BT$ projects into $U$. Step 1 and the pointwise definition of flatness [def-weil-flat-morphism] imply that $f_T$ is flat.

Cited nodes: lem-sfb-relative-flat-locus-base-change, def-weil-open-immersion, def-weil-flat-morphism.

### Returned Step 3 → lem-sfb-relative-universal-flat-open

Conversely suppose that $f_T$ is flat. Let $t\in T$ and $a\in A$ with $p(a)=h(t)$. Apply [lem-weil-pbc-base-change-image] to the fibre product $A\times_BT$ of $p$ and $h$, with projections $\pi_A,\pi_T$, and the subset $\{a\}$: $\pi_T(\pi_A^{-1}(a))=h^{-1}(p(a))$ contains $t$, so there is a point of $A\times_BT$ above $a$ and $t$. By Step 1 its projection $a$ belongs to $U$. Thus every point above $h(t)$ lies in $U$, so $h(t)\in F$. A morphism whose image lies in an open subscheme factors uniquely through it: restrict its continuous map and structure sheaf map to that open; the restricted sheaf of the open subscheme makes this a scheme morphism [def-weil-open-immersion]. We have proved, for every $T$, that $f_T$ is flat if and only if $h$ factors through $F$.

Cited nodes: lem-sfb-relative-flat-locus-base-change, lem-weil-pbc-base-change-image, def-weil-open-immersion.

### Returned Step 4 → parent current Step 2

Restrict to $F$, writing $A_F=p^{-1}(F)$, $C_F=q^{-1}(F)$ and $f_F:A_F\to C_F$. The restriction is flat by Step 1. It is locally of finite presentation: on compatible affine neighbourhoods over $\operatorname{Spec}R\subseteq F$, write the target as $\operatorname{Spec}D$ and the source as $\operatorname{Spec}E$. The affine-local finite-type and finite-presentation conditions [def-weil-finite-type-morphism, def-sbc-locally-finite-presentation] give $D$ finite type over $R$ and $E$ finitely presented over $R$. Apply [lem-weil-pbc-finite-presentation-over-finite-type-algebra] to $R\to D\to E$ to get finite presentation over $D$. These neighbourhoods cover $A_F$, proving the claim. Therefore [lem-weil-pbc-flat-lfp-open] implies that $I=f_F(|A_F|)$ is open in $|C_F|$.

Cited nodes: def-weil-finite-type-morphism, def-sbc-locally-finite-presentation, lem-weil-pbc-finite-presentation-over-finite-type-algebra, lem-weil-pbc-flat-lfp-open.

### Returned Step 5 → lem-sfb-open-image-universal-surjectivity

The restricted map $q_F:C_F\to F$ is closed. Indeed a closed subset of $C_F$ has the form $D\cap q^{-1}(F)$ for a closed $D\subseteq C$, and its image is $q(D)\cap F$, closed in $F$ by the hypothesis on $q$. Consequently $V=F\setminus q_F(|C_F|\setminus I)$ is open in $F$ and hence in $B$. Equip it with its open subscheme structure [def-weil-open-immersion]. For $b\in F$, membership in $V$ says exactly that every point of $C_F$ over $b$ belongs to $I$.

Cited nodes: def-weil-open-immersion.

### Returned Step 6 → lem-sfb-open-image-universal-surjectivity

Suppose $h:T\to B$ factors through $V$. Then it factors through $F$, so $f_T$ is flat by Step 2. Since $h$ lands in $F$, the projections $A\times_BT\to A$ and $C\times_BT\to C$ factor through the open subschemes $A_F$ and $C_F$ (Step 3), giving $\pi'_A:A\times_BT\to A_F$ and $g:C\times_BT\to C_F$ with $f_F\circ\pi'_A=g\circ f_T$. This square is a fibre product of $f_F$ and $g$ [def-pc-fibre-product]: given $u:W\to A_F$ and $v:W\to C\times_BT$ with $f_F u=g v$, the pair $(u,\pi_T v)$ is compatible over $B$ and gives $w:W\to A\times_BT$; then $\pi'_A w=u$ because open immersions are monomorphisms, and $f_T w=v$ because both have the same composites with the two projections of $C\times_BT$; $w$ is unique because a morphism to $A\times_BT$ is determined by its composites with $\pi_A$ and $\pi_T=\pi_T\circ f_T$. For any $c_T\in C\times_BT$, its image $c=g(c_T)\in C_F$ lies over a point of $V$, so Step 5 gives $a\in A_F$ with $f_F(a)=c$. Apply [lem-weil-pbc-base-change-image] to this fibre product square and the subset $\{a\}$: $f_T(\pi_A'^{-1}(a))=g^{-1}(f_F(a))$ contains $c_T$. Hence $f_T$ is surjective in the sense of [def-weil-surjective-morphism].

Cited nodes: lem-weil-pbc-base-change-image, def-pc-fibre-product, def-weil-surjective-morphism.

### Returned Step 7 → lem-sfb-open-image-universal-surjectivity

Suppose $f_T$ is surjective and flat. Flatness forces $h$ to factor as $h=\iota_F\circ h'$ with $h':T\to F$, by Step 3. The fibre product $C\times_BT$, with its projection to $C$ (which lands in the open $C_F=q^{-1}(F)$) and $\pi_T$, is a fibre product of $q_F:C_F\to F$ and $h'$ [def-pc-fibre-product]: a test pair compatible over $F$ is compatible over $B$, and conversely any test map to $C$ compatible with $h'$ lands in $C_F$ and factors uniquely through it (Step 3); $\iota_F$ is a monomorphism. Fix $t\in T$ and any $c\in C_F$ over $h(t)$. Applying [lem-weil-pbc-base-change-image] to this square and the subset $\{c\}$ gives $\pi_T(\pi_C^{-1}(c))=h'^{-1}(q(c))$, which contains $t$; hence there is a point $c_T\in C\times_BT$ over $c$ and $t$. Surjectivity [def-weil-surjective-morphism] lifts $c_T$ to $a_T\in A\times_BT$. The projection $a\in A_F$ of $a_T$ satisfies $f_F(a)=c$ by the defining commutative square of the base-changed map [def-pc-fibre-product]. Thus every point of $C_F$ over $h(t)$ lies in $I$, and Step 5 gives $h(t)\in V$. The open factorization argument of Step 3 [def-weil-open-immersion] now factors $h$ through $V$. This proves the required equivalence for arbitrary schemes $T$.

Cited nodes: lem-weil-pbc-base-change-image, def-weil-surjective-morphism, def-pc-fibre-product, def-weil-open-immersion.

## Work remaining / validation
The two new nodes are intentionally unsplit, as the return requests; each is a separate future proof task. The retained source-flat-locus node remains available as input to the 05XB task. No mathematical obstruction remains. Required remote dry run exited 0 and printed OK (not pushed) at cde7a96a76a; the server preflight passed, including the required DAG and split checks. This report was then corrected to cite the sorry at its actual current line 72; a final dry run and direct push follow.
