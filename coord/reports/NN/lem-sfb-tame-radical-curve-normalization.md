# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-tame-radical-curve-normalization.json`: unchanged statement; four assembly steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-radical-normalization-projective-etale.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-tame-galois-curve-normalization-smooth.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-cover-constant-field-marking.json`: statement, unsplit; no Mathlib match.

## Attachments

None. The project declaration `AlgebraicGeometry.tame_radical_curve_normalization` in `lean/Sheaf/AlgebraicGeometry/Curve/TameRadicalNormalization.lean:105` has `sorry`; searching `lean/WeilConjectures/` for the blueprint tag and radical/normalization vocabulary found no declaration of the entire item.

## Wanted literature

WANTED: de Jong, Families of curves and alterations (1997), §3.5, printed p.607, for lem-sfb-tame-radical-curve-normalization. The local PDF remains absent. The inherited report says a publisher PDF was read by the previous worker; I do not claim to have read that absent PDF. I read the local Stacks sources listed below and preserve the existing agent proof origin.

## Repair of the return

The sandbox initially contained only dispatcher brief markers, no node, report or search log. I copied the current repository item, which contains the returned ten steps, and saved that source as `returned-item.json` in the sandbox. This repair changes the proof and dependency graph substantively, and does not merely rebase the returned version. The parent statement and all existing audit/Lean/import/blueprint fields are retained.

The 8265-character proof is distributed as follows: returned steps 2--4 go to radical-normalization-projective-etale (2906 characters); steps 5--6 to tame-galois-curve-normalization-smooth (1971 characters); steps 7--10 to smooth-cover-constant-field-marking (3085 characters). Returned step 1 stays in the parent. These are three comparable arguments with different inputs and outputs: construct the normal projective cover and its unit locus; prove smoothness at the finite branch locus; refine a smooth projective marked cover to its canonical constants. They can be assigned independently. The first node assumes finiteness of the field extension and does not need roots of unity or geometric integrality; the second accepts any prime-to-characteristic Galois normalization, without radical or projectivity hypotheses; the third accepts any finite smooth projective cover, with no radical or Galois hypothesis. None restates the whole item.

Each new node is status `unsplit`, has only a self-contained statement, empty proof and proof_deps, null proof_origin and mathlib_match, explicit definition dependencies, and inherited chapter/unit and blueprint ancestry. The ancestor command returns None; I retained that inherited null and extended its via chain, rather than invent an imported ancestor. Blueprint searches normalization, radical, constant field, separable point, finite etale, Stein and Galois normalization found no identical blueprint statement. The unit and chapter routes are retained.

## Repair of the landing refusal, 2026-10-22

The return at branch head `573ddfca86e` says that the approved side completion was not promoted to the live DAG, and requires rebasing onto the current DAG and re-reading changed citations. I retained the sandbox split, citations, search outputs, search log and prior report. The mandatory initial dry run exited successfully at `efc739e9ad5`, rebuilding the delivery on the current server DAG. I compared `returned-item.json` against the current read-clone item: their JSON is identical, including the ten-step proof, statement, audit fields and dependencies. Relative to that live item this delivery still makes the substantive requested re-split: three independently assignable statement-only arguments and four assembly steps totaling 1903 characters. It does not re-push the old ten-step completion.

I re-opened the current statements of all 28 proof dependencies of the retained ten-step snapshot, rather than relying on whether their metadata changed. The actual parent citations are now the multiradical degree lemma and the three new nodes. Their statements still give respectively the Galois degree bound; finite surjective projective normalization with its etale unit locus and specified generic field; smoothness at separable branch points for prime-to-characteristic Galois degree; and canonical separable constants, geometric integrality, markings and the intersection. All four entries of citations.json are verbatim substrings of those current statements. The old dependencies remain available as sources for the complete preserved arguments below, and none is missing or merged.

I corrected one source precision issue while re-reading the local Stacks files. Tag 0BXS assumes both schemes are locally algebraic over K, so it must not be applied directly to Spec L over K when L has transcendence degree one. The first new node and its parent citation now instead name morphisms.tex Tag 035B (lemma-ubiquity-nagata) and Tag 0AVK (lemma-nagata-normalization-finite-general). On an affine chart Spec A of C, A is a finite-type K-algebra, hence Nagata by 035B. The generic morphism Spec L -> Spec A is affine, therefore quasi-compact and quasi-separated; its source is reduced and has one irreducible component; its only residue extension at the generic image is L/Frac A, finite by hypothesis, hence finitely generated as a field. These are exactly the five hypotheses of 0AVK. This avoids any assertion that L is finitely generated as an A-algebra. The mathematical statement and all recorded Mathlib search questions are unchanged. The old 0BXS source text is retained below solely as part of the verbatim historical arguments; this correction governs the new work item.

For B--E I checked the three new files still contain statements only, their hypotheses introduce every object, all assembly inputs come from the original hypotheses or preceding steps, and the independent three-way split preserves all nine delegated argument texts. The empty radical list, n=1, empty D and M, and a nontrivial finite separable constant cover remain valid cases. Reading the existing search outputs again finds no full Mathlib match; no search has been fabricated or repeated. No Lean or repository file was written and no compiler was run. The final server dry run and push below supersede earlier dry-run receipts in this retained report.

## Current-DAG repair continuation, 2026-10-23

The required initial dry run completed with exit 0 and `OK (not pushed)` at `15037d28cbe`. It rebuilt this retained split against the current server DAG. I compared the live item with `returned-item.json` by parsed JSON: no field differs. I compared all 28 current dependency files with the SHA-256 hashes in `current-dag-citation-audit.json`: all are unchanged, so there are no changed cited statements requiring a different argument. I nevertheless opened their statements again, including the four statements actually cited by the assembly. The current item still has the ten-step proof, while this delivery replaces it with the requested three new work items and four assembly steps; the released stage-1 repair note still requires that distribution. This is delivery of that substantive repair onto the current DAG, not promotion of the old completion by assertion.

I made assembly step 3 more explicit: choose e with de=n^r. In K the right side is nonzero because n is invertible, so d is nonzero and therefore invertible. This directly supplies the smoothness node's degree hypothesis without a characteristic case split. The parent statement and the three new statements remain unchanged, so the retained 18 logged Mathlib searches answer the same search questions and are reused. All four citation excerpts are still verbatim substrings. The statement-only nodes retain the affine normalization and unit-root argument, the residue-separability and smoothness argument, and the constants and marking argument, with the complete original texts below. The final dry run after this report update is the receipt applicable to the push.

## Search results

Each new node has six actual msearch.py calls: two LeanFinder phrasings, Loogle, two source greps, and LeanSearch. The raw output files and `searches.jsonl` are retained in the sandbox. All services answered. I read all returned signatures. Normalization commuting with smooth base change does not prove smoothness of a normalization; finite global sections of a proper integral scheme does not identify algebraic constants or supply geometric integrality and markings. Field-level finite etale product decompositions and Kummer cyclic-field theory do not give the scheme normalization theorem. No result matches a new statement or specializes to one in one line, so there are zero Mathlib leaves. Candidate sources read: Mathlib/AlgebraicGeometry/Normalization.lean (generic integral normalization and smooth base change), AlgebraicGeometry/Morphisms/Proper.lean (global sections a finite field), AlgebraicGeometry/Geometrically/Integral.lean (definition and permanence), RingTheory/Etale/Field.lean (finite separable algebra factors), and FieldTheory/KummerExtension.lean (cyclic Kummer fields). No compiler was run.

## Review by NN

On 2026-10-23 I re-read the local statements behind Stacks 035B/0AVK (Nagata normalization finiteness), 09EB and 0B8Y (Galois residue degrees and regular curve points), and 03H0/0BUG (canonical Stein factor and separable constants). The retained correction from 0BXS to 035B/0AVK remains necessary: Spec L need not be locally algebraic over K, whereas its generic residue extension over C is finite. In assembly step 1 the degree node gives exactly finite Galois and d dividing n^r; step 2 uses the first new node with the given unit locus; step 3 now explicitly checks that d is invertible before applying the smoothness node; step 4 uses geometric integrality of C and the finite smooth projective cover already obtained to get the canonical E, its marking, and the intersection E∩F. I checked these inputs against the four cited statements and their exact citation excerpts. The empty radical list and n=1 give degree one; empty D uses smoothness on the etale open; empty M yields an empty finite etale marking. No assumption of perfection is introduced. All new nodes remain statement-only and the full delegated arguments below remain preserved.


Continuation audit after the provider interruption: the only active dry run was polled to exit 0 and printed `OK (not pushed)` at `1924ae15a71`. This is a new server-built rebase, not an assertion that the previous side delivery was promoted. The current repository item is JSON-identical to retained `returned-item.json`; the sandbox differs in proof, proof_deps and split_report, retaining its substantive three-node re-split. I re-read all 28 current original proof-dependency statements, and saved their current statements and file hashes in `current-dag-citation-audit.json` in this sandbox for subsequent comparison. I also re-read all three new statements and the degree lemma: the four current citation excerpts remain verbatim, and all four steps have the required inputs. No changed live statement required a new mathematical route or a repeated search. The source correction to 035B/0AVK remains in force: a finite field extension is enough for the generic residue-field hypothesis, without treating Spec L as a finite-type K-scheme.

I checked again that projectivity in the first statement is over the affine Noetherian base Spec K, that the second statement requires prime-to-characteristic Galois degree and separable branch points even over imperfect K, and that the third uses the actual evaluated subfield E in L. In particular, a nontrivial separable constant cover is allowed and yields the claimed factorization over E; the empty marking introduces no finiteness or reducedness exception. The original nine delegated arguments remain verbatim in this report. The released stage-1 repair order explicitly authorizes the three statement-only nodes and the short assembly. The current Lean theorem still ends in sorry, so it cannot supply an attachment.


I read the item, all ten returned arguments, its complete Lean signature and sorry, the unit and chapter records, and sections B--E of delivery-errors.md. I read Stacks 03PL `lemma-kummer-sequence` in etale-cohomology.tex (including the explicit finite free unit-root algebra), 0BQL `lemma-finite-etale-covering-normal-unramified` in pione.tex, and 0BXS `lemma-relative-normalization-finite` in varieties.tex for the first node. These require respectively a unit radicand and invertible n, a normal integral base and finite etale cover, and locally algebraic schemes. Smooth integral C is normal; its affine opens are Noetherian; step 1 gives a finite field extension; the unit hypotheses are exactly those in the parent. Global projectivity is used over the affine Noetherian base Spec K, which is precisely the finite-over-projective theorem's valid case. The canonical generic identification is explicitly retained, rather than an abstract isomorphism of unrelated fields.

For the second node I read Stacks 09EB `lemma-galois-conclusion` in more-algebra.tex and 0B8Y `lemma-regular-point-on-curve` in varieties.tex. The first gives the residue-degree divisibility, not automatic separability in arbitrary residue characteristic. The degree hypothesis forces that residue degree prime to p; the derivative/minimal-polynomial argument is preserved below. The second applies to a closed point of an integral curve with normal local ring and separable residue field. The finite morphism makes points over the closed branch points closed. I did not infer smoothness of a regular curve over an imperfect field without checking residue separability.

For the third node I read Stacks 03H0 `theorem-stein-factorization-Noetherian` in more-morphisms.tex, 0BUG `lemma-proper-geometrically-reduced-global-sections` in varieties.tex, 0G80 `lemma-smooth-etale-permanence` in more-morphisms.tex and the projective refinement statement of lem-weil-pbc-finite-separable-base-refinement. The normal Stein node explicitly identifies the relative algebraic closure inside the function field and the canonical evaluation construction; the generic equation therefore specifies the actual E, not an arbitrary isomorphic field. Smoothness gives geometric reducedness for the separability assertion. Geometric connectedness plus smooth regular local rings after every extension gives geometric integrality; this full argument remains assigned to the new node. For P=Y×_C M, both finiteness and etaleness are base-changed and composed over K; cancellation along finite separable E/K gives etaleness over E, and a K-spanning family also spans over E. Reduction follows from an etale morphism to reduced M. Applying the same normal constants identification to C and 0BUG(8) gives K algebraically closed in F and then E∩F=K.

I opened the statement of every dependency used by each original step, rather than citing its proof. The preserved record below lists each of them alongside the exact argument. In particular, lem-fin-finite-over-projective asserts projectivity over an affine base, lem-sfb-finite-etale-normal-generic-components identifies precisely the field component with its normalization, lem-sbc-dvr-galois-normalization-ramification-dvd gives f|d without a separability hypothesis on residues, and lem-sfb-normal-stein-constant-field gives the canonical evaluation factorization and algebraic constants.

The new assembly step 1 uses lem-sfb-multiradical-galois-degree, whose statement explicitly gives finite Galois L/F and [L:F]|n^r, allowing r=0 and reducible binomials. Assembly step 2 uses the entire first new statement: its inputs are the given functions and U, and all its conclusions are exactly the finite normal projective curve and etale-open data needed later. Assembly step 3 uses the second new statement: the finite normal integral curve comes from step 2, Galois and the invertible degree from step 1, and D is finite etale by hypothesis. Assembly step 4 uses the third new statement: C is geometrically integral by the original hypothesis, Y is smooth/projective/integral by steps 2--3, ν is finite surjective by step 2, and M lies in its etale open because it is disjoint from D. That statement supplies every remaining conclusion, including the specified generic factorization and field intersection. citations.json contains a verbatim statement excerpt for every dependency in these four steps.

Small cases checked: r=0 gives L=F and the normal smooth base curve itself; n=1 has the same effect. An empty U imposes no unit conditions and claims etaleness only on the empty restriction. Empty D means etale composition alone establishes smoothness; empty M gives the empty reduced finite etale scheme over E. Degree d=1 satisfies the invertibility hypothesis. Over an imperfect field a nonseparable constant extension is excluded by smoothness, rather than assumed away by perfection. A finite constant extension Y=C_E is an allowed non-geometrically-integral K-cover; refinement recovers its actual E and the marking over E, so the third node does not silently assume E=K. There is no statement dispute or change to the parent, no SGA source, and no new non-elementary step over 2000 characters. The repair is the requested distribution of all existing arguments; none of them is discarded.

## Complete retained arguments, by new work item

These are the original proof texts, copied verbatim for the workers who will split the three statement-only nodes. They are report material, not proof steps on an unsplit node. Each original source and dependency list is preserved.

### lem-sfb-radical-normalization-projective-etale

Returned step 2 (1041 characters):

Write $Y=\widetilde C$ and $\nu:Y\to C$. By [lem-weil-pbc-normalization-in-residue-field-extension], applied to the generic point of the separated scheme $C$ and the finite extension $L/F$, this is an integral normal scheme with function field $L$. The finiteness theorem [lem-fin-normalization-extension-finite] makes $\nu$ finite. The scheme $C$ is Noetherian by [lem-weil-pbc-finite-type-over-noetherian], applied over the field $K$. On each nonempty affine open $\operatorname{Spec}A\subset C$, [lem-sc-integral-closure-dedekind-surjective-fibres] applies: $A$ is a Noetherian domain of dimension one because $C$ is a finite-type integral curve. The dimension assertion follows from [lem-weil-pbc-dense-open-dimension-comparison] applied to this nonempty, hence dense open of the integral curve. Its integral closure in $L$ is a Dedekind domain, and the spectrum map is surjective. These charts show that $Y$ has dimension one and that $\nu$ is surjective. The charts glue as the given normalization by [def-fin-normalization-extension].

Cited nodes: lem-weil-pbc-normalization-in-residue-field-extension, lem-fin-normalization-extension-finite, lem-sc-integral-closure-dedekind-surjective-fibres, def-fin-normalization-extension, lem-weil-pbc-dense-open-dimension-comparison, lem-weil-pbc-finite-type-over-noetherian.

Source: literature/stacks-project/morphisms.tex; Tags 035H, 035I, 035L (normalization); algebra.tex Tag 09IG (dimension-one integral closure); varieties.tex Tag 0BXS (relative normalization finite).

Returned step 3 (800 characters):

The scheme $\operatorname{Spec}K$ is affine and Noetherian, and $C\to\operatorname{Spec}K$ is projective in the convention of [def-pc-projective-morphism], because $C$ is a smooth projective curve [def-pc-smooth-projective-curve]. The morphism $\nu:Y\to C$ is finite by step 2. Apply [lem-fin-finite-over-projective] with $S=\operatorname{Spec}K$, $T=C$ and $h=\nu$: since $S$ is affine, the composite $Y\to\operatorname{Spec}K$ is projective in the convention of [def-pc-projective-morphism], i.e. there are $N\geq0$ and a closed immersion $Y\hookrightarrow\mathbf P^N_K$ over $K$; this is also projectivity in the convention of [def-kun-projective]. In particular $Y/K$ is proper by [lem-kun-projective-implies-proper] and of finite type; it is an integral projective curve with function field $L$.

Cited nodes: lem-fin-finite-over-projective, lem-kun-projective-implies-proper.

Source: literature/stacks-project/morphisms.tex; Tags 0B3I and 0C4P (finite over projective), 01WC (projective implies proper), as packaged in the cited nodes; over the affine base Spec K the embedding is into a finite projective space.

Returned step 4 (1065 characters):

Put $U=C\setminus D$. The smooth scheme $C$ is normal by [lem-trf-smooth-geometrically-normal]. On any nonempty affine $V=\operatorname{Spec}R\subset U$, all $a_j$ are units. Starting with $R_0=R$, form $R_j=R_{j-1}[T_j]/(T_j^n-a_j)$ successively. Each $\operatorname{Spec}R_j\to\operatorname{Spec}R_{j-1}$ is finite etale by [lem-sfb-unit-binomial-finite-etale]. Therefore $W=\operatorname{Spec}R_r\to V$ is etale by [lem-weil-pbc-etale-composition-cancellation]; it is finite directly from the basis of monomials $T_1^{e_1}\cdots T_r^{e_r}$, $0\leq e_j<n$. Sending $T_j$ to $\alpha_j$ gives a surjection of the generic algebra $R_r\otimes_R F$ onto $L$: its image is $F[\alpha_1,\ldots,\alpha_r]$, a finite-dimensional domain, hence a field, and equals $L$. By [lem-sfb-finite-etale-normal-generic-components], that field quotient selects one normal integral open and closed component of $W$, and that component is the normalization of $V$ in $L$. Hence $\nu^{-1}(V)\to V$ is etale. These affine opens cover $U$, so $\nu$ is etale above $U$. For $r=0$ take $W=V$.

Cited nodes: lem-trf-smooth-geometrically-normal, lem-sfb-unit-binomial-finite-etale, lem-weil-pbc-etale-composition-cancellation, lem-sfb-finite-etale-normal-generic-components.

Source: literature/stacks-project/etale-cohomology.tex; Tag 03PL, lemma-kummer-sequence, explicit unit-root algebra; pione.tex Tag 0BQL, componentwise normalization; varieties.tex Tag 056T.

### lem-sfb-tame-galois-curve-normalization-smooth

Returned step 5 (1293 characters):

Let $y\in Y$ lie over $x\in D$. The point $x$ is closed and $\kappa(x)/K$ is finite separable because $D/K$ is finite etale: apply [lem-weil-pbc-etale-algebra-residue-field-separable] to its affine algebra over $K$. The local ring $A=\mathcal O_{C,x}$ is normal by [lem-trf-smooth-geometrically-normal]. Since $\kappa(x)/K$ is finite separable, [lem-sfb-normal-curve-separable-point-smooth], applied to $C$ at $x$, makes $A$ a DVR. The normalization localizations over $A$ are the integral closures localized at the primes above its maximal ideal, by [def-fin-normalization-extension]. Apply [lem-sbc-dvr-galois-normalization-ramification-dvd] with the finite Galois extension $L/F$ and the integer $d=[L:F]$: it gives $[\kappa(y):\kappa(x)]\mid d$. In characteristic $p>0$ this degree is prime to $p$. For any $b\in\kappa(y)$ its minimal-polynomial degree over $\kappa(x)$ divides this degree by the tower formula. An inseparable irreducible polynomial has derivative zero, hence all exponents divisible by $p$, and therefore degree divisible by $p$, a contradiction. In characteristic zero irreducible polynomials have nonzero derivative and are separable. Thus $\kappa(y)/\kappa(x)$ is separable in either characteristic. Composing with $\kappa(x)/K$ gives a finite separable $\kappa(y)/K$.

Cited nodes: lem-sfb-normal-curve-separable-point-smooth, lem-trf-smooth-geometrically-normal, def-fin-normalization-extension, lem-sbc-dvr-galois-normalization-ramification-dvd, lem-weil-pbc-etale-algebra-residue-field-separable.

Source: literature/stacks-project/more-algebra.tex; Tag 09EB, lemma-galois-conclusion (residue degree divides Galois degree); elementary derivative criterion supplies separability; varieties.tex Tag 0B8Y for the base local DVR.

Returned step 6 (678 characters):

Every point $y$ above $D$ is closed: in a finite affine chart its prime lies above a maximal ideal, hence is maximal by [lem-weil-pbc-integral-prime-over-maximal-maximal]. Its local ring is normal by step 2 and its residue extension over $K$ is finite separable by step 5. Apply [lem-sfb-normal-curve-separable-point-smooth] to the integral curve $Y/K$, obtaining smoothness at each such $y$. Over $U$, the map $\nu$ is etale and $U/K$ is smooth, so [lem-sbc-smooth-relative-dimension-permanence] gives smoothness there. Together these neighbourhoods cover $Y$, proving that $Y/K$ is smooth. No assertion that every regular curve over an imperfect field is smooth has been used.

Cited nodes: lem-sfb-normal-curve-separable-point-smooth, lem-sbc-smooth-relative-dimension-permanence, lem-weil-pbc-integral-prime-over-maximal-maximal.

Source: literature/stacks-project/varieties.tex; Tag 0B8Y, lemma-regular-point-on-curve; smoothness off D follows by etale/smooth composition.

### lem-sfb-smooth-cover-constant-field-marking

Returned step 7 (948 characters):

Apply [lem-sfb-normal-stein-constant-field] to the proper dominant morphism $Y\to\operatorname{Spec}K$. Its source is normal integral and of finite type by steps 2--3. The theorem constructs the canonical factorization through $\operatorname{Spec}\Gamma(Y,\mathcal O_Y)$, identifies this field inside $L$ with the elements algebraic over $K$, and proves its finiteness over $K$. Thus this ring is exactly the specified $E$, the structural morphism factors canonically through $\operatorname{Spec}E$, and $Y/E$ is proper with geometrically connected fibre. Smoothness over $K$ implies geometric reducedness by [lem-trf-smooth-geometrically-normal]. Now [lem-pc-proper-geometrically-reduced-global-sections-separable] applied to the field of global sections gives that $E/K$ is separable. Finally [lem-weil-pbc-finite-separable-base-refinement] applies to the smooth projective $Y/K$ and its factorization, giving that $Y/E$ is smooth and projective.

Cited nodes: lem-sfb-normal-stein-constant-field, lem-trf-smooth-geometrically-normal, lem-pc-proper-geometrically-reduced-global-sections-separable, lem-weil-pbc-finite-separable-base-refinement.

Source: literature/stacks-project/more-morphisms.tex; Tag 03H0 (normal Stein factor); varieties.tex Tag 0BUG (separability of proper geometrically reduced global sections); more-morphisms.tex Tag 0G80 and morphisms.tex Tag 0C4Q (base refinement).

Returned step 8 (565 characters):

For any field extension $E'/E$, the scheme $Y_{E'}$ is nonempty and connected by geometric connectedness from step 7. It is smooth over $E'$ by smooth base change [lem-sbc-smooth-relative-dimension-permanence]. On smooth affine charts [lem-weil-pbc-smooth-over-field-regular-local] makes every local ring regular. Thus [lem-sc-regular-connected-integral] makes $Y_{E'}$ integral. This proves that $Y/E$ is geometrically integral. The scheme and its generic point have not changed on factoring the structure morphism, so its function field remains the specified $L$.

Cited nodes: lem-sbc-smooth-relative-dimension-permanence, lem-weil-pbc-smooth-over-field-regular-local, lem-sc-regular-connected-integral.

Source: literature/stacks-project/properties.tex; Tags 0569 and 033N, connected regular schemes are integral; smooth base change and regularity of smooth field algebras.

Returned step 9 (940 characters):

Let $P=Y\times_C M$. Since $M\subset U$, the morphism $P\to M$ is etale by [lem-weil-pbc-etale-scheme-base-change] and finite by [lem-trf-finite-radicial-basechange], using steps 2 and 4. Composing with finite etale $M/K$ shows $P/K$ finite etale, by [lem-trf-finite-radicial-basechange] and [lem-weil-pbc-etale-composition-cancellation]. By [etale-proposition-etale-reduced], $P$ is reduced because $M$ is reduced, so it is already the reduced inverse image required in the statement. Its map to $Y$ gives the $E$-structure. The map $\operatorname{Spec}E\to\operatorname{Spec}K$ is etale by [lem-weil-pbc-finite-separable-extension-etale]; etale cancellation then shows that $P/E$ is etale. It is finite over $E$: write the finite $K$-scheme as $\operatorname{Spec}B$; any finite $K$-spanning set of $B$ also spans $B$ over $E$, since $K\subset E$. Hence $P/E$ is finite etale. The empty $M$ gives the empty finite etale scheme throughout.

Cited nodes: lem-weil-pbc-etale-scheme-base-change, lem-trf-finite-radicial-basechange, lem-weil-pbc-etale-composition-cancellation, etale-proposition-etale-reduced, lem-weil-pbc-finite-separable-extension-etale.

Source: literature/stacks-project/morphisms.tex; Tags 02GN (composition), 02GO (base change), 02GW (cancellation); etale.tex Tag 025O (etale sources over a reduced base are reduced); finite base change and composition as in the cited node. E-finiteness is the explicit spanning argument.

Returned step 10 (632 characters):

Apply [lem-sfb-normal-stein-constant-field] also to $C\to\operatorname{Spec}K$; it applies because $C/K$ is projective, hence proper by [lem-kun-projective-implies-proper], and smooth, hence normal by [lem-trf-smooth-geometrically-normal]. It identifies the subfield of $F$ algebraic over $K$ with $\Gamma(C,\mathcal O_C)$. Since $C/K$ is geometrically integral, [lem-pc-h0-proper-variety](2) identifies this global-section field with $K$. Thus $K$ is algebraically closed in $F$. An element of $E\cap F$ is algebraic over $K$ by the definition of $E$, so belongs to $K$; the reverse containment is immediate. Therefore $E\cap F=K$.

Cited nodes: lem-sfb-normal-stein-constant-field, lem-kun-projective-implies-proper, lem-trf-smooth-geometrically-normal, lem-pc-h0-proper-variety.

Source: literature/stacks-project/more-morphisms.tex; Tag 03H0, normal Stein factor; morphisms.tex Tag 01WC (projective implies proper); varieties.tex Tag 0BUG(8), global sections of a proper geometrically integral scheme.

## Not duplicates

lem-sfb-radical-normalization-projective-etale vs lem-sfb-cover-nested-cartier-preparation: the existing node normalizes a generic field factor of an already given finite etale cover and then modifies two boundary ideals to effective Cartier divisors; it assumes that cover and does not construct radical unit-root covers or assert projectivity of their curve normalization. The new node instead constructs the normalization for specified radicals and proves its unit locus is etale and its curve is projective. Both use Nagata finiteness, but neither statement specializes to the other in one line.

lem-sfb-smooth-cover-constant-field-marking vs lem-sfb-equivariant-projective-stein-factor: the new node assumes a smooth finite projective curve cover and proves the actual algebraic constants, smooth projectivity over them, finite etale marking over them, and E∩F=K; this existing node supplies a normal/Stein factorization over a general base, without the marked smooth curve conclusion or constants intersection.

lem-sfb-smooth-cover-constant-field-marking vs lem-sfb-noetherian-normal-stein-model: the new node assumes a smooth finite projective curve cover and proves the actual algebraic constants, smooth projectivity over them, finite etale marking over them, and E∩F=K; this existing node supplies a normal/Stein factorization over a general base, without the marked smooth curve conclusion or constants intersection.

The following same-tag pairs were examined in the whole DAG. Sharing a source does not make their statements identical.

lem-sfb-radical-normalization-projective-etale vs lem-sbc-finite-normal-dense-open-comparison: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Comparison of a finite normal cover with an etale extension over a dense open, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-sbc-finite-normal-trait-purity: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Purity for a finite normal cover over a local base of dimension at most one, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-sbc-normal-integral-generic-hom-full: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Generic-point full faithfulness for finite etale covers of a normal integral scheme, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-sbc-finite-normal-dense-open-iso: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Finite normal extensions agree if their dense open restrictions agree, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-wf-curve-kummer-jacobian-tate-module: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Kummer identifies curve cohomology with the Jacobian Tate module, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-trf-excellent-base-marked-semistable-curve: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Marked semistable alteration of a curve over an arbitrary excellent base, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-trf-finite-etale-marking-sections: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Splitting a finite etale marking into disjoint sections after alteration, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs det-prop-diagonal-tower-system: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states The torsion diagonal classes as one morphism of inverse systems, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs sk-lem-geo-cartier: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states The cycle class of a Cartier divisor, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-sfb-stable-level-versal-branch-freeness: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Freeness on normalized abelian-level branches of a stable deformation, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-sfb-stable-relative-picard-kummer: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Relative semiabelian Picard object and smooth Kummer comparison, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-sfb-dm-finite-normalization-charts: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Finite normalization of smooth Deligne--Mumford stacks and its charts, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-sfb-unit-binomial-derivative-presentation: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Derivative certificate and inverse-generator presentation for a unit binomial, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-sfb-unit-binomial-finite-etale: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Finite etale algebra of a root of a unit, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-sfb-ramified-cartier-supported-purity: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Ramification multiplicity in the supported Cartier purity comparison, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-sfb-finite-etale-normal-generic-components: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Generic fields and normalization components of a finite etale cover, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-sfb-persistent-node-normalization: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Finite normalization at persistent nodes over an arbitrary trait, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-per-nodal-quotient-normalized-base-refinement: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Normalized base change of an ell-group marked nodal quotient, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-per-noetherian-prime-power-smooth-duality: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Prime-power diagonal smooth orientation over a Noetherian base, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-per-cartier-gysin-kummer-boundary: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Cartier Gysin normalization in the signed relative Kummer model, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs def-per-ordinary-kummer-first-chern: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Ordinary derived Kummer first Chern class, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-per-pure-principal-divisor-kummer-residue: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Localization residues of unit Kummer symbols when divisor purity is given, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-per-noetherian-supported-product-calculus: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Supported products and Cartier interchange on ordinary etale sites, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-per-divisor-purity-strict-local-criterion: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Strict-local complement criterion for regular divisor purity, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-per-strict-local-divisor-low-kummer: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Low-degree Kummer cohomology of a strict-local regular divisor complement, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-weil-pbc-reduced-algebraic-normalization-field-change: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Geometry and separable field change of reduced algebraic normalization, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs thm-sc-main: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Smooth-curve calculations, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-weil-pbc-normalization-geonormal-insep: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Normalization geonormal insep, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs thm-pur-kummer-affine-line: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Kummer computations on the line and the punctured line, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs def-asd-ordinary-finite-p1-arrows: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Canonical arrows and normalized data for ordinary finite projective-line duality, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs def-pur-kummer-line-geometry: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Canonical geometry and maps for the Kummer lines, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-pur-kummer-additivity: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Kummer additivity, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-pur-kummer-finite-biproducts: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Integral finite-basis cohomology and Kummer exactness, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs det-sp-tower-classes: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Kummer and diagonal classes of towers, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-pur-kummer-root-line-computation: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Roots-of-unity computation on the two lines, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs def-asd-ordinary-supported-kummer-boundary: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Relative supported Cartier Kummer boundary specification, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-pur-kummer-coefficient-base-change: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Base change of the Kummer coefficients, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs def-asd-ordinary-finite-p1-kummer-class: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Scalar Kummer class of O(1) with finite ordinary etale coefficients, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-asd-ordinary-supported-chern-normalization: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Ordinary Chern realization of a normalized supported class, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-pur-divisor-class: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Kummer class of a divisor and its $c_1$, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-pur-kummer-integral-root-comparison: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Integral basis reduction for the Kummer root sheaf, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-pur-cartier-class-agreement: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states The two Cartier divisor classes agree and pull back, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs def-asd-ordinary-finite-p1-data: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Normalized decomposition and adjunction data for ordinary finite projective lines, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs prop-pur-gm-relative-kummer: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states The affine line and the punctured line over a base, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs def-pur-frame-class: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Class of a frame, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-pur-twist-sheaf-locally-free: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states The twisting sheaves are locally free of rank one and derived complete, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-pur-supported-cup-functoriality: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Pullback and symmetry of supported Kummer cup products, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-pur-origin-class-projective-comparison: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Comparison of the supported affine-origin class with the projective Chern generator, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-pur-kummer-finite-free-comparison: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Normalized finite free Kummer cohomology comparison, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs def-asd-ordinary-supported-kummer-system: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Normalized ordinary supported Cartier Kummer map systems, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-asd-ordinary-supported-kummer: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Supported Cartier Kummer map for ordinary etale arbitrary finite coefficients, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-asd-ordinary-finite-p1-adjunction: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Ordinary etale projective-line adjunction with arbitrary finite invertible-exponent coefficients, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-sc-artin-schreier-polynomial-cover: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Surjective etale polynomial cover solving an Artin-Schreier equation, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-sc-artin-schreier-sequence-scheme: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Artin-Schreier short exact sequence for arbitrary schemes, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-sc-generic-kummer-residues: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states The generic Kummer residue sheaf, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-sc-as-sequence: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states The Artin–Schreier sequence, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-sc-field-kummer-h2-brauer-injection: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Kummer injection into the Brauer group of a field, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-sc-artin-schreier-scheme-section-data: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Construction of sectionwise Artin-Schreier maps, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-sc-artin-schreier-scheme-section-exact: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Exactness from specified Artin-Schreier section data, without that combined curve conclusion.

lem-sfb-radical-normalization-projective-etale vs lem-sc-field-artin-schreier-sequence: the new node constructs the projective curve normalization for a multiradical field and proves its etale unit locus; the existing node states Artin-Schreier exact sequence over a field, without that combined curve conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-trait-generic-normalization-charts: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Pointwise standard tame charts for a generic torsor over a DVR, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-root-normalization-generic-stalk-galois-model: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Galois integral-closure model for root-normalization residues, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-dvr-galois-root-factor-uniformizer: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states A tame root generates the maximal ideal in an integral-closure tensor factor, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-trait-generic-punctured-root-chart: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Punctured Kummer charts of a generic smooth-trait torsor, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-cartier-generic-stalk-galois-model: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Galois integral-closure models at generic Cartier DVR stalks, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-trait-generic-root-model: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Local normal root models containing the generic trait torsor as a dense open, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-strict-hensel-root-normalization-generic-etale: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Generic etaleness of the concrete strict-hensel root normalization, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-root-normalization-generic-stalk-residue-separable: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Separable normalization residue fields after the group-order root extension, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-regular-divisor-galois-punctured-root-chart: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Kummer charts for invertible-order torsors on a regular principal divisor complement, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-regular-divisor-strict-hensel-root-section: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states A group-order root cover admits a section over the strict henselization, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-root-normalization-generic-source-etale: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Generic source etaleness after root normalization, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-dvr-galois-components-root-cotangent: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states First-order root calculation for finite Galois field components, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-root-normalization-generic-source-etale-point: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Pointwise generic source etaleness after root normalization, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-dvr-galois-normalization-ramification-dvd: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Ramification and residue degrees in a Galois normalization divide the field degree, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-cartier-stalk-normalization-product: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Integral-closure product model of a Cartier torsor normalization over the actual DVR stalk, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-strict-hensel-root-finite-etale-model: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Finite etale extension of the punctured group-order root pullback, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-dvr-root-normalization-maximal-ideal: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Tame torsor ramification is killed by the group-order root over a DVR, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-root-normalization-generic-stalk-residue-degree-dvd: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Root normalization residue degrees divide the torsor group order, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-root-normalization-cotangent-root: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Root class spans the normalized stalk cotangent space, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-root-normalization-generic-stalk-maximal-ideal: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Maximal-ideal equality after the group-order root extension, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-root-normalization-root-not-square: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states The tame root has nonzero first-order class, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-strict-hensel-root-tame-normalization: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Finite tame normalization over a supplied root divisor, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-regular-divisor-galois-root-splitting: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Single root cover splits invertible-order torsors near a regular divisor, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-root-normalization-generic-stalk-unramified: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Unramified normalization stalks after the group-order root extension, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-root-normalization-generic-stalk-residue-degree-dvd-core: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Abstract normalization residue degree divisibility calculation, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-strict-hensel-root-purity-data: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Finite tame normalization model near the root divisor generic point, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-regular-divisor-prescribed-punctured-root-chart: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Punctured Kummer charts with a prescribed principal divisor equation, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-dvr-galois-components-root-not-square: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Nonzero first-order tame root class for finite Galois components, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sbc-cartier-generic-stalk-galois-model-core: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Selected geometric field-factor model and its compatible residue square, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-trf-valued-curve-etale-parameter: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states An etale rational parameter for a valued smooth function field, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-trf-curve-centred-valuation-dvr: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states A nontrivial centred valuation on a smooth curve and its etale coordinate, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sfb-kummer-normalization-boundary-etale: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Killing boundary ramification in normalized Galois tensor factors, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sfb-curve-closed-point-affine-local-model: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Affine local model at a closed point of a curve, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-sfb-normal-curve-separable-point-smooth: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Normal curve points with separable residue field are smooth, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-per-snc-root-punctured-torsor-splitting: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Simultaneous parameter roots trivialize an invertible-order punctured torsor, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-per-tame-trait-quotient-log-etale: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Tame trait quotient and change of logarithmic base, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-a1-nonconstant-normal-curve-map-flat: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states A nonconstant morphism of curves with normal target is flat, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs prop-weil-pbc-algebraically-closed-extension: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Algebraically closed extension for proper curves, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-weil-pbc-reduced-curve-normalization: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states A smooth finite modification of a reduced curve, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-exc-dvr-inertia-order-prime-part: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Prime-to-residue-characteristic part of finite inertia order, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-exc-dvr-galois-degree-data: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Global degree data for a finite Galois extension of a DVR, without this global curve-smoothness conclusion.

lem-sfb-tame-galois-curve-normalization-smooth vs lem-exc-finite-dvr-tame-inertia: the new node proves smoothness over an arbitrary possibly imperfect ground field for a finite prime-to-characteristic Galois curve normalization; the existing node states Finite discrete-valuation normalization and tame inertia character, without this global curve-smoothness conclusion.

lem-sfb-smooth-cover-constant-field-marking vs lem-trf-reduced-curve-normalization-genus: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states Normalization formula for the arithmetic genus of a reduced proper curve, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-trf-dejong-relative-marked-semistable: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states De Jong marked semistable model in the projective-bundle convention, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-trf-stein-smooth-generic-curve: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states Finite Stein base of a proper smooth generic curve, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-trf-marked-nodal-dualizing-degrees: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states Marked dualizing line bundle and contracted-component degrees, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-trf-nodal-curve-normalization-euler: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states Euler characteristic of a nodal curve from its normalization, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-trf-no-isolated-contracted-fibre-component: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states A curve modification cannot contract an isolated whole fibre component, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-trf-geometrically-integral-curve-factorization: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states Factorization with a geometrically integral generic curve, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-pc-h0-geom-connected: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states $H^0=k$ is equivalent to geometric connectedness, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-pc-base-change-closure-components: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states Components of a smooth projective curve over an algebraic closure, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-pc-scheme-connected-iff-idempotents: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states A nonempty scheme is connected iff its global sections have only the idempotents 0 and 1, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-pc-h0-proper-variety: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states Global sections of a proper scheme, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-pc-proper-geometrically-reduced-global-sections-separable: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states Separability of global sections of a proper geometrically reduced scheme, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-pc-alg-closed-reduced-algebra-no-idempotents-dim-one: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states A nonzero finite reduced algebra without nontrivial idempotents over an algebraically closed field has dimension 1, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-pc-global-sections-separable: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states Separability of global sections, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-sfb-gabber-global-snc-alteration: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states Gabber global projective alteration with a relative strict normal crossings boundary, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs def-sfb-dominant-function-field-map: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states Canonical function-field algebra of a dominant integral-scheme morphism, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-sfb-semilinear-equivariant-chow-modification: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states Semilinear equivariant projective Chow modification, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-sfb-finite-constant-projective-graph: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states Projectivity over a separated target after finite extension of constants, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-sfb-equivariant-curve-pencil: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states Equivariant curve-pencil preparation over a field, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-sfb-projective-fibre-product-closed-model: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states Finite projective-space embeddings of a fibre product and its closed models, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-sfb-normal-alteration-constant-regularization: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states Equivariant regularization of the constants of a normal alteration, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-sfb-normal-stein-constant-field: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states Normal Stein factor and its algebraic constant field, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-sc-proper-flat-global-sections: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states Proper flat geometrically reduced connected fibres have universal structure-sheaf pushforward, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-sc-rigidity: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states The rigidity lemma, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-per-h-projective-permanence: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states H-projectivity after factoring through a separated base morphism, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-per-normal-projective-compactification: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states Normal projective compactification over a complete trait, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-weil-pbc-proper-reduced-algclosed-global-sections-product: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states Global functions on a proper reduced scheme over an algebraically closed field, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-weil-pbc-finite-separable-base-refinement: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states Finite separable base refinement, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-weil-pbc-proper-flat-geometric-components-locally-constant: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states Geometric component count is locally constant in a proper smooth family, which does not include this marked-cover assertion.

lem-sfb-smooth-cover-constant-field-marking vs lem-sc-global-functions: the new node refines an already smooth finite projective curve cover to its actual algebraic constants, carries its etale marking to those constants, and computes E∩F; the existing node states Global functions on a proper curve, which does not include this marked-cover assertion.

## Unfinished work

The three new arguments are intentionally statement-only queue items for parallel work, as the return explicitly requires. No proof or Lean compilation is claimed for them. The first dry run requested comparisons with two additional Stein nodes now visible in the shared repository; I opened both and added their statement differences above. The next dry run passed server preflight at f9cfb607bed. No mathematical or structural repair point remains; final report formatting is checked by the last dry run before push.


