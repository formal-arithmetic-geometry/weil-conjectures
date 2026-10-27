## Worker report

Q17 split lem-per-cyclotomic-finite-etale-cover at stage 1 only. The sandbox is /home/ubuntu/weil-newtargets-sandbox/Q17/lem-per-cyclotomic-finite-etale-cover/.

Files written:

- dag/nodes/sec-deligne-laumon-a1/lem-per-cyclotomic-finite-etale-cover.json: item, seven proof steps, status split.
- dag/nodes/sec-deligne-laumon-a1/lem-per-cyclotomic-monic-positive-degree.json: statement, Mathlib leaf for monicity, positive degree and coefficient naturality.
- dag/nodes/sec-deligne-laumon-a1/lem-per-cyclotomic-field-root-criterion.json: statement, Mathlib leaf for the field-valued cyclotomic root criterion.
- citations.json: verbatim dependency-statement quotes for every step/node pair.
- searches.jsonl: real msearch.py results. write_split.py is a sandbox-only reproducibility aid, not a repository file.

Attachments: none. Searches of lean/WeilConjectures by the exact blueprint tag, cyclotomic/Cyclotomic, and the candidate polynomial names found no project declaration proving the whole item. The project cyclotomic-character and Tate-module declarations have different conclusions. lean/Sheaf also contains no candidate cyclotomic-polynomial theorem.

WANTED: none. I read the available ILO PDF and the named Stacks source files; the new leaves cite the pinned Mathlib source itself.

The imported item had a statement and search history but no proof or proof dependencies. No mathematical error was found in its statement. I retained every hypothesis and conclusion, adding only inline explanations of primitive roots, geometric inertia and references for the polynomial, localization, quotient and fibre-product notions already used. In particular, no finiteness or tame-action assumption on the acting group, and no regularity or Noetherian hypothesis on W, has been introduced. The inherited searches are preserved; this delivery adds its own whole-item queries and exact auxiliary matches.

Nothing remains unfinished at this split level. Both new nodes are exact Mathlib leaves, with no proof to postpone. No Lean was written and no compiler or Lake command was run.

## New nodes

lem-per-cyclotomic-monic-positive-degree is a Mathlib leaf: Polynomial.cyclotomic.monic, Basic.lean:292; Polynomial.degree_cyclotomic_pos, Basic.lean:331; Polynomial.map_cyclotomic, Basic.lean:263. I also read map_cyclotomic_int at line 241 to check that the integer-image convention is the same. These are three directly matching declarations, one per clause, with no intermediate theorem missing.

lem-per-cyclotomic-field-root-criterion is a Mathlib leaf: Polynomial.isRoot_cyclotomic_iff, Roots.lean:98, specialized to a field with nonzero image of N. I read the surrounding CommRing and IsDomain variables and the two-field IsPrimitiveRoot definition in PrimitiveRoots.lean:63-65. The statement uses exactly that definition, rather than assuming that a characteristic-zero result works in positive characteristic.

Each new node was searched by its own mathematical content with LeanFinder, Loogle, LeanSearch and msearch grep; actual queries, hits and verdicts are recorded on the nodes and in searches.jsonl. All services answered. One intermediate grep targeted Basic.lean directly and its output omitted the filename; that logged attempt was not used as location evidence. The subsequent directory grep returned the correct file and all four line numbers. The whole-item search was also tried in two phrasings and did not return the scheme-cover assertion.

## Not duplicates

lem-per-cyclotomic-field-root-criterion vs lem-sc-primitive-root: the existing node asserts existence and cyclicity of roots over an algebraically closed field; the new node identifies roots of a specific cyclotomic polynomial over every field of admissible characteristic. Existence alone does not supply this identification.

lem-per-cyclotomic-field-root-criterion vs lem-pur-primitive-root-etale-basis: the latter starts with a chosen primitive root over a field and trivializes a sheaf; it does not characterize cyclotomic polynomial roots.

lem-per-cyclotomic-field-root-criterion vs lem-asd-affine-roots-representability: the latter represents all roots of T^n-1, without isolating those of exact order n. Its statement does not mention cyclotomic polynomials.

lem-per-cyclotomic-monic-positive-degree vs lem-weil-pbc-monic-quotient-free: the existing node assumes a monic polynomial of given degree and computes its quotient module; the new node supplies the cyclotomic polynomial's monicity, positive degree and coefficient naturality.

I searched the whole DAG for cyclotomic polynomial, primitive-root/cyclotomic combinations and the full candidate declaration names. The only existing statement about this cyclotomic cover was the item itself. The mentions of isRoot_cyclotomic_iff and cyclotomic.monic in other nodes' search histories are not their statements. Whole-blueprint searches for cyclotomic, cyclotomic polynomial, primitive, primitive root, monic derivative and positive degree found no blueprint node stating either new lemma. Both new nodes therefore have same_as = []. No new Stacks-tagged theorem was made: all the standard-etale, unit and permanence facts reuse existing nodes.

## Review by Q17

I read ILO, Travaux de Gabber, VIII 5.3.6 and Lemma 5.3.7 on printed page 124 (PDF page 130). The proof really takes X' times Spec(Z[1/N,mu_N]) with trivial action on the second factor; the present item verifies that preparatory base change, not the rest of the rigidification theorem. I also read the current latest blueprint's ancestor statement and proof at lem-per-artin-gabber-affine-curve, and the chapter and unit records. The ancestry through the abelian inert rigidification lemma is retained. Below that ancestry this is only the polynomial verification of the root-adjoining step, so the unit and chapter route is unchanged and no SGA source is used.

For the first new leaf I read Basic.lean lines 229-333: the coefficient-map identity, monicity and positivity agree hypothesis by hypothesis with the new statement. Positivity requires a nonzero ring and positive N, both explicitly present. Naturality allows a zero target ring S. For the second leaf I read Roots.lean lines 40-103: the domain instance holds for a field, and the required NeZero (N : K) is explicitly assumed. No assertion is made in characteristic dividing N. These polynomial facts are strictly smaller than the item: they contain no scheme cover, global unit conclusion, base-change assertion or inertia assertion. They are neither a relabeling of the item nor artificial unresolved lemmas.

Step 1 uses the new polynomial-data leaf for monicity and positive degree, lem-weil-pbc-monic-quotient-free for the actual finite basis, and def-weil-finite-integral-morphism for finiteness of the affine morphism. I opened each statement. The monic-quotient node expressly says that the quotient is finite; it is not merely a definition of freeness. Separating the N factor in the defining finite product gives zeta^N=1 directly. No irreducibility claim over Z[1/N] or field is needed.

Step 2 uses the statement of lem-weil-pbc-standard-etale-monic-derivative, which expressly asserts that Spec of R[T,Y]/(f,Yf'-1) is etale. I read Stacks algebra.tex, definition-standard-etale (00UB) and lemma-standard-etale (00UC), item (1). I recomputed the derivative identity and the inverse Q(zeta)/(N zeta^(N-1)). The two explicit algebra maps identify the cited standard-etale algebra with C; the inverse-variable composite follows from uniqueness of a multiplicative inverse. This is a short quotient calculation, not an unstated comparison theorem.

Step 3 uses the polynomial-data leaf after mapping to an algebraic closure of the residue field, def-weil-pbc-localization-at-prime for that residue field, def-weil-algebraic-closure for both existence of the closure and existence of a root of a nonconstant polynomial, and def-weil-affine-spectrum for the contravariant point map. I verified that these statements actually include the asserted facts. The kernel of the evaluation map contracts to p since the residue-field embedding is injective. Thus a point over every prime is constructed, rather than invoking an uncited surjectivity criterion or the existence of primitive roots.

Step 4 uses coefficient naturality and the field-root criterion, together with the fibre-product and geometric-point definitions. The inverse of N survives in every receiving field, so its image is nonzero even in positive characteristic. The argument proves the fibre assertion for every field-valued point, hence in particular every algebraically closed geometric fibre; it does not treat zeta as an individual point of a possibly disconnected fibre.

Step 5 applies that already-established field calculation to the residue field at every prime of C. The localization-at-prime statement provides the ring, and the text proves its kernel is the prime using the fraction description and primality. The cited basic-open node explicitly states clause (ii), an element in no prime is a unit. I read Stacks 00E0, lemma-Zariski-topology, including its final unit assertion (numbered (17) in the current TeX). This avoids assuming that C is a field or that a nonzero element is automatically invertible. The small divisibility inference N divides a with 0<a<N is elementary and written out.

Step 6 cites finite-morphism-permanence clause (a), etale-scheme-base-change and surjective-base-change. I opened all three statements, and read Stacks morphisms.tex labels lemma-base-change-finite (01WL), lemma-base-change-etale (02GO) and lemma-base-change-surjective (01S1). Each allows arbitrary base change; no hidden quasi-compactness or finite-type assumption is used. These dependencies are already Mathlib leaves, so there is no off-unit unresolved tool request.

Step 7 is marked elementary: def-pc-fibre-product states its universal property for morphisms from every test scheme. Applying uniqueness to Spec Omega gives equality of a geometric point exactly when both projections agree. The group fixes the second projection, so stabilizers in the very same group coincide. This directly proves inertia preservation without replacing it by a theorem about decomposition groups or assuming the group is finite.

For edge cases I checked N=1: Phi_1=T-1, C=Z, the derivative is 1, the cover is the identity, and there are no difference units to prove. For N=2 one gets C=Z[1/2] and 1-zeta=2, which is indeed a unit. The new field criterion deliberately excludes characteristic dividing N; for example Phi_2 over F_2 has root 1, of order 1, showing why the nonzero-cast hypothesis is necessary. For a composite index such as N=6, the proof does not require a to be coprime to N: it uses N not dividing any 0<a<N, which is the needed condition. Empty W gives an empty identity-base-change situation; neither surjectivity under base change nor the inertia calculation requires a geometric point to exist. Arbitrary nonreduced W is allowed because only the three general permanence lemmas are applied.

Against delivery-errors B--E I checked self-contained statements and inline primitive-root meaning, the two exact Mathlib matches and their line numbers, all statement dependencies, the verbatim citations, absence of a circular node, and absence of a source-defined object imported from a cited node's proof. Elementary algebra and the stabilizer argument stay in the item, rather than becoming new nodes. All seven steps are below 900 characters, so no long step hides a standard lemma. The only corrections made during drafting were replacing a potential algebraically-closed-root existence citation by the polynomial's positive-degree argument, using the general no-prime unit criterion rather than a local-ring-only criterion, and choosing the existing finite-morphism-permanence node for its exact base-change clause. No statement dispute or source error remains.
