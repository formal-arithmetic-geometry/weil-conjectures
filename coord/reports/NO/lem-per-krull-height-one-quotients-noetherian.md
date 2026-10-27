# Stage-1 report: lem-per-krull-height-one-quotients-noetherian

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-krull-height-one-quotients-noetherian.json: item, statement unchanged, six proof steps, status split.
- dag/nodes/sec-deligne-laumon-a1/lem-per-krull-symbolic-graded-embedding.json: new statement-only input lemma, status unsplit; not in Mathlib after all four search kinds and a second semantic phrasing.
- citations.json: seven entries, one for every use in the six steps, with verbatim statement quotes.

One new node; zero new Mathlib leaves. The existing finite-product theorem is already a Mathlib leaf and is reused.

## Attachments

None. Searches by the item tag, Krull domain/height-one terminology and the proposed new node tag in lean/WeilConjectures found no exact project declaration. Mathlib declarations are not project attachments. Existing Sheaf source associated to the reused decomposition is not claimed as a finished project proof.

## WANTED

WANTED: Swanson–Huneke, Integral Closure of Ideals, Rings, and Modules, Definition 4.10.1, Proposition 4.10.3, Theorem 4.10.7, printed pp.89 and 92–93, for the item and lem-per-krull-symbolic-graded-embedding. Online author-hosted PDF read at https://www.math.purdue.edu/~iswanso/book/SwansonHuneke.pdf (PDF pages 102, 105–106, zero-based). literature/swanson-huneke-integral-closure.pdf is the established DAG source path but the file is absent in this read clone. No literature files were downloaded or written. proof_origin is agent as required when the local source is missing.

WANTED: Marot, Sur les anneaux universellement japonais (1975), printed p.104 footnote (1), original source of the item. The Numdam link could not be fetched. The independent author-hosted Swanson–Huneke Theorem 4.10.7 states precisely the same general Krull-domain criterion, and its complete proof was read instead.

## Findings and corrections

The statement has no mathematical error: it is exactly the general Mori–Nishimura criterion, without prior Noetherianity or finite dimension. Its Krull definition agrees clause by clause with Swanson–Huneke Definition 4.10.1. The source's last sentence, that Noetherian principal quotients imply the ring is Noetherian, needed the explicit arbitrary-ideal argument in Step 6. The proof also now distinguishes Noetherianity as a ring from Noetherianity as a D-module; these cannot be silently interchanged for arbitrary extensions.

The source's substantial symbolic-power argument is isolated as one strictly smaller lemma. It contains no Noetherianity conclusion and assumes neither D nor D/P Noetherian. It is not a restatement of the item or of its final clause. No proof text has been put in its statement or proof array. Its intended argument is preserved below for the next worker.

The latest blueprint ancestor proof is Artin–Gabber amplitude/duality; it does not contain a verbatim Marot or Krull-domain argument. The inherited from.place records the historical auxiliary-algebra descendant route. The item's split_report explicitly distinguishes that ancestry from the currently readable blueprint. No chapter/unit file was changed. Whole-blueprint searches for Krull, symbolic, symbolic power and Mori–Nishimura found no blueprint statement giving the proposed embedding. Whole-DAG searches also checked the existing Krull principal decomposition, divisorial lattices, and symbolic-power base-change statements.

## Intended argument for the new input (not part of its statement)

For a fixed height-one P, each height-one localization is a DVR by Stacks 00PD. Choose a in D with v_P(a)=1: write a uniformizer of D_P as a/s with s outside P. There are only finitely many other height-one primes Q_i containing a. For each, choose c_i in Q_i outside P (distinct height-one primes are incomparable), and choose N_i large enough that v_{Q_i}(c_i^{N_i}) >= v_{Q_i}(a). Set x=a/product(c_i^{N_i}) in Frac(D). Then v_P(x)=1, and v_Q(x)<=0 for every other height-one Q: when a is in Q the corresponding denominator factor suffices; otherwise its numerator has valuation zero and all denominator valuations are nonnegative. This also explains the approximation choice implicit in the source without imposing any Noetherianity on D.

Put B=D[x]. Since x lies in D_P, B is contained in D_P. For S_n=D intersect (PD_P)^n, show D intersect x^n B=S_n. One inclusion uses B contained in D_P and v_P(x)=1. For the reverse, if y is in S_n, then y/x^n lies in every height-one localization: its P-valuation is nonnegative, and every other valuation is nonnegative since y is in D and v_Q(x)<=0. The Krull intersection property gives y/x^n in D, hence y in x^nD. This works also for n=0 and y=0.

The constant inclusion D -> B/xB is surjective because every polynomial in x reduces to its constant term; its kernel is D intersect xB=S_1=P. Thus B/xB is D-linearly isomorphic to D/P. Since B is a domain and x is nonzero, multiplication by x^n gives a D-linear isomorphism B/xB -> x^nB/x^{n+1}B: cancellation gives injectivity, and writing elements as x^n b gives surjectivity. Inclusion S_n -> x^nB followed by the latter quotient has kernel S_n intersect x^{n+1}B=S_{n+1}. It therefore induces the required injective D-linear map S_n/S_{n+1} -> D/P. This is the two-paragraph construction behind Theorem 4.10.7, with the denominator choice and B/xB identification expanded.

## Not duplicates

lem-per-krull-symbolic-graded-embedding vs lem-trf-krull-principal-primary-decomposition: the existing node gives finite intersection decompositions of nonzero principal ideals and their radicals; it gives no injection between consecutive symbolic-power quotients and D/P.

lem-per-krull-symbolic-graded-embedding vs lem-per-divisorial-fractional-module-lattices: that node assumes D already Noetherian and concerns coherent reflexive fractional modules; it supplies no result for the arbitrary non-Noetherian Krull domains allowed here.

lem-per-krull-symbolic-graded-embedding vs lem-per-vertical-symbolic-powers-completion: that node concerns symbolic-power comparison under henselian completion, not embeddings of successive quotients in an arbitrary Krull domain.

lem-per-krull-symbolic-graded-embedding vs lem-sfb-symbolic-powers-flat-prime-extension: that node compares symbolic powers under flat extension of Noetherian rings with extended prime ideal; it does not assert the embedding here.

lem-per-krull-symbolic-graded-embedding vs lem-trf-normalization-integral-closure-krull: that node proves normalization is Krull; it has no assertion about consecutive symbolic powers.

## Review by NO

I read the item and its chapter/unit records, the current latest blueprint ancestor proof and unit/chapter text, Swanson–Huneke Definition 4.10.1, Proposition 4.10.3 and the whole proof of Theorem 4.10.7 through its final sentence. I read Stacks Tag 00PD, label lemma-characterize-dvr, algebra.tex:29104–29157, including its equivalence between a one-dimensional Noetherian normal local domain and a DVR with nonzero principal maximal ideal. I read the statement of every cited node, not merely its proof or name, and the relevant pinned Mathlib source for the finite product and maximal-ideal contraction leaves. The new node's source is precisely the intermediate embedding assertion on printed pp.92–93; it is not falsely attributed to a Stacks tag for a different fact.

Step 1 uses lem-trf-localization-maximal-contraction exactly to identify S_1=P, and the new node exactly for the injection of successive symbolic quotients into D/P. All three Krull hypotheses and the height-one assumption agree word for word in substance. The remaining interpretation of D-submodules of D/P as ideals, and pullback of finite generators through an injection, is written out. No Noetherianity of D is used.

Step 2 uses the assertion established in Step 1, with no hidden external result: for each arbitrary submodule, its image and intersection with the kernel have finite generators; lifts plus kernel generators generate it. The base n=1, the surjection, its kernel, and the induction are all specified. This is an elementary finite-generator argument, not an uncited application of a permanence theorem.

Step 3 uses the complete statement of lem-trf-krull-principal-primary-decomposition, which defines Krull with exactly the same three clauses, enumerates precisely the height-one primes containing b, defines J_i as contracted local principal ideals and asserts the required intersection equality. I checked b != 0 and the empty-list convention. It is declared as a generic commutative-algebra tool from another unit, not a replacement of a perverse-sheaf unit step.

Step 4 uses the localization-dimension node for dimension one, the normal-local-dimension-one node for the DVR conclusion, and the unit-times-uniformizer-power node for the exact factorization. I checked that the local rings are domains, Noetherian, normal and one-dimensional before the DVR criterion, and that b/1 is nonzero and nonunit before obtaining a positive exponent. The equality of the contracted local ideals with symbolic powers follows from those explicit definitions. The DVR criterion is the second declared generic tool. In its source description I use 00PD's conditions (5) and (4), which are the actual Noetherian-normal and principal-maximal-ideal conditions.

Step 5 uses the finite-product node as stated for arbitrary commutative base D and a finite set of Noetherian D-modules. I checked that Step 2 proves module Noetherianity, not just ring Noetherianity. The diagonal's kernel is written out, and the submodule finite-generation conclusion is its definition. No new node is needed for a finite-product corollary already in the DAG and Mathlib.

Step 6 is an explicit ideal-generator lifting argument: I=0, a nonzero b in I otherwise, and finite lifts of generators of I/bD. This avoids invoking Cohen's theorem without its prime-finite-generation hypothesis. It proves every ideal finitely generated, exactly the item's existing definition dependency.

Small cases checked: D a field (height-one hypotheses vacuous, all nonzero b units); D a DVR (one prime, symbolic layers one-dimensional over D/P); D=k[u,v] with P=(u) (the injection is division by u^n modulo u); n=0 in the new node (identity D/P); b a unit (empty product and zero quotient); the zero ideal in the final argument. Infinite-variable polynomial rings are Krull but violate the height-one quotient hypothesis, so the argument does not incorrectly make them Noetherian. The zero ring is excluded by the domain hypothesis. None of the steps is longer than 2000 characters. The new node remains statement-only, all search records come from searches.jsonl with the exact executed tool/query text, and citations.json copies statements verbatim. There are no SGA citations, Lean writes, compiles, or changes outside the sandbox.

## Unfinished

No part of this item's one-level split remains unfinished. The new symbolic-power embedding lemma is deliberately unsplit and retains its argument above for its future worker. Mechanical delivery checks and the final push follow this review.
