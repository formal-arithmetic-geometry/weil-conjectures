# Worker report: lem-sfb-prime-to-ell-linear-image-finite

1. Files written:
   - dag/nodes/sec-six-functors-basics/lem-sfb-prime-to-ell-linear-image-finite.json: repaired split; original statement unchanged.
   - dag/nodes/sec-six-functors-basics/lem-sfb-stable-lattice-finite-matrix-reductions.json: statement, unsplit; no exact or one-line Mathlib match.
   - dag/nodes/sec-six-functors-basics/lem-sfb-coprime-congruence-kernel-rigidity.json: statement, unsplit; no exact or one-line Mathlib match.
   - citations.json and this report; search results and searches.jsonl are retained in the sandbox.
2. Attachments: none. No matching declaration was found in lean/WeilConjectures by the blueprint tag or the prime-to-ell image keywords. Padic.primeToEll_linear_image_finite in lean/Sheaf/RepresentationTheory/PrimeToEllLinearImageFinite.lean has a whole-proof sorry and is not an attachment.
3. WANTED: none. L19.pdf is available and was read directly using pdftotext.
4. The returned split had 3551 characters of proof in five steps. The return asks to spread that work into at least two comparable statement-only nodes. The two extracted arguments have different inputs: the first is topological and works for any compact group without a coprimality hypothesis; the second is algebraic, needs prime-to-ell finite reduction images as hypotheses, and assumes no group topology. Neither restates the original theorem. No mathematical statement error was found or repaired.
5. Nothing mathematical remains unfinished for this split. The new lemmas deliberately remain unsplit for subsequent workers.

## Repair of the return

The sandbox initially contained only dispatcher brief markers, no node files, searches.jsonl or report. I continued from the current repository's delivered five-step version, copying only the item into the sandbox. Its five complete steps are retained verbatim below, so neither a shorter summary nor a rebase substitutes for extracting work. Old Steps 1 and 2 are the first new work item; old Steps 3, 4 and the separatedness part of Step 5 are the second. The final elementary group-image identification remains in the parent. Both new nodes have empty proof and proof_deps and null proof_origin; their sources identify the exact old argument and distinguish the notes from agent additions. The assembly is under 3000 characters. No Lean file or tool was written or compiled.

## New node proof plans (for the future workers)

### lem-sfb-stable-lattice-finite-matrix-reductions

This node owns the lattice-to-matrix and finite continuous reduction argument, not the prime-to-ell conclusion. Apply the existing lem-pod-profinite-stable-lattice statement: its hypotheses are a compact topological group and a jointly continuous finite-dimensional action, exactly those assumed. It supplies a full stable lattice free of rank r, the equality of adic and subspace topologies and continuity of the restricted action. Choose its r-element O-basis. Its E-span is V, of dimension r, so it is also an E-basis. Stability under g and g inverse makes the representing matrices and their inverses integral. Matrix multiplication agrees with the action, so this gives a homomorphism A.

For each n >= 1 use lem-weil-valued-dvr-finite-quotients and the coefficient datum to obtain the finite ring O/pi^n O. Entrywise reduction preserves products and inverses. A finite number of matrix entries in a finite ring gives a finite GL and a finite image. For each basis vector e_j, g maps continuously to rho(g)e_j in the lattice. Reduction to Lambda/pi^n Lambda has open fibres, which are cosets of the open submodule pi^n Lambda in the adic topology. The basis identifies this quotient with (O/pi^n O)^r. Thus every reduced column is continuous to a finite discrete set; the finitely many columns jointly give a continuous reduced matrix, and corestricting to its image gives a continuous surjection. At r=0 the empty basis, zero lattice and singleton matrix group satisfy every assertion. No coprimality assertion is smuggled into this lemma. These are precisely the first two previous steps below, except that their final coprimality inference belongs to the parent.

### lem-sfb-coprime-congruence-kernel-rigidity

This node owns the power congruence, complete induction and separatedness argument. It uses only the algebraic coefficient data, finite reduction images and their coprimality; there is no compactness or continuity assumption. For any n >= 1 and B over O prove (I+pi^n B)^m = I+m pi^n B modulo pi^(n+1), for every m >= 0, by induction on m. The base is I; in multiplying the induction formula by I+pi^n B, the extra product has factor pi^(2n), divisible by pi^(n+1). Because the extending absolute value has |ell|_E=ell^(-1)<1, ell lies in pi O. Taking m=ell proves that I+pi^n B has ell-th power I modulo pi^(n+1), including ell=2 and ramified extensions.

Induct on n to prove K_1=K_n. The base n=1 is equality. If h is in K_1=K_n, lift the entries of A(h)-I to write A(h)=I+pi^n B. Its reduction at n+1 has ell-th power one. Apply the existing lem-sfb-finite-matrix-group-coprime-power with R=O/pi^(n+1)O, finite subgroup G=Q_(n+1) and exponent ell. Its hypothesis gcd(|Q_(n+1)|,ell)=1 is explicitly assumed in the new node. The power map is injective and sends 1 to 1, so A_(n+1)(h)=1. Reverse inclusion follows by reducing to level one. Hence K_1=K_n for every positive n.

Finally if h is in K_1, each entry a of A(h)-I lies in pi^n O for all positive n, so |a|_E <= |pi|_E^n. Since 0<|pi|_E<1 the bounds tend to zero, giving a=0 and A(h)=I. Conversely an element of ker A has identity at every reduction. This proves K_1=K_n=ker A. Rank zero is tautological. The assumption on all reduction images is essential: multiplication by 1+ell (or 3 for ell=2) in rank one gives a nontrivial first congruence element once the prime-to-ell reduction-image hypothesis is dropped. These are precisely the previous Steps 3-5 below, with only the final elementary isomorphism left in the parent.

## Previous delivered proof, retained verbatim

### Previous Step 1

If $M=0$, its only automorphism is the identity, so the image has order $1$. Otherwise put $r=\dim_E M$. Apply [lem-pod-profinite-stable-lattice] with $G=H$ and $V=M$: a profinite group is compact and the action is jointly continuous by hypothesis. Obtain a stable free $\mathcal O_E$-lattice $\Lambda$ of rank $r$ spanning $M$, with continuous restricted action and its maximal-ideal-adic topology equal to the subspace topology. Choose a basis of $\Lambda$. It is an $E$-basis of $M$: its $r$ vectors span a space of dimension $r$. In this basis write $A(h)\in\operatorname{GL}_r(\mathcal O_E)$ for the action; stability for $h$ and $h^{-1}$ supplies both an integral matrix and an integral inverse.

Cited nodes: lem-pod-profinite-stable-lattice.

### Previous Step 2

Write $\mathcal O=\mathcal O_E$, $\pi=\varpi_E$, and $A_n=\mathcal O/\pi^n\mathcal O$ for $n\geq1$, with the coefficient notation of [def-weil-l-adic-coefficient-extension]. The rings $A_n$ are finite by [lem-weil-valued-dvr-finite-quotients], applied to the valuation ring and uniformizer supplied by that coefficient datum. Reduction of the matrices defines $\rho_n:H\to\operatorname{GL}_r(A_n)$; put $Q_n=\rho_n(H)$ and $K_n=\ker\rho_n$. Each $Q_n$ is finite because its matrices have finitely many entries in a finite ring. Moreover $\rho_n$ is continuous for the discrete topology: for each basis vector $e_j$, $h\mapsto\rho(h)e_j$ is continuous into $\Lambda$ by [lem-pod-profinite-stable-lattice], and reduction modulo $\pi^n\Lambda$ has open fibres in the adic topology. Finitely many such evaluations determine the reduced matrix. Thus $H\to Q_n$ is a continuous surjective homomorphism to a finite group, so $\gcd(|Q_n|,\ell)=1$ by the hypothesis on $H$.

Cited nodes: def-weil-l-adic-coefficient-extension, lem-pod-profinite-stable-lattice, lem-weil-valued-dvr-finite-quotients.

### Previous Step 3

For every $n\geq1$ and matrix $B$ over $\mathcal O$, repeated multiplication gives $(I+\pi^nB)^m\equiv I+m\pi^nB\pmod{\pi^{n+1}}$ for all integers $m\geq0$: the base $m=0$ is immediate, and the induction step multiplies by $I+\pi^nB$, whose extra product term is divisible by $\pi^{2n}$, hence by $\pi^{n+1}$. By [def-weil-l-adic-coefficient-extension], $|\ell|_E=|\ell|_\ell=\ell^{-1}<1$, so $\ell\in\mathfrak m_E=\pi\mathcal O$. Taking $m=\ell$ gives $(I+\pi^nB)^\ell\equiv I\pmod{\pi^{n+1}}$. This calculation works also at $\ell=2$ and for ramified $E$.

Cited nodes: def-weil-l-adic-coefficient-extension.

### Previous Step 4

We prove $K_1=K_n$ by induction on $n\geq1$. The base $n=1$ is equality. Suppose $K_1=K_n$ and take $h\in K_1$. Since $h\in K_n$, every entry of $A(h)-I$ is divisible by $\pi^n$, so $A(h)=I+\pi^nB$ for a matrix $B$ over $\mathcal O$. The previous calculation implies $\rho_{n+1}(h)^\ell=1$ in $Q_{n+1}$. Apply [lem-sfb-finite-matrix-group-coprime-power] to $R=A_{n+1}$, $G=Q_{n+1}$ and exponent $\ell$; the needed coprimality was established in Step 2. Its power map is injective and sends $1$ to $1$, so $\rho_{n+1}(h)=1$. This proves $K_1\subseteq K_{n+1}$; the reverse inclusion follows by reduction modulo $\pi$. This completes the induction.

Cited nodes: lem-sfb-finite-matrix-group-coprime-power.

### Previous Step 5

If $h\in K_1$, Step 4 gives $A(h)-I\in\pi^nM_r(\mathcal O)$ for every $n\geq1$. For any entry $a$ of this difference, $a\in\pi^n\mathcal O$ implies $|a|_E\leq|\pi|_E^n$. Here $0<|\pi|_E<1$ by [def-weil-l-adic-coefficient-extension], so the right side tends to zero and $a=0$. Thus $A(h)=I$, which implies $\rho(h)=1$ since $\Lambda$ spans $M$. Conversely $\rho(h)=1$ implies $h\in K_1$. Therefore $\ker\rho=K_1$. The rule $\rho(h)\mapsto\rho_1(h)$ is consequently a well-defined bijective group homomorphism $\rho(H)\to Q_1$: equality of reductions is equivalent to $h_2^{-1}h_1\in K_1=\ker\rho$. Its target is finite and has order prime to $\ell$ by Step 2, proving both assertions.

Cited nodes: def-weil-l-adic-coefficient-extension.

## Searches and sources

Read Stanford seminar L19.pdf Proposition 1.1.9, especially the second and third bullets on printed p. 3. It states the stable lattice construction and the finite quotient modules. It does not state the prime-to-ell congruence-kernel assertion; that part is explicitly agent-written, both in the item source and in the second new node source. No SGA source or change of route is used. Read the main-20261015 direct-images proof paragraph (3), the chapter and unit records and SETUP.md's three levels; this remains the existing tame-boundary expansion, without a change to either fixed upper level.

Before creating nodes I searched all DAG statements for stable lattice, matrix/congruence kernels and reductions, and searched the project Lean by the same notions. Whole-blueprint searches via tools/blueprint_refs.py for congruence, stable lattice, prime-to-ell, matrix reduction, compact representation and congruence kernel gave no statement matching either extracted lemma. The two congruence blueprint hits concern trace-formula coefficient choices, not this assertion. The inherited chain's null ancestor is preserved, with the exact open-direct-image place and full via chain, as already explained in the previous delivered split.

All fourteen new Mathlib searches were run through the required msearch.py and read in search-a1.txt through search-b7.txt. Each node has two semantic phrasings, Loogle and source grep. LeanSearch was rate limited; it is recorded as unavailable, never no match. The stable-lattice searches returned real Z-lattices, order lattices, scalar p-adic residue descriptions and GL continuity lemmas. I opened Mathlib/Topology/Algebra/Group/Matrix.lean:35-43: continuous_apply requires an already continuous GL map and Continuous.generalLinearGroup_map requires a continuous coefficient homomorphism. Neither constructs an invariant integral lattice or proves continuity from the given jointly continuous action. Hence neither states the first node in one line. The kernel searches returned scalar PadicInt.ker_toZModPow/ker_toZMod, modular congruence subgroups, number-field roots of unity and unrelated inertia/Selmer kernels. Nat.Coprime.pow_left_bijective was read at Mathlib/GroupTheory/OrderOfElement.lean:1245-1247; it is exactly the already-existing finite-matrix-group-coprime-power auxiliary leaf, not the new congruence induction and separatedness theorem.

## Not duplicates

lem-sfb-stable-lattice-finite-matrix-reductions vs lem-pod-profinite-stable-lattice: the existing statement supplies an invariant full free lattice and its topology, but not integral matrix coordinates, finite reduced matrix groups or continuous reduced matrix homomorphisms. The new node owns that additional argument.

lem-sfb-stable-lattice-finite-matrix-reductions vs lem-weil-valued-dvr-finite-quotients: the existing node states finiteness of coefficient rings, without a group action, invariant lattice or reduced representation.

lem-sfb-stable-lattice-finite-matrix-reductions vs lem-sfb-prime-to-ell-linear-image-finite: the new lemma has no prime-to-ell assumption and asserts no finiteness of the original image, only finite continuous reductions for arbitrary compact monodromy.

lem-sfb-coprime-congruence-kernel-rigidity vs lem-sfb-finite-matrix-group-coprime-power: the existing leaf is bijectivity of a power map in one finite group. The new lemma is a theorem about a whole filtered family of matrix kernels and equality with an integral representation kernel.

lem-sfb-coprime-congruence-kernel-rigidity vs lem-sfb-prime-to-ell-linear-image-finite: the new lemma assumes integral matrices and coprimality at every reduction level, with no topology or continuity. It proves equality of kernels, not the original finite-image assertion for a profinite group acting on an E-vector space. The parent must construct those reductions and check their orders before using it.

lem-sfb-coprime-congruence-kernel-rigidity vs lem-sfb-integers-profinite-tower: the existing node identifies O with the inverse limit of its scalar quotients. It neither treats a matrix representation nor proves the coprime-image congruence induction. Its scalar separatedness assertion alone cannot replace the new lemma.

## Review by NK

I read the source and the full statements of the original cited nodes, not just their names: lem-pod-profinite-stable-lattice explicitly includes the free full lattice, its rank and restricted-action topology; lem-weil-valued-dvr-finite-quotients explicitly includes finiteness of every positive coefficient quotient; def-weil-l-adic-coefficient-extension explicitly gives the absolute value, uniformizer and quotients; lem-sfb-finite-matrix-group-coprime-power explicitly gives bijectivity for a finite matrix subgroup and a coprime exponent. These supply exactly the future-worker plans above. The source's lattice argument is not advertised as a source proof of the agent corollary.

Parent Step 1 cites only the first new statement. Its compact-G and joint-continuity hypotheses hold for the given profinite H and representation; its vector-space topology, field and rank agree exactly. It explicitly supplies the E-basis, integral matrices and all finite continuous quotient-image maps which the step takes. M=0 is discharged directly. Parent Step 2 cites only the second new statement: the previous step's integral A is its input, its positive-level images are finite, and the original finite-continuous-quotient assumption makes their orders coprime to ell. Its conclusion explicitly says ker A=K_1. Parent Step 3 is elementary from these statements: the E-basis equates ker A with ker rho; equality of reductions is equivalent to h_2 inverse h_1 in K_1, so the displayed map on images is well defined, injective, multiplicative and surjective. No unquoted comparison or theorem is used. citations.json quotes the actual new statements for both citations.

For B1-B10 I checked both new statements introduce every object, define GL as two-sided invertible matrices, cite the coefficient and matrix definition nodes, use ordinary TeX escaping, contain no proof sketch, and have empty proof/proof_deps. They are unsplit, with source and blueprint fields and real recorded searches; no Mathlib match is claimed. For C1-C8 I checked all parent uses against statements, removed direct uses of old tools now internal to the future proof plans, and introduced no backwards dependency: neither new node depends on the parent or on the other. No new off-unit proof citation occurs. Existing maintainer fields are preserved. For D1-D5 this is two comparable complementary arguments, not the entire theorem moved to one node or clauses of its original conclusion renamed. The exact old five steps above show that every original argument has an assigned location. For E1-E7 I verified the positive exponent n>=1 (needed for 2n>=n+1), finiteness and coprimality of Q_(n+1) at the induction step, the extension norm and uniformizer facts, the E-basis identification, ell=2, arbitrary ramification, r=0 and the trivial group. The coefficient bounds prove separatedness without an extra completeness hypothesis. No statement dispute was found.

The specific repair changes are the two new unsplit nodes, replacement of the long five-step proof by a three-step assembly, and retention of every prior argument in this report. The original item statement is byte-for-byte unchanged. Required remote dry-run and delivery outcomes are recorded below once run.

## Validation

The required deliver.py --no-push invocation exited 0 and printed `OK (not pushed) deliver/NK/lem-sfb-prime-to-ell-linear-image-finite at 13c3a419e91: preflight passed`. The server ran the required preflight and DAG/split checks. The report was then extended with this validation result; the delivery invocation reruns preflight before pushing.
