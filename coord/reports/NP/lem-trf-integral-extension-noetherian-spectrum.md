# Stage-1 delivery: lem-trf-integral-extension-noetherian-spectrum

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-integral-extension-noetherian-spectrum.json`: item, statement unchanged, complete seven-step proof by Noetherian induction, status split.
- `dag/nodes/sec-trace-formula/lem-trf-normalization-principal-minimal-primes.json`: new statement-only lemma, unsplit, no Mathlib match. A nonzero principal radical in a normalization is a finite intersection of primes.
- `dag/nodes/sec-trace-formula/lem-trf-almost-finite-residue-field-degree.json`: new statement-only lemma, unsplit, no Mathlib match. Prime-quotient fraction fields in an almost finite integral extension have finite degree.
- `citations.json`: one verbatim statement quotation for each step/node citation.
- `searches.jsonl`: actual msearch records; the earlier searches already present in the repository item have been retained.
- `report.md`: this report. `write_split.py` is a sandbox-only preparation script, not a delivery file.

There are two new nodes and zero new Mathlib leaves. No unit record is changed: this item is not the unit's key statement.

## Attachments

None. Searched the project source under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id/docstring tag, integral/noetherian combinations, Mori–Nagata, Krull domains, principal minimal primes and normalization residue-field finiteness. No declaration proves the item or either new input. The project has some finite-normalization and DVR special cases, which impose extra hypotheses.

## WANTED

WANTED: W. Heinzer, Minimal primes of ideals and integral ring extensions, Proc. Amer. Math. Soc. 40 (1973), 370–372, Theorem 2 and Corollary, for lem-trf-integral-extension-noetherian-spectrum; intended local path `literature/heinzer-minimal-primes-integral-extensions.pdf`.

WANTED: I. Swanson and C. Huneke, Integral Closure of Ideals, Rings, and Modules, Proposition 4.8.5 (printed p. 85), Definition 4.10.1 and Proposition 4.10.3 (p. 89), Theorem 4.10.5 (pp. 90–91), for both new nodes and the item's alternative detailed proof; intended local path `literature/swanson-huneke-integral-closure.pdf`. The author-hosted book was read online at https://www.math.purdue.edu/~iswanso/book/SwansonHuneke.pdf. It was not downloaded into the read-only literature tree.

## What needed repair or clarification

The received item is already the corrected Heinzer statement, restricted to the integral closure of a Noetherian domain in a finite fraction-field extension. I have not changed it, and do not reintroduce the withdrawn arbitrary-integral-extension claim. Its source field and all existing searches are retained. There is no new statement dispute.

The accessible ResearchGate search copy exposed the article's abstract and the beginning of Theorem 1, but not a complete proof of Theorem 2. AMS access was denied. Thus I do not claim to have checked or followed Heinzer's proof. Instead, the item records `proof_origin.by = agent`: an explicit ascending-prime induction using the two precise, separately stated book inputs. No absent source is disguised as a Stacks lemma.

In particular, the argument must not apply the Noetherian-ring finite-minimal-primes theorem to the normalization, and must not identify algebraicity of residue fields with finite degree. Those are exactly the two substantive inputs left as new unsplit nodes. No ring-Noetherianity or finiteness of normalization is inferred.

## What remains

The item's mathematical split is complete. The two new nodes are intentionally unsplit and carry no proof or proof dependencies. Their later splitting is separate work. The local literature copies remain wanted. No Lean was written, compiled or built.

## Searches and route

Read the chapter and `sk-i-curve-zero` unit record, the item's ancestry, its reviewed parent `lem-trf-normalized-base-change-noetherian-topology`, and the current `blueprint_update` of `lem-trf-local-term-locality`. This item supplies the Heinzer input already specified in the finite-type alternative of Orgogozo Lemma 8.3.2. The induction elaborates that algebraic input and changes no trace/purity route. The new nodes inherit this unit and have the original blueprint ancestor and full via chain, with this item prepended.

Before creating nodes, searched the whole DAG by Mori–Nagata/Krull, normalization, principal/minimal-prime and residue-field terms, and used `tools/blueprint_refs.py search` for Noetherian spectrum, integral closure, principal ideals, Krull, Mori, normalization principal, and integral residue finite. Read the plausible one-dimensional and root-normalization candidates. None supplies these arbitrary-dimensional statements. Reused the existing quotient-Noetherianity, quotient-spectrum and lying-over nodes.

Ran logged LeanFinder, Loogle, grep and LeanSearch queries, with second semantic phrasings, for the item and each new node. The full actual summaries are in the corresponding `mathlib_searches`, keyed to `searches.jsonl`. Read `DedekindDomain/IntegralClosure.lean` lines 145–175 and 206–208, `Ideal/MinimalPrime/Noetherian.lean` lines 23–27, `LocalRing/ResidueField/Instances.lean` and the quasi-finite definition in `QuasiFinite/Basic.lean`. Normalization finiteness requires a normal base plus separability, minimal-prime finiteness requires the upper ring Noetherian, and the general integral residue-field instance only gives algebraicity. Finite-dimensional fibre hypotheses of `Algebra.QuasiFinite` have not been proved here and cannot be silently inferred from a finite extension of generic fields. Hence no match is a one-line specialization.

## Not duplicates

lem-trf-normalization-principal-minimal-primes vs lem-sc-finite-minimal-primes-over-ideal: the existing node assumes the ring containing the ideal is Noetherian; the new node concerns a possibly non-Noetherian normalization of a Noetherian base.

lem-trf-normalization-principal-minimal-primes vs lem-weil-pbc-noetherian-finitely-many-minimal-primes: the latter assumes its ring is Noetherian and concerns minimal primes of zero; neither its hypothesis nor its conclusion supplies the principal-radical assertion here.

lem-trf-normalization-principal-minimal-primes vs lem-trf-integral-extension-noetherian-spectrum: the new node gives only finite prime decompositions of nonzero principal radicals. The item still proves topological Noetherianity by a genuine induction using quotient-field degrees, quotient spectra and integral descent; it is not an application of this input alone.

lem-trf-almost-finite-residue-field-degree vs lem-sc-integral-closure-dedekind-surjective-fibres: the existing result assumes dimension one; the new statement allows arbitrary Noetherian domains and integral intermediate subrings, and asserts only finite degree of the prime-quotient fraction fields.

lem-trf-almost-finite-residue-field-degree vs lem-sbc-root-normalization-generic-stalk-residue-degree-dvd-core: the existing node assumes finite flat algebras and Galois group data and gives divisibility. The new result assumes neither module finiteness nor flatness and only gives finite degree.

lem-trf-almost-finite-residue-field-degree vs lem-trf-integral-extension-noetherian-spectrum: finite residue degree alone does not state topological Noetherianity; it is used to verify the smaller-base induction hypothesis.

## Review by NP

I checked delivery-errors B–E against the actual statements and the book. For the principal input I read Definition 4.10.1, Proposition 4.10.3 and Theorem 4.10.5: normalization in the base fraction field is Krull, whose nonzero principal ideals have finite primary decomposition. Taking radicals yields the stated finite prime intersection. For a finite extension F, choose finitely many integral field generators (clearing their algebraic denominators), form the module-finite Noetherian domain R' they generate over R with fraction field F, and normalize R' in F. This is the same D: integrality over R implies integrality over R', and transitivity gives the converse. This finite-extension reduction is also explicitly used in the proof of Proposition 4.8.5. It is part of the unsplit input to be formalized later, not an unrecorded lemma in the item. For the residue input I read the exact statement and proof of Proposition 4.8.5 on printed p. 85: it permits a subring of the integral closure in a finite extension and concludes finite residue degree at any prime. Writing residue fields as fraction fields of the prime quotients makes the input self-contained and avoids an unstated localization comparison.

For Step 1 I reread `def-weil-pbc-noetherian-ring` and the statement of `lem-weil-pbc-surjective-image-noetherian`, together with Stacks 00FM/00FN. They give finite generation in A and Noetherianity of A/p, respectively. The proof spells out ascending-chain stabilization and the induction assertion quantifies over every integral intermediate C and every finite F. This strengthening is necessary for quotients of D, which need not themselves be normalizations. The maximal-prime field case is verified explicitly.

Step 2 uses exactly `def-weil-pbc-integral-closure`: its monic polynomial definition supplies the minimal-degree relation. Cancellation occurs in the field F, x is nonzero, and the nonzero constant coefficient gives a strictly larger contracted prime in A. It is not assumed that a nonzero prime contracts nontrivially without proof.

For Step 3 I reread both cited statements. The new degree input applies to R=A/p, with D integral in the specified finite extension F. It states precisely finiteness of Frac(D/Q) over Frac(R/(Q intersect R)); the quotient isomorphism with A/q is written. Reducing each monic equation proves the integrality hypothesis for D/Q, and q is strictly larger by Step 2. Thus the induction hypothesis is used only at a smaller closed subset of Spec A. Stacks 00E5 and `lem-weil-pbc-spec-quotient-homeomorphism-zero-locus` say exactly that Spec(D/Q) is homeomorphic to V(Q); this is not taken from a definition of closed immersion.

For Step 4 the new principal-radical statement supplies only a finite prime intersection; the finite-union equality of vanishing sets and the chain argument are written out. All Q_i contain the nonzero b, so Step 3 applies to each. If b is a unit, the empty intersection yields an empty vanishing set, which is harmless. A proper closed subset V(J) has J nonzero and choosing b in J is legitimate, even without Noetherianity of D. Step 5 directly checks descending-chain stabilization once a proper term occurs.

In Step 6 I checked the injective integral-map hypotheses of `lem-weil-pbc-integral-injective-lying-over` against Stacks 00GQ: C and D are actual subrings, and the R-monic equation is also C-monic. The cited affine-spectrum node gives a scheme morphism, hence continuity. Surjectivity then reflects equality of pulled-back closed sets, proving the required descent in full. I did not cite the similarly named `lem-weil-pbc-surjective-image-noetherian` for this topological claim: that existing node is about quotient rings, and is used only in Step 1. Step 7 is the p=0 specialization, using the integral-closure definition and the equivalent well-founded closed-subset formulation.

I tested the new statements on a field base, on degree-one normalization, on b a unit, on nonnormal Noetherian bases and on inseparable finite field extensions. The field base has D=F and no nonzero proper prime. The empty principal decomposition is necessary for units. Neither theorem needs separability or excellence; the finite-subalgebra reduction works equally in the inseparable case. No zero-ring case is admitted because the domains explicitly have 1 different from 0. No step assumes finite Krull dimension or a uniform bound on heights. The new statements introduce their objects, define the fraction-field/radical terminology, cite their definition nodes, have no proof sketches in their statements, and are weaker inputs rather than repetitions of the item's conclusion. Every cited proof node has a verbatim quote in citations.json. All seven steps are below 2000 characters, and no comparison or standard lemma is hidden by a long step. The proof graph has no backward use of this item or its parent.

## Repair of returned delivery (2026-10-18)

I repaired F1 by reading the complete ResearchGate full-text transcription of Heinzer, *Minimal primes of ideals and integral ring extensions*, including the exact statement and proof of Theorem 2 on printed pages 371–372 and the Corollary on page 372. The theorem says that an almost finite integral extension of a Noetherian integral domain has Noetherian spectrum. Its proof first reduces to the integrally closed case, proves finite minimal-prime decompositions for extended finitely generated ideals by induction on the number of generators (using that the derived normal ring is Krull), and then derives an ascending chain of contractions in the Noetherian base. The Corollary gives the derived normal ring of a Noetherian domain. I checked that the present item is the finite fraction-field integral-closure specialization: its closure is integral over A and has fraction field finite over Frac(A), so it is almost finite in Heinzer's terminology. The seven steps retained in this delivery spell out a prime-contraction induction and use the two separate algebraic inputs as nodes; they do not claim that the seven-step wording is a quotation of Heinzer's proof.

I also re-read all three delivered JSON files after the repair. The two child nodes now carry the full stage-1 metadata defaults (`merged_into: null`, both `lean_audit` branches with state `none`, chapter and unit, and complete blueprint ancestry). I checked the decoded TeX strings in the item and both children for doubled backslashes, plain arrows, and unmatched math delimiters; each command has one TeX backslash in the decoded value. Their source places now identify the exact book propositions used and explicitly record the local-PDF limitation. `citations.json` was regenerated from the current node statements, so every quote remains a verbatim statement substring. No statement or proof dependency was weakened or silently changed.
