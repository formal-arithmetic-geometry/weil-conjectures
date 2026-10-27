# Stage-1 report: lem-trf-restricted-submodule-adic-topology

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-restricted-submodule-adic-topology.json`: item, split; statement and statement dependencies retained. Four proof steps establish the comparison through the saturation of N.
- `dag/nodes/sec-trace-formula/lem-trf-restricted-saturated-submodule-finite.json`: new statement-only lemma, unsplit; no Mathlib match. States finite generation of a power-of-pi-saturated submodule of a finite restricted-series module.
- `citations.json`: the one proof-node citation, at step 2, with its verbatim conclusion.
- `searches.jsonl`: actual searches recorded by the prescribed msearch.py command.

One new node; zero Mathlib leaves. No Lean files were written and no compiler, Lake, build, local checker, or repository git command was run.

## Attachments

None. Searches of `lean/WeilConjectures/` for the item tag and the restricted-series, Tate-algebra, saturated-submodule and induced-topology notions found no declaration stating the item or the new lemma. The unrelated saturation declarations do not concern this ring/module situation.

## WANTED

WANTED: `literature/bosch-formal-rigid-geometry-2008.pdf`, Section 2.3, Lemma 7(i)–(ii), printed pp. 131–132 (PDF pages 132–133), for the item and `lem-trf-restricted-saturated-submodule-finite`. The primary April 2008 PDF was read online at https://www.uni-muenster.de/IVV5WS/WebHop/user/weckerm/heft378.pdf; no local archival copy was found. No download or change of the repository's literature list was made. This is a proof read from a human-authored document, so proof_origin.by is document.

## Corrections and route

No statement dispute: the supplied item is precisely Bosch 2.3/7(ii) in case (V), specialized to A equal to the restricted-series ring. Its arbitrary submodule and possibly torsion finite module are allowed by the source. The source leaves the last containment implicit; step 4 supplies the element y and its power explicitly. Finite generation is applied to the saturation P, not to N. It would be incorrect to apply ordinary Noetherian Artin–Rees: nondiscrete V and its restricted-series ring are not assumed Noetherian.

Read SETUP's three levels, GOAL, the chapter and unit records, and the latest blueprint local-term node. This is the already recorded historical analytic input below the normalization chain of lem-trf-local-term-locality. The current contracting-correspondence unit proof is not replaced. The new lemma inherits the item's chapter and unit and exact historical blueprint provenance; same_as is empty after whole-DAG and blueprint searches.

## Searches

All added mathlib_searches entries come from searches.jsonl, with exactly the logged tool and query. For the new lemma I used LeanSearch, two LeanFinder phrasings, Loogle (including a corrected broad FG query after IsSaturated was unknown), and two source grep patterns. The item also has fresh LeanFinder, LeanSearch, Loogle and grep searches in addition to its retained searches. Read the returned declarations: Submodule.FG.of_le and FG.of_le_of_isNoetherian (Noetherian/Basic.lean:377–384) assume a Noetherian module or ring; Ideal.exists_pow_inf_eq_pow_smul (Filtration.lean:389–391) assumes IsNoetherianRing. None applies here. MvPowerSeries/Restricted.lean supplies the restrictedness predicate and subring, not the finiteness or topology theorem. The adic topology and completion hits define their objects, and the real Z-lattice hit concerns a different ring. These are no matches, not unavailable services. No unrun query was recorded.

Searches of dag/nodes and tools/blueprint_refs.py for saturated submodules, saturation, restricted series, Bosch, Artin and adic topology found no node stating the new lemma. The finite-type valuation-ring presentation result is a different algebraic theorem, as detailed below. No Stacks tag is assigned to the analytic lemma: the precise source here is Bosch, not a guessed Stacks tag.

## Not duplicates

lem-trf-restricted-saturated-submodule-finite vs lem-trf-restricted-submodule-adic-topology: the new lemma concludes finite generation only for saturated submodules; the item concludes comparison of two topologies for every submodule, without claiming that submodule is finite. Steps 1, 3 and 4 carry the saturation and uniform-exponent argument.

lem-trf-restricted-saturated-submodule-finite vs lem-trf-valuation-finite-type-module-presentation: the existing Stacks 053E lemma assumes a ring algebra of finite type and a module flat over the valuation ring, concluding finite presentation. The new lemma concerns a topologically finite-type restricted-series algebra, which is not assumed algebraically of finite type, and a saturated submodule of an arbitrary finite module. This is not a one-line specialization of the existing theorem.

lem-trf-restricted-saturated-submodule-finite vs def-trf-restricted-series-presentation: the latter defines the ring and presentations; it asserts no saturated-submodule finiteness theorem.

lem-trf-restricted-saturated-submodule-finite vs lem-trf-restricted-quotient-complete: that node asserts completeness of quotient rings and depends on this item; it does not state finite generation and must not be cited here (that would make a cycle).

## Unfinished work

The new lemma is deliberately statement-only and joins the stage-1 queue. Bosch proves it using his Theorem 4 (finite flat modules over topologically finite-type valuation-ring algebras are finitely presented), then a finite-free presentation mapping onto M. That is the argument to split when the new lemma is taken up. It is not asserted as an additional proof step of this item. No necessary part of the item's one-level split remains unwritten.

## Review by Q67

I read the primary Bosch PDF's Section 2.3, particularly Theorem 4 and Lemma 7(i)–(ii) on printed pp. 130–132. The item is 7(ii), and the new node is the saturated-submodule assertion 7(i), with all field, valuation, completeness, nontriviality, pi, number-of-variables, and finite-module hypotheses stated explicitly. Here the chosen pi generates an ideal of definition: its powers tend to zero, and every nonzero valuation neighbourhood contains a power because the absolute value is real-valued. This places our V within Bosch's case (V). For a principal ideal, his condition I^k x contained in P is equivalent to pi^k x in P. The new statement adds neither finite presentation nor torsion-freeness of M.

In step 1, closure of P under addition uses the maximum of two exponents, and closure under scalars uses commutativity; the written exponent-addition argument checks saturation. This is a direct submodule verification and needs no external lemma. In step 2, I opened the actual new JSON statement: it says exactly that such a saturated P is finitely generated. Every hypothesis is inherited or proved in step 1. The quote in citations.json is an exact substring of its statement. This is the sole non-elementary input of the proof.

In step 3, each generator belongs to the union defining P, so each has an exponent; a maximum of finitely many exponents, also including 0, works for every finite linear combination. This gives pi^c P contained in N with the coefficients displayed. In step 4, writing x as pi^(m+c)y does not require an injective scalar action: x in N itself shows y is in P, and the uniform bound puts pi^c y in N. The reverse inclusion is a submodule axiom. Cofinality of the two displayed zero-neighbourhood bases establishes equality of the translated topologies. These steps cite no theorem they have not proved and hide no general comparison lemma.

For the small cases I checked m=0 (the inclusion into N is tautological), N=0 and M=0 (the saturation can contain torsion, but the finite-generator/max argument still works), N=M (P=M and one may take c=0), and r=0 (the ring is V). For the new lemma I checked P=0, P=M, and a module killed by a power of pi: saturation forces P=M in the last case. A nondiscrete maximal ideal of V is generally not finite but is not saturated, since multiplying 1 by pi puts it in that ideal; thus it is not a counterexample. These checks also explain why the new lemma cannot be misread as finite generation of arbitrary submodules. There is no cancellation of pi, no assumption of a discrete value group, and no invocation of Noetherianity.

Against delivery-errors B–E: the new node is self-contained and statement-only, defines saturation inline, and cites the actual definition nodes for its three inherited notions (their statements were opened). Its source is an exact Bosch location, and its TeX has single escapes after JSON decoding. All search records are real command output. C1/C4 reduce to the one quoted finiteness assertion at step 2; no definition node is used as a theorem and no proof of another node is used. The new node is neither an elementary finite-maximum calculation nor a restatement of the item's topology conclusion. There is no reverse dependency to the parent completeness node. All proof steps are below 2000 characters, and the assembly proof is below 3000 characters. I made no statement correction; I expanded precisely the source's implicit containment to account for torsion.
