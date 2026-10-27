# Q114 stage-1 report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-perfect-coinduction-tor-independent-base-change.json: item, statement; split using existing nodes, no Mathlib match.
- citations.json: a verbatim statement quotation for every proof-step citation.
- searches.jsonl: actual Q114 msearch records, in addition to the inherited item searches retained in the item.

No new nodes and no Mathlib leaves were created. No unit file, Lean file, repository file or launcher file was written. There was no prior sandbox item/proof/report to repair and no released repair note in the read clone.

## Attachments

None. Searched lean/WeilConjectures for the item tag and coinduction/coinduction-base-change concepts. The ChangeOfRings and sheaf-coinduction declarations found concern ordinary modules or sheaves, not this complete derived statement. They do not prove every clause, and are not an attachment.

## WANTED

None. All source material used is available locally.

## Findings

The item statement is unchanged. Its main conclusion overlaps the already existing lem-sfb-perfect-coinduction-tor-independent-exchange (created by Q42). That node includes the B'-linear isomorphism for unbounded inputs, the restriction/tensor identification, the counit-mate characterization and tower compatibility. Creating another such lemma would be a duplicate and would just move the item's content into a new node. Instead, step 2 specializes that existing statement and the remaining steps verify the explicit Tor hypothesis, Hom-map normalization, identity and ordered-sign clauses.

The inherited blueprint ancestor is null, and blueprint_refs.py ancestor reports null too. The long, precise inherited from.place and via chain are retained. I read the latest unit and its direct-images proof (3); this is an auxiliary module-duality input inside the already recorded alteration/nodal-family/polynomial-model chain, not a replacement for the unit route. Blueprint searches for coinduction, 0661, 0A6A and base.change.*Hom returned no separate blueprint node. No statement dispute or source error was found.

The item had no Lean audit entry or proof. Its earlier Q60 Mathlib searches remain intact; Q114 ran a second pair of semantic phrasings, Loogle and grep, read the hits and appended the actual logs. In particular IsBaseChange.linearMapLeftRight is only an ordinary finite-free module Hom statement (Mathlib/RingTheory/TensorProduct/IsBaseChangeHom.lean:135, with Free and Module.Finite hypotheses at line 133), and ModuleCat.restrictCoextendScalarsAdj (Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:659) is the underived adjunction. Neither specializes in one line to a derived, perfect, Tor-independent statement.

## Not duplicates

No new nodes. The existing exchange node, canonical perfect RHom base-change definition and theorem, and perfect-dual scalar calculus are reused explicitly.

## Review by Q114

I read Stacks more-algebra.tex at lemma-base-change-comparison (Tag 0661), its preceding warning that ordinary base-change cancellation need not hold for derived tensors, equation-base-change-RHom and lemma-base-change-RHom (Tag 0A6A, case (1)), and lemma-dual-perfect-complex (Tag 07VI) with its sign discussion. I also read dualizing.tex lemma-right-adjoint and lemma-RHom-ext (Tags 0A70 and 0A71). These sources separate the underlying Hom theorem from the algebra action. That distinction is why the proof takes the B'-linear isomorphism from the existing exchange node and checks its underlying Hom normalization rather than trying to lift an arbitrary underlying isomorphism. The proof is marked agent: the assembly and compatibility calculations are mine, supported by these source results and existing nodes. There are no new-node sources to review.

For step 1 I opened def-weil-pbc-tor-modules and lem-pc-module-bounded-flat-kflat. The former defines Tor by a projective/free resolution; the latter actually concerns ordinary modules and makes the chosen bounded-above flat resolution K-flat. The cohomology calculation, including H^0 and the absence of positive cochain degrees, proves the precise derived Tor-independence hypothesis needed next. I avoided the ringed-space bounded-flat lemma, which would require an extra transport, and did not assume that base change of every resolution remains a resolution.

For step 2 I opened the complete statement of lem-sfb-perfect-coinduction-tor-independent-exchange and substituted (P,A,T)=(A,B,A'). Its perfectness and derived Tor assumptions are exactly verified, its input M is unrestricted, and it gives the map in D(B') with theta and the stated adjunct. I also read lem-trf-derived-coinduction-adjunction: it supplies the underlying RHom identification, the actual evaluation-at-one counit, and the adjunction used in the equation. No claim about faithful restriction of derived morphisms is used.

For step 3 I read def-pc-perfect-rhom-base-change-map and lem-pc-base-change-rhom-perfect. The definition specifies the product-coordinate formula, finite-projective source representative, K-flat target representative, K-injective comparison maps and independence of the resulting normalized morphism. The theorem makes this very map invertible for arbitrary target complexes and arbitrary ring extension. The formula obtained by applying the coinduction adjunction to the extended counit is that formula; the comparison uses the canonical representative maps, rather than identifying maps just from cohomology or testing evaluation at one after forgetting the B' action. I explicitly included the tensor symmetry needed for the definition's left-scalar convention; the scalars introduce no degree sign.

For step 4 I checked the exchange statement's naturality and further-scalar-extension clauses and the adjunction statement's counit. Identity is proved directly: the adjunct is the original counit, hence corresponds to the identity. Towers are asserted only under the Tor-independence conditions on the indicated squares. The counit equality is the defining mate equation, not an unspecified compatibility.

For step 5 I read the complete lem-pod-perfect-dual-scalar-calculus statement, particularly its signed evaluation formula and its arbitrary-ring-map hypothesis. A finite polynomial Koszul complex is bounded finite free, so this applies to its dual evaluation. I wrote the value (-1)^(pj) iota(phi(x)) ab and explained ordered tensor signs as a product of the same signs. This is a routine specialization and is marked elementary. The assertion applies only when the evaluation maps themselves are scalar-extended, as the item says; it does not assert exactness of arbitrary Koszul complexes or preservation of regular sequences under a nonflat map. The step uses the common Hom normalization of step 3.

I checked B=A, N=0, zero rings, an empty Koszul complex and a one-generator Koszul complex: the mate is respectively the scalar-extension identity or zero map and the evaluation formulas retain their unit and sign. A genuinely nonflat allowed example is A=Z, B=Z x Z, A'=F_2: B is finite free and Tor independence holds although A' is not flat; no flatness of A' was introduced. For the necessity of Tor independence, A=k[t], B=A'=k gives Tor_1=k and the ordinary fiber cannot replace the derived fiber. Perfectness is used by the exchange theorem, with no Noetherianity or boundedness of N. Finite projective resolution lengths may be zero; all arguments include that case.

Against delivery-errors B--E: all objects and hypotheses remain introduced in the unchanged item; there are no new statement-only nodes to conceal a proof, no tag-only invocation, no new duplicate, no false Mathlib leaf and no unrun search claim. Every cited node's statement was opened and its relevant assertion checked as above, and citations.json quotes those exact statements. proof_deps equals the union of uses. Off-unit generic algebra tools are declared in split_report.tool_uses; the existing exchange is in the item's own unit. No proof step is longer than 2000 characters (lengths 531, 790, 1255, 708, 959), and the steps do not introduce a hidden independent theorem.

## Unfinished work

No mathematical part remains. The required server dry run and direct delivery follow this report; their outcome is recorded by the delivery tool.
