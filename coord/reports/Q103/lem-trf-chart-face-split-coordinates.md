# Stage-1 report: lem-trf-chart-face-split-coordinates

## Files written

- dag/nodes/sec-trace-formula/lem-trf-chart-face-split-coordinates.json: item, statement, split by ten explicit elementary calculations; no exact Mathlib match.
- citations.json: the verbatim statement excerpt used by Step 1.
- report.md: this report. searches.jsonl is the search command's own log.

New nodes: 0. Mathlib leaves: 0. No unit record is changed: this item is an internal algebraic input, not its unit's key statement.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and for logification, characteristic monoids, sharp charts and chart pushouts. The hits for scheme gluing concern a different notion of chart; none states this item. There is no item Lean declaration or audit attached in the current node. No Lean was written and no compiler, Lake or build command was run.

## WANTED

None. The source document is available locally. The elementary algebraic expansion is labelled agent-written rather than attributed to a theorem not stated by the source.

## Corrections and findings

The statement is retained verbatim. The item was unsplit, with no proof and no earlier sandbox copy. Its hypotheses already give the chart pushout, the monoid section, and the chosen characteristic identification. Proving existence of a section, fs sharpening, or spreading a stalk chart would introduce unused hypotheses and arguments. In particular, lem-trf-integral-monoid-free-sharpening-splitting has a freeness hypothesis not needed here, and lem-trf-chart-face-localization-logification is a geometric stalk result whose log-scheme hypotheses are absent here. Neither is used to bypass a missing inference.

The important cancellation is in the integral monoid M, not in the ring A: the value b(q) can be a zero divisor or zero, so it cannot be cancelled to obtain uniqueness of u. The proof instead cancels b_M(q) after embedding M in M^gp and uses injectivity of the unit inclusion. Likewise no injectivity of alpha on F is assumed.

The existing definition node supplies exactly the group-completion and fs conventions, not a theorem about chart splitting. All splitting maps, extension maps, pushout comparisons and the ideal identification are proved explicitly. No new statement node just restates a clause of the item.

## Search and duplicate audit

Read and retained all inherited search records. Ran six additional searches through the required msearch.py command; their exact tool/query pairs are appended to the item and recorded by the command in searches.jsonl. Both semantic phrasings were read. The first returned number-field logarithmic embeddings, unrelated to log structures. The second returned associatesEquivOfUniqueUnits, unitsEquivProdSubtype and normalizationMonoidOfMonoidHomRightInverse; reading Mathlib/Algebra/GCDMonoid/Basic.lean shows the first assumes trivial units and the normalization construction does not state these chart pushout and ideal identities. Read Mathlib/Algebra/Group/Units/Hom.lean for the Loogle unit-map hits. LeanSearch returned ring-ideal/localized-module results and AddLocalization: ring ideals are different from the monoid ideals here, while the latter is localization infrastructure, not this statement. The grep searches found no log-chart theorem and only localization-predicate documentation; read Mathlib/GroupTheory/MonoidLocalization/Basic.lean. No service was unavailable.

Searched the whole DAG for monoid/face, sharp monoid, integral monoid and monoid pushout terminology, and used tools/blueprint_refs.py search for monoid, characteristic monoid and face localization. Read the closest nodes: lem-trf-face-localization-fs (fs properties, not the coordinate formulas); lem-trf-face-subgroup-saturated (subgroup saturation); lem-trf-integral-monoid-free-sharpening-splitting (existence under freeness); lem-trf-chart-face-localization-logification (geometric chart germs); lem-trf-prelog-pushout-log-axiom (sheafified associated log structures); lem-trf-log-regular-sharp-chart (existence of a neighbourhood chart); lem-per-integral-monoid-unit-pushout (general mixed pushout integrality/equality criterion). None is a missing exact attachment or a reason to create a duplicate. The last theorem is unnecessary because M is assumed integral and the pushout comparison here is proved by actual inverse maps.

## Not duplicates

No new nodes, hence no new/existing node pairs.

## Review by Q103

I read ILO, Expose VI 1.1--1.2 (printed p.69), 3.7(a) (p.75), and Expose VIII 3.1.1--3.1.5 (pp.98--99), directly from the local PDF. VI fixes the log structure, its characteristic and the comparison by unit-valued characters. VIII defines sharpening and localization of integral monoids. The source does not assert our complete algebraic statement as a named theorem; I therefore wrote the fraction and quotient proof and recorded agent origin. I also read the chapter/unit records and the current main-20261015 ancestor proof: this input stays on the inherited nearby-duality alteration branch. No SGA source is used.

Step 1 cites only def-trf-fs-log-blowup. I opened its statement: it explicitly defines group completion and fine saturated monoids with the injective canonical map used here. The verbatim fine-saturated sentence is in citations.json. The face assertion is proved using the explicit inverse yz of x when xyz=1; it does not invoke a definition node as a theorem. The description of F^gp as differences is the subgroup-generation calculation written in the step.

Step 2 proves the units of P_F in both directions, checking the face hypothesis in the converse. Equality of fractions is tested in P^gp, and injectivity of P to that group puts the cross equality back in P. Multiplication by inverses of alpha(f), alpha(f') gives well-definedness of alpha_F; multiplication and uniqueness are written out. There is no use of regularity, locality of A, or saturation beyond the stated integrality.

Step 3 uses the definition of quotient by a subgroup, proving the orbit relation is already the congruence. Its remainder r-s(pi r) lies in G for exactly that reason. Both composites and the homomorphism property are computed. The section is an assumption, so no unquoted splitting theorem is needed.

Step 4 uses the stated log-monoid axiom to identify a_M(f) with the specified unit lift. It defines the extension on every fraction and checks the same cross equality as in Step 2, now with inverses of units of M. The equations with beta give alpha_F and v. This needs no injectivity of beta.

Step 5 writes actual inverse maps between the original and localized pushouts. I checked that the displayed representatives for j_F agree after moving f or f' across the defining relation, that j_F(g) is the image of v(g), and that both composites fix each representative. Thus there is no hidden assertion that a change of pushout preserves an isomorphism.

Step 6 gives actual inverse maps for the split pushout, checks the G-relation with v(g), and reduces the second composite to [s(q)+g,e]=[r,e]. The first coordinate is the given characteristic identification, since it is pi(p) on the original chart and trivial on units. No choice of a different characteristic is made.

Step 7 proves all of the b_M coordinate isomorphism: the assumed characteristic identification selects q, the unit-orbit definition supplies e, integrality and the specified injective unit lift make e unique, and multiplying unique coordinates proves that the inverse is a homomorphism. Step 8 uses those unique coordinates to construct u, checks the identity and multiplicativity, and applies beta. In particular I did not cancel b(q) in A.

Step 9 proves surjectivity P to Q by removing the denominator in the quotient. It uses that surjectivity when checking H_x is an ideal. For the harder inclusion of the preimage identity it writes r-h=f_1-f_2 and uses h+f_1 in H. This is why the assertion concerns the image of H, with no generated-ideal replacement. The splitting then gives the asserted equality of subsets.

Step 10 specifies the compatible ring and log-monoid maps and checks the unit inclusion by the unique unit lift, the fraction extensions by preservation of inverses, and the pushout coordinates on each representative. Uniqueness of the unit coordinate proves naturality of u. The maps of P,F,s and H are fixed as in the statement's preservation condition. Thus this step supplies the actual compatibility calculation, rather than saying only that transport is natural.

Steps 2--10 have no external theorem citations: all facts are proved by the displayed formulas from hypotheses or previous steps. Step 1 is the only citation occurrence and its exact quote is recorded. Each step is under 900 characters, and I checked that none hides an existence theorem, a comparison lemma, or an invocation of a standard result. The elementary marking is based on the inverse maps and fraction calculations, not on the importance of the clause being proved.

I tested the edge cases H empty and H=P (both preimage and split equalities give empty/full subsets), F={0} in a sharp P, F=P (then Q=0, P_F=P^gp and every nonempty monoid ideal localizes to all of P^gp), P a group, and A the zero ring (all alpha(p) are units, and the chart hypothesis forces the trivial log monoid). For P=N^2, F=N times {0}, the formulas reduce to P_F=Z times N, G=Z times {0}, Q=N; an ideal generated by (a,b) localizes to all integer first coordinates and second coordinate at least b. A nontrivial unit character changes the chosen Q-chart by exactly u, with the same characteristic. These tests confirm that neither torsion-freeness of P^gp nor an injective alpha nor a nonempty H was silently used.

## Unfinished work

None in the one-level split. There are no new statement-only nodes to defer. Delivery validation and push are recorded below after the commands exit.
