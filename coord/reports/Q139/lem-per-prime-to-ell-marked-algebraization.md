# Q139 stage-1 delivery: lem-per-prime-to-ell-marked-algebraization

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-prime-to-ell-marked-algebraization.json: statement, now split in ten steps; inherited Mathlib searches retained, no match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-prime-to-ell-equivariant-cohen-presentation.json: statement-only unsplit input; Mathlib searches found no match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-equivariant-marked-cylinder-algebraization.json: statement-only unsplit input; Mathlib searches found no match.
- citations.json: a verbatim quotation for each node use in each numbered step.

## Attachments

None. Searches under WeilConjectures/ in the read-only slopmaster2 source for the exact blueprint tag, algebraization/algebraisation, Cohen-Gabber, and normal complete local presentations yielded no declaration proving this item. No compilation was attempted. The upstream master is reference material, not proof of completion.

## WANTED

None. The proof uses the locally available Illusie–Laszlo–Orgogozo volume and existing Stacks-based DAG statements.

## What needed correction

The imported item was an unsplit statement, not a proof. Its mathematical clauses are retained. I removed unused imported convention dependencies about strict normal crossings, alteration topology, properness and reducedness. None of those notions occurs in this lemma. No statement dispute was necessary.

The older partial-algebraization node has strictly henselian hypotheses and no exact marking or prime-to-ell degree. The older Cohen-presentation node has separably closed residue field and no tame-group quotient or prime-to-ell degree. They cannot justify the present general-residue-field statement. In particular one cannot claim that the invariant quotient itself is etale on a p-dense open: ILO IV 4.3.2 explicitly disproves that assertion. The proof keeps the etale presentation on B and performs equivariant algebraization before taking invariants.

During self-review I replaced a tentative nonexistent dimension citation with the existing lem-weil-pbc-finite-type-domain-dimension-trdeg, wrote out normality of the fixed subring, restricted the field case of the marked-cylinder input to the trivial group as in the source, and simplified the marking argument so that empty Z needs no extra shrinking.

## Unfinished work

The two new inputs are intentionally statement-only and unsplit, as required for a one-level split. Their proofs are future DAG work. There is no other unresolved mathematical clause in the item's split. The server dry run passed after the reference-format repair recorded below; direct delivery follows the final successful dry run.

## Source and search record

I read ILO Expose IV 2.1.1 (printed p.50), the equivariant discussion 2.2.2–2.2.3, IV 4.3.1–4.3.7 (pp.59–61), Expose V 1.1–1.2, 2.1–2.2.8 and 3.1–3.2.4 (pp.63–68), and the geometric uses in VII 3.1–3.2 and IX 1.3. The item follows V 3.1.3–3.1.4, with exact ideal descent from V 2.2 and 3.2. This is the blueprint ancestor lem-per-artin-gabber-affine-curve's Step 3 finiteness/duality branch through the recorded uniformization chain. I read its unit and chapter; the item is not the unit's key statement, so no unit realization is edited. No SGA source is used.

For the first new input, IV 4.3.1 gives B, the ell-group H, the coefficient DVR and the invariant quotient finite of prime-to-ell generic degree. IV 4.3.5–4.3.7 give the compatible coefficient action; V 3.2.1 uses exactly this formal diagram. IV 2.1.1 supplies the equal-characteristic positive-characteristic case; the Cohen presentation with generic separability supplies characteristic zero, as used in V 2.2.1. The regular power-series coefficient rings have the stated dimensions; taking tame invariants of the coefficient DVR gives the coefficient DVR used explicitly in V 3.2.3–3.2.4. This input stops before algebraization and says nothing about marked ideals or a finite-type curve.

For the second new input, V 2.2.1–2.2.8 and 3.2.2–3.2.4 give descent from a finite formal presentation. One first decomposes the finitely many ideals into primary ideals. In mixed characteristic, the vertical height-one primary pieces are symbolic powers in the normal invariant ring; the other pieces have smaller special-fibre dimension. The product of their images and the ramification divisor admits the invariant Weierstrass change of variables. Elkik descends the finite algebra and the group action to the henselian cylinder. Finite quotients and the symbolic primary pieces then descend as in the source, and finite presentation descends all this finite data to a pointed ordinary etale neighbourhood of D[T]. A finite algebra over that neighbourhood is quasi-finite over D[T]; this is why the new statement includes that useful conclusion rather than just an unspecified finite-type model. It assumes the full tame equivariant presentation, not an arbitrary complete local ring, and it does not construct a prime-to-ell cover. The two inputs are independent portions of the source's proof rather than a renamed clause asserting the item.

Before creating the nodes I searched the whole DAG by Cohen/Gabber, equivariance, algebraization, marked ideals, henselian cylinders, the source places and coefficient presentations, and searched the whole blueprint with tools/blueprint_refs.py (Cohen Gabber equivariant; algebraization; normal completion neighbourhood). No blueprint statement is the same; same_as is empty. The project Lean searches found no relevant completed declarations. Existing Elkik and Weierstrass nodes cover ingredients, not either full new assertion. The launcher searches for each new id were run through msearch.py: leanfinder, leansearch with a second natural-language phrasing, loogle, and grep. Complete responses are retained in search-results.jsonl, and the launcher's searches.jsonl records the actual queries. I read the returned types: standard etale presentations, invariants, Henselian and adic-completion instances do not construct these presentations or descend the marked ideals. Both symbolic searches returned no hits. The inherited item's recorded searches were read and retained; its mathematical question has not changed.

## Not duplicates

lem-per-prime-to-ell-equivariant-cohen-presentation vs lem-per-cohen-gabber-finite-presentations: the existing assertion requires separably closed residue field and has neither an equivariant tame presentation nor a quotient of prime-to-ell degree; the new assertion applies to arbitrary residue fields and supplies precisely those missing data.

lem-per-prime-to-ell-equivariant-cohen-presentation vs lem-per-gabber-partial-algebraization: the existing assertion is geometric algebraization with strictly henselian hypotheses and no equivariant formal presentation or degree control; the new assertion is a formal presentation only.

lem-per-equivariant-marked-cylinder-algebraization vs lem-per-gabber-partial-algebraization: the existing statement has strictly henselian hypotheses and gives only a completed strict localization, without marked ideals or a quasi-finite polynomial-cylinder model; the new statement assumes an explicit tame equivariant finite formal presentation and descends its invariant ring together with arbitrary finitely many ideals.

lem-per-equivariant-marked-cylinder-algebraization vs lem-per-elkik-finite-etale-away-completion: Elkik is a categorical descent theorem for finite algebras over a henselian pair; it does not choose invariant Weierstrass coordinates, descend ideals of a normal invariant ring, or descend the result to a finite-type polynomial-cylinder neighbourhood.

lem-per-equivariant-marked-cylinder-algebraization vs lem-per-weierstrass-henselian-cylinder: the existing statement constructs the henselian cylinder and its completion; it neither algebraizes a finite equivariant algebra nor carries marked ideals to its invariant quotient.

The new statements have no Stacks tag in common with an existing node: these are the substantive ILO inputs. All generic Stacks commutative algebra statements are reused, not recreated.

## Review by Q139

I checked delivery-errors B–E against the actual statements and source, not just their dependency lists. The item and both new nodes introduce their own rings, maps, ideals and actions. Completeness is maximal-ideal completeness; the point uses ordinary localization, not a tacit strict localization. There is no separably-closed residue-field hypothesis. The two new lemmas are neither elementary facts nor restatements of the conclusion. Every elementary assembly argument remains a step. Each non-elementary inference is assigned to a cited statement; none is justified by citing only its definition. All quotations in citations.json are copied directly from those statements.

Step 1 uses the formal presentation, finite-algebra integrality, lying over, and finite algebras over complete local rings. I opened each: the last theorem explicitly supplies complete local Noetherianity when the algebra is a domain; lying over assumes the injection and integrality supplied here. I wrote the fixed-subring normality argument explicitly. The prime degree is the fraction-field degree in the formal input, not a residue-field degree or the full B/A degree. In equal characteristic the same input makes p the identity.

Step 2 uses the two new inputs with I A+. The coefficient inclusion, finite equivariant presentation, invertible group order, and the divisor with nonzero coefficient-special-fibre reduction all come from the first input. The second supplies the exact extended ideal, not just a closed set containing the marking. The two coefficient cases give dimension d−1: r=d over a field and r=d−1 over a DVR. I checked d=2 in mixed characteristic, where D is the invariant coefficient DVR and no lower formal variables remain.

Step 3 uses complete-local excellence and finite-type/localization permanence exactly as stated, then faithful flatness of the local completion and contraction of zero and principal ideals. These statements have no residue-field restriction. Normality descends by the displayed fraction calculation, with the denominator nonzero in both domains. Step 4 uses the definitions of Noetherianity, localization and finite type: kill the finitely generated kernel away from the marked maximal ideal, rather than silently assuming the original finite-type algebra is integral. Principal localization preserves the same local completion and removes points from finite fibres.

Step 5 uses excellent normalization preparation only to exhibit a dense normal open. Its conclusion explicitly gives an isomorphism over a dense open and normality upstairs. That produces a nonzero h with C_h normal, the hypothesis of the normal-locus-open node; I do not apply that node merely from excellence. Step 3 places the marked point in the normal locus, permitting a principal shrink containing it. Finite-type/localization permanence proves excellence of the resulting W.

Step 6 uses the marked-cylinder assertion's D-algebra isomorphism, injective coefficient inclusion, and finite residue extension. Thus dominance, the closed point over the closed point, and invertibility of ell are retained. Finite type under principal localization follows by adjoining an inverse with one equation. Step 7 uses only the locally-quasi-finite part of the base-change node, not a hidden separatedness assumption, and the exact polynomial-algebra dimension bound for one variable. Every fibre is finite type over its residue field; empty fibres are allowed by that bound.

Step 8 uses dimension invariance under completion and under injective integral extensions to identify dim L=d. I read the catenary dimension equality: D is Noetherian universally catenary by excellence, D and R are domains, the inclusion is finite type, and the primes contract correctly. The residue extension is finite by Step 2, so its transcendence degree is zero. The equality gives generic transcendence degree one, and the finite-type-domain dimension theorem turns this into generic-fibre dimension one. This does not infer generic dimension from the upper bound alone.

Step 9 uses the G-ring completion theorem, localization regularity, and regular composition. I checked the extra Noetherian-fibre hypothesis of the composition theorem: a prime contained in w has the corresponding completion fibre, explicitly Noetherian in the completion theorem, and every other fibre is zero. This yields the actual canonical completion morphism's regularity, with no finite-type assertion about that map.

Step 10 uses the exact ideal equality of Step 2 after the principal shrinks and the previously established injections. A nowhere dense V(I) in the integral X means I is nonzero, including I=A for empty Z. Hence the extended ideal and its descended ideal are nonzero; their zero set in integral W is nowhere dense. I tested empty Z, principal and nonreduced ideal markings, and the possible empty nongeneric fibres. I also checked the trivial group, equal characteristic zero and positive characteristic, arbitrary imperfect/nonseparably closed residue fields, and the mixed-characteristic example of IV 4.3.2. The example explains why taking the invariant quotient before Elkik would be wrong and why the equivariant input is necessary.

All non-elementary steps are below 2000 characters. I checked them for hidden comparisons and sublemmas nevertheless: the substantial formal-presentation and marked-descent arguments are new statement nodes, and normality descent, kernel killing, and nowhere density are explicit short arguments from cited statements. Off-unit uses are declared individually as generic tools; they do not replace the unit's route. No files in the shared project or launchers were modified.

## Continuation validation

The interrupted attempt left the full split, report, citations and eight logged Mathlib searches. No delivery process was active when this continuation began. I retained that work and ran the required dry run first. Its only failures were the two new statements using grouped definition references that the preflight did not recognize. I changed those to individual bracketed node references, refreshed citations.json from the current statements, and reran the dry run. It exited successfully with `OK (not pushed)` at 3d74c0eea0.

I independently reread ILO IV 4.3.1–4.3.7 and V 2.2–3.2.4, each cited existing statement, and the nearby complete-coordinate, reduced-special-fibre-cover and henselian-local-model nodes. None of those newer nodes supplies the equivariant prime-to-ell presentation or arbitrary marked ideal descent. In particular the henselian-local-model node assumes a separably closed residue field, which is absent here. The proof's completion, dimension and regular-composition hypotheses match the current cited statements. The blueprint ancestor search again returns lem-per-artin-gabber-affine-curve, and the blueprint searches found no exact duplicate. No mathematical statement changed in this continuation.
