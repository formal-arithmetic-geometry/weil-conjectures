## Files written

- `dag/nodes/sec-trace-formula/lem-trf-fixed-point-stalk-transport-cocycle.json`: statement, now split into four explicit elementary deductions from existing comparison and coherence results. Mathlib: no exact match.
- `citations.json`: verbatim statement excerpts for every proof-step dependency.
- `report.md`: this report. `searches.jsonl` is the search command's unedited log.

New nodes: 0. New Mathlib leaves: 0. Statement and statement dependencies unchanged. The existing blueprint ancestry is retained and its same_as field checked by whole-blueprint searches.

## Attachments

None. The blueprint-id search in WeilConjectures and dag/lean_names_upstream.json returned no declaration for the item. The concept search found `AlgebraicGeometry.ProEtale.globalSectionsTransport_comp` in SixFunctors/ProEtale/UpperLowerStar/Restriction.lean:181, `AlgebraicGeometry.WeilSheaf.globalSectionsTransport_frobeniusPowStr_comp` in WeilSheaf/StalkCharpoly.lean:353, and `AlgebraicGeometry.WeilSheaf.stalkFrobeniusIso` in WeilSheaf/StalkMonoidal.lean:89. I read these declarations and their context. The first concerns underived sheaves; the second assumes a Weil structure and acts on its stalk sections; the third is an underived stalk functor comparison with adic coefficients. None states every clause for arbitrary objects of the ordinary unbounded derived category with the specified scheme-to-Galois comparison, so none is an attachment.

## WANTED

None. The relevant blueprint and Stacks sources are present.

## Problems found and corrections

The imported item was unsplit, with no proof and no Lean audit attachment. Its statement is correctly typed: c maps from P_(a+b)L to P_a P_b L, so the final composite starts at J(L) and ends at J(P_a P_b L). I retained its complete statement. The apparent shorthand “iterate the canonical stalk identification” in the ancestor proof is expanded into an equation, rather than treated as a new lemma with the same conclusion.

The source lemma for composition does not itself state triple associativity. I therefore cite the already existing `lem-trf-derived-pullback-coherence` for that assertion, rather than attribute it to Stacks 0D6D alone. I also cite `lem-trf-constant-coefficient-composition` to verify the coefficient normalization explicitly. The bounded termwise-stalk result `lem-trf-proetale-pullback-stalk-coherence` was read and deliberately not used: the item's stalk is RΓ composed with derived point pullback on the unbounded category.

No source error or STATEMENT-DISPUTED was found. No SGA source is used. No Lean file was written and no compiler or build command was run.

## Unfinished work

None in this one-level split. Dependencies retain their own existing stage-1 states.

## Not duplicates

No new nodes. Whole-DAG and whole-blueprint searches for stalk transport, fixed-point stalk, multiplicative iterate and pullback identify existing comparison/coherence tools; no imported blueprint node states this complete fixed-point transport cocycle. The broader Frobenius operators definition includes a Weil map and does not assert this coefficient-independent cocycle.

## Review by N1

I read the current main-20261015 ancestor proof `sec-trace-formula/sk-c-proper-global/lem-trf-frobenius-degree-formula.proof.md`, Step 1, including its displayed iterated Weil calculation. The item isolates exactly its canonical fixed-point identification and naturality, before any Weil structure or trace is introduced. I also read the chapter and unit records. This item is not the unit's key statement, so the unit's realized fields are not edited. The proof stays on the ancestor's route through the scheme–Galois comparison; the off-unit citations in split_report.tool_uses are generic composition/coefficient tools, together with the comparison expressly named by the ancestor.

I read Stacks `sites-cohomology.tex`, Tag 0D6D, label lemma-derived-pullback-composition, and its K-flat representative proof. I read the full statements of each node cited in the four steps: `lem-weil-pbc-proetale-derived-pullback-composition`, `lem-trf-constant-coefficient-composition`, `pur9-def-derived-stalk`, `lem-trf-derived-pullback-coherence`, and `prop-trf-scheme-galois-comparison`. I checked the latter's current blueprint_update and read its existing proof to verify the comparison convention, but use only its stated natural isomorphisms and multiplicative-iterate assertion. No new node requires a separate source.

Step 1 uses the constant-coefficient statement's displayed equality to satisfy the composition lemma's ring-sheaf hypothesis. The composition lemma explicitly supplies a natural isomorphism of functors, hence applying RΓ gives the displayed naturality of rho. The stalk definition explicitly is that RΓ of derived point pullback, including points not of finite type. The only independent calculation is induction on j/d to show Phi^j z=z. This does not require z to lie above a closed point.

Step 2 uses the comparison proposition's natural-isomorphism clause, applies J, then substitutes Step 1's equation. Its general finite-ring coefficient hypothesis is satisfied by the fixed finite quotient O_E/varpi_E^n; its annihilating ell-power is invertible in k because ell differs from the base characteristic. I checked that the proposition is on the full ordinary derived category, so no constructibility, perfectness or Weil-structure assumption is silently added.

Step 3 uses exactly the displayed triple-associativity equation of `lem-trf-derived-pullback-coherence`, substituting j=z, h=Phi^a and k=Phi^b. All three morphisms are schemes maps, and that lemma uses a finite constant ring with canonical coefficient identifications and unbounded ordinary derived pullbacks. Replacing Phi^a z with z turns its second comparison into c_(z,Phi^b), with no change of geometric point or residue-field automorphism. Applying the single functor RΓ then gives the rho cocycle. Thus the non-elementary associativity assertion is a cited statement, not a purported consequence of the mere existence of a composition isomorphism.

Step 4 writes out the meaning of the comparison proposition's multiplicative iterate using e_(a,b) and c_(a,b), with both sides landing in P_a P_b L. Naturality of kappa_a identifies the two possible orders of its whiskered factors. Substitution of Step 3 and naturality of rho_a for the actual arrow kappa_b,L gives the three displayed equalities. Every intermediate object is specified, in particular rho_a is evaluated at Q_b L before it is moved past kappa_b,L, and at P_b L afterward. This checks the order of the cocycle rather than assuming that transports commute.

For B1–B9 and C1–C8, there are no new statement-only nodes, duplicate tags, hidden new definitions, or circular new dependencies. All proof uses have verbatim statement excerpts in citations.json; the excerpts were checked as substrings of the cited statements. Each remaining step is an elementary substitution or naturality calculation from those statements. Step texts have 741, 629, 794 and 1057 characters, respectively; none exceeds 2000 characters or hides a separate comparison theorem. The statement retains the supplied notions and its six statement dependencies. No existing node is modified besides this item.

I tested the indexing at d=1 and a=b=d, where the formula is the twice-iterated transport with target J(P_d P_d L), and at a=d,b=2d, where no interchange of a and b is made. For L=0 or the zero arrow u the equations are maps between the same zero objects or the same composable objects and impose no additional hypothesis. On X_0=Spec k_0 the calculation still uses the canonical Frobenius comparison rather than identifying the semilinear g with a k-map. A nonreduced X_0 causes no new issue: the comparison theorem covers arbitrary finite-type X_0, and this proof uses no reducedness. The case X empty has no chosen z and is vacuous. Only positive multiples are claimed; no identity-iterate normalization is smuggled into the argument.

Mathlib searches were made through msearch.py and read as returned. The two LeanFinder phrasings yielded ring Frobenius iteration, fibered-category and nonabelian cocycle results; LeanSearch yielded topological or structure-sheaf stalk maps. The two grep patterns and Loogle query are logged verbatim. I opened SheafOfModules.pullback_assoc at Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:193 and PresheafOfModules.pullback_assoc at Mathlib/Algebra/Category/ModuleCat/Presheaf/Pullback.lean:142; these normalize underived module pullbacks but do not state the derived fixed-point Frobenius cocycle. These are not one-line specializations proving every clause of this item. Existing inherited searches were retained, and actual searches for this delivery appended without inventing results.
