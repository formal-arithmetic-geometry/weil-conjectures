# Q46 stage-1 delivery: sk-def-sf-admissible

## Files written

- `dag/nodes/sec-six-functors-basics/sk-def-sf-admissible.json`: definition, split; no Mathlib match. All defining conditions are retained; thirteen existing notion nodes supply the objects used.
- `dag/units/sk-def-sf-admissible.json`: only `realized` and `realized_by` set, with this definition realizing the statement and no proof steps.
- `citations.json`: empty list, because a definition has no proof steps.
- `searches.jsonl`: actual msearch log; every recorded query was executed and its output read.

No new nodes; no Mathlib leaves; no Lean written or compiled.

## Attachments

None. I searched the whole project source for the literal `(blueprint: sk-def-sf-admissible)` tag and for HasUniformCohomologicalDimensionLE, HasAmbientExceptionalRightAdjoint, IsExceptionalAdjointAdmissible, and admissibility. I read `lean/WeilConjectures/SixFunctors/ProEtale/ExceptionalAdjoint.lean` in full and `ExceptionalAdjointUniqueness.lean` in full. The most relevant declarations are AlgebraicGeometry.ProEtale.HasUniformCohomologicalDimensionLE (line 131), HasAmbientExceptionalRightAdjoint (line 150), and IsExceptionalAdjointAdmissible (line 183). The first agrees with the full quantifier in this unit. The second has right-adjoint existence as an additional field; the current unit defines the ambient condition by FullCD alone and explains existence as a consequence. The admissibility declaration extends that different structure. These declarations alone do not state all the imported explanation, and the finite-stage qualifications are explicit in their docstrings. Therefore I do not report a partial or definition-only attachment as an attachment of the whole item. No sorry map or compiler was used to certify an attachment.

## WANTED

None. The current blueprint and the definitions needed for this item are present locally.

## What changed and why

The source read is `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-sf-admissible/_section.md`, clauses (1), (2), (3) and the paragraph defining their conjunction. I also read the current chapter introduction, the stored unit record, SETUP's three-level rule, and `stages/1-dag.md`. This is a definition: its split names the notions from which its conditions are formed, rather than introducing new nodes that simply restate its clauses.

STATEMENT-DISPUTED: the imported text leaves A and the subscript n unbound when read as a standalone node. I restored the inherited finite coefficient setting A=A_{E,n} and the finite-type k-scheme setting. This is the intended finite stage: both the detailed coefficient definition and the upstream admissibility docstring say so. It does not identify these ordinary pro-etale derived categories with the integral/rational module-object coefficient layers. No condition (1), (2), or (3) has been weakened or replaced. The constants remain signed, independent of the interval, and uniform over the right adjoints. No ordering on c_f^- and c_f^+ is added.

I expanded FullCD directly, with all sheaves on each base-changed source. In particular, the sheaf G on Xbar times_Y V is arbitrary, not required to be a pullback from Xbar. I deliberately did not cite `def-weil-full-cohomological-dimension` as though it said this: its current statement explicitly restricts its base-change clause to pulled-back original-source sheaves. This is a genuine quantifier mismatch. The FullCD formula is already clause (1) of the item, so a new node with that same formula would be the forbidden relabelling of a clause.

I also did not substitute `def-weil-ambient-exceptional-adjoint` or `def-weil-exceptional-adjoint-admissibility`: those records include coherent adjunction data for every compactification refinement, while this current unit uses one chosen compactification and the FullCD condition alone for the ambient datum. The stored unit record is the older sec-smooth-purity snapshot: it still requires refinement compatibility and lists the older AmbientExceptionalAdjointData name. I preserve that maintainer-owned text and record this discrepancy here; the statement realization refers to the current source, not a silent alteration of the unit record.

As required by the stage-1 convention for claims inside definitions, the definition contains the data and conditions only. The original nondefining explanations are preserved below and audited against their existing sources. They do not become extra hypotheses of the definition. In particular, saying that the second notion includes additional preservation requirements does not claim to have proved a counterexample separating the two predicates: the source's word 'strictly' supplies no such witness.

## Existing explanatory claims and their sources

The original Brown-existence explanation says that FullCD makes Rf_{!,n} preserve coproducts and hence gives a right adjoint on ordinary unbounded pro-etale derived categories. The existing `lem-sp-fullcd-ambient-adjoint` states precisely that implication for the finite-stage compact-support candidate, even including coherent refinement data. I read its statement, including the base, properness, coefficient and compactification hypotheses. Our stronger base-changed-source FullCD condition implies its weaker pullback-only one by substituting G=g_V^*F. The present definition does not need to choose or construct that adjoint. Brown representability is not made a defining condition or smuggled into a definition proof.

The original restriction comparison says that an ambient adjoint satisfying clause (3) restricts to the small finite-Tor categories and agrees there with the constructible exceptional inverse image. The first assertion is exactly what clause (3) requires of the object map; since the categories are full, restriction simply keeps the same morphism map. For the comparison, `sk-def-sf-operations` (vi) and the final paragraph of its statement record the constructible comparison, and `thm-sf-ambient-adjoint-class` (2) supplies the Hom bijections on bounded-below etale-origin inputs. I read both statements. Clause (3) puts the ambient value in the constructible finite-Tor class, and there the two representing objects have the natural Yoneda isomorphism. The upstream explicit implementation is AlgebraicGeometry.ProEtale.IsExceptionalAdjointAdmissible.rightAdjointIsoRightDerivedUpperShriek, `ExceptionalAdjointUniqueness.lean:127`, read with its assumptions, not treated as an exact attachment of this unit. This explanation is not a prerequisite for defining admissibility, so the node no longer depends on sk-def-sf-operations and closes no cycle through that exposition.

The original warning is not lost: for an elliptic curve over the algebraic closure of F_p and A=F_r, r different from p, the source asserts an arbitrary pro-etale sheaf outside etale origin having nonzero cohomology in every positive degree; full cohomological dimension fails, R p_* does not preserve the coproduct of its shifts, and neither the unbounded nor bounded-below ambient functor has a right adjoint. I read `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-rem-sf-fullcd-scope.md` in full. It is a remark, not a DAG definition to cite for an existence theorem. The upstream implementations are in `AmbientCounterexample.lean`, including not_hasAmbientExceptionalRightAdjoint_of_isAbelianVariety:300 and not_isLeftAdjoint_rightDerivedLowerShriekPlus_of_isAbelianVariety:320; this report does not assert their dependency closures were checked sorry-free. The warning explains why neither datum is assumed for all smooth proper structure morphisms. It is not a new defining condition or a lemma needed to make this predicate well defined.

The final source explanation concerns unconditional constructible functors, rather than arbitrary ambient adjoints. I read the statements of `thm-sf-ambient-adjoint-class`, `thm-sf-preservation-class`, and `thm-sf-ctf-stability` (v). Their existing statements give the class-restricted Hom bijections and preservation, with their actual domain restrictions. In particular the current preservation theorem assumes separated Y, and stability assumes separated X and Y; the imported informal blanket sentence does not restate these hypotheses. They are not used to assert ambient admissibility and do not enter the definition's dependency list. Removing these expository citations as definition prerequisites avoids making a definition depend on theorems about its neighboring constructible functor.

## Not duplicates

There are no new nodes. Whole-DAG text searches and `tools/blueprint_refs.py search` were made for admissibility, exceptional-adjoint admissibility, and ambient exceptional right adjoint datum, and the ancestor command confirms this item is its own blueprint ancestor. The related detailed definitions above differ in refinement data and, for FullCD, the sheaf quantifier. None is an exact duplicate of this combined current-unit definition, so `blueprint.same_as` is empty. No existing node is edited or recreated.

## Review by Q46

I checked delivery-errors B through E in full, including the repeated isolated-run sections. For B1/B2, this is one self-contained definition, no new nodes and no proof sketch masquerading as an unsplit statement. All schemes, coefficient symbols, degree-zero embeddings, the chosen functor, bounds, and quantifiers are introduced. The only constructions are actual categories and functors from the existing definitions; no unspecified data are chosen from a sorried existence assertion. B3 was checked by opening every one of the thirteen statement dependencies:

- `def-weil-finite-field-fiber` gives exactly the fixed finite-field algebraic closure context, not a claim about arbitrary bases.
- `def-weil-l-adic-coefficient-extension` defines the valuation ring, uniformizer and finite quotient A_{E,n}.
- `def-weil-finite-type-morphism` supplies finite type for morphisms and structure morphisms.
- `def-weil-proper-morphism` explicitly defines separatedness and properness; its title alone was not the justification.
- `def-weil-compactifications-refinements` supplies the actual factorization with open j and proper p. The definition uses only a chosen compactification, not the unused refinement compatibility clauses.
- `def-weil-pbc-proetale-modules` defines the finite discrete coefficient module category and its ordinary unbounded derived category, with a universe convention.
- `def-weil-derived-cohomology-sheaves` supplies H^r in that category, including the degree-zero sheaf convention written explicitly in the item.
- `def-weil-derived-direct-image` defines the finite-level total right-derived functor on the unbounded pro-etale module categories, for schemes with ell invertible.
- `def-compact-support-direct-image-detailed` defines exactly Rp_*j_! for a chosen compactification on these categories. Its independence claims have a restricted domain, and I do not extend them.
- `def-pc-fibre-product` supplies the source Xbar times_Y V and its projection to V with no smallness or finite-type assumption on V. Thus the arbitrary site-base-change clause is correctly typed.
- `def-weil-finite-torsion-constructibility` defines bounded complexes with constructible finite-coefficient cohomology.
- `def-weil-constructible-intervals` defines the vanishing interval inside bounded constructibility. I wrote out the meaning for a potentially empty shifted interval so the statement does not invoke that node outside its declared a<=b domain.
- `def-weil-finite-tor-amplitude` defines precisely the full finite-Tor subcategory used in clause (3), rather than identifying bounded constructibility alone with finite Tor dimension.

These are statement dependencies, so there are no item proof steps and no per-step C1/C4 citations to quote. `citations.json=[]` records that fact; it is not an omitted audit. The explanatory paragraphs above separately record which existing statements support them and distinguish their precise hypotheses. For C4 I corrected the tempting misuse of the older FullCD definition and of underived right-adjoint instances. For C1 there is no hidden invocation of finiteness, descent, or Brown representability in constructing the predicates. The Brown and comparison claims have been separated from the definition rather than disguised as elementary proof steps.

For B4/B5 the JSON contains single TeX escapes and no unverified Stacks numbering; this definition's primary source is the current blueprint, not an invented Stacks tag. For B6/B8 no Mathlib leaf is claimed: semantic hits were read and found to concern ordinary pushforward adjunctions or basic morphism properties. B7 is enforced by the actual searches.jsonl log. I ran LeanFinder twice with different formulations, Loogle, LeanSearch (available on this run), and the required Mathlib greps; all are recorded with exact query texts. B9 is satisfied by the whole-blueprint searches, unchanged blueprint.is, empty same_as, and the split_report mapping to the current defining clauses. B10 is satisfied by the full attachment check described above, not by treating a partly matching definition as a finished result.

For D1/D2 I introduced no node for a clause of the item or for a renamed conjunction. For D3-D5 no argument is moved to an unexplained proof step: definitions have no proof steps here, and there are consequently no long non-elementary steps. The predicates use their actual quantified conditions. For E1-E4 I checked the coefficient invertibility hypothesis (ell differs from p_0 on finite-type k-schemes), the compactification maps and base-change projection, arbitrary sheaves on the correct source, and the absence of any finite-type restriction on pro-etale site objects. For E5/E6 I use neither 'transport' nor an undocumented comparison as part of defining the predicate. The old and current coefficient categories and the full versus restricted sheaf quantifiers are explicitly distinguished.

Edge cases: the empty source or target has only the zero sheaf category where appropriate, so the vanishing and preservation conditions remain meaningful; no nonempty chart or dimension maximum is used. For an identity compactification, c=0 makes the FullCD condition hold, and the identity right adjoint preserves both interval and Tor conditions with shifts (0,0). The zero input lies in every vanishing interval, including empty shifted intervals. A bound c=0 still imposes all positive-degree vanishings, and n=1 is the nonzero residue-field stage, not an accidental zero quotient. An arbitrary site object V need not be finite type; the referenced derived functor is defined for its schemes nonetheless. These checks test the predicates; they do not claim that ambient admissibility holds for a nontrivial smooth proper morphism.

## What remains unfinished

No stage-1 work on this definition remains. Its thirteen existing dependency nodes continue on their own recorded statuses. No Lean, compiler, Lake, global build, or local DAG/preflight checker was run. Server dry-run and delivery results are recorded by the delivery tool after this report is packaged.

## Original nondefining exposition, preserved verbatim

The admissibility datum is strictly stronger than the ambient datum (1): it is
(3) that makes the restriction $Rf^{\times}|_{\Dctf}$ of the ambient functor a
functor of the small categories, and when (1)–(3) hold that restriction
coincides, by uniqueness of adjoints, with the constructible exceptional
adjoint $Rf^!$ of [sk-def-sf-operations] (vi). Both data are *assumptions*,
not properties that hold in general.

*Warning: the ambient datum is not satisfied in general.* Its
$\operatorname{FullCD}$ clause quantifies over *every* pro-étale sheaf
of $A$-modules, and this fails for the structure morphism $p$ of an elliptic
curve $E$ over $\overline{\mathbf F}_p$ with $A=\mathbf F_r$, $r\ne p$: there is
a pro-étale $A$-module sheaf (not of étale origin) with nonzero cohomology in
every degree $n\ge1$, $Rp_*$ does not preserve the coproduct of its shifts, and
no right adjoint of $Rp_!=Rp_*$ exists on $D(E_{\Proet},A)$ or on
$D^+(E_{\Proet},A)$ ([sk-rem-sf-fullcd-scope]). Hence neither (1) nor the
admissibility datum may be presupposed for the structure morphism of a
smooth proper variety. For the constructible exceptional adjoint $Rf^!$ of
[sk-def-sf-operations] (vi), by contrast, the analogues of all three clauses
are theorems for every separated finite-type morphism of finite-type
$k$-schemes: the adjunction on $\Dctf$, with compatible units and counits
([thm-sf-ambient-adjoint-class]), and the two preservation clauses with explicit
constants ([thm-sf-preservation-class],
[thm-sf-ctf-stability] (v)).
