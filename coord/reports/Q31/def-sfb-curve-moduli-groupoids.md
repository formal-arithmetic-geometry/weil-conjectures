## Files written

- dag/nodes/sec-six-functors-basics/def-sfb-curve-moduli-groupoids.json: definition; not in Mathlib. Its constituent notions are all existing nodes. Added the direct algebraic-space chart dependency and citation, precise Stacks source labels, logged searches for the current predicate, and the stage-1 split report.
- citations.json: empty list, because a definition has no proof steps.
- No new nodes; no Mathlib leaves created.

## Attachments

None. Searched lean/WeilConjectures for the item tag and curve/moduli terms and for HasNonemptyNodalGeometricFibres, IsOrdinaryNode and ProperCurveFamily; no matching declaration was found. The existing Sheaf.AlgebraicGeometry.CurveModuliGroupoids declaration is reference material and its lean record is retained; it is not an attachment under the brief's WeilConjectures-only rule.

## WANTED

None.

## Corrections and scope

The live item is already a narrowed definition of nonempty nodal geometric fibres, not its historical groupoid title. It has a stage-2 review but no stage-1 reviewed record or released repair note. There was no earlier sandbox split or report to reuse. This delivery audits that live definition, without changing its mathematical predicate or Lean record. The omitted direct dependency was def-trf-algebraic-space, whose statement actually defines representability and etaleness of scheme charts. The existing def-sfb-proper-curve-moduli also uses it, but the item now cites it explicitly.

Stacks 0DSY allows the empty curve. The item's explicit nonempty-fibre refinement is intentional, already recorded in the live statement and its user lem-sfb-nodal-curve-stack-smooth; it is not attributed to 0DSY alone. No equivalence of all-chart conditions, descent, openness, algebraicity or smoothness of a stack is asserted by this definition. Those are separate theorem obligations, not claims to smuggle into a definition.

The existing blueprint ancestor utility reports from.node = None. I retained this inherited provenance and its precise place/via description; searches of the whole blueprint found no alternative statement of this definition. The latest detail proof (3) now discusses compactification and proper/open direct-image preservation, rather than explicitly spelling out the recorded alteration prerequisites; the supporting definition does not replace any unit proof step. No unit or chapter file was changed.

## Not duplicates

No new nodes. The existing def-trf-nodal-geometric-fibres is a different predicate on scheme morphisms: it requires connected geometric fibres and dimension one, whereas this item is on the given algebraic-space proper-curve family and requires pure dimension one on etale charts with no connectedness condition. def-sfb-nodal-geometric-fibre-local-rings defines completion, the split-node ring and the scheme fibre projection, not this family predicate. def-sfb-ordinary-geometric-node defines the point predicate, reused here rather than duplicated.

## Review by Q31

I read Stacks moduli-curves.tex lemma-nodal-curves (0DSY), including the distinction between relative dimension one and arbitrary dimension-at-most-one curve families. I read curves.tex section-nodal (0C46), its completed-local-ring formula, and definition-nodal (0C47). There are no new nodes needing independent sources. I also read the latest blueprint chapter/unit context and direct-images detail proof via literature/blueprint/latest, and SETUP's chapter/unit/node restrictions.

This item is a definition, so it has no numbered proof steps, uses entries or proof citations to check under C1/C4, and no long proof step. For the analogous statement-dependency audit I opened every cited node and read its statement. def-pc-scheme gives the ambient schemes; def-weil-size-convention fixes universes; def-sfb-proper-curve-moduli gives the algebraic-space family and projection, its proper/flat/finite-presentation hypotheses and its geometric-fibre convention. def-weil-field and def-weil-algebraic-closure give the algebraically closed fields, not a restriction to algebraic extensions of a fixed base field. def-a1-space-point-topology defines the field-valued point classes whose nonemptiness is required. def-weil-pure-dimension gives dimension of every irreducible component, with empty schemes allowed. def-sbc-smooth-morphisms defines smoothness and the etale scheme notion. def-sfb-ordinary-geometric-node gives precisely a closed point with ring-isomorphic completion to the split-node ring, with no extra field-action compatibility. The added def-trf-algebraic-space defines representable etale maps from schemes and the representable presheaves h_U. I take no theorem about these notions from a definition node.

I read Sheaf/AlgebraicGeometry/CurveModuliGroupoids.lean and the point-predicate body in Sheaf/TraceFormula/NodalOpenLocus.lean without compiling. The former quantifies over all fields in universe u, forms the actual presheaf pullback using X.projection, requires Nonempty of its point classes and tests every representable etale scheme-source map. Its smooth branch uses an open neighbourhood and the second pullback projection, exactly as the node states. There is no change to this Lean definition in this delivery.

Small cases: over an empty base the geometric-point quantifier is vacuous. Over a nonempty field base an empty total fibre fails the explicit nonemptiness clause, even though all its empty charts satisfy pure dimension one vacuously. Empty charts of a nonempty fibre are allowed because they have no irreducible components or points. A disjoint union of smooth proper curves is permitted; no connectedness or genus condition is introduced. A disjoint union of a curve and an isolated reduced point is excluded by the pure-dimension-one clause. Over an algebraically closed field the local model uv=0 is still the split ordinary node in characteristic two; no division by two or characteristic hypothesis appears. The ordinary-node branch is only used with algebraically closed Omega. These checks reveal no statement dispute.

I checked B--E in full: no new unsplit proof sketches, non-self-contained nodes, unlogged search records, clause-restatement children, hidden proof facts, or changed target hypotheses are introduced. Existing search history is preserved, and new queries are precisely the logged msearch queries. Two semantic phrasings return only scheme/Weierstrass/power-series primitives; the whole-Mathlib grep finds only the unrelated Lagrange interpolation use of nodal. The Loogle unknown-identifier diagnostic is recorded as such, not relied on alone as a proof of absence.

## Unfinished work

None within the one-level definition split. The constituent existing nodes remain their owners' work; the definition makes no theorem claims that would require new statement nodes.
