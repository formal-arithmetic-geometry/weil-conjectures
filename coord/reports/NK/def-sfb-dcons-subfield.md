# def-sfb-dcons-subfield — stage 1

## Files written

- `dag/nodes/sec-six-functors-basics/def-sfb-dcons-subfield.json`: existing definition, status split; no Mathlib match for the whole definition. All logged searches are recorded with their original tool and query.
- `citations.json`: empty list, because this definition has no proof steps.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No Lean, compiler, Lake, live-project write, direct git operation, or push was used.

## Attachments

None. Searched the whole slopmaster2 `WeilConjectures/` for `def-sfb-dcons-subfield`, `PadicSubfieldConstructible`, `BoundedConstructible`, and `padicSubfieldRingObj`, as well as nearby notions. The exact named abbreviation does not occur. The upstream master reference has `AlgebraicGeometry.ProEtale.PadicSubfieldConstructible` at `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Colimit/TwoColimit.lean:155`, abbreviating `BoundedConstructible (padicSubfieldRingObj X ℓ E)`. This is reference material, not an attachment to finished slopmaster2 Lean.

The slopmaster2 category `ProEtale.DerivedCategoryBoundedConstructible` is cut out by essential image from the étale category with a fixed external coefficient category. Its own docstring in `SixFunctors/ProEtale/Derived/Constructible.lean:39-51` explicitly restricts its intended agreement to finite coefficients and warns that it is the wrong notion for E and O_E. The rational Karoubi category at `SixFunctors/ClosedImmersionStages.lean:313` is also a different construction. Neither was substituted for the module-object category here.

## Wanted sources

None. This item is a definition supplied by the current blueprint; it requires no independent Stacks theorem or proof. No SGA source is used.

## Problems found and changes

The imported statement was mathematically correct, but its dependencies included `def-sfb-subfield-coefficient-map`, which defines a morphism E_X to F_X for a pair of fields. There is no such morphism in this item. Replaced that dependency with the existing precise definitions of the condensed field, pulled-back ring, and module objects. The statement now references them where used, and explicitly records that morphisms are ambient derived morphisms, already implicit in “full subcategory.” This changes neither the objects nor morphisms of the category and adds no hypothesis.

The imported `lean_not_found` and `in_cycle` flags are retained as required. Cycles internal to other imported definitions are not repaired by editing those other workers' nodes. No mathematical error in the chapter or unit route was found. This item is not the key node of its unit, so no unit realization fields were changed.

## Unfinished work

None for this one-level definition split. The existing general-category and constructibility nodes retain their independent work. The delivery is left for the second reader; only a no-push dry run is performed.

## Not duplicates

No nodes were created. Searched the whole DAG and imported blueprint for “bounded constructible,” “subfield,” the exact D_cons(X,E) notation, and “full subcategory,” using both repository text search and `tools/blueprint_refs.py search`; also ran the ancestor lookup. The general `sk-def-sfb-bounded-constructible` and `def-sfb-bounded-constructible-complexes` take a general ring object, while this existing item names its E_X specialization. `def-sfb-dcons-qlbar` uses a different coefficient ring. The constructible scalar-extension and cocone nodes use this category rather than independently defining the same category. No other blueprint node supplies this exact named specialization; `same_as` is empty. The imported node has `blueprint.is` equal to its id and `from: null`, as required for imported nodes.

## Review by NK

I read the current source `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/def-sfb-dcons-subfield.md` in full, the chapter record, and the unit record. The unit's cocone paragraph (step 9) uses precisely these categories as the domains of restricted scalar-extension functors. Nothing in this definition asserts descent, preservation of constructibility, transitivity, or a 2-colimit theorem, and no such result was smuggled into a dependency. The definition stays on the unit's stated route. There are no new nodes whose sources need separate review.

I opened and read each of the four retained statement dependencies. `def-sfb-padic-subfield-condensed-ring` defines the actual condensed ring by continuous functions with E's topology induced from the fixed algebraic closure, and states that it is commutative. The inclusion of the finite intermediate field E into the fixed algebraic closure is the embedding required there. `sk-def-sfb-pulled-back-coefficients` defines p_X^* of a condensed ring and gives its ring-object structure, including preservation of commutativity. `sk-def-sfb-module-objects`, clause 3, defines precisely modules over this pulled-back ring in abelian sheaves on the small pro-étale site. Finally, `sk-def-sfb-bounded-constructible` defines the full subcategory of D(Mod_R) with bounded, constructible cohomology and ambient morphisms. Its hypotheses specialize to A = Ab and R = E_X; the topology and commutativity required for E_X are supplied by the first two dependencies. I also read the current blueprint sources for the general bounded constructible definition and the condensed subfield definition, and the statement of `sk-def-sfb-constructible`, to check that constructibility is the pro-étale finite constant local model condition, locally on affine opens for general X. This is why no qcqs, Noetherian, or invertibility-of-ell assumption was added.

There are no proof steps: stage-1 splitting of a definition consists of naming its constituent notions. Consequently C1 and C4 were checked for the defining references just described; no claim is made by citing a definition as a theorem. `citations.json` is empty rather than manufacturing proof-step citations. The coefficient-map dependency was removed after checking its statement, since it supplies a comparison with a second coefficient field that this definition never uses.

I tested the definition on the zero complex, shifts, E = Q_ell, an empty scheme, arbitrary non-qc schemes, and schemes in characteristic ell. The zero complex has vanishing cohomology; shifts translate a finite cohomological interval; E = Q_ell still has the specified topology and condensed ring. On the empty scheme the same full-subcategory construction makes sense. Constructibility on arbitrary schemes is already defined locally on affine opens; the present statement does not silently impose a global finite stratification. Characteristic ell changes neither formation of E_X nor the definition of its modules. No t-exactness, triangulated-closure assertion on arbitrary schemes, derived completeness condition, or finite Tor-amplitude condition is needed or claimed.

I checked delivery-errors B–E against the actual files. There are no new statement-only nodes, auxiliary clauses, duplicate lemmas, false inference, induction, base change square, or omitted proof to audit. JSON uses ordinary single TeX escapes on decoding. Mathematical content is unchanged from the source, so no STATEMENT-DISPUTED correction is required. All Mathlib searches were performed through msearch.py, including a second semantic phrasing; the exact queries and returned hits are retained. I read the closest source hits: `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE` (Mathlib/Algebra/Homology/DerivedCategory/TStructure.lean:180–188) is a bounded-representative lemma with no constructibility assertion, and `LightCondMod` (Mathlib/Condensed/Light/Module.lean:44) is a module category on the site of a point, not the present derived category over X. Neither is a match for this whole definition. The grep searches for boundedConstructible names and for constructibility in Algebra/Homology returned zero hits.

## Second reading by NK

- Item statement: checked against upstream master `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Colimit/TwoColimit.lean:153–156` and the blueprint definition; verdict PASS. The finite intermediate field, scheme, pulled-back condensed ring, module derived category, boundedness, constructibility, and ambient morphisms all agree.
- Dependency `sk-def-sfb-bounded-constructible`: checked its full statement; verdict PASS. It supplies exactly the bounded-constructible full-subcategory condition and ambient derived morphisms.
- Dependency `def-sfb-padic-subfield-condensed-ring`: checked its full statement; verdict PASS. It supplies the condensed ring of the topological subfield and commutativity required for the specialization.
- Dependency `sk-def-sfb-pulled-back-coefficients`: checked its full statement; verdict PASS. It defines $E_X=p_X^*\underline E$ and transports the commutative ring-object structure.
- Dependency `sk-def-sfb-module-objects`: checked clause 3; verdict PASS. It defines sheaves of modules over the pulled-back coefficient ring on the small pro-étale site.
- Proof steps: none are present because this is a definition node; verdict PASS. `citations.json` is therefore correctly empty.
- New nodes: none; verdict PASS. No new statement, proof dependency, or Mathlib leaf requires a separate audit.
- Edge cases: checked the zero complex, shifts, $E=\mathbf Q_\ell$, the empty scheme, and characteristic $\ell$; verdict PASS. The definition remains meaningful and imposes no unintended hypotheses.
- Changes made: none to the mathematical statement or dependencies. This second-reading section is the only change, documenting the source and dependency checks required before delivery.
