# Worker report: def-trf-cohomological-comparison

## Files written

- `dag/nodes/sec-trace-formula/def-trf-cohomological-comparison.json`: definition, split using existing nodes; no complete Mathlib match.
- `citations.json`: `[]`, since the item is a definition with no proof steps.
- `report.md`: this report. `searches.jsonl` is the unmodified log produced by msearch.py; `varshavsky.txt` is a local extraction for the reader, not a delivery file.

New nodes: 0. New Mathlib leaves: 0. No Lean or unit file changed.

## Attachments

None. Searches of the read-only slopmaster2 WeilConjectures tree for the exact blueprint id, cohomological comparison/morphism and compactifiable terminology found no declaration stating this datum. The `GeometricOperations` package in SixFunctors/ProEtale/TraceFormula/Defs.lean concerns operations on one coefficient system, not a comparison between two correspondence diagrams; its fields cannot attach this item. Master was searched only as reference material and supplies no attachment evidence.

## WANTED

None. The item source is available locally as `literature/varshavsky-lefschetz-verdier-trace-formula_arXiv-math0505564.pdf`.

## Corrections and statement dispute

STATEMENT-DISPUTED: the imported clause (VII) used open immersions into proper schemes without requiring their images to be dense. Varshavsky Notation 1.1.2(c), printed p. 7, requires dominant open embeddings for a compactification. For example, the inclusion of Spec(k) as the first component of Spec(k) disjoint union Spec(k) is an open immersion into a proper scheme but is not a compactification in that source's sense. Clause (VII) now requires dense open immersions for X, C and their barred partners, and writes the commuting correspondence squares. This repairs the missing source hypothesis rather than silently using a weaker notion of compactification.

Notation 4.1.2 supplies actual natural isomorphisms between restriction of the compactified functors and application of the open functors to restricted objects. Those isomorphisms, their tensor/ordinary/exceptional compatibility, and the coefficient identification at the base are now specified. The compactification embeddings are called u_Z to avoid collision with the coefficient map j_Z in Notation 4.2.3.

The statement now says explicitly that the displayed maps are natural transformations, gives their object quantifiers, specifies whiskering in (III), and spells out composition of pre-comparisons. Diagram objects are labelled entries: for example X=s does not collapse the diagram into a differently shaped set. No exactness or strong monoidal property of f_Z has been added; the source only asks for functors, lax tensor maps and the stated axioms. In particular, alpha_g and beta_g are not required to be isomorphisms for arbitrary g. The duality comparison is the evaluation-defined map, not an independently chosen isomorphism.

Finite-Tor closure under internal Hom and Verdier duality is now explicitly supplied by the existing preservation theorem, rather than being inferred from a definition of those operations. The generic mate definition and the canonical pullback tensor/composition comparisons have been named as dependencies. No trace-compatibility theorem has been moved into this definition.

The source uses classical constructible categories; the project definition uses its specified finite-coefficient pro-etale geometric operation system. This is the existing realization convention of def-fix-six-functor-datum and def-trf-admissibility, not an assertion about arbitrary ambient pro-etale exceptional right adjoints. No higher coefficient stage or change in the coefficient category is asserted.

## Unfinished work

None for this one-level definition split. A fresh second reader must review and deliver it. The item is an auxiliary definition below lem-trf-trace-specialization, not the key statement of sk-i-curve-zero; the unit's realization fields are not this delivery's to change.

## Searches and reuse

The sandbox initially had no node, split, report or search log, only dispatcher brief markers. I read the current repository item and retained its Q48 metadata and all its inherited Mathlib search records. The inherited records are not claimed as searches run by NF. NF's additional entries are exactly the commands present in this sandbox's searches.jsonl. Both LeanFinder phrasings, Loogle, grep and LeanSearch ran successfully. The hits concern ordinary sheaf/module pullback and pushforward, generic natural transformations, and exponentiable morphisms in slice categories. I read Mathlib/AlgebraicGeometry/Modules/Sheaf.lean at the ordinary adjunction (line 188) and conjugateEquiv_pullbackComp_inv (line 265), ModuleCat/Sheaf/PullbackContinuous.lean at pullbackComp (line 167), and ModuleCat/Sheaf/PushforwardContinuous.lean at pushforwardNatTrans (line 192). Their objects and conclusions do not state compactifiable comparisons of constructible six-operation diagrams.

The whole DAG search for cohomological pre-comparison/morphism and compactifiable comparison finds this definition and lem-trf-specialization-cohomological-comparison; the latter is an example theorem depending on this definition and cannot replace it. Whole-blueprint searches for 'cohomological comparison', 'cohomological morphism' and 'compactifiable' found no equivalent blueprint definition. The ancestor command returns lem-trf-local-term-locality, as already recorded. Existing generic adjunction, finite-Tor, internal-Hom and monoidal-pullback nodes were reused, with no new notion or lemma node.

## Not duplicates

No new nodes. The definition is not the specialization theorem: the former specifies arbitrary comparison data and seven axioms, whereas the latter constructs such a comparison for nearby cycles. Existing adjunction and monoidal nodes supply ingredients rather than the complete notion.

## Review by NF

I read Varshavsky Notation 1.1.2(c), §§4.1.1--4.1.3, and Notation 4.2.3 in the local PDF extraction (printed pp. 7, 25--27 and 32), and checked the current blueprint ancestor and its sk-i-curve-zero unit. This definition serves the existing normal-cone specialization route; it introduces no competing purity route. Every primitive transformation and all seven axioms match the source: (I) associativity and signed commutativity, (II) multiplicativity at the point, (III) identity/composition, (IV) tensor compatibility, (V) invertibility of the specific evaluation-induced duality map, (VI) inverse ordinary/exceptional mates when both arrows are proper, and (VII) extension to dense compactifications. Finite composites, including the identity convention, reproduce §4.1.3(b). The units h and external comparison Pi reproduce Notation 4.2.3, with iota inverse in the coefficient map.

This is a definition, so there are no proof steps to audit under C1/C4 and no non-elementary long proof steps. I instead opened all seventeen dependency statements and checked precisely what they supply:

- def-trf-coefficient-conventions supplies n>=1, ell distinct from the characteristic, A=O_E/varpi_E^n and the finite pro-etale conventions. def-trf-correspondence supplies the two-leg correspondence convention; def-trf-fixed-scheme supplies the fixed fibre product, i_F, d and c i_F=Delta d. The legs are interchanged relative to Varshavsky's coefficient-map convention, without changing the fixed diagram.
- def-trf-admissibility supplies the specified constructible ordinary and exceptional adjunctions, their units/counits and exceptional composition. def-fix-six-functor-datum supplies the geometric operations and the normalized proper identification Rg_!=Rg_* used in (VI). These definitions are not cited as a proof of internal-Hom closure.
- def-weil-finite-tor-amplitude defines the full category used here. thm-sf-ctf-stability, at finite level only, supplies tensor and internal-Hom closure in clause (ii), both direct images and exceptional inverse image in (iii)--(v), and duality preservation in (vi). Hence f_Z RHom(M,N), f_Z D_Z M and every mate are defined on the stated category. All diagram schemes are separated of finite type over k, and all their arrows are separated of finite type, which are the theorem's hypotheses. No perfect-on-the-whole-site formula RHom(M,N)=M-dual tensor N is used.
- def-trf-dualizing-complex defines omega and D from the actual exceptional adjoint and specifies evaluation. lem-weil-pbc-ringed-internal-hom-exact-restriction states the derived currying isomorphism, and lem-pur-rhom-global-sections identifies its global degree-zero Hom with derived-category morphisms. These two statements give exactly the tensor–internal-Hom transpose used to define r_Z; all objects are complexes of modules over the constant commutative ring sheaf on the project's small pro-etale site. No stalk-internal-Hom commutation is used.
- def-weil-pbc-adjunction-mate specifies the general mate and its inverse. The ordinary construction transposes via bar g^* left adjoint to R bar g_* using the unbarred ordinary counit. The exceptional construction transposes via R bar g_! left adjoint to bar g^! using the unbarred exceptional unit. The types are respectively f_V Rg_* to R bar g_* f_U and R bar g_! f_U to f_V Rg_!, opposite directions as required for (VI). No arbitrary mate is assumed invertible.
- lem-pur-derived-pullback-tensor-iso supplies the canonical finite-coefficient pro-etale tensor, unit and signed symmetry identifications and their coherence. lem-weil-pbc-proetale-derived-pullback-composition supplies the pullback compositors for constant coefficient ring sheaves; its ring identifications are those of the coefficient operation datum. These are used in (I)--(IV), the coefficient unit and the composition formulas, not to assert anything about the f_Z being strong monoidal.
- prop-exc-open-adjoint states u_! left adjoint to u^* on the entire ordinary pro-etale derived category for open immersions and finite commutative coefficients. Together with the specified constructible exceptional adjunction and composition, this identifies u^! with u^* and types the exceptional restriction identifications in (VII). No general non-Cartesian exceptional base change is assumed: both sides identify with the exceptional inverse image along the same composite through open immersions.
- def-weil-proper-morphism defines properness and separatedness; def-weil-open-immersion defines the open embeddings. Density is defined inline. The correspondence squares and the restriction isomorphisms are data required by (VII), not an existence theorem asserted without proof. def-trf-external-product supplies exactly the ordered pullback tensor expression used in Pi.

I tested the identity comparison (all f and comparison maps identity), X=s (keeping diagram labels), n=1 and n>1 (finite Tor is still required), the empty correspondence/fixed scheme (zero derived category and no nonempty fixed component is required), and a nonproper arrow (VI imposes no inverse-mate requirement). At a proper diagram, compactification may be the identity. For an empty scheme a dense open compactification must itself be empty, consistent with the source. The non-dense two-point example above detects the imported omission in (VII). I also checked that density is imposed only on the basic X,C embeddings and their barred versions: no density of the induced fixed-scheme open immersion is added. The source does not require the fixed locus to be dense in its compactification's fixed locus.

B1--B9 hold without a new node or leaf. C1--C4 and D1--D5 do not require artificial proof steps for a definition; every construction remains prescribed by data and existing adjunctions. C5 was checked through the whole DAG and blueprint searches above; no new node is needed. There is no off-unit proof citation or route replacement. The corrections are the density requirement, explicit extension and composition data, and the missing typing dependencies described above. No claim is made that definitions alone prove preservation or trace compatibility.

## Second reading by NF

- Item definition: checked the full statement against Varshavsky Notation 1.1.2(c), §§4.1.1--4.1.3, and Notation 4.2.3 in the retained PDF extraction; the labelled correspondence diagram, pre-comparison data, mates, axioms (I)--(VII), finite composites, coefficient sections, and external product have the source's objects, directions, and hypotheses. Verdict: pass after the wording repair below.
- Proof steps: none, because this is a definition node; there are no hidden proof steps to cite.
- New nodes: none; the item creates no auxiliary node or Mathlib leaf.
- Dependency audit: reread all 18 `stmt_deps` statements. The finite coefficient/site/category conventions, correspondence and fixed diagram, dualizing complex, admissibility, six-functor datum, external product, proper/open immersion notions, finite-Tor closure, pullback tensor/composition, internal-Hom transpose, global Hom identification, mate convention, and open-immersion adjunction each supply exactly the notions used.
- Edge cases: checked identity comparisons and length-zero composites, (n=1) and (n>1), empty schemes/fixed scheme, a field-valued point, and a nonproper arrow (which is excluded from (VI)); compactification of an already proper diagram may be the identity, and a dense compactification of the empty scheme is empty.
- Source dispute: retained and independently verified the worker's correction that compactifications require dominant/dense open embeddings; the two-point disjoint-union example shows why an arbitrary open immersion is too weak.
- Change made: axiom (I) now says explicitly “commutative (with the signed tensor symmetry) and associative,” matching the source's commutative-and-associative requirement.
- Blueprint and duplication checks: the ancestor remains `lem-trf-local-term-locality`; whole-DAG and whole-blueprint searches found no equivalent definition and no reusable node that replaces this definition. No attachment, WANTED item, route change, or SGA citation was introduced.
