# Stage-1 report: lem-sfb-power-reductive-free-affine-quotient

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-power-reductive-free-affine-quotient.json: item, split into five steps; original statement and hypotheses preserved.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-power-lifting-affineness.json: statement, unsplit; no Mathlib match. Global power-lifting affineness test for arbitrary-base qcqs algebraic spaces.
- dag/nodes/sec-six-functors-basics/lem-sfb-affine-torsor-algebra-invariants.json: statement, unsplit; no Mathlib match. Coactions, invariant sections and equivariant surjections for arbitrary quasi-coherent algebras on an affine torsor.
- citations.json: verbatim statement quotes for every proof-step citation.
- searches.jsonl: unaltered output log of the required msearch.py commands.

## Attachments

None. Read-only searches of lean/WeilConjectures by the item tag and by power reductivity, geometrical reductivity, adequate affineness, quotient and torsor concepts found no declaration giving this result. Existing finite-etale and constant-group torsor declarations do not cover an arbitrary flat affine finitely presented group scheme over an arbitrary ring.

## Wanted literature

WANTED: Alper, Adequate moduli spaces and geometrically reductive group schemes, journal version, Proposition 9.7.8; Lemmas 4.1.8 and 9.2.5; Theorem 4.3.1, for the item and lem-sfb-space-power-lifting-affineness. The file literature/alper-adequate-moduli-spaces.pdf is absent. Read the cited original journal PDF at https://content.algebraicgeometry.nl/2014-4/2014-4-022.pdf online, including printed pp.502-506, 522-523 and 528; no file downloaded or repository literature list edited. The assembly is explicitly marked agent-written.

## Corrections and scope

No statement dispute or hypothesis change. The item had no proof. The existing adequate-moduli definitions and affine-target criterion explicitly assume a field; they cannot be used for arbitrary R. The existing power-lifting adequate affine quotient lemma additionally assumes a smooth finite-type group and finitely generated algebras over a field. The split therefore uses a general algebraic-space power-lifting criterion with every notion spelled out. This is a genuine criterion for arbitrary spaces, not a restatement of the torsor quotient clause.

The original citation def-sc-group-scheme is field-specific, but the item itself already specifies group-object diagrams over S and its coactions explicitly, so its intended arbitrary-base meaning is unambiguous. The new torsor lemma defines the group object over S inline and does not reuse that field-only definition.

The coaction prerequisite makes no reductivity assumption and proves no affineness conclusion; the power-lifting prerequisite has no group action or torsor. Neither new statement restates the item or a clause under the item's hypotheses. Both remain statement-only. Their eventual proofs are separate tasks. The torsor coaction lemma follows by translating the canonical descent datum through the affine quasi-coherent equivalence: the two restriction maps are rho and e -> e tensor 1; the cocycle is coassociativity, and faithful flatness plus affine exactness handles surjections. This explanation is in the report, not smuggled into an unsplit statement.

## Searches and blueprint route

Read AGENTS.md, GOAL.md, worker and stage-1 rules, SETUP's three levels, delivery-errors B-E, the chapter and unit records, and the latest blueprint unit and direct-image proof under literature/blueprint/latest. The legacy created chain reaches a null blueprint ancestor, as blueprint_refs.py ancestor prints; preserved that explicit null and the entire via list, with precise nonempty places. The current direct-image step (3) is the ancestor route context, not a new proof of this algebraic-group prerequisite. No chapter or unit record changed.

Ran blueprint_refs.py searches for adequate, affine quotient, Serre, coaction, power, invariant, power lifting and quasi coherent algebra; inspected the relevant DAG statements and source tags. No blueprint node states either new result. The existing Serre affineness node uses H^1 vanishing, which is not invariant power lifting. Mathlib searches all used the mandated msearch.py command. The log records two natural-language phrasings for each new result, Loogle, and source grep; all services used here returned successfully. Hits concern schemes, affine spaces, abstract module descent or type-valued torsors, not the statements delivered. Read the relevant Mathlib AffineScheme and Morphisms/Descent sources and the quotient-ideal grep hits; none is a one-line specialization covering these space or coaction assertions. Existing item search records were retained and supplemented with searches logged by Q132.

## Review by Q132

I read the journal source for the item (Proposition 9.7.8, printed p.528), the global algebra-surjection criterion (Lemma 4.1.8, printed pp.502-504), the adequate Serre criterion (Theorem 4.3.1, pp.505-506), and the all-algebra invariant condition (Lemma 9.2.5(3), pp.522-523). These places do not require X to be finite type. For the torsor coaction prerequisite I read the actual local Stacks statements: spaces-descent.tex, proposition-fpqc-descent-quasi-coherent, Tag 04W8; schemes.tex, lemma-equivalence-quasi-coherent, Tag 01IB. The source place identifies it as the algebra/coaction translation of those results, rather than pretending either tag literally states coactions. The new affineness lemma is the global formulation of the source criterion and has no field hypothesis.

Step 1 explicitly constructs the local inverse: the torsor relation supplies the unique g with x=s_i g, functorially in every test scheme. It needs no external lemma and is elementary, with no choice of geometric-point orbit in place of a sheaf isomorphism.

Step 2 uses the covering-calculus node precisely for base change and composition of fppf covers. The flat-lfp descent node requires a single surjective map, not an arbitrary member of a covering family. I corrected the initial draft by using the existing scheme-coproduct node, whose statement gives disjoint open components covering the coproduct, so that U is a single flat locally finitely presented surjection. The local definitions of these properties justify checking its source components. The flat-lfp descent node applies since maps of algebraic spaces are representable by algebraic spaces. The four-property node explicitly gives affineness under arbitrary base change and fppf-family descent. The affine-permanence node explicitly gives quasi-compactness and separatedness on scheme tests. These are exactly the extra two conditions for finite presentation; no finite-type assumption on X is inserted.

Step 3 uses the quasi-compact-surjection node with X as the quasi-compact source and Y as a discrete algebraic stack; it places no finiteness condition on the surjection. For the absolute diagonal I recomputed the cartesian test: pullback along q times q is X times_Y X -> X times_Z X, not the diagonal of X. The source is X times_S G by the given relation. The affine-spectrum fibre-product node explicitly identifies the products with spectra of tensor rings over R and Z. The covering-calculus node makes q times q an fppf cover via two base changes; the four-property node descends affineness of this diagonal. Affine permanence then gives precisely its required quasi-compactness. Thus Y is absolutely quasi-separated even if R and X are non-Noetherian.

Step 4 applies only the new torsor algebra-invariants statement, whose hypotheses are supplied by Step 2 and the original relation. I checked its statement explicitly supplies the equivariant surjection, the section-to-invariant isomorphism and compatibility with powers. The item assumption applies to arbitrary commutative R-algebras E_B and E_C, using R'=R, without requiring them to be finitely generated as R-algebras or as A-algebras. The lifted invariant descends by that same isomorphism. No exactness of invariants is asserted.

Step 5 applies the new global power-lifting criterion only after Step 3 has checked both compactness conditions. Its statement is precisely the general algebraic-space criterion needed and is independent of torsors. The spectrum description then regards the represented affine scheme as affine over Spec R. The q assertion has already been proved independently in Step 2.

I checked all source-tag pairs locally in tags/tags. Every cited node's statement was opened and read, including the two new ones; citations.json records verbatim parts (the full statements) so each use is independently visible. No step uses a node's proof. The three off-unit citations are generic scheme tools (coproduct existence, affine fibre-product coordinates, affine permanence), individually declared in split_report.tool_uses; they do not replace the unit route. All other statement tools are in the item unit.

Edge cases: the empty affine X gives empty Y by local sections and the relation, so no nonemptiness is needed. For trivial G the relation identifies the quotient with X, compatible with the criterion. R=0 gives the empty base. Arbitrary nonreduced rings and infinite-type X are permitted by all quantifiers. For finite groups in positive characteristic the power exponent may exceed one, so the proof never replaces adequate lifting by invariant exactness. A nonreductive group such as G_a can have nonaffine free quotients, but does not satisfy the assumed all-algebra invariant power-lifting property; the argument isolates that hypothesis in Step 4.

Against B-E: new statements introduce their own objects and inline algebra/sheaf notions, cite the actual definitions they use and contain no proof. No elementary fact became a node. No clause was moved wholesale to a node. No SGA source, compiler, Lean write, direct git command, or write outside this sandbox was used. Each non-elementary step has a cited statement for its substantive input. All step lengths are below 2000 characters, so none hides an unreviewed long-step lemma. No conclusion is claimed merely from pointwise containment, no arbitrary-algebra quantifier is restricted, and the absolute diagonal's base was checked explicitly.

## Not duplicates

lem-sfb-affine-torsor-algebra-invariants vs lem-trf-polarized-scheme-etale-descent: The existing statement concerns Effective etale descent for polarized schemes; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-trf-ample-scheme-test-line-preparation: The existing statement concerns Line-module preparation on an arbitrary scheme test of a locally polarized space; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-trf-algebraic-space-invertible-descent: The existing statement concerns Etale descent of line modules on an algebraic space; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-trf-scheme-descent-quotient-chart-isomorphism: The existing statement concerns Recovering each base chart from an etale descent quotient; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-trf-scheme-descent-cocycle-etale-relation: The existing statement concerns A scheme descent cocycle gives an etale equivalence relation; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-trf-polarized-fine-log-etale-descent: The existing statement concerns Effective etale descent of fine log schemes with a compatible polarization; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-trf-etale-scheme-line-morphism-gluing: The existing statement concerns Etale gluing of morphisms of schemes with line modules; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-space-coherent-fppf-stack: The existing statement concerns Fppf descent of flat finitely presented proper-support families; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-space-fppf-qcoh-descent: The existing statement gives effectiveness/full faithfulness for module descent data on a general fppf covering; it does not state the coaction identification, invariant global sections or the induced equivariant algebra surjection on an affine group torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-fppf-face-heart-descent: The existing statement concerns Effective quasi-coherent module descent with face maps; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-space-relative-proj-graded-twists: The existing statement concerns Canonical graded twisting algebra on relative Proj of an algebraic space; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-regular-space-divisor-line-dictionary: The existing statement concerns Divisors and rationally trivialized lines on a regular algebraic space; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-relative-degree-gminusone-theta: The existing statement concerns The degree-g-minus-one Picard torsor and its determinant theta divisor; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-rigidified-space-picard: The existing statement concerns Rigidified Picard representability for proper geometrically integral algebraic-space families; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-space-connective-perfect-sections-affine: The existing statement concerns Sections of a universally nonnegative perfect complex form an affine space of finite presentation; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sbc-affine-section-associated-stalk: The existing statement concerns Unequal affine module sections are detected at an associated stalk; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sbc-affine-module-germ-localization: The existing statement concerns Quasi-coherent affine module germs are localization maps; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs new-affine-dual-restriction-comparison: The existing statement concerns Restriction of an affine dual is the sheaf dual; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs prop-nagata-relative-proj-functoriality: The existing statement concerns Restriction, base change, and functoriality of Proj; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-a1-finite-locally-free-polynomial-basis-charts: The existing statement concerns Polynomial base change and constant polynomial bases of a finite locally free algebra; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-trf-affine-pushforward-quasi-coherent-quotient: The existing statement concerns Affine pushforward preserves quasi-coherent quotients canonically; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-trf-coherent-finite-support-skyscrapers: The existing statement concerns Finite-support coherent modules decompose into finite-length skyscrapers; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-trf-relative-differential-sheaf-base-change: The existing statement concerns Relative differential sheaves: finite type and canonical cartesian base change; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-trf-iterated-transform-structure-algebra: The existing statement concerns Structure algebra of an iterated scheme strict transform; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-trf-qcqs-line-section-algebra-evaluation: The existing statement concerns QCQS line section algebra, coproduct comparison and affine evaluation charts; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-trf-supported-quotient-saturation: The existing statement concerns Saturation and quasi-coherence of the supported-section quotient; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-trf-supported-kernel-blowup-charts: The existing statement concerns Supported-section kernels on affine blowup base-change charts; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-trf-positive-copy-graded-quotient: The existing statement concerns Quasi-coherent positive-copy graded algebra and symmetric quotient; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-trf-log-ideal-algebraization-descent: The existing statement concerns Algebraization and etale descent of a coherent log ideal; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-trf-principal-support-quotient-exact: The existing statement concerns Principal supported-section quotients of powerwise injective sequences; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-trf-fitting-ideal-generate-locally: The existing statement concerns Fitting subscheme complement is the bounded-generator locus; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-trf-pointed-devissage-affine-translation: The existing statement concerns Affine sections turn a scheme devissage chain into an algebra devissage; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-trf-strict-transform-affine-pushforward: The existing statement concerns Strict transform commutes with affine pushforward; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-trf-universal-exact-affine-power-reduction: The existing statement concerns Affine base-change charts detect divisibility modulo every power; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-trf-valuation-specialization-stalk-model: The existing statement concerns Local stalk model at a valuation special-fibre component generic point; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-pc-finite-retract-sheaves-affine-trivialization: The existing statement concerns Simultaneous affine trivialization of finitely many finite free sheaf retracts; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sc-mixed-affine-sections-underived-chart-model: The existing statement concerns Ordinary affine chart extension and sections comparison with its unit equation; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-pc-affine-isomorphic-source-normalized-models: The existing statement concerns Normalized affine pullback models from an isomorphic source chart; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-pc-affine-perfect-flat-model-replacement: The existing statement concerns Affine perfect replacement with a quasi-isomorphism; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-pc-affine-tensor-pullback-homology-comparison: The existing statement concerns Affine tensor pullback comparison of homology; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs new-pc-single-retract-sheaf-affine-trivialization: The existing statement concerns Affine trivialization of one finite free sheaf retract; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-pc-affine-sheaf-resolution-from-ring-model: The existing statement concerns Sheafifying an actual finite-free affine ring resolution; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-pc-affine-sections-complex-counit: The existing statement concerns Affine quasi-coherent complex reconstructed from ordinary sections; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-pc-proper-cohomology-finite-free-resolution: The existing statement concerns Actual affine finite-free resolution of a quasi-coherent complex; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sc-affine-finite-module-free-locus: The existing statement concerns Finite modules free at all primes are locally free on an affine cover; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-pc-affine-universal-tensor-exact: The existing statement concerns Square-zero affine base-change tests detect module tensor exactness; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-pc-affine-opcycles-flat-from-sections: The existing statement concerns Transfer flat global-sections opcycles to affine sheaf opcycles; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sc-coherent-affine-free-resolution: The existing statement concerns Finite free resolution of a coherent sheaf on a Noetherian affine neighbourhood; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-pc-self-tor-ambient-resolution-charts: The existing statement concerns Affine self-Tor comparison before tensor pullback; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-pc-affine-projective-sections-sheafification: The existing statement concerns Sheafification of a finite-projective affine section comparison; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-pc-affine-perfect-sections-projective-model: The existing statement concerns Bounded finite-projective model of ordinary affine sections; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-pc-strictly-perfect-finite-free-refinement: The existing statement concerns Finite free refinement of a strictly perfect local representative; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-pc-affine-universally-exact-opcycles-flat: The existing statement concerns Flat degree-zero opcycles from universal degree-minus-one vanishing on an affine scheme; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-pc-affine-tensor-pullback-complex-comparison: The existing statement concerns Affine tensor pullback comparison of complexes; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-affine-invertible-finite-set-section: The existing statement concerns A section of an invertible sheaf avoids any finite set on an affine scheme; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-qcoh-grothendieck-generators: The existing statement concerns Grothendieck generators for quasi-coherent sheaves on an arbitrary scheme; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-koszul-closed-immersion-affine-criterion: The existing statement concerns Affine and principal neighbourhood criterion for a Koszul-regular closed immersion; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-affine-lci-conormal-splitting: The existing statement concerns Affine splitting of the lci conormal transitivity sequence; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-qcoh-bounded-submodule-union: The existing statement concerns Uniformly bounded-generated quasi-coherent subsheaves exhaust every quasi-coherent sheaf; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-polynomial-quotient-proj-presentation: The existing statement concerns Projective presentation and affine coordinate charts of a homogeneous polynomial quotient; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-graded-fibre-hilbert-functions-finite: The existing statement concerns Finitely many fibre Hilbert functions of a finite graded module; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-affine-action-quasicoherent-descent: The existing statement concerns Quasi-coherent algebra descent on affine action quotients; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-finite-pinching-invertible-patching: The existing statement concerns Invertible sheaves on a finite pinching square; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-flat-affine-action-algebra-descent: The existing statement concerns Quasi-coherent algebras and invariant sections on a flat affine action quotient; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-equivariant-coherent-tor-calculus: The existing statement concerns Equivariant coherent Tor sheaves and their exact-sequence calculus; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-affine-derived-coherator: The existing statement concerns The affine derived coherator has invertible comparison unit and counit; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-space-affine-module-correspondence: The existing statement concerns Affine module correspondence on algebraic spaces; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-zariski-square-zero-scheme-realization: The existing statement concerns Zariski square-zero ring-sheaf extensions with quasi-coherent kernel are schemes; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-maximal-point-blowup-generated-cohomology: The existing statement concerns Globally generated sheaves on a regular surface point blowup have no H1; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-proj-scalar-extension-twist-comparison: The existing statement concerns Scalar extension compares all Proj twists with their normalized fraction maps; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-bounded-generators-fitting-pullback-criterion: The existing statement concerns Bounded generators and the Fitting relation ideal under arbitrary pullback; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-relative-flat-tensor-charts-sheaf-exact: The existing statement concerns Relative-flat tensor chart criterion for sheaf short exactness; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-affine-space-invertible-trivial: The existing statement concerns Invertible sheaves on affine space over a field are trivial; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-flat-integral-free-surjection-iso-locus: The existing statement concerns Closed universal isomorphism locus for a finite-free quotient on a flat integral-fibre family; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sc-affine-regular-stalk-scalar: The existing statement concerns Scalar endomorphisms act on the affine unit germ by their germs; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs new-picard-residue-homology-comparison-source-residue: The existing statement concerns picard_residue_homology_source_residue_comparison; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sc-picard-residue-homology-chosen-geometric-maps: The existing statement concerns Chosen chain maps and one common geometric residue comparison; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sc-affine-chart-scalar-transport: The existing statement concerns Affine chart and slice scalar transport; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs new-affine-perfect-sections-counit: The existing statement concerns Natural section reconstruction counit on affine perfect complexes; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs new-picard-residue-source-model-homology: The existing statement concerns picard_residue_source_model_homology; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sc-affine-regular-stalk-comparison-bijective: The existing statement concerns The regular affine unit germ generates its ambient stalk freely; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sc-affine-free-sheaf-stalk-realization: The existing statement concerns Natural finite-coordinate stalk comparison for affine sheafification; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sc-affine-free-stalk-comparison-bijective: The existing statement concerns Bijectivity of finite coordinate combinations of affine basis germs; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sc-affine-principal-model-comparison: The existing statement concerns Exact associated-sheaf comparison on a principal affine neighbourhood; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sc-affine-free-residue-sections-derived-model: The existing statement concerns Derived residue model from an affine free section complex; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sc-picard-ordinary-raw-coordinates: The existing statement concerns Raw degree-zero and degree-one scalar coordinates and residue naturality; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs def-sc-affine-free-basis-germs: The existing statement concerns Explicit affine basis germs and their linear combination map; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sc-affine-free-basis-germ-map: The existing statement concerns Matrix action on the explicit finite free basis germs; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs new-picard-derived-fibre-residue-bridge-core: The existing statement concerns Fixed-model residue naturality core; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs new-picard-derived-fibre-residue-bridge: The existing statement concerns Common affine residue model bridge for derived fibre naturality; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs new-picard-derived-fibre-residue-model-data: The existing statement concerns Simultaneous affine strictly-perfect residue model data; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sc-tilde-scalar-section-action: The existing statement concerns Associated sheaf scalar action on all sections; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs new-picard-residue-quotient-model-homology: The existing statement concerns picard_residue_quotient_model_homology; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sc-affine-scalar-section-action: The existing statement concerns Affine scalar endomorphism action on sections over its chart; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs new-affine-residue-model-naturality: The existing statement concerns Naturality of all represented affine residue arrows; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs new-affine-perfect-residue-model-naturality: The existing statement concerns Natural derived residue model on the full perfect subcategory; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs new-affine-residue-evaluation-homology-naturality: The existing statement concerns Natural residue homology comparison with evaluation scalars; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sc-affine-free-terminal-sections-reconstruction: The existing statement concerns Finite free slice complex reconstructed from terminal sections; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-weil-pbc-affine-global-formal-comparison: The existing statement concerns Affine formal equivalence with quotient-system and section-limit natural comparisons; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-weil-pbc-affine-map-annihilation-sheafification: The existing statement concerns Transfer a uniform annihilator bound through affine sheafification; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-weil-pbc-coherent-formal-modules-affine-reconstruction: The existing statement concerns Affine formal modules: Reconstruction; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-weil-pbc-quasi-coherent-finite-type-affine: The existing statement concerns Modules of finite presentation are quasi-coherent; a quasi-coherent module is of finite type (finite presentation) on an affine open iff its sections there are a finite (finitely presented) module (Stacks 01BO, 01PB, 01PC); it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-weil-pbc-quasi-coherent-iso-on-affine-cover: The existing statement concerns A map of quasi-coherent modules bijective on an affine open cover is an isomorphism; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-weil-pbc-affine-intersection-quotients-stalk: The existing statement concerns Localization of affine quotient systems with a prescribed kernel filtration; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-weil-pbc-quasi-coherent-module-cokernel-image: The existing statement concerns Cokernel and image of a morphism of quasi-coherent modules: quasi-coherent, computed on affine opens; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-weil-pbc-quasi-coherent-affine-section-base-change: The existing statement concerns Sections of a quasi-coherent module on nested affine opens satisfy tensor base change; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-weil-pbc-affine-coherent-tilde-presentation: The existing statement concerns Associated-module presentation of a coherent sheaf on an affine scheme; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-weil-pbc-formal-kernel-affine-stalk-filtration: The existing statement concerns Affine exact intersection-filtration models of stabilized kernel stalks; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-weil-pbc-formal-affine-morphism-realization: The existing statement concerns Affine formal morphism realization; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-weil-pbc-finite-type-subalgebra-multiplication-image: The existing statement concerns Multiplication image of two finite type quasi-coherent algebra subsheaves; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-weil-pbc-completion-affine-sections-coordinates: The existing statement concerns Affine coordinates for coherent completion quotient sections; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-weil-pbc-affine-tilde-gamma-adjunction: The existing statement concerns On Spec R, M ↦ M~ is left adjoint to global sections, fully faithful, and an equivalence onto quasi-coherent modules; it preserves colimits; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-weil-pbc-affine-section-linear-map-extension: The existing statement concerns Extending an affine linear section map from a quasi-coherent source; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-pur-affine-punctured-line-algebra: The existing statement concerns Units and Picard groups of the line and the punctured line; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-fin-spread-finite-algebra: The existing statement concerns Spreading a finite algebra from the generic fibre; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sc-affine-cap-section-open-dictionary: The existing statement concerns Affine dictionary for an invertible module and its section; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-affine-torsor-algebra-invariants vs lem-sc-affine-cap-section-open: The existing statement concerns Intersecting an affine open with a line-bundle nonvanishing locus is affine; it does not supply the coaction of an arbitrary flat affine group over R on every pulled-back algebra, together with invariant sections and equivariant surjections for its affine torsor.

lem-sfb-space-power-lifting-affineness vs lem-sfb-space-serre-affineness: The existing criterion assumes H^1 vanishes on every quasi-coherent module; the new criterion assumes power lifting along all commutative algebra surjections, with no claim of module exactness.

lem-sfb-space-power-lifting-affineness vs lem-sfb-affine-target-adequacy-criterion: The existing statement is over a field and identifies global power lifting with adequate affineness of a stack map; it does not assert that an arbitrary-base algebraic space is an affine scheme.

lem-sfb-space-power-lifting-affineness vs lem-sfb-power-reductive-free-affine-quotient: The item concerns group actions, a torsor relation and invariant power lifting; the new statement is an intrinsic criterion for any qcqs algebraic space and contains none of those action hypotheses or the morphism q conclusion.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-space-groupoid-module-descent: The existing statement is an equivalence of module categories for a stackified groupoid, without affine coordinates, coactions, invariant-section identifications or surjective algebra maps.

lem-sfb-affine-torsor-algebra-invariants vs lem-sfb-linearized-qcoherent-cohomology-coaction: That statement is over a field, for separated schemes and cohomology of linearized modules; it does not give descent of arbitrary-base torsor algebra invariants.

## Unfinished work

No part of this one-level split remains unfinished. Both new non-Mathlib statements are deliberately unsplit, for future workers. Server dry run and push results are recorded below when complete.
