# Stage-1 re-split: lem-pur-system-primitive-comparison-shift

1. Files written: the item node, retaining its statement and statement dependencies verbatim; two new statement-only nodes below.
   - lem-pur-diagram-pullback-monoidal-shift-models: statement, unsplit; no Mathlib match.
   - lem-pur-diagram-open-clopen-shift-models: statement, unsplit; no Mathlib match.
2. Attachments: none. The project declaration at lean/Sheaf/SixFunctors/SystemPrimitiveComparisonShift.lean:220 contains sorry. The required project-source tag/notion search under WeilConjectures found no exact completed declaration.
3. WANTED: none.
4. The released 2026-10-22 stage-1 repair note expressly requires spreading this already-reviewed proof across at least two new nodes, keeping the statement and the old route. This supersedes the ordinary prohibition on extracting clauses merely to relabel a completed proof. The new nodes have independent chain/section-model content and are not the whole item. No statement dispute or change is needed.
5. Nothing remains in this worker's authorized stage-1 split; the two new nodes deliberately remain unsplit. No Lean was written or compiled.

## Review by Q128

I read GOAL.md, the stage-1 brief, the worker role, the three blueprint levels in SETUP, delivery-errors B-E in both copies, the chapter/unit records, and the released keep_plan repair note. I read the actual maps-used sentence in main-20261015/fix-prop-coherence.proof.md: it specifies primitive maps, not this shift theorem. Hence the proof remains agent-origin. For the first new node I read Stacks more-algebra.tex, section-sign-rules (0FNG), in particular shift differential, shifted tensor, unsigned reassociation and signed flip, and sites-cohomology.tex lemma-symmetric-monoidal-derived (0FPT). For the second I read the open normalization node's full statement, sites-modules.tex lemma-j-shriek-and-tensor (0E8I), sites-cohomology.tex lemma-j-shriek-and-tensor (0GL1), and the exact project theorem's proof docstring. None is represented as already proving the new model obligations.

I opened all five statements cited by the original item: simultaneous realization, basic-operation shifts, shifted tensor calculus, open normalization, and semilinear proper/open mate pasting. I also opened the general semilinear-derived-sections, exact-pullback-signed-comparison, derived-tensor-additive-constraints, resolving-tensor-signed-coherence, cochain-pullback-tensor-coherence, slice-tensor-integer-shift, total-tensor-integer-shift, module-derived-functor-compositor-shifts, system-clopen-tensor-compatibility and normalized-tensor-constraint-transport statements. They are used only for the operations and normalizations they actually state. In particular the realization/basic-operation nodes have constructibility/normalization bounds for integral realization; I do not infer an arbitrary-system integral realization from them. The new obligations concern ordinary derived categories of whole systems and impose no such extra hypothesis on the item.

Assembly step 1 uses the first new statement: its ordinary degree-p pullback formula covers compositors and equal scheme composites, its bidegree-preserving tensor formula covers the tensor/pullback comparison, and its ternary sign and symmetry equations cover the tensor constraints. I checked all three associator slots and both action unitors. The triple exponents bp+c(p+q) and cq+(b+c)p are equal. In the two-variable symmetry exponents the difference is 2bp, and for a single shifted occurrence a*b=0. Thus no unrequested sign is inserted in the item's single-slot square. The termwise/K-flat normalization is fixed, rather than chosen afterward to force commutation.

Assembly step 2 uses the second new statement: it includes the normalized open compositor and restriction map, the correct base-change substitution g=b, j=k, j'=s, g_U=id, and the product decomposition for clopen s. I checked that k=b composed with s (not the reverse), and that pi has source identity on V' and target J_s P_s. The clopen direct image is exact, so its localization-to-right-derived comparison uses the same K-injective shift as the mate of inverse image. The statement explicitly makes that identification an obligation; it is not inferred from mere finite-level evaluations. I removed the misleading literal claim that arbitrary sections of extension by zero are always either identity or zero: the source's identity/zero description is a restriction/component description, with extension transitivity globally.

Assembly step 3 uses both new statements' intrinsic derived identities, naturality and shift-addition clauses. Composition is an elementary substitution of the two shift equations; no faithfulness of evaluation or scalar restriction is invoked. citations.json gives a literal sentence/formula from every new statement cited by each assembly step. Every non-elementary assertion in assembly is covered by those statements. No proof step exceeds 2000 characters. The old step-7 exclusion of extra transformations is preserved in the item's unchanged statement; the assembly proves only the enumerated primitives.

Small cases checked: shifts r=0 and negative r, both-shift parity a=b=1, unit concentrated in degree 0, zero complexes, zero coefficient rings, n=1 for the quotient tower, identity compositors, empty opens and identity open immersions. For clopen decomposition the empty component is the zero category and the projection is zero; for an isomorphism the complementary component is zero and the projection is identity. No coefficient-transition flatness, compactification choice, etale-origin witness or evaluation detection of morphism equality enters the model statements.

All Mathlib queries were executed by msearch.py, with hits read and alternative phrasings tried. ExactFunctor supplies functor/factorization shift structures, PullbackContinuous supplies an abelian pullback compositor, and TotalComplexShift/BifunctorShift supply total-shift formulas; none supplies all specified chain representatives, canonical-system identifications and open/clopen normalization in either new node by one specialization. Loogle's attempted qualified MonoidalCategory.associator query returned an unknown identifier, recorded honestly; I corrected it to HomologicalComplex.associator and read its result. Generic NatTrans.CommShift.associator concerns composition of functors, not tensor reassociation.

## Not duplicates

lem-pur-diagram-pullback-monoidal-shift-models vs lem-pur-exact-pullback-signed-comparison: covers exact single-pullback tensor comparison, not the simultaneous compositor/equal-composite representatives and all tensor-constraint shift squares on ring diagrams.

lem-pur-diagram-pullback-monoidal-shift-models vs lem-pur-resolving-tensor-signed-coherence: compares a pullback tensor map with constraints; it does not state the tensor constraints themselves commute with slot shifts or give the inverse-image compositor shift formula.

lem-pur-diagram-pullback-monoidal-shift-models vs lem-pur-derived-tensor-additive-constraints: constructs normalized tensor constraints and detects equality on resolutions; it does not assert their shift squares or pullback-compositor compatibility.

lem-pur-diagram-pullback-monoidal-shift-models vs lem-pur-shifted-tensor-morphism-calculus: states B(f,g) identities from degree-zero flat source sheaves; the new obligation gives canonical primitive representatives and all derived input-slot squares.

lem-pur-diagram-pullback-monoidal-shift-models vs lem-weil-pbc-total-tensor-integer-shifts: only generic total-bifunctor shifts and their interchange; lacks tensor-constraint and ringed-diagram pullback comparisons.

lem-pur-diagram-pullback-monoidal-shift-models vs lem-weil-pbc-slice-tensor-integer-shift-compatibility: only restriction to a localized slice and its tensor comparison; lacks arbitrary scheme pullback compositors and tensor associator/unitor/symmetry slot squares.

lem-pur-diagram-pullback-monoidal-shift-models vs lem-sfb-module-derived-functor-compositor-shifts: uses condensed module objects; not ordinary modules over a varying inverse ring diagram and does not state monoidal constraint squares.

lem-pur-diagram-pullback-monoidal-shift-models vs lem-pur-cochain-pullback-tensor-coherence: cochain pullback/tensor construction and scalar coherence, not the specified derived integer-shift squares.

lem-pur-diagram-pullback-monoidal-shift-models vs lem-pur-normalized-tensor-constraint-transport: realization by reduction/total limit on normalized systems; lacks shift squares and does not address arbitrary systems.

lem-pur-diagram-open-clopen-shift-models vs lem-sf-open-tensor-normalization: defines the normalized maps, but states no shift compatibility or clopen derived direct-image comparison.

lem-pur-diagram-open-clopen-shift-models vs lem-pur-open-adjunction-shift: only unit/counit of open adjunction; not extension composition, normalized restriction or clopen direct-image/component maps.

lem-pur-diagram-open-clopen-shift-models vs lem-sf-semilinear-proper-open-mate-pasting: defines clopen component maps within proper/open squares and proves mate pasting, not their simultaneous shift representatives.

lem-pur-diagram-open-clopen-shift-models vs lem-pur-system-clopen-tensor-compatibility: tensor projection/proper-open compatibility, not cochain shifts of clopen comparisons or projections.

lem-pur-diagram-open-clopen-shift-models vs lem-sf-canonical-open-restriction-model: coefficient reduction/total-limit adjunction mate, not P_b J_k identification or clopen shift squares.

lem-pur-diagram-open-clopen-shift-models vs lem-sf-open-semilinear-tensor-model: open extension commutes with coherent reduction through tensor models, not the specified primitive open/clopen shifts.

The new nodes carry no Stacks tags in their source field: that source records the same agent-formulated blueprint place as the item, rather than falsely attributing a system shift theorem to a Stacks tag. The source tags actually inspected are documented above. Whole-DAG keyword and tag searches and whole-blueprint searches for shift, shift comparison, associator, clopen, extension by zero and pullback compositor found no node giving either full model statement. Neither new node cites the item, so the dependency orientation remains downward.

## Preservation of the original argument

The following paragraphs retain the original item proof verbatim as takeover material. They are not proof steps in the new unsplit nodes. Steps 1-3 become obligations in the first node's statement, steps 4-6 in the second; step 7 is distributed between their intrinsic-equality conclusions and the final elementary assembly. This record prevents the mandated shorter assembly from discarding the old proof's calculations.

### Original step 1

Work on the simultaneous ringed-diagram sites supplied by [lem-sf-integral-compactification-system-realization]. There the system operations are termwise inverse image, K-injective direct image, exact open extension and K-flat tensor, and their canonical pullback composition maps and tensor/pullback maps are induced by degree-zero maps of the corresponding resolutions. The shift comparison for each operation, including the signed tensor comparison, is the one in [lem-pur-integral-basic-operation-shift]. Reindexing a resolution and multiplying its differential by the usual shift sign commutes with every degree-zero component map and with the quotient transition maps. Hence the shift square holds for every canonical pullback compositor and for every square identification obtained by equality of scheme composites, in each input slot; the same argument gives naturality in the input morphisms and the cocycle for adding two shifts.

### Original step 2

For the pullback/tensor comparison, choose K-flat system resolutions. The comparison sends a pure tensor in degrees (p,q) to the tensor of the two pulled-back pure tensors, so it preserves (p,q). The shifted tensor comparison multiplies this component by (-1)^(b p), exactly on both routes; the signed formula and its naturality are the statement of [lem-pur-shifted-tensor-morphism-calculus]. Therefore the pullback/tensor square commutes for arbitrary integers and either shifted input. The realization node identifies this ringed-diagram comparison with the canonical system comparison before evaluation.

### Original step 3

The tensor associator and unitors are the degree-zero rebracketing and insertion/removal of the unit on total K-flat complexes, so they commute with reindexing and with the shift differential signs. For the symmetry, on a shifted bidegree (p,q) the two composites have exponents b p + (p+a)(q+b) and a b + p q + a q; their difference is 2 b p. Thus the Koszul symmetry square is the required equality, including the graded factor (-1)^(a b). These are precisely the associativity and symmetry identities for the signed comparison t in [lem-pur-shifted-tensor-morphism-calculus], and descent there transfers the calculation to the derived system category.

### Original step 4

For composable open immersions, termwise extension by zero is exact and its composition map is the identity on sections over the composite open and zero elsewhere. The shift functor only reindexes the same termwise sections and changes the differential sign, so this composition map is unchanged and its shift square is immediate. The normalized open extension and tensor maps on the system ringed topoi are the maps of [lem-sf-open-tensor-normalization], while [lem-pur-integral-basic-operation-shift] supplies their operation shifts; therefore the assertion holds before evaluation and is coherent under iterated composition.

### Original step 5

Let b:V_W to V and s:U to V_W be the open immersions with k=b s. On the ringed diagram sites the canonical identification P_b J_k to J_s is the open-base-change map normalized by the open unit: after restriction to the open it is the identity on sections. Its components are degree-zero maps of termwise complexes, and its inverse is the open-adjunction adjunct described in [lem-sf-open-tensor-normalization]. Reindexing therefore gives the same map after any shift in either input. The system realization in [lem-sf-integral-compactification-system-realization] identifies this normalized map with the intrinsic system transformation, so the square is an equality of system maps before evaluation.

### Original step 6

If s is also closed, the clopen decomposition makes J_s the component functor and S_s the same componentwise direct image. The comparison J_s to S_s is therefore the identity on the s(U) component and zero on the complementary component, and the projection pi_s is exactly the map (x,y) maps to (x,0). Shifts preserve each component, the identity map and the zero map, so both the clopen comparison and pi_s commute with every shift. The proper/open mate-pasting node states these maps and their normalization as semilinear-system transformations before evaluation, and the realization node identifies them with the canonical system maps. This also proves naturality and compatibility with adding shifts.

### Original step 7

All preceding calculations are componentwise on the same simultaneous models, hence they remain equalities of semilinear-system transformations rather than equalities inferred from finite evaluations or scalar restriction. Whiskering by any of the listed operations and composing the displayed squares preserves the shift equations. No step introduces an integral realization comparison, an arbitrary expression-tree comparison, a proper/open mate, or an exchange/projection transformation beyond the explicitly listed primitive maps.

