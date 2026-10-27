# Stage-1 delivery: lem-per-geometric-affinoid-jacobian-unit

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-geometric-affinoid-jacobian-unit.json: item, split into six steps; statement preserved, no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-affinoid-residual-conormal-injective.json: one new statement-only analytic lemma, unsplit; not in Mathlib. Its conclusion concerns the residue conormal vector space, not the colon-minor ideal.
- citations.json: nine step/node entries, each quoting the cited statement verbatim. Searches actually executed are retained in searches.jsonl.

## Attachments

None. Searched the project source under lean/WeilConjectures for the exact blueprint tag and the notions affinoid, TateAlgebra and continuous Jacobian. Read Algebra.exists_jacobian_unit_presentation_of_regularAtMaximal in AlgebraicGeometry/RegularMaximalJacobianPresentation.lean:52 and its use in SmoothAtMaximalIdeal.lean. This is a polynomial presentation of a finite type algebra over an algebraically closed field, not the assigned fixed Tate presentation, and hence is not an attachment.

## Literature wanted

WANTED: Michael Temkin, Desingularization of quasi-excellent schemes in characteristic zero, Proposition 3.3.2 and proof, printed pp.20--21, https://math.huji.ac.il/~temkin/papers/Excellent_Desingularization.pdf, for the item and lem-per-affinoid-residual-conormal-injective. Read online; no local archival copy was found.

WANTED: Bosch--Luetkebohmert--Raynaud, Formal and rigid geometry III: The relative maximum principle, section 1 and criteria 2.5, 2.8, for lem-per-affinoid-residual-conormal-injective. These are the continuous-conormal and analytic smoothness criteria Temkin cites; not claimed read in the original. The node's proof is deliberately left open.

WANTED: Brian Conrad, Irreducible components of rigid spaces, Ann. Inst. Fourier 49 (1999), pp.473--541, section 3.3, especially pp.509--512, https://www.numdam.org/article/AIF_1999__49_2_473_0.pdf, for the general complete-field geometric-regularity interpretation in lem-per-affinoid-residual-conormal-injective. Read online; no local archival copy found.

The assembly proof is marked agent-written. Neither analytic paper is silently treated as an archived source, and the algebraic criterion from Stacks is not substituted for an analytic theorem.

## Corrections and provenance

The item had an empty proof. Its statement is mathematically consistent and is unchanged: arbitrary characteristic, nontrivial real-valued valuation, all complete isometric extensions, all cardinalities of minors, and the zero quotient remain included. No STATEMENT-DISPUTED correction was required.

There is a source-scope qualification: the setup of Temkin Proposition 3.3.2 is discretely valued and starts with a formal model. It does not verbatim state the item's general-valued hypothesis. The analytic residue-fibre input is therefore explicitly a new agent-formulated statement, supported by Temkin's continuous-conormal argument and Conrad's discussion of general complete fields. It is not a claimed one-line specialization of the formal-model proposition. The subsequent argument uses only finite generators and local algebra, and works for exactly the original generality once that new input is supplied.

The newest blueprint, literature/blueprint/latest (snapshot main-20261024), has been read for lem-per-artin-gabber-affine-curve and the unit sk-p-dl-a1-perverse. The inherited branch passes through lem-per-regular-generic-continuous-jacobian and formal algebraization below ancestor Step 3. The newest ancestor has no separate algebraization sentence. This delivery retains the assigned inherited branch; it changes no chapter or unit route or target. The blueprint fields retain that qualification, give the actual place served, and record no synonymous imported node.

## Not duplicates

lem-per-affinoid-residual-conormal-injective vs lem-per-geometric-affinoid-jacobian-unit: the new lemma concerns injectivity of the continuous conormal map on a single residue fibre and does not mention minors or colon ideals. The item proves the independent-equation selection, the localized ideal generation, the global colon element, the nonzero minor, and the unit-ideal argument.

lem-per-affinoid-residual-conormal-injective vs lem-per-regular-affinoid-complete-field-extension: the latter deduces regularity after complete field extension from regularity in characteristic zero over a discretely valued field. The new lemma assumes regularity after all such extensions, permits arbitrary characteristic and valuation, and concludes a differential-fibre injection.

lem-per-affinoid-residual-conormal-injective vs lem-per-regular-generic-continuous-jacobian: that node concerns a power-of-t splitting over the original adic quotient and already depends on this item. The new node concerns a Tate quotient's residue fibre, has no power-of-t splitting conclusion, and does not depend on the item or its parents.

lem-per-affinoid-residual-conormal-injective vs lem-per-completed-jacobian-homology-comparison: the latter compares homology under Noetherian adic completion of a finite type algebra; it does not prove residue injectivity for a Tate quotient from analytic geometric regularity.

DAG searches covered affinoid, Tate algebra, continuous Jacobian, conormal residue/fibre, and the cited analytic sources. Whole-blueprint searches with tools/blueprint_refs.py covered affinoid, Jacobian, continuous differential, geometrically regular, conormal and residual conormal; no imported statement supplies the analytic input. Existing elementary/local-algebra facts were reused rather than recreated. There is no Stacks tag in the new node's source requiring a tag-duplicate pair.

## Mathlib searches

Ran msearch.py for the item and for the proposed residue-conormal statement, including LeanFinder, Loogle, grep and LeanSearch, with alternate formulations. Read the hits. Mathlib has Algebra.FormallySmooth.iff_split_injection (RingTheory/Smooth/Basic.lean:291) and Algebra.FormallySmooth.iff_injective_lTensor_residueField and iff_injective_cotangentComplexBaseChange_residueField (RingTheory/Smooth/Local.lean:35,47), as well as SubmersivePresentation.cotangentComplex_injective. These concern algebraic differentials and assume algebraic formal smoothness of the presentation ring, with finite algebraic differential module in the local criterion. They do not establish continuous conormal injectivity from regularity under completed valued-field extensions. The global grep for TateAlgebra, RestrictedPowerSeries, affinoid and continuous conormal found no hit. The standard-smooth Jacobian-unit declarations are about polynomial presentations. All searches and their actual returned names are recorded without inventing queries or treating a service failure as absence.

## Review by Q14

I read Temkin Proposition 3.3.2 and the formula immediately preceding it online, including both directions of its proof on printed pp.20--21. The forward direction chooses equations whose conormal classes are independent and generating, obtains local ideal generation by Nakayama, and combines a colon element with a Jacobian minor. That is the argument in this delivery. I also read the discussion of geometric regularity/smoothness in Conrad section 3.3, including the warning that other geometric properties cannot always be tested by finite extensions. The item requires every complete extension, so no such finite-extension reduction is presumed. For the new node I checked that the field, the restricted-series convention, all equations, the coefficient-extended quotients, and the maximal ideal and its residue field are introduced inside its own statement. Its proof and proof_deps are empty as required. It records the source-scope qualification rather than claiming Temkin directly gives the full generality.

Step 1 uses exactly the new node's displayed residue-fibre derivative map and injectivity. Pullback of a maximal ideal through the surjection A to C is maximal because the quotients are the same field. This involves no affinoid Nullstellensatz or assertion about the analytic stalk. The zero ring is removed before choosing a maximal ideal.

Step 2 cites lem-weil-span-independent-subfamily. I opened its complete statement: it selects a linearly independent subfamily spanning the same subspace from any finite family over a field. The classes of the given f_j span by writing an element of I as their finite linear combination. Injectivity from Step 1 makes the corresponding Jacobian columns independent. The lemma does not need an a priori dimension or freeness of I/I^2.

Step 3 cites def-weil-pbc-localization-at-prime, def-weil-pbc-module-localization, and lem-weil-pbc-nakayama-local-generators. I opened each statement: the first states that the localization is local with maximal ideal nR; the second supplies actual fractions and the zero criterion; the third gives generation of a finite module from generation of its residue quotient. The proof writes the residue-quotient isomorphism explicitly, including inverse denominators. The module is finite because I was given the finite generating family f_1,...,f_s; no theorem about Tate-algebra Noetherianity is needed here. I checked the Stacks source for Nakayama, Tag 00DV, algebra.tex label lemma-NAK, especially (4),(8).

Step 4 is elementary fraction algebra citing precisely the zero criterion in def-weil-pbc-module-localization. I checked the denominators for each equation and then multiplied the finitely many annihilating denominators. Every factor is outside the prime maximal ideal n, so their product is also outside. The resulting a lies in the actual ideal quotient (I_E:I), with no assumption that the colon construction commutes with a topology, analytic stalk, or general flat base change. Empty products and E empty are explicitly allowed. This replaces the more involved analytic-stalk/flat-colon argument in Temkin's proof with a direct finite-generator argument after Step 3.

Step 5 cites lem-weil-pbc-field-injective-matrix-nonzero-maximal-minor and def-weil-pbc-matrix-determinant. I read the full statements. The former gives exactly an ordered subset of rows with nonzero full-column determinant for an injective rectangular matrix, including the empty-column case. Our rows are the variable indices and columns are the selected equation indices, matching the item's convention without a hidden transpose. The latter's Leibniz formula verifies reduction modulo n commutes with determinant. I checked its cited local-algebra source in algebra.tex, Tags 00MY/00MW (lemma-exact-depth-zero-local and lemma-trivial-case-exact). This is a generic linear algebra tool filed in another unit; split_report.tool_uses explains the use without setting maintainer-owned tool_uses.

Step 6 cites lem-weil-pbc-proper-ideal-contained-in-maximal. Its statement says precisely that a proper ideal of any commutative ring lies in a maximal ideal; no Noetherianity is assumed. I read Tag 00E0, algebra.tex label lemma-Zariski-topology, items (2),(8), including the proof by the quotient ring. Membership of the product in H is the definition of the sum in the item, and nonvanishing is multiplication in the residue field. Thus avoiding every maximal ideal proves the whole ideal is C, not merely that H is radical or locally nonzero.

Small cases checked: C=0 is immediate; I=0 and s=0 give E empty, a=1 and determinant 1; r=0 has target vector space zero, so injectivity forces the residue conormal space zero and the same Nakayama argument applies; redundant or zero equations need not be selected; no uniform codimension is used. In characteristic p the equation x^p-a over an imperfect field illustrates why plain regularity cannot replace the extension hypothesis: after adjoining a pth root the quotient is nonreduced. Thus the new node does not silently use perfectness. For a smooth hypersurface the map reduces to the usual nonzero gradient on a residue fibre, which gives a one-by-one minor. No proof step is over 2000 characters; all six are below 800 characters.

I checked B1--B10, C1--C8, D1--D5 and E1--E7 against the source and node statements. In particular the new analytic lemma is not presented as an existing algebraic theorem, the local-to-global colon argument stays in the item, and the generic local-algebra tools are existing nodes. The only unfinished mathematics in this one-level split is the deliberately unsplit analytic residue-conormal lemma, whose complete statement and search record are delivered for the next worker.
