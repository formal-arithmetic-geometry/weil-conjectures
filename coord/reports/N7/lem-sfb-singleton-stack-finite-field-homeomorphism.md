# Stage-1 worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-singleton-stack-finite-field-homeomorphism.json: item, split; unchanged statement.
- dag/nodes/sec-six-functors-basics/lem-sfb-noetherian-singleton-gerbe.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-gerbe-smooth-universal-homeomorphism.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-reduced-quasifinite-space-field-decomposition.json: statement, unsplit; no Mathlib match.
- citations.json: verbatim statement excerpts for all seven step/node incidences.

## Attachments

None. Searched the project Lean by the exact blueprint tag, gerbe, residualGerbe and algebraic-stack terminology. There is no finished project declaration stating the item. Scheme-only finite/singleton results do not state the stack assertion.

## WANTED

None.

## Audit findings

The original item has no proof and no Lean audit declaration. Its statement is correct; no STATEMENT-DISPUTED is needed. Its blueprint ancestry has null from.node, as confirmed by blueprint_refs.py ancestor; retained that ancestry and its via list, adding precise supporting places for new nodes. Read the current latest blueprint unit and direct-image proof (3). This singleton result supports the pre-existing alteration/moduli branch recorded by the parent, without changing that route. The item is not the unit's key node, so no unit record changes.

The main subtlety is representability in local finite-type descent: the existing descent node requires BOTH maps to be representable by algebraic spaces. The gerbe map is generally nonrepresentable. Instead its composite with the chosen scheme atlas is smooth and surjective, hence flat and locally finitely presented, and is a map between algebraic spaces. Apply descent to U -> Q -> Spec k. No finite inertia or separation assumption enters. The existing discreteness node's first equivalence has no separatedness/decentness condition: singleton implies discrete directly; its second, separated finite-point clause is not used.

The proof is split into local Noetherianity and the gerbe construction; descent to the base; finite-field identification; and the universal topological conclusion. No new node restates the original finite-field topological-model conclusion. The gerbe construction has only local Noetherianity, no finite-type field assumption and no finite-field conclusion; the gerbe geometry result applies to any gerbe over any algebraic space; the field-space classification has no stack in its hypotheses or conclusion. Each is substantive rather than an elementary combination of the existing DAG statements. All four proof steps are below 2000 characters, and their total is below 3000 characters.

Mathlib searches: every node and the item received two distinct LeanFinder formulations, Loogle, grep and LeanSearch via the required msearch.py wrapper. Actual outputs are retained in search-results.json and searches.jsonl and copied into mathlib_searches. Services returned successfully. Hits are scheme/ring results or abstract stacks on sites; none supplies the algebraic-stack or algebraic-space assertions. In particular AlgebraicGeometry.isFinite_iff_locallyOfFiniteType_of_jacobsonSpace assumes a Scheme and therefore cannot be an attachment or one-line specialization for an arbitrary algebraic space or stack. The complete match decision was made from the displayed types, rather than inferred from keywords. Whole-DAG tag and statement searches, blueprint_refs searches (gerbe, singleton, Artinian, reduced locally quasi, locally quasi-finite), and project Lean searches found no existing node for the three new statements. Existing local-Noetherianity, source descent and field-discreteness statements were reused.

## Not duplicates

lem-sfb-noetherian-singleton-gerbe vs lem-sfb-singleton-stack-finite-field-homeomorphism: the former constructs a gerbe over a singleton space under local Noetherianity; it does not identify that space with a finite field spectrum or assert the universal homeomorphism.
lem-sfb-gerbe-smooth-universal-homeomorphism vs lem-sfb-singleton-stack-finite-field-homeomorphism: arbitrary gerbes over arbitrary spaces are considered; no singleton gerbe is constructed and no field finiteness is proved.
lem-sfb-reduced-quasifinite-space-field-decomposition vs lem-sfb-singleton-stack-finite-field-homeomorphism: classifies reduced locally quasi-finite algebraic spaces, allowing arbitrary coproducts; no algebraic-stack gerbe or universal topological assertion.
lem-sfb-gerbe-smooth-universal-homeomorphism vs lem-sfb-flat-inertia-algebraic-space-quotient: the existing statement constructs an algebraic-space quotient from flat locally finitely presented inertia and asserts smoothness; it does not state the gerbe hypothesis or universal homeomorphism, so cannot supply the topology clause used here.
lem-sfb-gerbe-smooth-universal-homeomorphism vs lem-sfb-universally-closed-stack-rational-point: that node proves an object over a specified algebraically closed field under quasi-compactness and diagonal hypotheses, not the geometry/topology of a given gerbe over a space.
lem-sfb-gerbe-smooth-universal-homeomorphism vs lem-sfb-picard-space-curves-smooth: that node states smoothness of a relative Picard space under proper-curve hypotheses, not a statement about arbitrary gerbe maps.
lem-sfb-gerbe-smooth-universal-homeomorphism vs lem-sfb-adequate-geometric-fibres-submersion: the adequate-moduli hypothesis and geometric closed-orbit equivalence differ from the gerbe condition; universal submersiveness is not a universal homeomorphism.
lem-sfb-noetherian-singleton-gerbe vs lem-sfb-flat-inertia-algebraic-space-quotient: the quotient node assumes flat inertia, which must be proved for a reduced Noetherian singleton stack, and does not state reducedness or singleton topology of the resulting space.
lem-sfb-noetherian-singleton-gerbe vs lem-sfb-universally-closed-stack-rational-point: rational-point existence for universally closed stacks is not the gerbe construction for reduced Noetherian singleton stacks.
lem-sfb-reduced-quasifinite-space-field-decomposition vs lem-sfb-field-groupoid-identity-finite-relation: the existing node concerns a groupoid's arrow space with unramified relation and its identity component; it does not classify arbitrary reduced locally quasi-finite spaces.
lem-sfb-reduced-quasifinite-space-field-decomposition vs lem-sfb-space-field-discreteness-criterion: the existing node supplies discreteness iff local quasi-finiteness, not schemeness or decomposition into field spectra.

lem-sfb-gerbe-smooth-universal-homeomorphism vs lem-sfb-stack-chartwise-smooth-etale-calculus: that statement gives composition and smoothness implications only for representable morphisms; the gerbe map need not be representable, and it gives no universal homeomorphism for gerbes.
lem-sfb-gerbe-smooth-universal-homeomorphism vs lem-sfb-dm-open-finite-etale-permanence: that node treats open substacks and finite etale decorations of smooth finite-type Deligne--Mumford stacks with finite diagonal, not arbitrary gerbes and their universal topology.

## Review by N7

I read stacks-morphisms.tex Tags 06QK (lemma-noetherian-singleton-stack-gerbe), 06QC (definition-gerbe), 06QI (lemma-gerbe-fppf), 06R9 (lemma-gerbe-bijection-points), 06QE (lemma-base-change-gerbe), 0DN8 (lemma-gerbe-smooth), and 075V (lemma-composition-smooth). For the decomposition I read spaces-over-fields.tex Tag 06S0 (lemma-locally-quasi-finite-over-field), all five equivalent clauses and its proof, and decent-spaces.tex Tag 0ACA. I read spaces-descent.tex Tag 06EW for source descent and morphisms.tex Tag 01T6 for local Noetherianity. These are the sources for the item and the new nodes; no SGA source is used.

Step 1 uses exactly the statement of pqf-lem-locnoeth-lft on the given smooth chart U over Spec k; the field's two ideals give the Noetherian base hypothesis. The input already supplies reducedness of U, so the new 06QK node applies to Z over Spec k. Its statement explicitly returns a gerbe over a reduced locally Noetherian singleton space over that same base. I checked that the structural map is over k by choosing the ambient base S=Spec k throughout, rather than identifying an absolute quotient without a structural map.

Step 2 uses the atlas-composite clause of the new gerbe geometry node. I compared that clause with 0DN8, composition of smooth maps, and the smooth-atlas convention: its map U -> Q is surjective, flat and locally finitely presented, and both U and Q are algebraic spaces. I then opened lem-sfb-representable-lft-fppf-source-descent: its stated hypotheses require representability of both maps, and the proof uses it only for U -> Q -> Spec k, where both conditions hold. This corrected the tempting but invalid direct application to p. No quasi-compactness is smuggled into the descent.

Step 3 uses the first equivalence in the existing field-discreteness statement, not its separatedness-dependent extra clause. Its local finite-type hypothesis was proved in step 2; singleton gives discreteness with no theorem needed. The new decomposition statement requires precisely reducedness and local quasi-finiteness, now both available. In the source, 06S0 gives a union of finite-dimensional local Artinian algebras. Reducedness of X makes each such algebra reduced; a local Artinian reduced ring is a field (its unique prime/maximal ideal is its nilradical, hence zero). That remaining algebra fact belongs in the later split of the classification node; no proof was placed in its statement. Since each field spectrum has one point, singleton topology selects exactly one summand, giving a finite extension K/k.

Step 4 uses the full universal clause of the gerbe geometry statement, which quantifies over all algebraic stacks T, not merely field or scheme tests. Pullback along the k-isomorphism e:Q=Spec K identifies the two 2-fibre products and their projections by their defining universal property. Thus the projection in the item is exactly the projection to which the cited node applies. No assertion about residual-gerbe finiteness or separated inertia is used here. I produced a verbatim quote for each cited node in each step and checked each quote against its actual statement.

I tested Z=Spec K for inseparable finite extensions (permitted), Z=B G for positive-dimensional or non-etale flat finite-presentation groups (shows why nonrepresentable maps must be allowed), and nonneutral gerbes (no section was chosen). The decomposition includes empty X and infinite disjoint unions, so it does not assert finiteness without the item's singleton hypothesis. The empty stack is excluded only by the nonempty singleton hypothesis. Removing reducedness admits Spec(k[epsilon]/epsilon^2) and would invalidate the gerbe construction over a reduced singleton base; reducedness is retained. I also checked B1-B10, C1-C8, D1-D5 and E1-E7: self-contained statements with inline gerbe/reduced/locally-quasi-finite meanings and definition citations; correct tags and labels; no fabricated searches, cycles, hidden clause restatements, or unlicensed route changes.

## Unfinished work

None within this one-level split. New nodes are intentionally statement-only for later workers. No Lean was written and no compiler or local DAG check was run.
