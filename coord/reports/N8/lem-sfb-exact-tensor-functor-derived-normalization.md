# Stage-1 worker report

Item: lem-sfb-exact-tensor-functor-derived-normalization. Group: N8. Date: 2026-10-21. Direct delivery, with this worker's self-review and the maintainer's independent review. No agents started.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-exact-tensor-functor-derived-normalization.json: existing statement retained, nine proof steps, exact dependency union, native model equations, normalization calculations, blueprint provenance and actual additional Mathlib searches.
- dag/nodes/sec-six-functors-basics/lem-sfb-termwise-strong-monoidal.json: statement-only supporting lemma; no Mathlib match. The project already has the termwise monoidal functor theorem, recorded for attachment verification. It concerns complexes before localization and has neither exactness nor flat resolutions among its hypotheses.
- citations.json: fourteen verbatim citations, one for every cited node in every step.
- report.md: this report. searches.jsonl is the unmodified output log of msearch.py. The private write_split.py records generation of the sandbox JSON; it is not a delivery file.

No Lean files, project files, launcher files, chapter records or unit records were changed. All writes were in the assigned sandbox. All checks run on the Weil server through the supplied wrappers; no compiler, Lake or build command was run.

## Attachments

CategoryTheory.Functor.mapCochainComplexMonoidal belongs to lem-sfb-termwise-strong-monoidal (candidate for the maintainer's attachment/audit).

The supporting identifications are CategoryTheory.Functor.mapCochainComplex_δ, CategoryTheory.Functor.mapCochainComplex_η and CategoryTheory.Functor.ιTensorObj_mapCochainComplexμIso_hom_f. I read WeilConjectures/Algebra/Homology/Monoidal/MapHomologicalComplex.lean, lines 28-248: the instance is at 227, associativity at 152, unit checks at 189 and 206, inverse tensor/unit identifications at 242 and 247, and the summand formula at 61. The unit definition at 86 and its degree-zero formula at 95 include the canonical single-complex identifications. No sorry occurs in this file. The statement's all-colimit and tensor-preservation hypotheses supply the source's tensor-existence/interchange interfaces, and preservation of countable coproducts supplies its summand-indexed preservation hypothesis. This is a project declaration, not Mathlib. I report an attachment candidate rather than set the maintainer's Lean/audit fields or claim a new compiled closure audit.

There is no attachment for the item: source searches by its blueprint tag and by derived monoidal/tensor normalization found the project tensor-comparison theorem, but that theorem does not assert all the item's native associator and both native unit equations for the prescribed comparison and specified unit.

## Wanted sources

None. Both cited Stacks passages and the project source are present. Tags 0FPQ and 0FPT omit diagram checks and are about ringed sites, not a verbatim proof of this abstract functor assertion. Accordingly proof_origin.by is agent. I use no SGA source.

## What was wrong

The item was an unsplit statement with no proof, although its inherited searches cover earlier symmetry questions as well as its current monoidal assertion. I retained all those searches and appended actual N8 searches for the current statement. I did not add an ordinary symmetry hypothesis, and I did not identify two independently fixed derived tensors by an arbitrary equivalence. Every equation is checked with their native model maps. No statement correction or dispute was necessary.

The current blueprint ancestor is lem-sfb-dc-hom-preserves through lem-sfb-module-object-ringed-site-derived-comparison and lem-sfb-constructible-internal-hom-continuity. I read the current ancestor text and the chapter/unit records. The item's role is a generic coefficient-model tensor tool inside that reduction; it does not replace the unit's preservation/restriction argument. This is not a key node of the unit, so its realization fields are untouched.

The inherited brief mentions coord/dag-sync.md, which is absent in this live read clone; I followed the current direct-delivery/sync instructions instead. Nothing in the split requires that missing historical coordination file.

## What remains

The item has a complete natural-language proof. The new statement is not recursively split: its supporting project declaration is reported above for independent attachment verification. No new Mathlib leaf is claimed. The maintainer retains responsibility for its independent mathematical review and any compiled attachment audit.

## Searches and leaf decisions

All new records come directly from this sandbox's searches.jsonl, populated only by the required msearch.py command. The item was searched with LeanFinder in two phrasings, LeanSearch, Loogle and grep. Results included mapDerivedCategory, its factorization isomorphisms, ordinary monoidal coherence, and monoidal localization. Those do not state the fixed-model normalization theorem. In particular, Localization.Monoidal.functorCoreMonoidalOfComp assumes a strong monoidal localization functor: localization on all complexes is only lax monoidal here, so it does not apply in one line.

The new termwise lemma was searched with LeanFinder in two phrasings, LeanSearch, Loogle and grep. Hits are HomologicalComplex.monoidalCategory, its associator/tensor-existence infrastructure and summand associator formulas, not a monoidal structure on an arbitrary termwise functor. The actual functor theorem is in WeilConjectures, as above. Neither node is therefore marked Mathlib on the strength of those hits. All services used here answered; no unavailable service is described as no match.

Whole-DAG searches included the shared Stacks tags, mapCochainComplexMonoidal, termwise strong monoidal and cochain monoidal functor phrases. Whole-blueprint searches used blueprint_refs.py with exact tensor, monoidal functor, termwise and cochain. The existing cochain pullback equations are ringed-pullback-specific; they cannot be applied to the item's arbitrary F. The new node's same_as is empty after those searches.

## Not duplicates

lem-sfb-termwise-strong-monoidal vs lem-sf-ringed-derived-closed-symmetric-monoidal: the existing node constructs the closed symmetric monoidal derived category of a ringed site; the new node concerns an arbitrary coproduct-preserving monoidal functor on ordinary complexes, with no derived category.
lem-sfb-termwise-strong-monoidal vs lem-sf-ringed-tensor-complex-constraints: the existing node gives native constraint formulas inside one category of ringed-site complexes; the new node compares two categories through an arbitrary specified monoidal functor.
lem-sfb-termwise-strong-monoidal vs lem-sfb-module-object-ringed-site-derived-comparison: the existing node compares particular coefficient module-object and ringed-site derived categories/internal Homs; the new node concerns complexes and any additive monoidal functor.
lem-sfb-termwise-strong-monoidal vs lem-sfb-exact-tensor-functor-derived-normalization: the item proves invertibility and coherence after localization with fixed K-flat derived tensors and factorization kappa; the new lemma has no localization, exactness, K-flatness or flat-resolution hypotheses and supplies only the termwise equations used in that proof.
lem-sfb-termwise-strong-monoidal vs lem-sfb-exact-tensor-functor-derived-braiding: the existing node asserts compatibility with the native derived braidings under an ordinary symmetry hypothesis; the new node proves neither a braiding nor a derived assertion.
lem-sfb-termwise-strong-monoidal vs lem-pur-shifted-tensor-morphism-calculus: the existing node concerns signed shifted derived morphisms and exact ringed pullbacks; the new node concerns unshifted ordinary complexes and arbitrary monoidal functors.
lem-sfb-termwise-strong-monoidal vs lem-pur-cochain-comparison-monoidal-equations: the existing statement requires a RingedPullback and its particular normalized coefficient comparison; the new lemma makes no ringed-site or scalar-extension assumption.
lem-sfb-termwise-strong-monoidal vs lem-sfb-total-tensor-homotopy: that node constructs the monoidal structure on complexes and its passage to homotopy; the new node gives preservation of that structure by F, which is not an assertion of the existing statement.

## Review by N8

I checked the statement against its source intent and read Stacks sites-cohomology.tex at lemma-symmetric-monoidal-cat-complexes (0FPQ) and lemma-symmetric-monoidal-derived (0FPT). The former specifies the degree-zero unit and total tensor and calls the diagrams straightforward; the latter omits the proof. They do not give this abstract cross-functor result without further work. The nine steps supply that work by the normalized representative formula; proof_origin is explicitly agent. For the only new lemma I read the full project implementation mentioned above and compared its instance hypotheses, tensor maps and unit maps, not just its title. No braiding of F is needed in that implementation.

Step 1 cites the actual left-adjoint-colimit theorem, whose statement supplies preservation of each small diagram and the canonical comparison isomorphism. F is a left adjoint by hypothesis; closedness and symmetry give the same property to either tensor variable. The new termwise statement then supplies exactly tau, j and the three equations that are used, including its prescribed bidegree formula. This avoids borrowing a ringed-site-only cochain theorem for an arbitrary F.

Step 2 cites the abstract K-flat existence statement in exactly the closed symmetric Grothendieck setting of the item, including a functorial flat epimorphism. It has no boundedness requirement. I did not use a ringed-site resolution theorem here. Closure of K-flat objects under total tensor is written out by two successive applications of the two-sided preservation test, using the actual complex associator from lem-sfb-total-tensor-homotopy. The unit test follows from the unitors. I checked that F's stated K-flat-preservation hypothesis covers all intermediate complexes, not just the individual P,Q,R.

Step 3 uses the normalization already assumed in the item's statement, and explicitly solves for t at a K-flat pair as a composite of invertible maps. It is elementary once the given model maps and Step 1 are in force. The formula for e is invertible for the same reason. This is not a new lemma restating an item clause.

Step 4 uses precisely the two relevant sentences of lem-sfb-derived-monoidal: constraints are induced from complexes, and localization is lax monoidal. Multiplication by the invertible native model maps gives the three displayed equations. The unit comparison has the direction Q(I) to the derived unit, as in the item; m is the inverse lax tensorator. I checked the associator's domain by defining A-left and A-right explicitly. The actual complex associator/unitors are supplied by the cited total-tensor statement. No identification of unrelated monoidal structures is inserted.

Step 5 cites the new lemma for its ordinary complex associativity equation and the derived-monoidal statement for the native equation from Step 4. Its two displayed residual composites have common source E Q((P tensor Q) tensor R), common target Q(FP) tensor (Q(FQ) tensor Q(FR)), and the same A-D-right and kappa factors. The two applications of the normalization are legitimate for P tensor Q and Q tensor R by Step 2. Naturality moves the intermediate model isomorphisms across t; the residual equality is exactly the cited complex associativity equation, with no extra symmetry condition.

Step 6 checks the left unit using the precise identity e E(u-C) = u-D Q(j) kappa-I. After moving the source unit isomorphism through t by naturality and applying the normalization at (I,P), the resulting target unitor equation has j in its first tensor variable. Step 7 repeats the calculation with j in the second variable and uses the right unitor. In each case the displayed residual composite is the actual corresponding equation from the new lemma, while the native derived-monoidal statement supplies Step 4's unitor. I checked that FI is K-flat and that j is its isomorphism with the target degree-zero unit, so all the natural model maps used here exist and are invertible.

Step 8 writes the conjugation formula for t and explicitly describes pre- and postcomposition for each of the three equations. These maps are isomorphisms, and the chosen representatives exist by Step 2; the conclusion is therefore valid for arbitrary unbounded objects without assuming a universal property for a possibly large product localization. Step 9 simply inverts the proved oplax maps and multiplies the three equations to obtain the three displayed strong-monoidal defining equations. I read def-sfb-strong-monoidal-functor and checked its unit convention is 1-D to E(1-C), so the answer must use e inverse, not e.

For the new lemma I tested degree-zero complexes, zero complexes, and shifted single-term complexes. Degree zero recovers the specified ordinary tensorator and unit; zero complexes add no maps because F is additive; shifted single terms retain the signed differential and do not introduce a symmetry sign into associativity or unit identities. The arbitrary-unbounded case uses direct sums, not products; their preservation is an explicit hypothesis. The new lemma is a genuine termwise functor theorem, not a clause of the derived item. It has only a statement, with no proof or hidden proof sketch. The shared-tag distinctions are listed individually above.

Against delivery-errors B-E, I verified self-contained hypotheses, TeX and source labels, genuine logged searches, precise blueprint ancestry, no unwarranted leaf/attachment claim, verbatim statement citations, no dependencies on proofs of nodes, no circular split and no missing non-elementary claim in the normalization argument. I corrected the new-node shape by omitting the maintainer-owned merged_into field. The parent statement and all inherited metadata are unchanged. All nine steps are shorter than 1200 characters, so there is no long step hiding a further lemma; the only extracted comparison theorem is the new termwise node. Generic off-unit tools are declared in split_report.tool_uses rather than the maintainer-owned tool_uses field. The server check_dag has already reported no introduced finding; final delivery checks follow this report.
