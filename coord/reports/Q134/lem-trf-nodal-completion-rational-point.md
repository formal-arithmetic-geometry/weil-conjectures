## Files written

- dag/nodes/sec-trace-formula/lem-trf-nodal-completion-rational-point.json: item, statement, split; no exact Mathlib match. The statement is unchanged.
- dag/nodes/sec-trace-formula/lem-trf-algclosed-fg-field-finite.json: new statement-only unsplit lemma; no Mathlib match. An algebraically closed field finitely generated as a field over any base is finite over that base.
- citations.json contains a verbatim statement quote for every step/node pair.
- searches.jsonl retains the actual msearch.py results. No Lean source was written and no compiler or build was run.

## Attachments

None. Searched the live WeilConjectures source for the item id, nodal/completion/rational terminology, algebraically closed finite-generation terminology, and the field-theory candidates. The nodal mentions are counterexamples or unrelated material; none states every clause of this item. The Mathlib algebraic-closure and essential-finite-type hits have additional algebraicity or formally unramified hypotheses. An exact project attachment was not found.

## WANTED

None. The proof is explicitly agent-written, refining the retained argument in coord/reports/N9/lem-trf-node-algebraically-closed-extension.md. Its contextual source and all background source passages are available locally.

## What was wrong or incomplete

The item was statement-only, extracted by N9 from the earlier completion argument. Its statement is correct and was retained. Stacks Tag 0C56, curves.tex lemma-node-field-extension, concerns dimension-one schemes and a closed-node reduction; it is context for the argument rather than a theorem asserting this dimension-free statement. I did not import its dimension hypothesis or pretend that its text proves the abstract-ring refinement. The assembly proof and its origin are marked agent-written.

A ring isomorphism of the completion with the nodal ring need not be a k-algebra isomorphism. In particular an abstract isomorphism L ≅ k alone does not establish that the structure map k → L is onto. The split first proves algebraic closedness of L, then finite generation as a FIELD, then finite degree, then bijectivity of the specified map. Finite generation as an algebra is not assumed for L. Closedness in one affine chart does not establish global closedness without further argument; Step 4 supplies the specialization argument using all finite-type charts.

I initially considered the existing local-completion-residue theorem, read its complete statement, and observed its Noetherian hypothesis. It is unnecessary here: the ring isomorphism already gives localness, and the surjective first projection of the completion identifies its residue field with A/m. Thus no Noetherian-transfer theorem or completion exactness is used implicitly.

## What remains

No part of this one-level split is unfinished. The new field-theoretic lemma is intentionally statement-only, ready for its own later stage-1 split. Its full retained argument is recorded below so the extraction loses no mathematics.

## Retained argument for the new field lemma

Identify F with its image in L. Write L = F(a_1,...,a_n). Choose a maximal algebraically independent subfamily t_1,...,t_r among these generators. The maximality implies that each remaining generator is algebraic over E = F(t_1,...,t_r); finite algebraic generation gives a finite degree e = [L:E]. These are precisely the finite-basis argument of Stacks Tag 030F (fields.tex lemma-transcendence-degree, proof with generating set G) and Tag 09GH (lemma-algebraic-finitely-generated).

If r > 0, put H = F(t_2,...,t_r), so E = H(t_1). Choose a prime integer ell > e different from char(F). The polynomial Z^ell - t_1 is Eisenstein at t_1 in H[t_1][Z]: its leading coefficient is one, every other coefficient is divisible by t_1, and its constant coefficient is not divisible by t_1 squared. Gauss's lemma therefore makes it irreducible over E. Algebraic closedness of L gives a root b in L. Thus [E(b):E] = ell, while E(b) ⊆ L gives [E(b):E] ≤ [L:E] = e, a contradiction. Therefore r = 0, all generators are algebraic over F, and Tag 09GH gives [L:F] finite. The argument is valid in every characteristic, for every base field, and does not assume that the base is algebraically closed. The Eisenstein/Gauss ingredient belongs to the proof of this new unsplit lemma, rather than being hidden in an elementary step of the item.

This retains N9's finite-generation, transcendence-basis, finite-degree, prime-choice, Eisenstein, Gauss, root and degree-contradiction argument. Its restriction to algebraically closed base k gives the precise subargument required by the parent. The item itself separately proves the nodal residue-field identification and global geometry; the new lemma is neither a nodal statement nor a clause restatement of the item.

## Not duplicates

lem-trf-algclosed-fg-field-finite vs lem-weil-pbc-finitely-generated-field-finite-transcendence-basis: the existing theorem gives a finite transcendence basis and an algebraic extension of the rational-function subfield, but does not show that the basis is empty when the target is algebraically closed.

lem-trf-algclosed-fg-field-finite vs lem-exc-transcendence-basis-exists: the existing theorem gives a basis for an arbitrary field extension; it neither uses finite field generation nor proves finite degree.

lem-trf-algclosed-fg-field-finite vs lem-weil-pbc-algebraic-generators-finite-extension: the existing theorem requires algebraic generators. The new theorem must exclude positive transcendence degree from algebraic closedness of the target; it does not assume algebraicity over the base.

lem-trf-algclosed-fg-field-finite vs lem-sfb-separating-basis-algebraic-diamond: the existing theorem concerns four fields with a separable algebraic diamond and geometric reducedness; it gives a simultaneous separating basis, not finiteness from algebraic closedness of the target.

lem-trf-algclosed-fg-field-finite vs lem-sfb-semilinear-fixed-field-finite-generation: the existing theorem concerns a finite group acting on two fields and proves finiteness over fixed fields plus finite generation; no such group action is present in the new theorem.

lem-trf-algclosed-fg-field-finite vs lem-coef-full-subcategory-kan-trivial-restriction: the existing node is a quasicategory restriction theorem; its source contains the same four-character string 030F in a different reference context, and states no field theorem.

lem-trf-algclosed-fg-field-finite vs lem-weil-pbc-algclosed-fg-field-separating-basis: the existing theorem assumes the BASE algebraically closed and provides a separating basis, which can be nonempty. The new theorem assumes the TARGET algebraically closed and proves finite degree.

lem-trf-algclosed-fg-field-finite vs lem-weil-pbc-alg-closed-finite-extension-trivial: the existing theorem assumes the BASE algebraically closed and the extension finite; the new theorem supplies finiteness under algebraic closedness of the TARGET and finite field generation. The existing finite-extension-triviality node is cited separately in Step 3.

lem-trf-algclosed-fg-field-finite vs lem-trf-nodal-completion-rational-point: the item concerns a scheme point with an abstract nodal completion. The new theorem concerns arbitrary field extensions and has no scheme, local ring, completion, point, or rationality assertion.

## Review by Q134

I read the project goal, worker contract, stage-1 rules, SETUP's three levels, chapter sec-trace-formula, unit sk-i-curve-zero, the ancestor lem-trf-local-term-locality and the parent lem-trf-node-algebraically-closed-extension with N9's retained report. I read delivery-errors B through E in both copies of that document. This is a refinement within the existing semistable/nodal base-change branch, not a replacement of the unit or chapter route.

For the item I read curves.tex Tag 0C56, lemma-node-field-extension, including its distinction between closed and nonclosed images and its formal-presentation discussion. For the new lemma I read fields.tex Tag 030F, lemma-transcendence-degree, its proof choosing a basis inside a generating set, Tag 09GH, lemma-algebraic-finitely-generated, and Tag 09GR, lemma-algebraically-closed. I also read algebra.tex Section 00M9's compatible-sequence definition, the prime residue-field description at lines 3337ff, and more-algebra.tex Tag 07C1's explicit finite-generation sentence. The Eisenstein obstruction is an agent-written extension of this background, rather than a false attribution of that conclusion to 030F or 09GH.

Step 1 cites exactly the formal-power-series coefficient definition, the adic-completion compatible-sequence definition, and the definition of algebraically closed. I read all three statements. It explicitly constructs the geometric-series inverse (positive total degree makes each coefficient finite), obtains the unique maximal ideal by constant-term evaluation, and uses only the surjective first projection of the completion. No unquoted completion-flatness, same-residue-field or Noetherian theorem is needed. The abstract field isomorphism transfers roots of polynomials, while the structure map is deliberately left for Step 3. This is a routine explicit calculation from definitions and is marked elementary.

Step 2 cites the finite-type definition for choosing a finitely generated affine chart, the affine-open stalk-localization statement for the actual germ map, and the finite-type residue-field extension theorem. I read each entire statement. The last theorem applies to k → S at p over the unique prime (0) of the field k, and says finite generation as a field, exactly what is used. The stalk identification preserves this actual k-structure. It does not assert that every residue field is finitely generated as an algebra.

Step 3 cites the new field lemma and the existing algebraically closed BASE/finite-extension-triviality node, whose full statement and Mathlib match I read. Their hypotheses are supplied in the correct order: first L is algebraically closed and finitely generated as a field over k, giving finite degree; only then the algebraic closedness of k makes the specified structure map bijective. This avoids confusing the algebraic-closure predicate of L with an algebraic-closure extension over k.

Step 4 cites clause (a) of lem-kun-closed-point-field, the same affine-stalk theorem and finite-type definition. I read that criterion in both the node and its blueprint source. Its finite-type hypothesis is checked for each affine V, not imposed on the whole locally finite-type X. Since L is finite over k independently of charts, x is closed in every such V. The quotient identification for a maximal prime follows directly because localization of a field at its nonzero elements is itself. The final generalization/specialization argument is written explicitly; it requires neither separatedness nor a finite affine cover. All quoted dependencies are recorded verbatim in citations.json, and proof_deps is exactly the union of the uses lists.

For B1--B3 the new node is self-contained, introduces both fields and the specified map, spells out finite field generation and the finite-dimensional conclusion, cites definitions, and has empty proof/proof_deps and null proof_origin. It contains no proof sketch in its statement. B4--B10: TeX is singly escaped, source places identify actual Stacks tags/labels with their limited role explained, the whole DAG/blueprint and project Lean were searched before creating the node, and actual msearch.py queries/results are retained. LeanFinder and LeanSearch candidates require algebraicity; IsAlgClosed.isAlgClosure_of_transcendence_basis in Classification.lean:50 assumes a basis and does not make it empty; Algebra.finite_of_essFiniteType_of_isAlgebraic in IntermediateField/Adjoin/Algebra.lean:180 requires algebraicity; Unramified/Field.lean:61 requires formally unramifiedness, absent here. I read those local source passages. A second semantic phrasing found transcendental/infinite and cardinality statements, not the required finite-degree theorem. No new Mathlib leaf is claimed.

For C1--C8 every non-elementary input of the four assembly steps is a cited node statement, not a node proof, definition posing as a theorem, or external tag alone. The new lemma has no dependencies on this item and thus cannot create a cycle through it. Tool uses of another unit are declared in split_report for the generic residue extension and closed-point criterion; the two other off-unit algebra tools are Mathlib leaves. For D1--D5 the proof retains the nodal local calculation and the geometric conclusion; the smaller field lemma removes only the independent transcendence-degree obstruction. No conclusion of a source with omitted details is silently imported.

For E1--E7 I tested the new lemma on L=F algebraically closed (degree one), C/R (finite degree two, illustrating why no rationality is claimed for arbitrary F), an algebraic closure of a finite field over its finite prime field (not finitely generated, so excluded), and the algebraic closure of F(t) over F (also not finitely generated as a field; this is the positive-transcendence obstruction). For the item the standard origin in Spec k[u,v]/(uv) satisfies the conclusion; a nonclosed point such as a generic point of A^1 has residue k(t), which is not algebraically closed and cannot have the specified completed nodal ring. Empty X has no x, so the pointed statement is vacuous. Arbitrarily many affine components and nonseparated gluings do not affect the pointwise specialization argument. Characteristic two affects neither the constant-term inverse nor Eisenstein at t_1; no Hessian or division by two occurs. Each non-elementary step has fewer than 2000 characters, and the source/report distinction preserves the full field argument without hiding it in a long assembly step.
