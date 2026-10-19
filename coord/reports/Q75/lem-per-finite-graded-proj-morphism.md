# Q75: lem-per-finite-graded-proj-morphism

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-finite-graded-proj-morphism.json`: split, seven steps; original mathematical statement preserved.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-finite-graded-module-dehomogenization.json`: new statement, unsplit, no Mathlib match. This is the algebraic finite-module assertion of Stacks 07Z2(2), not a Proj finiteness assertion.
- `citations.json`: one entry per step/node citation, quoting the cited statement verbatim.
- `report.md`: this report.

No unit file is changed: the item is not its unit's key statement. No Lean was written and no compiler, Lake or build tool was run. All writes are in the item sandbox. The earlier attempt left searches but no item, split or report; its saved results and search log were read and reused.

## Attachments

None. Searched all of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item identifier, finite graded extensions, and finite Proj morphisms, and inspected `WeilConjectures/RingTheory/GradedAlgebra/Standard.lean`. Its `GradedAlgebra.IsStandard.finite_away` has a field base, standard grading, and two degree-one elements covering Proj. It is not the item or the new graded-module assertion. The project has no exact completed declaration found for either. Upstream master sorry declarations were not treated as proofs.

## WANTED

None for this split. All the documents actually used are available under `literature/stacks-project/`. The parent's Rydh reference is context only; no quotient theorem or claim about finite group actions is used here.

## Findings and repairs

The imported item had no proof. Its source correctly distinguished the canonical partial map in 01MY from the additional finite-extension assertion. I supplied the missing argument, without adding equality of the degree-zero rings, Noetherianity, generation in degree one, or a field hypothesis.

The finite-cover argument is not an unsupported appeal to homogeneous lying over: finite homogeneous module generators bound the degrees of A modulo C_+A. Thus every relevant homogeneous prime misses an image from C_+. Surjectivity is proved later on injective finite chart ring maps using ordinary lying over. This avoids creating a second homogeneous lying-over lemma.

The earlier searches found `HomogeneousLocalization.Away.finiteType` and ordinary `Module.Finite.of_isLocalizedModule`. I read the former at Mathlib/RingTheory/GradedAlgebra/HomogeneousLocalization.lean:1097-1098: it asserts finite TYPE of the degree-zero RING over C_0. It does not give finite MODULE generation for a graded M over C_(f), and ordinary localization finiteness is over the full localized ring. The new node is consequently unsplit. The two recorded LeanFinder phrasings, Loogle, LeanSearch and the targeted grep all ran, with their original queries and results retained. Existing item searches are preserved; Q75's actual item searches are appended.

No mathematical statement dispute was found. The original statement is unchanged; the statement dependency for its homogeneous-localization notation is now explicit. The proof origin is agent synthesis because the combined assertion is not the statement of 01MY alone.

## Not duplicates

No existing node cited Tag 07Z2 before this new node. Searched the whole DAG by that tag, `dehomogenize-finite-type`, homogeneous localization, finite graded modules and degree-zero fractions, and searched the whole blueprint by `07Z2`, `dehomogen`, `finite graded`, `graded module`, `graded`, `functoriality`, `01MY` and `homogeneous localization`.

lem-per-finite-graded-module-dehomogenization vs lem-per-finite-graded-proj-morphism: the new node concerns arbitrary graded modules and their fractions, with no injective graded ring map, scheme map, surjectivity, domain-of-definition or chart-map assertion; it is the algebra lemma used in Step 6, rather than a restatement of the item's geometric clauses.

lem-per-finite-graded-module-dehomogenization vs lem-sc-graded-localization-exact: the existing node states preservation of exact sequences, not finite generation of the degree-zero localized module.

lem-per-finite-graded-module-dehomogenization vs def-sc-degree-zero-module-fractions: the existing node defines equal-degree fractions; it makes no finite-generation assertion. It is reused as a statement dependency.

lem-per-finite-graded-module-dehomogenization vs lem-sc-p1-finite-homogeneous-generators: finite homogeneous generators before localization over a polynomial ring do not assert finite generation over the degree-zero chart ring, and that node is not about an arbitrary finite-type graded C over an arbitrary C_0.

lem-per-finite-graded-module-dehomogenization vs lem-trf-local-graded-flat-module-finite-presentation: finite presentation of a flat graded module over a local coefficient ring differs from degree-zero localization finiteness, and imposes hypotheses absent here.

lem-per-finite-graded-module-dehomogenization vs lem-per-finite-type-graded-proj-proper: the existing node concerns properness of the structural morphism to Spec C_0 and asserts nothing about arbitrary module dehomogenization.

Existing gluing, chart-intersection, finiteness-locality, finite-implies-integral and injective-integral-lying-over nodes were reused. No node for finite Proj functoriality, homogeneous lying over, finite homogeneous generators, or injectivity of a localization was created. The first is constructed in the proof and the others have short arguments or existing statements.

## Review by Q75

I read Stacks `constructions.tex`, Tag 01MY, statement and proof; Tag 01M4, statement and proof of standard-open restrictions; `algebra.tex`, Tag 07Z2, both clauses and its bounded-exponent monomial proof, as well as the homogeneous-component argument in Tag 00K0; and `morphisms.tex`, Tag 01WI. For the surjectivity argument I read Algebra Tag 00GQ and the finite-algebra statement of Tag 00GK through the existing node. I checked the blueprint chapter and unit, the current main-20261015 ancestor text, and the recorded quotient-support ancestry. This is an algebraic input below that fixed route and changes no chapter or unit argument. No SGA source is used.

For the only new node I verified 07Z2(2) with R=C_0. The statement introduces C, its grading and finite-type hypothesis, the grading and compatibility of M, module finiteness, the positive degree of f, and the module of fractions with its scalar action. It contains a statement only. The source's proof explains the genuine smaller lemma: for finite homogeneous algebra generators f_i and module generators x_j, monomials with each exponent less than deg(f) suffice after factors f_i^deg(f)/f^deg(f_i) are removed. Neither Noetherianity nor a standard grading is needed. This explanatory argument belongs in this report, not in the unsplit node.

I opened every cited node and compared its actual statement with what the following steps use. The quotes in citations.json are their complete statements, so they also expose the scope to the independent reader.

1. Step 1 uses exactly the generator characterization in `def-weil-finitely-generated-module` and the point description in `def-pc-proj`. The finite replacement by homogeneous components and the degree projection are written out. The bound N and the choice kt>N make all coefficients positive-degree, so the argument does not assume C_0=A_0. This step is elementary; it does not apply a nonexistent homogeneous lying-over theorem.
2. Step 2 uses the explicit fraction convention and ordinary localization relation in `def-nagata-homogeneous-localization-degree-zero`, the affine chart description in `def-pc-proj`, and contravariant spectrum functoriality in `def-weil-affine-spectrum`. Both well-definedness and injectivity are proved using the annihilating-power relations, not by cancelling possibly zero denominators. It is elementary.
3. Step 3 uses `lem-weil-pbc-proj-basic-open-intersection`, whose statement explicitly gives the element g^d/f^e and the intersection D_+(fg). The Proj definition explicitly says its restriction maps are graded localization maps. I checked the degrees in both rings and wrote the identical formula on every c/(fg)^m, justifying agreement of ring maps and, by spectrum functoriality, scheme maps. No mere definition is cited for a separate gluing theorem.
4. Step 4 cites `lem-weil-pbc-scheme-morphism-gluing`, whose statement gives precisely existence and uniqueness of a morphism from maps on an open cover agreeing on pairwise intersections. Its hypotheses are Steps 1 and 3. This uses its statement, not anything buried in its proof.
5. Step 5 applies the same intersection node with f and g in the correct order: the target g chart uses f^e/g^d. Its image is iota(f)^e/iota(g)^d. Principal-open inverse images follow directly from contraction of primes. The equality is checked on every chart in the cover; hence no global preimage identity has been assumed in constructing r.
6. Step 6 applies the new algebra node to M=A, with the actual C-action through iota and the given grading compatibility. The two fraction relations are the same because f acts by multiplication by iota(f), so this identifies the correct scalar action as well as the underlying module. The existing `lem-weil-pbc-finite-local-on-target` explicitly includes condition (2), affine inverse images with finite ring maps; the chart maps and preimage equality established before this step meet exactly that condition. It is a Mathlib leaf already in the DAG, so no second locality node is needed.
7. Step 7 uses the exact finite-algebra-implies-integral statement of `lem-weil-pbc-finite-algebra-is-integral`, then the injective integral ring-map statement of `lem-weil-pbc-integral-injective-lying-over`. Injectivity was proved in Step 2 and finiteness in Step 6 for the chart rings themselves. The affine spectrum and Proj definitions identify those spectrum maps with r on each inverse image. Finally `def-weil-surjective-morphism` defines the resulting pointwise surjectivity. No stronger conclusion about graded primes is taken from the ordinary lying-over node.

I tested zero rings and zero modules, an empty finite generator family (Step 1 includes 1), rings concentrated in degree zero (both relevant Proj spaces must be empty under the finite-extension hypotheses), nilpotent or zero f (zero localization rings and empty charts), arbitrary positive degrees rather than degree one, and a finite extension of coefficient rings C_0 subset A_0. In each case the fraction relations and cover argument still apply. The example C=k[t] subset A=k'[t] for a finite field extension k'/k checks that the proof permits unequal degree-zero rings. No step exceeds 2000 characters; the overlap calculation and module identification are explicitly present, without a hidden comparison lemma.

This checks B (self-contained searched statement-only new node, exact Stacks tag/label, references and no false leaf), C (all used non-elementary statements cited and quoted, no proof-of-node substitution, no unnecessary duplicate), D (the item's argument remains in its own steps), and E (all finiteness, injectivity, grading and localization hypotheses checked where applied). Remote checks below verify the dependency graph, including cycles, on the full delivery tree.

## Unfinished work

No unfinished part of this one-level split. The new graded-module dehomogenization node intentionally remains unsplit for the next stage-1 item. There are one new node and zero new Mathlib leaves.

## Validation

The required server dry run is run after this report is written; its output is the authoritative validation and delivery record.
