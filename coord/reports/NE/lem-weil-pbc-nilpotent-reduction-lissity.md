# Stage-1 report

## Files written

- `lem-weil-pbc-nilpotent-reduction-lissity.json`: split statement, four proof steps, and blueprint reference.
- `lem-weil-pbc-locally-constant-tensor.json`: new unsplit statement node; Mathlib searches found no match.
- `lem-weil-pbc-locally-constant-derived-serre.json`: new unsplit statement node; Mathlib searches found no match.
- `citations.json`: verbatim citations for every step/node use.

## Attachments

None. No declaration tagged `(blueprint: lem-weil-pbc-nilpotent-reduction-lissity)` or an exact sorry-free declaration was found in the source trees.

## WANTED:

None. The cited Stacks source is present locally.

## Not duplicates

- `lem-weil-pbc-locally-constant-tensor` vs existing DAG nodes: no existing node states Tag 094H for arbitrary small sites and Noetherian coefficients; nearby constructible/tensor nodes are restricted to etale schemes or different coefficient hypotheses.
- `lem-weil-pbc-locally-constant-derived-serre` vs `thm-constructible-serre`: the existing node concerns constructible etale sheaves over finite rings on a scheme, whereas this node concerns locally constant finite-type sheaves on an arbitrary small site over a Noetherian ring and includes the derived triangulated consequence.

- `lem-weil-pbc-locally-constant-derived-serre` vs `lem-weil-pbc-nilpotent-reduction-lissity`: the new node isolates the weak-Serre and derived triangulated closure input (Tag 093U/094I proof), while the item is the full ideal-power propagation theorem (Tag 094I).
- `lem-weil-pbc-locally-constant-derived-serre` vs `lem-pc-constant-extension-cokernel-presentation`: the existing node gives a cokernel presentation for constant extensions; it does not state weak-Serre closure or derived triangulation.
- `lem-weil-pbc-locally-constant-derived-serre` vs `lem-pc-constant-extension-cokernel-aux-cover`: the existing node concerns an auxiliary covering in a presentation argument, not kernels/cokernels/extensions of locally constant sheaves.
- `lem-weil-pbc-locally-constant-derived-serre` vs `lem-pc-constant-extension-cokernel-aux-finite`: the existing node proves finiteness of an auxiliary presentation object, not weak-Serre closure.
- `lem-weil-pbc-locally-constant-derived-serre` vs `lem-pc-constant-extension-presentation-lift`: the existing node lifts presentations and does not assert closure under extensions or derived triangles.
- `lem-weil-pbc-locally-constant-derived-serre` vs `lem-pc-finite-free-constant-local-lift`: the existing node is a finite-free local lifting statement, not a Serre-subcategory theorem.
- `lem-weil-pbc-locally-constant-derived-serre` vs `lem-constructible-constant-extension-cover`: the existing node concerns constructible constant extensions on schemes, not arbitrary sites and Noetherian finite-type locally constant modules.
- `lem-weil-pbc-locally-constant-derived-serre` vs `lem-constructible-constant-exact`: the existing node is an exactness result for constructible constant sheaves, not the general weak-Serre plus derived consequence here.
- `lem-weil-pbc-locally-constant-tensor` vs `lem-weil-pbc-nilpotent-reduction-lissity`: the new node is Tag 094H's independent tensor-product lemma; the item is Tag 094I's induction over ideal powers.

## What was checked and corrected

I read the imported item, its unit/chapter records, and the parent blueprint proof (c), then read Stacks Project `sites-cohomology.tex` at Tags 094H and 094I and `sites-modules.tex` at Tag 093U. The item hypotheses match Tag 094I: a small site, Noetherian coefficient ring, ideal, bounded-above derived object, and locally constant finite-type cohomology after reduction modulo the ideal. I checked the edge cases `m=1` and `J^m=0`; the latter identifies the quotient with the coefficient ring itself.

Step 1 uses the new weak-Serre/derived-subcategory statement, whose quoted sentence explicitly supplies closure under kernels, cokernels, extensions, and triangles. Step 2 uses exact sheafification for the constant quotient sequence and the K-flat resolution theorem for a termwise-flat model. It uses only the K-flat computation clause of derived change of rings; the displayed balancing maps prove associativity, and the cone calculation proves the triangle directly. Step 3 uses the new Tag 094H tensor statement and the same triangulated closure to perform induction on powers of `J`. Step 4 uses the existing change-of-rings node for the unit identification when `J^m=0`. I recorded every citation in `citations.json` and checked each quote against the cited node text. I ran LeanFinder, Loogle, grep, and LeanSearch searches for both new nodes; LeanSearch was unavailable and is recorded as such. No Mathlib declaration states either site/derived assertion.

## Review by NE

I checked the source and dependency statements line by line, verified that each proof step names all non-elementary inputs, and corrected the imported empty proof by adding the Stacks induction argument. On the one-point site both new statements reduce to finite-module closure and derived tensor of finite-cohomology bounded-above complexes; these allow infinite negative Tor tails, so no finite projective-dimension assumption has slipped in. Zero complexes and the zero coefficient ring are included. The case J=B reduces to zero quotient rings, while J=0 gives the original hypothesis at every positive power. The inherited parent proof route is amplification (c), as recorded in the source blueprint; no proper morphism or new finite-Tor hypothesis is introduced. I also checked that the new nodes are not restatements of existing constructibility or etale-only nodes, and that the proof preserves the coefficient category and the derived scalar-extension morphisms.

## What could not be finished

No Lean code was written or compiled, as required for this stage.

## Final self-check corrections

The quotient-coefficient induction now explicitly verifies Noetherianity of B/J, finite generation of J^n/J^{n+1}, and boundedness above using the existing arbitrary-site bounded flat replacement nodes. The quotient triangle is computed on a termwise-flat K-flat model; the balancing map verifies scalar associativity directly, rather than taking it from a change-of-rings statement that does not state associativity. Exact sheafification is cited for the constant quotient sequence. All citations are full verbatim statements. The duplicate comparisons above follow reads of each listed statement, including their finite-ring and scheme restrictions.

## Second reading by NE

- Item statement: compared every hypothesis and conclusion with sites-cohomology.tex, Tag 094I, lemma-locally-constant-bounded; small site, Noetherian coefficients, arbitrary ideal, bounded-above object, finite-type locally constant reduction, and all positive powers agree. The final nilpotent clause is the identity-coefficient specialization, not an extra assumption.
- Step 1: compared 093U(3) and derived.tex Tag 06UQ, lemma-cohomology-in-serre-subcategory, with the statements of lem-weil-pbc-locally-constant-derived-serre, lem-sbc-cohomology-in-weak-serre-subcategory, and def-weil-sheaf-of-modules-category; pass after replacing the duplicated derived consequence by the existing generic node. Zero and invariance under isomorphism follow directly from the local-description definition; smallness gives the abelian category required by the generic node.
- Step 2: read all six cited statements (exact presheaf/module sheafification, K-flat resolution with flat terms, flatness, K-flatness, derived change of rings, derived-category cone definition) against 094I's quotient triangle and reassociation. Pass: termwise flatness gives the short exact complex, the cone-to-quotient kernel is the identity cone, and balancing gives the stated reassociation. Restriction of a quotient-module acyclic complex remains acyclic because kernels are sectionwise and cokernels are sheafified sectionwise; hence the K-flat scalar extension argument has the required hypotheses. No associativity claim is borrowed from the change-of-rings node's proof.
- Step 3: read the statements of the tensor node, Noetherian-ring definition, exact sheafification node, bounded flat replacement and bounded-above flat K-flatness nodes, plus the reused generic triangulated-closure node; compared against 094H and 094I. Pass after repointing triangulated closure. Quotient Noetherianity and the projected generators of the ideal-power quotient are explicit. Good truncation and bounded flat replacement give the tensor lemma its boundedness hypothesis. The finite generating set of the annihilating ideal and exact constant sheafification justify the coefficient-module quotient even on a site without points.
- Step 4: read lem-pur-derived-change-of-rings, specifically its K-flat computation clause, against the displayed unit chain maps; pass. The chain maps, rather than any unstated unit theorem, identify the nilpotent reduction with K.
- New node lem-weil-pbc-locally-constant-derived-serre: compared with sites-modules.tex Tag 093U, lemma-kernel-finite-locally-constant (3). Pass after removing the derived consequence already supplied by lem-sbc-cohomology-in-weak-serre-subcategory. Remaining kernel/cokernel/extension assertion is a genuine smaller independent theorem, not elementary (extensions require local lifts and finite presentations), and is neither the item nor its ideal-power clause. Statement-only, all objects introduced, definition references checked, single-escaped TeX and exact source label checked. Existing lemma-constructible-flc-serre requires a finite ring; thm-constructible-serre requires a scheme and finite ring, so neither covers arbitrary Noetherian coefficients on this site.
- New node lem-weil-pbc-locally-constant-tensor: compared with sites-cohomology.tex Tag 094H, lemma-locally-constant-tensor-product. Pass after replacing the irrelevant scalar-extension-computation sentence by the explicit definition of derived tensor and its K-flat/tensor-complex definition references, and defining D^- inline. This is independent of ideal powers and non-elementary, so retained. Statement-only, all hypotheses introduced, definitions checked, single-escaped TeX and tag/label checked; nearby scheme-only derived-tensor nodes do not state this arbitrary-site finite-cohomology assertion.

Small cases: on the one-object trivial-topology site these two new nodes give finite-module kernels/cokernels/extensions and finite Tor modules degree by degree. Noetherianity is needed for the kernels; bounded-above factors suffice and allow infinitely many negative Tor degrees. Over a field tensor has no Tor obstruction. Zero modules/complexes and the zero ring satisfy both statements. On the empty site or the site admitting empty covers the assertions include the zero sheaf; the proof never infers module faithfulness from constant sheafification. For the item, m=1 is precisely the hypothesis, m=0 is outside the positive-power conclusion, J=0 leaves K unchanged, J=B gives zero reductions, and a nilpotent ideal gives K at its vanishing power.

Independent searches: ran two new LeanFinder queries using “homology” and “kernels cokernels and extensions” and a Mathlib grep for IsWeakSerre/WeakSerre and locally-constant kernel/homology terminology. Read their actual hits: condensed-module ambient structures and internally projective tensor criteria do not state either theorem; grep had zero hits. Added the actual records to both nodes, preserving earlier searches and service-unavailable records. Searched all imported blueprint nodes by locally-constant tensor and weak-Serre terminology, and DAG source tags/keywords; the generic derived closure was found and reused. Read source-tree identifier/concept searches; no exact closed declaration of either arbitrary-site theorem was found. Upstream master is reference material, not a finished proof.

Changes: narrowed the Serre node to 093U(3), cited the existing derived closure in Steps 1 and 3, removed ambiguous stalk language from both new statements, supplied the tensor and bounded-above definitions, added the item's site/module definition references, regenerated every citation verbatim, and recorded independent searches. The existing generic node is a tool from another unit implementing the exact 06UQ input used by 094I; no proper-base-change route is replaced. The first worker's report and Review by NE remain above; descriptions there of the former combined Serre/derived node are superseded by this second reading.
