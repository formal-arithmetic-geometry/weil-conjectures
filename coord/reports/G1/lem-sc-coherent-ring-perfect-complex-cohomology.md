1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-coherent-ring-perfect-complex-cohomology.json` (statement, split; no Mathlib match).
- `dag/nodes/sec-abelian-varieties/lem-sc-coherent-ring-fp-kernel-cokernel.json` (statement-only child; no Mathlib match).
- `citations.json` (verbatim citations for both proof steps).

2. Attachments: none.

3. WANTED: none; the cited Stacks source files are available in the local review checkout at `/home/ubuntu/c1-stacks-review`.

4. The imported item had an incorrect creation parent and no proof. I retained its mathematical statement and corrected the blueprint place to the coherent-ring algebraic clause. The split adds only the real supporting lemma that finitely presented modules over a coherent ring are closed under kernels, images, and cokernels; the item proof then identifies cycles, boundaries, and cohomology as the corresponding kernel, image, and cokernel constructions. No existing DAG node states this closure result, and Mathlib searches found no coherent-ring analogue.

## Not duplicates

lem-sc-coherent-ring-fp-kernel-cokernel vs lem-sc-coherent-ring-perfect-complex-cohomology: the child states closure of finitely presented modules under kernels, images, and cokernels, while the item states finite presentation of every cohomology module of a bounded finite-projective complex and uses that closure in its proof.

## Review by G1

I read the item source reference (More on Algebra, Lemma 0EWZ, with Algebra Lemma 05CX) and the underlying coherent-module closure statement in Algebra Lemma 05CW. The child statement matches 05CW plus 05CX: coherent modules form an abelian category, and over a coherent ring coherent modules are exactly finitely presented. In step 1, finite projective terms are finitely presented by the definition of finite projective, and the cited child explicitly supplies finite presentation of each differential's kernel and image. In step 2, the inclusion of boundaries into cycles is a map between finitely presented modules, and the same cited statement explicitly supplies finite presentation of its cokernel, which is the cohomology module. I checked the zero complex and a one-term complex as edge cases. I also ran LeanFinder, Loogle, and Mathlib grep searches for both the item and the new child; no coherent-ring theorem was found, while LeanSearch was unavailable and recorded as such. The citation quotes are copied verbatim from the child statement.

## Second reading by G1

- Item statement: checked against More on Algebra Lemma 0EWZ and Algebra Lemma 05CX; the bounded finite-projective affine specialization has the stated hypotheses and conclusion.
- Child statement: checked against Algebra Lemmas 05CW and 05CX; rewritten to state the coherent-ring hypothesis directly, so it is self-contained with its finitely-presented-module definition citation.
- Step 1: checked that each differential has finitely presented source and target and that 05CW/05CX give finite presentation of its kernel and image; no unstated hypothesis is used.
- Step 2: checked that boundaries embed in cycles and that the cited closure result gives the cokernel, which is exactly cohomology; the zero and one-term complexes give the expected cases.
- Mathlib searches: checked the recorded LeanFinder, Loogle, grep, and unavailable LeanSearch results; no exact declaration exists.
- Changes: corrected the item's `created.item` metadata, made the child hypothesis self-contained, and updated this audit and the citation record.
