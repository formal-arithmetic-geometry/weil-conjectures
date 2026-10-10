Files written:

- `dag/nodes/sec-abelian-varieties/pqf-lem-locqf-fibre-discrete.json`: statement split into one proof step.
- `dag/nodes/sec-abelian-varieties/pqf-lem-finite-type-algebra-finite-spectrum.json`: new unsplit statement node; Mathlib searches found no exact match.
- `citations.json`: verbatim quotes for every citation in step 1.

Attachments:

None. No sorry-free project declaration states the item.

WANTED:

None.

What was wrong in the imported material:

The imported proof cited `pqf-lem-qf-finitefibres`, but that node's statement does not provide the affine algebra argument needed here. I replaced that citation with a smaller statement-only node for the finite-type algebra with finite spectrum argument, and added the missing `pqf-def-quasifinite` statement dependency. The scheme-conventions dependency is now cited by the proof step.

What could not be finished:

The new algebra node remains unsplit because its Jacobson/Artinian proof is a separate DAG item. All required Mathlib searches were run; LeanSearch was unavailable.

## Review by G1

I read the item source blueprint node and the statements of `pqf-lem-qf-finitefibres`, `pqf-def-quasifinite`, `def-weil-pbc-scheme-conventions`, and the new algebra node. The single proof step uses the new node exactly for the finite-spectrum affine fibre algebra conclusion, uses the quasi-finite definition for the affine local criterion, and uses the scheme conventions for the locally finite type affine setup. The finite fibre hypothesis gives a finite prime spectrum on each affine fibre chart; the new node then supplies discreteness and isolated points, including the zero-ring edge case. I checked the small cases `Spec k`, `Spec(k[ε]/(ε²))`, a finite disjoint union of points, and the empty fibre. I also searched the whole DAG and blueprint for duplicates before creating the algebra node; no existing node states the finite-spectrum hypothesis and conclusion together.

Blueprint realization: the item realizes the imported proof paragraph, and the new node makes precise its sentence about the finite type `κ(s)`-algebra with finitely many primes.

## Second reading by G1

The item statement was checked against Morphisms Lemma 01TH (`lemma-finite-fibre`): locally finite type and finite set-theoretic fibre are the exact hypotheses, with conclusions that the fibre is finite discrete and the map is quasi-finite at every point over `s`. I checked the empty scheme, `Spec k`, a finite disjoint union of points, and a nonreduced finite algebra.

Step 1 was checked against the affine fibre argument and the statements of `pqf-lem-finite-type-algebra-finite-spectrum`, `lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs`, `pqf-def-quasifinite`, and `def-weil-pbc-scheme-conventions`. The algebra node gives discreteness on each affine fibre chart; the cross-unit node supplies the missing isolated-point-to-quasi-finite affine witness; the definition and convention nodes supply the remaining notions. Verdict: repaired and accepted.

The new algebra node was checked against Algebra Lemma 0ALW (`algebra-lemma-finite-type-algebra-finite-nr-primes`) together with 00KH (`algebra-lemma-Noetherian-dimension-0`). Its finite-spectrum, maximal-prime, finite-dimensional, and discrete conclusions agree; the zero-ring clause is the vacuous extension and was tested separately. It is statement-only, self-contained, cites its definitions, uses the required TeX, records three search kinds and the unavailable LeanSearch result, and has no blueprint duplicate.

Changes: replaced the unsupported appeal to the quasi-finite definition as an affine criterion with the existing accepted node `lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs`, and added its dependency and citation. This is a cross-unit tool; the maintainer should record that tool use at merge.

## Not duplicates

pqf-lem-finite-type-algebra-finite-spectrum vs lem-weil-pbc-noetherian-local-quotient-artinian-local: the new node assumes a finite type algebra over a field with finite prime spectrum; the existing node treats a prescribed quotient of a Noetherian local ring containing a power of its maximal ideal.
pqf-lem-finite-type-algebra-finite-spectrum vs lem-weil-pbc-artinian-local-unique-prime: the new node derives Artinian and discrete conclusions from finite spectrum and finite type; the existing node assumes an Artinian local ring and concludes its spectrum has one point.
pqf-lem-finite-type-algebra-finite-spectrum vs lem-weil-pbc-artinian-local-noetherian-nilpotent: the new node concerns finite type field algebras with finite spectrum; the existing node assumes an Artinian local ring and proves Noetherianity and nilpotence.
pqf-lem-finite-type-algebra-finite-spectrum vs lem-weil-pbc-dim-le-one-principal-quotient-finite-length: the new node has a finite-spectrum hypothesis and finite-dimensional algebra conclusion; the existing node concerns a principal quotient by a nonzerodivisor in dimension at most one.
pqf-lem-finite-type-algebra-finite-spectrum vs lem-weil-pbc-finite-type-dim-zero-artinian: the new node assumes finite prime spectrum of an algebra and includes the Jacobson step that all primes are maximal; the existing node assumes scheme-theoretic topological dimension at most zero and treats finite type schemes.
pqf-lem-finite-type-algebra-finite-spectrum vs lem-weil-pbc-zero-dimensional-base-change-points: the new node is an algebra lemma over an arbitrary field with finite spectrum; the existing node is a base-change theorem for separated zero-dimensional schemes over an algebraically closed field.
pqf-lem-finite-type-algebra-finite-spectrum vs lem-weil-pbc-zero-dimensional-sections-stalks: the new node proves an algebraic finite-spectrum criterion; the existing node computes sections and stalks for a separated zero-dimensional scheme over an algebraically closed field.
pqf-lem-finite-type-algebra-finite-spectrum vs lem-weil-pbc-finite-type-algebra-dim-zero-finite: the new node assumes finite prime spectrum and must first deduce every prime is maximal; the existing Mathlib leaf assumes every prime is already maximal and concludes finite-dimensionality.
