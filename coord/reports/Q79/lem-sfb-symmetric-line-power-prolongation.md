# Q79 stage-1 report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-symmetric-line-power-prolongation.json: repaired item, six proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-normal-semiabelian-generic-torus-quotient.json: independent quotient statement; Mathlib no match.
- dag/nodes/sec-six-functors-basics/lem-sfb-torus-torsor-picard-rational-surjectivity.json: rational Picard descent; Mathlib no match.
- dag/nodes/sec-six-functors-basics/lem-sfb-normal-semiabelian-hom-extension.json: generic homomorphism extension; Mathlib no match.
- dag/nodes/sec-six-functors-basics/lem-sfb-normal-smooth-group-local-ample-line.json: local relative ampleness; Mathlib no match.
- dag/nodes/sec-six-functors-basics/lem-sfb-abelian-symmetric-ample-endomorphism-span.json: Raynaud XI 1.14 input; Mathlib no match.
- citations.json: verbatim excerpts for every item proof citation.

## Attachments

No sorry-free project declaration states this item.

## WANTED

WANTED: Lan, Structures of Semi-Abelian Schemes, Proposition 3.3.1.7 and Chapter I §2, for lem-sfb-normal-semiabelian-generic-torus-quotient.
WANTED: Sansuc, Groupe de Brauer et arithmétique des groupes algébriques linéaires, Proposition 6.10, for lem-sfb-torus-torsor-picard-rational-surjectivity.
WANTED: Faltings–Chai I Proposition 2.7 / Raynaud IX 1.4, for lem-sfb-normal-semiabelian-hom-extension.
WANTED: Raynaud, Faisceaux amples sur les schémas en groupes, Corollaire VI 2.4, for lem-sfb-normal-smooth-group-local-ample-line.
WANTED: Raynaud, Faisceaux amples sur les schémas en groupes, Proposition XI 1.14, for lem-sfb-abelian-symmetric-ample-endomorphism-span.

## What was wrong and repaired

The imported generic ample-symmetrization step depended transitively on the five-node biextension/Picard/cubical cycle named by the released repair note. I removed that edge while retaining the prescribed statement, statement dependencies, and independent ample-difference, tensor, finite-type, and vertical-Cartier inputs. The replacement takes the generic abelian quotient by the maximal torus, descends a power along the torus torsor, expresses the symmetric line as a difference of symmetric ample lines, and applies Raynaud XI 1.14 after a local ample line is chosen on the quotient. The comparison is spread by denominator clearing and extended over the open by vertical Cartier descent. The exponent is d = 4abc, hence positive.

## What could not be finished

The five supporting statements are intentionally statement-only stage-1 nodes. Their primary sources are WANTED because those books/articles are absent from the local literature snapshot. Mathlib searches were run for all five and returned no matching declarations.

## Review by Q79

I reread the item and repair note and checked that no hypotheses, rigidification, or symmetry clause changed. Step 1 uses the new quotient statement for a closed torus, faithfully flat torsor, and abelian generic quotient, then applies the rational Picard statement; the tensor calculation uses the existing pullback/tensor statement. Step 2 uses the full ample-difference and ample-tensor statements, giving ample A and B and preserving ampleness under symmetrization. Step 3 uses the local-ample statement for R, Raynaud XI 1.14 for both symmetric ample generic lines, and generic homomorphism extension before defining the E lines; the exponent 4abc follows from the 2c comparison. Step 4 uses pullback along the identity and the supplied rigidification. Step 5 uses finite-type-over-Noetherian only for finite affine denominator clearing. Step 6 uses the full vertical-Cartier statement: D=p*e*D and the normalized identity section gives e*D=0, so the comparison is invertible on all of G over U intersect W. I checked r=0, U=S, trivial N, characteristic two, and a non-factorial normal base. No new node duplicates an existing statement; the existing split-torus line-pullback lemma is a split special case of the new nonsplit rational statement.

## Not duplicates

lem-sfb-torus-torsor-picard-rational-surjectivity vs lem-sfb-split-torus-torsor-line-pullback: the new node allows nonsplit tori and only a positive power; the existing node assumes split torus and descends the line itself.
lem-sfb-normal-semiabelian-generic-torus-quotient vs lem-sfb-geometric-semiabelian-split-quotient: the new node is a relative normal-base quotient by the generic maximal torus; the existing node is a finite Galois field splitting statement.
lem-sfb-normal-semiabelian-hom-extension vs lem-sfb-normal-semiabelian-biextension-extension: the new node extends one generic homomorphism; the existing node extends a biextension with two laws and coherence.
lem-sfb-normal-smooth-group-local-ample-line vs lem-sfb-raynaud-generic-ample-power-model: the new node supplies an arbitrary local ample line; the existing node extends a prescribed generic ample line after a power and assumes generic properness.
lem-sfb-abelian-symmetric-ample-endomorphism-span vs lem-sfb-raynaud-generic-ample-symmetrization: the new node is a field-level endomorphism-span identity; the existing node is a relative extension theorem.
