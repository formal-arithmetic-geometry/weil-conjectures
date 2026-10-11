1. Files written

- `dag/nodes/sec-algebraic-groups-lie-algebras/lem-wf-lie-algebra-derivation-bracket.json`: split statement.
- `dag/nodes/sec-algebraic-groups-lie-algebras/lem-wf-mixed-commutator-tangent.json`: unsplit auxiliary statement; Mathlib search found no match.
- `dag/nodes/sec-algebraic-groups-lie-algebras/lem-wf-liehom-map-lie.json`: Mathlib leaf, `LieHom.map_lie` in `Mathlib/Algebra/Lie/Basic.lean:368-369`.
- `citations.json`: verbatim step citations.

2. Attachments

None.

3. WANTED

None; the Milne Chapter 10 reference is used as the source, with the mixed-term calculation written explicitly.

4. What was wrong or incomplete

The imported item had no proof steps and recorded only the broad Milne reference. Its two assertions need separate arguments: closure follows from the two-parameter commutator, while the representation equation follows from the Lie-homomorphism law and the matrix commutator definition. No existing DAG node stated the mixed-term calculation. The item is stated over an arbitrary field, which is sufficient for the displayed algebraic calculation even though the surrounding blueprint definition specializes to algebraically closed characteristic zero.

## Review by C1

I read the item's source context in the blueprint definition `def-wf-lie-algebra-derivation` and the corresponding source module `AlgebraicGeometry/GroupScheme/GeneralLinear/Lie.lean`, including the definitions of `toMatrixLieHom` and `RationalHom.differential`; those declarations confirm that the differential is a Lie-algebra homomorphism by type. I also read Mathlib's `LieHom.map_lie` at `Mathlib/Algebra/Lie/Basic.lean:368-369` and recorded it as the exact leaf used in step 4. Step 1 uses only the tangent-vector identification stated by the definition node. Step 2 uses the new mixed-commutator statement verbatim; it supplies both subgroup closure and the coefficient calculation. Step 3 uses the definition of a Lie algebra and checks bilinearity, alternation, and Jacobi by associative-ring expansion. Step 4 uses the rational-representation definition for linearity and the Mathlib leaf for bracket preservation. Step 5 expands the commutator in the endomorphism algebra. I checked the hypotheses: finite-dimensionality gives the endomorphism algebras, the subgroup hypothesis supplies closure of the two-parameter commutator, and the homomorphism hypothesis supplies the differential Lie homomorphism. The small cases `X=0`, `Y=0`, and the trivial subgroup give zero mixed coefficient and agree with the statement. The only correction to the imported material was replacing its empty proof with these explicit steps and adding the required dependency and citation records.

5. What could not be finished

The mixed-commutator auxiliary node remains unsplit by design; its statement is the elementary dual-number calculation used by the item.

## Second reading by C1

- Item statement: checked against `def-wf-lie-algebra-derivation` (Lie algebra and rational-actions paragraphs) and Milne, *Algebraic Groups* (2017), Chapter 10; restored the inherited hypotheses that (k) is algebraically closed of characteristic zero.
- Step 1: checked the dual-number tangent description and linear-space operations; its elementary status is appropriate.
- Step 2: checked against `lem-wf-mixed-commutator-tangent`; the two-parameter base change and coefficient extraction are stated explicitly.
- Step 3: checked against `def-wf-lie-algebra`; bilinearity, alternation, and Jacobi are direct associative-algebra expansions and are elementary.
- Step 4: checked the group-homomorphism calculation in Milne Chapter 10; replaced the unsupported generic `LieHom.map_lie` citation with the explicit two-parameter commutator expansion for (r), including linearity of (dr).
- Step 5: checked against the commutator clause of `def-wf-lie-algebra`; the displayed matrix formula is an immediate definition expansion.
- `lem-wf-mixed-commutator-tangent`: checked on zero vectors and the trivial subgroup, and for the coefficient map (k[\\eta]/(\\eta^2)\\hookrightarrow k[\\varepsilon,\\delta]/(\\varepsilon^2,\\delta^2)); repaired the statement to be self-contained and to avoid misidentifying tangent vectors with Lie-algebra definitions.
- `lem-wf-liehom-map-lie`: removed as an unnecessary Mathlib leaf; the item does not obtain that its differential is a Lie homomorphism from the generic theorem, and the needed identity is proved directly.

Changes made: narrowed the item to the source's algebraically closed characteristic-zero setting, made the mixed-commutator statement self-contained, removed the invalid generic LieHom dependency, and synchronized `proof_deps` and `citations.json`.
