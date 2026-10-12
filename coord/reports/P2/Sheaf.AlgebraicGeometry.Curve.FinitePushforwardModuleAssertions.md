## What changed

Repaired the landing rejection by removing the private declarations
`AlgebraicGeometry.comparison_properties`, `AlgebraicGeometry.finite_counit_epi`
and `AlgebraicGeometry.finite_pullback_properties` from the item. The sibling
versions are private and cannot be used through an import. Their public theorems
specialize to CurveCoefficientPair and integral coefficients, whereas this item
allows arbitrary commutative coefficient rings. No sibling interface was changed.

The torsion reflection proof now proves its needed counit epimorphism locally.
The target proof specializes the finite pullback comparison to the particular
underlying abelian sheaf A, using finite exchange and the edge-map identity. Its
function-comparison argument is local at the cohomology universe. No duplicate
library theorem is declared. All four proof imports remain used.

Both delivered modules compile through lcompile.py --all. The original public
signature is unchanged. The target docstring's constructibility argument is
corrected to the direct-summand reduction already described by the helper/node.

## Proved and sorry left

Closed by decomposition:
`AlgebraicGeometry.IsCurve.Assertions.of_finite_pushforward_module`
(node b3-finite-pushforward-module-assertions).

One hole split off in the inherited delivery remains:
`AlgebraicGeometry.Scheme.isConstructibleSheaf_of_finite_lowerStar_module`
(node p2-finite-pushforward-module-constructible-reflection).
This is the only textual sorry in the delivered modules. No further holes were
added in this repair. The target is proved from this strictly smaller coefficient
step and the existing imported declarations, rather than claimed axiom-free.

## No longer needed

The three duplicate private helper declarations listed above are removed.
No existing import or DAG node is pruned. The original module had no proof imports;
the four proof imports added by the decomposition remain necessary. No unit
statement or realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

The landing checker identified identical private statements in sibling modules.
Although these are inaccessible to importers, redeclaring them fails its duplicate
statement check. The repair removes the declarations and specializes their
arguments inside the existing proofs instead. No dummy hypothesis or renamed
copy is used to evade the check.

The original quotient argument for arbitrary-ring constructibility was insufficient:
the general subquotient result requires Noetherian coefficients. The inherited
helper uses finite stratification and direct summands instead, preserving arbitrary
coefficients. Its mathematical proof and DAG dependencies remain unchanged.

## New nodes

The inherited node p2-finite-pushforward-module-constructible-reflection remains
the single strictly smaller constructibility step for C4 and C5. No additional
node is introduced by this repair.

Change record: coord/changes/finite-pushforward-module-constructible-reflection.md.

## Second reading by P2

1. Compared the item with the repository by diff and compared the existing theorem
   signature byte for byte: identical. The only existing public declaration is
   unchanged in parameters, hypotheses, conclusion, and visibility. There are no
   changed definitions. The new coefficient lemma is declared in the change record.
   Verdict: pass.
2. Compiled both delivered modules in import order through lcompile.py --all,
   without errors or warnings. Scanned both files: the single named constructibility
   theorem is the only sorry; no forbidden declarations or implementation escapes,
   and no definitions selecting data from unproved existence. Compiled a scratch
   copy with #print axioms: the private torsion reflection uses only propext,
   Classical.choice, and Quot.sound; the target and constructibility lemma also
   use sorryAx. Verdict: valid decomposition, not an axiom-free proof of the target.
3. Read the complete constructibility argument against the actual finite-generation
   definition. The projector argument works over arbitrary rings: finitely many
   generator images locally determine the projector, and its image is finitely
   generated. The existing constant-sheaf morphism lemmas provide the local linear
   maps, without requiring a Noetherian coefficient ring. Generic finite-algebra
   splitting and topological invariance justify the source pieces; the remaining
   closed fibres are finite unions of algebraically closed points after reduction.
   Checked empty source/fibres, zero sheaves/ring, identity maps, nonreduced curves,
   zero-dimensional components, and inseparable finite maps. This is strictly the
   C4/C5 coefficient step, not a restatement of the eight assertions. Independent
   leanfinder search for retracts of locally constant finitely generated module
   sheaves, Loogle search for Module.Finite and LinearMap.range, and Mathlib grep
   for locally constant retracts found no complete replacement. Loogle does supply
   Module.Finite.range for the elementary image-finiteness step. Searched lean/:
   of_retract requires Noetherian coefficients, while the existing coefficient
   control theorem is specialized to integral torsion coefficients. Verdict: true,
   needed, strictly smaller; not closable by an existing theorem in a few minutes.
4. Read the proof from its eight-clause conclusion downwards. Finite edge
   bijectivity handles C1--C5, and the commuting edge square handles C6--C8.
   All four proof imports are plain imports and used. The helper's public imports
   supply its signature. The old node's proof_deps is empty, so there is no old
   dependency to list as pruned. Read sk-thm-p1.json realized: no unit realization
   is bypassed or changed. Verdict: pass; no further pruning found.
5. Checked both node statements and Lean records, every listed proof dependency,
   their Lean declarations or Mathlib matches, and the union of step uses. The
   existing node records the actual torsion, edge-map, coefficient, and pullback
   reductions. The new node has source, natural-language proof, searches, origin,
   creation, blueprint, chapter/unit, and verbatim Lean statement. Verdict: pass.

Changes in this second reading: added this independent review and recorded fresh
searches and axiom checks. No Lean proof or statement needed repair. One original
hole is closed by decomposition and one named lower hole remains; no additional
holes were introduced, and no module is pruned.
