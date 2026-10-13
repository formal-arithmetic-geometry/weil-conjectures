## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.DerivedRestrictionEvaluationMatePostcompBijective`
with an explicit composition of Hom-set equivalences. Added a proof-only import of
`Sheaf.AlgebraicGeometry.DerivedOpenTensorTestObjects`. This new module isolates the
extension-by-zero/tensor-stability part of the original plan. The original signature,
visibility, public import and docstring are unchanged. Mathlib `Iso.homFromEquiv` supplies the elementary categorical transport.

The proof uses canonical tensor-Hom naturality on X and U, cancels the supplied tensor
comparison's naturality equation, and cancels the initial restriction bijection. It
requires neither a normalized tensor comparison nor tensor-unit coherence.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.derivedRestriction_evaluationMate_postcomp_bijective`
(blueprint `lem-sc-derived-restriction-evaluation-mate-postcomp-bijective`).
No sorry remains in the assigned module.

Added one hole:
`AlgebraicGeometry.Scheme.exists_derivedOpen_tensorTestObject`
(blueprint `lem-sc-derived-open-tensor-test-objects`), in
`Sheaf.AlgebraicGeometry.DerivedOpenTensorTestObjects`.
Its entire proof is `by sorry`. It states the geometric test-object property, without
internal Hom, evaluation, or tensor comparisons. The docstring and node specify its
construction by exact derived extension by zero and the stalkwise counit argument.
This is a decomposition: one upper hole closed, one lower hole added, net zero holes.

## No longer needed

No original import was removed: the assigned module originally had only the public
import `Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom`, which its statement needs.

The assigned theorem no longer directly uses these planned dependencies:
- `lem-sc-derived-open-restriction-adjunction-exact` /
  `Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact`;
- `lem-pc-kflat-resolution` / `Sheaf.Algebra.Homology.KFlatResolution`;
- `lem-pc-kflat-derived-tensor-comparison` /
  `Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison`;
- `lem-sc-derived-tensor-stalk-vanishing` /
  `Sheaf.AlgebraicGeometry.DerivedTensorStalkVanishing`.

These are still needed by the geometric lemma's proof plan, and KFlatResolution is
also used by CanonicalDerivedTensorHom. This delivery therefore claims no globally
pruned module. The canonical tensor-Hom dependency remains. No unit statement or
realized proof step is bypassed (the unit's realized lists are empty).

## Where the brief, the DAG or earlier work was wrong

The assigned proof plan's dependencies describe the ingredients, but do not directly
state the tensor-stable geometric Hom-bijection needed to combine them. The new node
makes this step precise. All hypotheses of the assigned declaration are preserved.

Stacks Tag 08BS states preservation of K-injectivity under open restriction; the
explicit derived extension-by-zero adjunction is Tag 08BT. The geometric lemma cites
08BT, 00A7 and 06YB, read on the Stacks website because the named local TeX files are
absent from this checkout. Its deduction of tensor-stable test objects is marked as
an agent argument based on those sources, rather than attributed verbatim to Stacks.

Edge cases: for U empty the derived category on U is zero and B=0 works; for U=X,
restriction is an equivalence and B is its inverse image of A. For general U the
exact extension construction and stalk calculation impose no boundedness, compactness,
finite presentation or closed-support hypothesis. The existential witness is used
only locally in a theorem proof; no definition chooses arbitrary data from this hole.

Searches: LeanFinder returned scalar-change adjunction and tensor-product results;
Loogle found the generic Adjunction.homEquiv; the Mathlib CategoryTheory grep returned
no extension-by-zero result. LeanSearch was unavailable (Internal Server Error).
The blueprint search found analogous finite-coefficient pro-etale projection formulas,
but none for the scheme's Zariski structure-module derived category used here.

## New nodes

`lem-sc-derived-open-tensor-test-objects`:
`dag/nodes/sec-picard-framework/lem-sc-derived-open-tensor-test-objects.json`, module
`Sheaf.AlgebraicGeometry.DerivedOpenTensorTestObjects`, declaration
`AlgebraicGeometry.Scheme.exists_derivedOpen_tensorTestObject`. It isolates extension
by zero, its invertible unit, and tensor stability of its essential image. The source,
complete proof steps and actual Mathlib searches are recorded. No change record is
needed: no existing interface is changed, and the new import is proof-only.

## Second reading by S3

1. PASS: compared the complete module diff with the repository. The existing
   theorem signature is byte-for-byte identical, including all universes,
   instances, the arbitrary comparison t and its sole naturality hypothesis.
   Its visibility, original public import and docstring are unchanged. There
   are no changed definitions or statement-change records to review.
2. PASS: compiled both modules individually in dependency order using lcompile.py.
   The assigned theorem has no sorry. The only added hole is the public named
   theorem exists_derivedOpen_tensorTestObject, with its entire proof `by sorry`.
   No forbidden declarations or hollow definitions occur. Scratch copies with
   #print axioms were checked; dependency holes contribute sorryAx, and no
   nonstandard axiom is introduced. Existential B and i are eliminated locally
   inside a proof; no definition chooses arbitrary data from an unproved theorem.
3. PASS: independently checked the geometric lemma against Stacks
   [08BT](https://stacks.math.columbia.edu/tag/08BT),
   [00A7](https://stacks.math.columbia.edu/tag/00A7), and
   [06YB](https://stacks.math.columbia.edu/tag/06YB).
   Exact extension by zero is fully faithful after deriving; its essential image
   consists of objects with vanishing cohomology stalks outside U. Derived tensor
   preserves this property by K-flatness. The counit and triangle identities
   identify the adjunction bijection with the actual restriction map on Hom.
   Empty U, U=X, A=0 and L=0 satisfy the statement without extra hypotheses.
   This lemma contains no internal Hom, mate or tensor comparison; the explicit
   naturality calculation in the assigned module is a genuine further argument.
   The docstring gives the construction and full proof, and its node matches.
   Independent LeanFinder search for fully faithful extension by zero and tensor
   ideals found only ordinary open restriction/direct-image adjunction results.
   Local searches found supported_open_extension, which requires perfect objects,
   quasi-coherence, affine opens and closed support, and hence cannot supply this
   unrestricted lemma. The existing planned dependency statements were read;
   none already states tensor-stable derived test objects.
4. PASS: followed e0, e1 and the equality he from the top downward. Naturality
   on X and U gives uncurrying through evaluation; cancelling ht yields hc;
   he identifies the composite with postcomposition by the exact displayed mate.
   Bijectivity then cancels e0. All four unused old proof dependencies are listed
   above; no globally pruned module is claimed. The unit sk-thm-picard-duality has
   empty realized statement and step lists, so no realized route is bypassed.
5. PASS: the existing node changes only proof, proof_deps and proof_origin.
   Its two dependencies are precisely the geometric lemma and canonical tensor-Hom
   family used by the code. The new node records the actual signature, source,
   complete geometric proof, dependency union, searches, provenance, chapter,
   unit and creation metadata required by brief-stage3 section 3.

Changes made by the second reader: removed the private precompEquiv implementation
and used Mathlib Iso.homFromEquiv.symm at both sites, without an additional import.
Reduced the new geometric module's public import from CanonicalDerivedTensorHomModel
to DerivedTensorStructure, which supplies its statement without importing the
unneeded internal-Hom and canonical pullback comparison framework. No theorem
statement, definition, geometric proof plan or hole count changed. This remains
one original hole closed and one strictly geometric hole split off, net zero.
