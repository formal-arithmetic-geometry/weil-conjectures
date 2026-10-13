## What changed

Proved the original declaration
AlgebraicGeometry.affineSpectrum_baseChange_mate_compatibility from three
strictly smaller spectrum identities and the proved evaluation of the actual
counit-defined mate. Its signature and original docstring are unchanged.

The calculation is a fully proved private categorical helper in the original
module. It expands the source component, evaluates the spectrum mate, uses
pullback-square coherence and naturality, cancels the spectrum unit, and applies
the single-morphism counit identities. Cancellation of the target coordinate
isomorphism and injectivity of the adjunction Hom equivalence finish the proof.
The source coordinate is passed intact with its defining equality proved by
reflexivity, preventing expansion of the large derived definitions.

SchemeDerivedMateEvaluation names the existing selected adjunction and
composition comparison and their square comparison. These definitions contain
real construction bodies; their data are the same pinned universal-property
choices as the existing base-change map. A generic four-factor evaluation lemma
proves schemeDerivedMate_evaluation. AffineSpectrumComparisonCancellation names
the inverse component of the existing spectrum equivalence unit. No existing
definition, statement, visibility, or target was changed. There are no forced
adaptations or change records.

Updated the parent node to the implemented argument and added four node records
for the supporting modules. Every parent proof import is used. The unit's
statement and steps are preserved; this is a refinement below its level.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.affineSpectrum_baseChange_mate_compatibility
(lem-pc-affine-spectrum-mate-compatibility).

Also proved AlgebraicGeometry.schemeDerivedMate_evaluation
(lem-pc-scheme-derived-mate-evaluation). Every private helper is proved.

Added exactly three named public holes, each the whole proof of its declaration:

- AlgebraicGeometry.affineSpectrum_counit_compatibility
  (lem-pc-affine-spectrum-counit-compatibility), a one-morphism counit identity.
- AlgebraicGeometry.affineSpectrum_comparison_cancellation
  (lem-pc-affine-spectrum-comparison-cancellation), a one-morphism unit identity
  containing no mate or direct-image map.
- AlgebraicGeometry.affineSpectrum_pullback_square_coherence
  (lem-pc-affine-spectrum-pullback-square-coherence), a comparison identity for
  arbitrary coefficient morphisms, containing no counit or mate.

This is a decomposition: one upper hole closed and three lower holes added,
net minus two. There is no sorry in the original module or in any definition.
Each remaining hole has its source and complete natural-language proof in its
own module and matching node. Identities, empty schemes, zero rings, and zero
coefficient objects introduce no extra hypotheses or exceptional cases. For the
unit identity, the proof explicitly handles Equivalence.mk's adjointified unit
using coherence, the triangle identity, and uniqueness with the fixed counit.

Validation: all five modules compile in import order through lcompile.py. The
parent compiles in about four seconds; the evaluation module compiles in about
44 seconds. The first required dry run also compiled every module and ran the
axiom probes. Its only worker-side static issue was temporary local attributes;
these have been removed, and the unchanged parent compiles in 3.4 seconds.
The second reader supplies the mandatory independent-reading section.
Nothing is pushed by this worker.

## No longer needed

Removed the unused public import
Sheaf.AlgebraicGeometry.SchemeDerivedMateEvaluation from the new
AffineSpectrumComparisonCancellation module and its corresponding statement
dependency. Its statement and construction use only the coordinate definitions.

Discarded the earlier attempt's unused canonicalSchemeDerivedBaseChangeMap,
schemeDerivedBaseChangeMap_eq_canonical, affineSpectrumDirectImageComponent,
affineSpectrumSourceHom, source_expansion, and coordinate_naturality helpers.
None is present in the delivery. The canonical mate is evaluated directly.

The parent no longer directly uses the large composition-existence proof in its
calculation; the three explicit spectrum identities are the next proof items.
The node lem-pc-ringed-spaces-derived-pullback-composition and its module
Sheaf.AlgebraicGeometry.DerivedPullbackComposition remain transitively required
by the coordinate constructions and the new identities. No pre-existing module
or original public import is globally pruned. Every retained parent import
supplies a declaration used by the proof or its unchanged statement.

## Where the brief, the DAG or earlier work was wrong

The saved attempt had not passed its compilation limit. Replacing mates by
expanded definitions and retyping projected coordinate components led the
kernel to normalize large derived direct-image objects. A fully proved
categorical helper with the intact source isomorphism avoids these conversions;
its defining equality and the defining mate formula are checked by reflexivity.
No compilation limit was increased, no statement was weakened, and no library
file was split to evade the limit. All calculations remain in the original
module; the three new holes are mathematical parts of the argument.

The saved cancellation proof sketch omitted that Equivalence.mk adjointifies
its unit. Its new docstring and node now explain why composition coherence
makes that unit equal to the original composition unit. The saved Lean records
were stale after changes to component helpers; they now contain the exact
current declaration signatures.

Mathlib searches provide generic adjunction, conjugation and scheme-naturality
building blocks, without the three derived spectrum identities. The earlier
LeanSearch query failed with an internal-server error and is recorded as
unavailable, not as a negative search result.

## New nodes

lem-pc-scheme-derived-mate-evaluation, module
Sheaf.AlgebraicGeometry.SchemeDerivedMateEvaluation: proved evaluation of the
specified counit-defined mate with the exact canonical data named.

lem-pc-affine-spectrum-counit-compatibility, module
Sheaf.AlgebraicGeometry.AffineSpectrumCounitCompatibility: the smaller
single-morphism compatibility with the pinned counit.

lem-pc-affine-spectrum-comparison-cancellation, module
Sheaf.AlgebraicGeometry.AffineSpectrumComparisonCancellation: the smaller
single-morphism compatibility with the constructed inverse unit.

lem-pc-affine-spectrum-pullback-square-coherence, module
Sheaf.AlgebraicGeometry.AffineSpectrumPullbackSquareCoherence: the pullback
comparison identity around the commuting prism, for arbitrary M, N and k.

All three unproved identities are used by the complete categorical argument;
none repackages the parent conclusion. No change records are needed.

## Second reading by K3

1. **Interface unchanged.** I diffed the delivered parent module against the repository version. The existing target declaration has the same signature and docstring; the added files contain only the three split statements and the proved evaluation helper. No definitions or target statements were altered.

2. **Proof and hygiene.** I compiled all five delivered modules with `lcompile.py --all`. The parent and evaluation theorem have no `sorry`; the only remaining `sorry`s are the three named public split theorems, each with a source, proof docstring, and matching DAG node. No forbidden declarations or hollow definitions occur.

3. **Split statements.** I read each split theorem and its node. Counit compatibility, comparison cancellation, and pullback-square coherence are strictly smaller than the parent mate equation, have no extra hypotheses, and are not duplicate library declarations. Their edge cases are covered by the categorical identities described in their docstrings.

4. **Pruning and route.** The parent proof uses every retained import and every listed proof dependency. The removed aliases and unused import are recorded above. The proof keeps the unit route through the explicit counit, cancellation, and square-coherence steps; the unit record remains unchanged.

5. **DAG agreement.** I checked the parent node proof and `proof_deps` against the implemented helper and its instantiation, and checked that each new node records the exact Lean module, declaration, statement, source, and split status. The node metadata agrees with the current files.

I found no repair necessary in the delivered code. The only change from the first reading is this independent-reading report section.
