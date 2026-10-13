## What changed

Proved `AlgebraicGeometry.Scheme.affine_open_perfect_source_model` with its existing
signature and visibility unchanged. The proof constructs the exact affine sheaf
equivalence, transports a derived localization in the supplied Hom universe,
identifies the inverse restriction with derived open pullback, and applies the
existing perfect affine bounded-projective criterion. The final isomorphism is
an explicit composition of the given comparison at P, the constructed termwise
comparison, the transported model isomorphism, and the derived counit.

Two proved private helpers handle exact realizations of derived pullback and
localization size transfer. The former uses the left-derived universal property
as in the private `perfect_exactOpenRestriction` proof of
`PerfectRestrictionClassesSmall`, generalized to the composite open immersion.
The latter uses Mathlib's equivalence invariance of local smallness and
`hasLocalizationOfLocallySmall`. Neither introduces unproved data or a hole.

Added proof imports `DerivedOpenLocalization`, `DerivedPullbackPerfect`,
`PerfectImpliesQCoh`, the source derived `ExactFunctor` API, and Mathlib's
`PointwiseLeftDerived` and `LocallySmall`. Updated the existing node's proof,
proof dependencies, and proof origin. The unit's realized statement and steps
are unchanged. No definition or public interface changed.

Read Stacks Tags [08EB](https://stacks.math.columbia.edu/tag/08EB),
[06Z0](https://stacks.math.columbia.edu/tag/06Z0), and
[09UA](https://stacks.math.columbia.edu/tag/09UA). Search with LeanFinder,
Loogle, logged Mathlib grep, and local source grep found the bounded-projective
criterion and derived-pullback preservation already available, but no exact
open-site theorem. The proof handles empty opens and the zero ring using the
same equivalences, without choosing a point or imposing extra bounds.

Single-file `lcompile.py` compilation passes without warnings; final dry-run
validation is through the required `deliver3.py --no-push`.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.affine_open_perfect_source_model`
(node `lem-sc-affine-open-perfect-source-model`).

Proved both new private helpers `perfect_exact_pullback` and
`localization_on_source`. No `sorry` remains in the item and none was added.
This is one hole closed, zero split off, not a decomposition. Existing imported
proof dependencies retain their own downstream proof status.

## No longer needed

Removed proof imports and corresponding direct proof dependencies:

- `Sheaf.AlgebraicGeometry.OpenDerivedRestrictionComparison`
  (`lem-pc-open-derived-restriction-comparison`): the support, Hom, and
  quasi-coherence comparisons are unnecessary. The needed localizations are
  constructed directly through the sheaf equivalence and local smallness.
- `Sheaf.AlgebraicGeometry.AffineLocalizedSiteDerivedTransport`
  (`lem-pc-affine-localized-site-derived-transport`): construct the specific
  equivalence and its tilde comparison directly from the exact-functor API,
  so its inverse is visibly the exact restriction used in the perfectness proof.
- `Sheaf.AlgebraicGeometry.SchemeIsoPerfectTransport`
  (`lem-pc-scheme-iso-perfect-transport`): perfectness follows from derived
  pullback along the composite open immersion.

These three modules and nodes are no longer direct dependencies of this proof;
no assertion is made that other targets or modules no longer use them.
The two original public imports are retained as statement dependencies.

## Where the brief, the DAG or earlier work was wrong

No false statement or source error was found. The old plan did not expose a
perfectness clause in `open_derived_restriction_comparison`; its signature only
provides quasi-coherence, support, orthogonality, and zero-object comparisons.
The missing perfectness bridge is supplied by existing derived-pullback
preservation, with an explicit uniqueness-of-derived-functor comparison.
The original existential affine transport theorem hides the specific inverse
functor, so this proof constructs the equivalence instead of assuming its
existential witness has an additional perfectness compatibility.

Lean distinguishes the category instances of `Scheme.Modules` and the explicit
`SheafOfModules` carrier. Annotating tilde with the latter codomain, then
transporting its additivity instance, makes the localized comparison use exactly
the intended category instance. No downstream adaptation was necessary.

## Second reading by W3

1. PASS: compared the complete module and node against the repository versions.
   The existing `affine_open_perfect_source_model` signature is byte-for-byte
   unchanged, including both localization hypotheses, the arbitrary realization
   functor, its comparison, and all four conclusions. The two original public
   imports remain public. No definition, existing visibility, or target changed;
   there are no change records or forced adaptations.
2. PASS: independently compiled the delivered file with `lcompile.py`, without
   errors or warnings. Scanned the whole file: no `sorry`, forbidden declaration,
   or forbidden implementation attribute occurs, and all lines meet the width
   limit. A scratch copy with `#print axioms` reports `propext`,
   `Classical.choice`, `Quot.sound`, and inherited `sorryAx`. Thus the local hole
   is closed, while imported unfinished proofs remain; this is not a claim that
   the theorem's entire import closure is proved. The delivery probe additionally
   checks every declaration. The affine equivalence and localization are explicit
   constructions; the chosen derived pullback has its left-derived universal
   property, and the open-localization existence theorem supplies a proved
   construction. No arbitrary object is chosen from an unproved mere existence.
3. PASS: no statement was split off and no new public statement or node was added.
   Read both private helpers. Exactness transfers across the displayed natural
   isomorphism, and left-derived uniqueness gives the correct comparison direction.
   The source localization uses equivalence-invariance of local smallness and
   Mathlib's actual localization construction. Empty schemes, the empty affine
   open, and the zero ring need no extra premise at any step. Independently read
   Stacks Tags [08EB](https://stacks.math.columbia.edu/tag/08EB),
   [06Z0](https://stacks.math.columbia.edu/tag/06Z0), and
   [09UA](https://stacks.math.columbia.edu/tag/09UA): affine perfectness and
   pullback preservation supply exactly the mathematical reductions used here.
4. PASS: independently searched local Lean sources for perfectness under derived
   functors, restrictions, and isomorphisms, and ran logged Mathlib grep for
   `mapDerivedCategory.*IsPerfect|IsPerfect.*mapDerivedCategory|leftDerivedUnique|hasLocalizationOfLocallySmall`.
   The existing private open-restriction argument is correctly generalized;
   the affine bounded-projective criterion is reused rather than duplicated.
   Each added import supports a proof API; neither public import is proof-only.
   The three removed old dependencies are all listed under No longer needed.
   Read `dag/units/sk-thm-picard-duality.json`: none of the removed nodes occurs
   in its realized fields, which are unchanged. This is a reduction below the
   unit level and does not replace a unit statement or step.
5. PASS: the only changed node fields are `proof`, `proof_deps`, and
   `proof_origin`. Read the declarations associated with the revised dependencies:
   the derived-localization construction, derived pullback and its perfectness
   preservation, perfect-implies-quasi-coherent, the affine bounded-projective
   criterion, and affine sheafification. The four proof steps match the Lean:
   build the equivalence/localizations, transfer perfectness to C, obtain P,
   and compose the comparison at P with the transported model and counit.
   The removed three dependencies are unused, and no new-node obligations arise.

Changes by the second reader: appended this independent review and recorded the
inherited `sorryAx` limitation explicitly. No repair to the Lean proof or DAG was
necessary. Holes closed: `AlgebraicGeometry.Scheme.affine_open_perfect_source_model`;
holes added: none. Local file compilation and the scratch axiom check pass.
