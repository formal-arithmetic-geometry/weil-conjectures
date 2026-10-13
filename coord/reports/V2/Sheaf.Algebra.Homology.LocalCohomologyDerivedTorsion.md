## What changed

Replaced the proof hole of
`ModuleCat.nonempty_localCohomology_iso_derived_torsion` with the source's
injective-resolution argument, keeping its signature and original public imports.
Three proof imports expose distinct parts of the argument:

- `ExtInjectiveResolutionComparison`: a natural comparison between projectively
  computed Ext and the Hom complex of an arbitrary injective resolution.
- `FilteredColimitCochainHomology`: a proved comparison between the colimit of
  cohomology modules and the cohomology of the degreewise colimit complex.
- `QuotientHomComplexColimit`: an explicit evaluation-at-one construction identifying
  the colimit of quotient-Hom complexes with the torsion subcomplex.

The main proof evaluates the functor-category colimit, whiskers the Ext comparison
by the quotient diagram, passes homology through the filtered colimit, maps the
explicit complex isomorphism through homology, and finishes with Mathlib's
`InjectiveResolution.isoRightDerivedObj`. No definition chooses data from an
unproved existence theorem. The natural comparison remains a proposition until
its isomorphism is obtained inside the theorem proof.

## Proved and sorry left

The intended reduction closes the one original hole:
`ModuleCat.nonempty_localCohomology_iso_derived_torsion`
(node `lem-sbc-local-cohomology-derived-torsion`).

The two structural component proofs are complete:
`ModuleCat.nonempty_colimit_homology_iso`
(node `lem-sbc-filtered-colimit-cochain-homology`) and
`ModuleCat.nonempty_colimit_quotientHomComplex_iso_torsion`
(node `lem-sbc-quotient-hom-complex-colimit`).

One new public theorem remains exactly `:= by sorry`:
`ModuleCat.nonempty_ext_iso_injectiveResolution_homology`
(node `lem-sbc-ext-injective-resolution-comparison`). It concerns arbitrary
modules in the first argument and an arbitrary injective resolution, independently
of ideals, torsion, filtered colimits, and the derived torsion functor. Its
naturality is part of its type and is what the upper proof needs. Its docstring
and node give the two double-complex augmentations and the comparison-map argument.

This is a decomposition: one upper hole closed, one lower hole added, net zero
holes; the torsion identification and colimit/homology interchange are proved.
The filtered-colimit theorem and scalar evaluation cocone compile locally, as
does a scratch version of the isomorphism composition with a general additive
functor. `#print axioms` for the filtered-colimit theorem and `homComplexDiagram` lists
only `propext`, `Classical.choice`, and `Quot.sound`. The required local dry run now compiles all five sandbox modules successfully; the previously missing baseline artifact was restored by compiling its unchanged repository source into the sandbox.

## No longer needed

No original import, node, or module is pruned: the only original proof dependency
was the torsion functor, which the proof still uses. No additional DAG-planned
lemma is bypassed. The unit record has no realized node for this item, and the
unit's route is retained. The general comparison does not require a finitely
generated ideal; the original `hJ` binder stays unchanged and is cleared only
inside the proof.

The new Ext-comparison module needs only the explicit injective resolution; it
imports neither `ModuleCat.EnoughInjectives` nor the right-derived-functor API.
The original module retains both original public imports for these APIs.

## Where the brief, the DAG or earlier work was wrong

The original DAG gave two proof paragraphs with no intermediate theorem for the
projective/injective Ext comparison, its naturality, or colimit/homology
interchange. The new nodes expose those parts without moving the entire original
statement under another name. The proof follows [Stacks Tag 0954](https://stacks.math.columbia.edu/tag/0954), read directly;
its displayed Hom-colimit calculation and exactness of filtered colimits agree
with this reduction.

An earlier shared compiled snapshot lacked
`Sheaf/Algebra/Homology/IdealPowerTorsionFunctor.olean`, although the assigned
module imports that baseline module. The unchanged repository source was copied
into this sandbox solely so `lcompile.py` could rebuild the missing local artifact;
this does not alter its declaration or proof. The required `deliver3.py ...
--no-push` dry run now compiles all five sandbox modules successfully. This was a
shared-build artifact issue, not a timeout or error in the proof.

New statements were checked at exponent zero, the zero and unit ideals, degree
zero, zero modules, and arbitrary (not necessarily finitely generated) ideals.
The evaluation construction includes all these cases without extra hypotheses.
Scratch proofs of the zero-ideal and unit-ideal primary-component equalities
compile; the scalar colimit cocone also passes the three-axiom check.
LeanSearch returned HTTP 500; this is recorded as unavailable. LeanFinder,
Loogle, local Mathlib/library searches and blueprint searches were also run.
The existing fixed-resolution sheaf Ext comparison uses `Abelian.Ext` rather
than the projectively defined `_root_.Ext`, and does not supply the needed
contravariant natural comparison.

## New nodes

`lem-sbc-ext-injective-resolution-comparison`, in
`lean/Sheaf/Algebra/Homology/ExtInjectiveResolutionComparison.lean`, carries the
one remaining general homological comparison and the explicit functor of Hom
complexes. Its source is the injective-resolution computation in Tag 0954.

`lem-sbc-filtered-colimit-cochain-homology`, in
`lean/Sheaf/Algebra/Homology/FilteredColimitCochainHomology.lean`, is proved using
module AB5, short complexes in a diagram category, pointwise homology, and the
explicit degreewise colimit complex.

`lem-sbc-quotient-hom-complex-colimit`, in
`lean/Sheaf/Algebra/Homology/QuotientHomComplexColimit.lean`, is the explicit
algebraic identification: evaluation at one, quotient scalar maps,
filtered-colimit recognition on underlying types, and evaluation in each degree
of a complex. No new axiom or hollow definition is introduced.

The original node's proof, proof dependencies and proof origin now follow these
three components. No existing statement, definition or visibility is changed;
there are no forced adaptations or change records.

## Second reading by V2

1. **Visible declarations and statements.** Compared every delivered module with
the repository versions. Existing declaration signatures, including the target,
are unchanged byte for byte; only proof imports and proof bodies changed.
Verdict: pass.

2. **Proof and axioms.** Compiled all five sandbox modules with `lcompile.py` and
ran the delivery preflight. There is one documented split theorem,
`ModuleCat.nonempty_ext_iso_injectiveResolution_homology`, with its matching DAG
node and proof docstring. No definitions contain `sorry`, and no forbidden
declarations occur. The completed declarations use only the permitted axioms.
Verdict: pass (with the existing unused `hJ` binder linter warning).

3. **Split statements.** Checked the three added node statements against their
Lean declarations and tested zero/unit ideals, exponent zero, zero modules,
degree zero, and arbitrary ideals. The Ext comparison is strictly more general
than the target and is the only remaining hole; the other two component results
are proved. Searches found no duplicate upstream declarations. Verdict: pass.

4. **Pruning and route.** The proof follows the unit's planned comparison,
filtered-colimit, and torsion-complex steps. All imports and proof dependencies
remain used; no node or module can be pruned. Verdict: pass.

5. **DAG agreement.** Node proof metadata and dependencies match the imports and
declarations used by the Lean proofs; each added theorem has a corresponding
node, source, docstring, and module record. Verdict: pass.

Changed during this reading: no Lean code or statements; appended this review
record only. The dry run was repeated after the review and still compiled all
modules successfully.
