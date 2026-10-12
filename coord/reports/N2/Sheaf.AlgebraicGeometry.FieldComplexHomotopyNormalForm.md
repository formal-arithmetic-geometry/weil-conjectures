## What changed

Repaired the false intermediate
AlgebraicGeometry.Scheme.Modules.homotopyEquiv_of_single_field_homology in
Sheaf.AlgebraicGeometry.FieldComplexHomotopyNormalForm by adding explicit negative-degree
homology vanishing. The previous counterexample helpers are preserved verbatim.
Its body now combines the two vanishing ranges, contracts onto its actual cohomology,
proves that a rank-r locally free sheaf on a field spectrum is the rank-r free sheaf,
and composes the two homotopy equivalences. The free-sheaf identification is proved
in private nonempty_iso_free_of_field_rank using a trivializing cover and the fact
that Spec R has a single point; no finite-dimensionality assumption is added.

Added the proof-only import Sheaf.AlgebraicGeometry.FieldComplexSingleCohomology.
The new module isolates only the vector-space contraction, independently of finite
rank and basis identification. Its sole theorem has a complete proof in words and
its own DAG node. Updated the repaired node and the caller's proof dependencies.
Adapted only the forced application in Sheaf.AlgebraicGeometry.FiniteFreeSingleFieldFibre;
its existing signature and visibility are identical. See
coord/changes/field-complex-negative-homology.md.

All three modules compile in import order with lcompile.py. The original caller
fails against the repaired dependency with the expected argument-type mismatch;
the adapted caller compiles. Zero-rank, acyclic, unbounded and arbitrary integer
concentration degrees are covered by the new contraction statement. The retained
rank-one complex in degree -1 fails the added hypothesis, exactly as required.
No target signature or definition changes, and the unit route is preserved.

## Proved and sorry left

The item's sole hole is closed after correction of its false signature:
AlgebraicGeometry.Scheme.Modules.homotopyEquiv_of_single_field_homology,
node new-field-complex-homotopy-normal-form. This is an interface repair plus a
one-hole decomposition, not a proof of the old false statement and not a net
reduction in the number of holes. The proved rank identification and composition
are actual Lean proofs, rather than a renamed copy of the original claim.

One hole is added and is the only sorry in this delivery:
AlgebraicGeometry.Scheme.Modules.homotopyEquiv_single_cohomology_of_field,
node new-field-complex-single-cohomology, in its own new module. It states only
contraction onto the actual cohomology and has no finite local freeness, rank,
free-sheaf target, or restriction to natural degrees. Its docstring gives the
complement choices and all three summand calculations for the homotopy equation.

No sorry remains in the item's module or its adapted caller. The pre-existing
sorry in imported AlgebraicGeometry.Scheme.Modules.single_field_fibre_homology
(node new-field-fibre-homology) is unchanged and not part of this delivery.

## No longer needed

None: no imports are removed and no formerly needed modules are pruned. The original
item node had no proof dependencies. SingleHomology and FreeComplex remain necessary
for the retained certified counterexample. The adapted caller still uses
FieldFibreHomology; its indirect FlatComplexDerivedPullback dependency remains needed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (old signature, now repaired): natural-degree vanishing does not
imply negative-degree vanishing. The rank-one free sheaf in degree -1 satisfies the
old hypotheses with i = r = 0 and cannot be equivalent to the proposed target.
The previous worker correctly found the obstruction but deferred the interface
repair. This delivery supplies it without changing any caller's hypotheses.
The old item plan also called the complex bounded even though its signature never
assumed boundedness. Vector-space splitting is degreewise and works unboundedly,
so a boundedness assumption is unnecessary. The caller's old DAG proof dependencies
did not record the field-homology and normal-form declarations actually used by
its Lean body; those dependencies now agree with the proof.

## New nodes

new-field-complex-single-cohomology isolates the contraction of a complex over a
field spectrum onto its sole homology sheaf. Its hypotheses omit the rank and local
freeness, and its target is the actual homology, so it is strictly a part of the
original splitting-plus-basis argument. The complement-based proof, including the
unbounded and acyclic cases, is recorded in the node and module docstring. LeanSearch
was unavailable, and LeanFinder, Loogle and source grep found no matching theorem.
The blueprint duplicate search found none. The change record is
coord/changes/field-complex-negative-homology.md.

## Forced adaptations

Sheaf.AlgebraicGeometry.FiniteFreeSingleFieldFibre is unclaimed. Its original line 58
fails against the repaired dependency:

```text
Application type mismatch: h.right has type
(Q.homology i).IsFiniteLocallyFreeOfRank r
but is expected to have type
∀ q < 0, IsZero (Q.homology q)
```

Replaced only this final application (lines 58 onward) with the same application
supplying negative vanishing, preceded by installing the existing hge as a local
instance and inferring strict nonnegative support for termwise pullback. Each added
line supplies the newly required argument from existing hypotheses; every existing
signature and visibility is unchanged. An independent lcompile.py run of the original
against the sandbox overlay failed with the above error; the delivered adaptation
compiled in the same overlay.

## Second reading by N2

1. Compared both existing modules with the repository using diff. The only public
signature change is the declared negative-homology assumption, justified by the
retained certified counterexample and recorded in field-complex-negative-homology.md.
All caller signatures and counterexample helper signatures and bodies are identical.
No definition or target is changed. Repaired the change record: both Old and New
signatures had been truncated at the free-sheaf named argument and now appear whole.

2. Independently compiled all three delivered modules in import order: no errors
or warnings. Source scanning finds exactly the reported public contraction theorem
with sorry, and no forbidden declarations or hollow definitions. Scratch #print axioms
checks show only propext, Classical.choice and Quot.sound for all four private
helpers, including the free-sheaf identification. The normal-form theorem also
uses sorryAx solely through the recorded contraction theorem. The split-off theorem
uses the same three standard axioms and sorryAx. The caller's axiom check and the
delivery tool's complete declaration probe are also run before delivery.

3. Read the split-off theorem, its source, full docstring proof and new node.
The complement construction is valid for arbitrary vector spaces, all integer
concentration degrees, the zero complex, rank zero, acyclic complexes and unbounded
complexes. The existing proved global-sections equivalence over a field supports
the transport argument. No data is chosen from an unproved existence statement
in a definition. This is a genuine contraction subproblem: the rank-r free-sheaf
identification and composition are proved separately, not assumed under a renamed
copy of the item. Independent LeanFinder search for semisimple-category splitting,
Loogle search for HomologicalComplex/IsSplit, and source searches using semisimple,
contractible and homology/splitting found no direct replacement. In particular,
the upstream private exists_quasiIso_of_zero_differential in DerivedCategory.Perfect
gives a quasi-isomorphism, not the required homotopy equivalence. Closing the
remaining contraction is not a short application of the results found.

4. Read the proof top-down: integer vanishing, contraction, proved rank
identification, composition. All imports are needed for signatures, these steps,
or the retained certified counterexample; there were no old proof_deps to prune.
The unit sk-thm-picard-perfect and its realized fields are untouched, and the
existing field-fibre route is kept. Independently compiled the original caller
against the repaired sandbox dependency: it fails exactly at the former h.2
argument, now expected to supply negative vanishing. The adapted caller compiles
and derives this argument only from its pre-existing hge support assumption.

5. Read all three delivered node files and compared existing nodes with their
repository versions. The normal-form proof_deps names only the contraction;
the caller names field-fibre homology and the repaired normal form. Their proof
steps and proof_origin agree with the Lean argument. The new node contains its
source, searches, creation and blueprint records, full contraction argument and
matching Lean signature. The statement_change records the original false
statement; its empty citers list agrees with the original DAG, whose caller
previously omitted this dependency.

Second-reading changes: completed both verbatim signatures in the change record
and added this review. No Lean proof or signature needed a further repair.
The delivery closes one corrected upper hole and adds one strictly simpler lower
hole; it is an interface repair and decomposition, with zero net holes closed.

## Forced adaptations

### Sheaf.AlgebraicGeometry.FiniteFreeSingleFieldFibre
Original against changed dependencies failed:
```
/tmp/forced-adaptation-yc03en10/lean/Sheaf/AlgebraicGeometry/FiniteFreeSingleFieldFibre.lean:58:60: error: Application type mismatch: The argument
  h.right
has type
  SheafOfModules.IsFiniteLocallyFreeOfRank
    ((((pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homology ↑i) r
but is expected to have type
  ∀ q < 0, IsZero ((((pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homology q)
in the application
  homotopyEquiv_of_single_field_homology hR (((pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) i r h.left
    h.right

(with the modules compiled into /tmp/forced-adaptation-yc03en10/.lbuild) [3.1 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
