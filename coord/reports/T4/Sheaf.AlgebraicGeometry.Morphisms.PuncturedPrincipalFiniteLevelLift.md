## What changed

The existing theorem `AlgebraicGeometry.Scheme.punctured_principal_finite_level_lift`
keeps its signature and now follows from a finite-stage scalar-image comparison,
by induction over consecutive restriction maps. Its original public imports are
unchanged; the new comparison module is a plain proof-only import.

Added `Sheaf.AlgebraicGeometry.Morphisms.PuncturedPrincipalEventualScalarImage`.
It constructs `puncturedPrincipalSectionRestriction` by recursion and states the
remaining comparison as `punctured_principal_eventual_scalar_image`. The
comparison has a complete natural-language proof and a matching DAG node.
Updated the parent node's proof, proof_deps and proof_origin to the actual route.
No existing statement or definition changes; no change records are needed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.punctured_principal_finite_level_lift`
(node `lem-sbc-punctured-principal-finite-level-lift`).

Added one hole:
`AlgebraicGeometry.Scheme.punctured_principal_eventual_scalar_image`
(node `lem-sbc-punctured-principal-eventual-scalar-image`). Its whole proof is
`by sorry`. This is the finite-stage pro-zero cokernel comparison, not another
statement about compatible infinite families. The restriction function is a
concrete composition of the existing transitions and contains no sorry or
choice of a witness from an unproved theorem.

This is a decomposition: one original hole closed, one lower hole added,
net zero holes closed. No target is claimed to be axiom-free. Both theorem
axiom checks permit `sorryAx` from the explicitly recorded remaining comparison;
no additional axiom is introduced. The restriction construction uses only
standard axioms. Every delivered module compiled individually, in import order.

## No longer needed

Removed the first worker's unsubmitted
`punctured_principal_finite_level_lift_core`, its node
`lem-sbc-punctured-principal-finite-level-lift-core`, and the unused private
`punctured_principal_scalar_restriction_transition`. The core was merely a
classical-choice reformulation of the original theorem.

Every old direct proof dependency of the parent is now handled inside the
comparison node's mathematical proof plan:
`def-weil-pbc-depth`, `def-weil-pbc-noetherian-ring`,
`def-weil-pbc-scheme-conventions`,
`lem-sbc-depth-two-puncture-global-sections`, and
`lem-sbc-finite-etale-adic-sections-transfer`.
They are retained as dependencies of the new comparison node, not abandoned
mathematical inputs. The parent now depends directly on
`lem-sbc-punctured-principal-eventual-scalar-image`.
No existing imports removed and no existing modules pruned.

## Where the brief, the DAG or earlier work was wrong

The first worker's claim that simultaneous representatives were a strictly
stronger reduction was incorrect: classical choice converts the original
pointwise existentials into exactly that function of representatives. Its
sorry docstring contained no proof, the target's docstring was accidentally
attached to the private helper, and the parent node was not updated to the
Lean proof. The second reading repaired all three faults.

The first four steps of the original plan supply a genuine finite-stage
comparison; the fifth step is now formalized, including iteration of
compatibility rather than a renamed application of the whole goal.
The derived-cohomology comparison itself remains to be formalized.

## New nodes

`lem-sbc-punctured-principal-eventual-scalar-image` records the finite-stage
cokernel comparison, in its own new module. For each n a uniform finite gap k
makes every section at n+k restrict into the scalar image at n. This isolates
the pro-zero comparison before using an infinite compatible family.
Its `lean.declarations` also records the concrete recursive restriction.
Searches used different wording from the first worker: Lean Finder for
eventual images and local cohomology, Loogle for localCohomology, and grep for
pro-zero/eventual section infrastructure. LeanSearch was also attempted and
returned Internal Server Error; no absence conclusion is drawn from it.
None of the available searches supplies this depth-three
punctured comparison. Repository searches also checked the separate
restriction-kernel theorem: it concerns injectivity, not the required image.

Sources checked directly:
[0H3E](https://stacks.math.columbia.edu/tag/0H3E),
[0BK0](https://stacks.math.columbia.edu/tag/0BK0), and
[0AVY](https://stacks.math.columbia.edu/tag/0AVY).
The docstring explains the finite-stage consequence, without claiming that
the source states this Lean formula verbatim.

## Second reading by T4

1. PASS. Compared every delivered existing declaration with the repository.
   The target signature is byte-for-byte unchanged; public imports and existing
   definitions are unchanged. The only import addition is proof-only. No
   consumer-visible interface or target meaning changes.
2. PASS with the recorded remaining hole. Both files compiled locally in
   dependency order through lcompile.py. Scratch `#print axioms` checks covered
   the target, the new comparison and the concrete restriction. No forbidden
   declaration, hidden sorry, hollow definition or nonstandard added axiom.
3. REPAIRED. Removed the equivalent simultaneous core. The replacement is the
   finite-stage cokernel step of the original plan, with a uniform gap and
   arbitrary single sections; it has its own module, node and full proof in
   words. Checked g=0 (k=0 and Hartogs), nilpotent g (late source is W), and
   k=0 (restriction definition is identity). No regularity of g is assumed;
   annihilator stabilization handles zero divisors. An empty puncture of a
   nonzero depth-three local ring is excluded by the dimension/depth bound.
   Searches found infrastructure but no duplicate image comparison. The
   remaining derived-cohomology proof cannot be closed by a short existing
   lemma found in these searches.
4. PASS after repair. The target uses precisely the finite-stage comparison
   and an induction on the restriction gap. Removed the unused helper. Both
   original public imports supply names in the unchanged signature; the new
   import only supports the proof. All old direct dependencies are accounted
   for above. The unit `sk-prop-input-spreading` retains its route and its
   unchanged `realized` record (empty statement and seven empty step lists).
   No unit or chapter step is bypassed.
5. REPAIRED. The parent proof/dependencies now record the comparison and
   compatibility induction. The new node records its construction and theorem,
   complete source argument, dependencies, provenance, searches, chapter/unit
   and verbatim Lean theorem signature. Only stage-3-owned fields of the
   existing node change.

Changes made by the second reader: replaced the restatement with the genuine
finite-stage comparison; constructed finite restriction maps; proved the
compatibility induction; removed the unused private helper; restored the
target docstring to the target; repaired both DAG records and this report.
