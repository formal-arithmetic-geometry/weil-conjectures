## What changed

Proved `AlgebraicGeometry.Scheme.Modules.affine_isSplitEpi_of_residue_epi` in
`Sheaf.AlgebraicGeometry.AffineResidueEpiSplitting`, with its signature unchanged.
Added four proof-only imports: the source modules `Modules.FiniteDescent` and
`Modules.QuasicoherentCokernel`, and the project modules
`FiniteTypeModuleSupportPullback` and `Algebra.Homology.ModuleStalkFunctor`.
The two new private helpers are completely proved: finite type descends through an
epimorphism, and residue epimorphisms imply an epimorphism for quasi-coherent modules
with finite-type target. The latter uses support pullback on the cokernel.

The affine argument proves projectivity of sections, reflects the restricted
sheaf epimorphism through tilde, constructs the section with `Projective.factorThru`,
and proves the two counit/restriction transport equations explicitly.
Updated the existing node's proof, proof_deps and proof_origin to this route.
No definition, public signature, public import, unit record or other module changed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.affine_isSplitEpi_of_residue_epi`
(node `lem-pc-affine-residue-epi-splitting`). Holes added: none. Holes left: none.
This is a proof, not a decomposition. Both private helpers are proved.

The recovered earlier attempt was checked against the current module and stage brief.
Its single-file compile succeeds without warnings (16.9 seconds), and the delivery
dry run prints OK, with only the independent second reading outstanding. The axiom
probe passes. Nothing was pushed. The node copy changes only `proof`, `proof_deps`
and `proof_origin`, and every Lean line is at most 100 characters.
The empty scheme is covered by vacuous stalk conditions and sheaf separation;
no nontriviality of the section ring or finiteness of the source module is used.
The dependency `FiniteTypeModuleSupportPullback` and the source section/projective
lemmas already have complete proofs. The delivery dry run performs the axiom probe
and preflight. No global build was run.

## No longer needed

No original import is removed and no whole module is claimed pruned.
The explicit maximal-localization detection argument in the original plan is
unneeded: support pullback detects the zero cokernel directly. The original direct
proof dependency `lem-weil-pbc-nakayama-local-generators` is replaced by
`lem-weil-pbc-support-pullback-finite-type`; Nakayama remains a dependency of that
existing support theorem, so this is not a claim that its node leaves the closure.
The planned `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine` statement is not
applied directly: its required finite-presentation assertion is supplied by the
proved source `finitePresentation_sections_of_isFinitePresentation`. The support
module still reaches QuasicoherentFiniteTypeAffine, so no closure pruning is claimed.
The three other original proof dependencies (affine tilde/Gamma, finite presentation
on affine opens, and finitely presented flat implies projective) remain in the route.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The existing APIs support a shorter residue argument
than the explicit section-cokernel tensor/localization calculation. `IsFlatOver`
is defined by affine section flatness, so its evaluation on top already provides
exactly the flatness needed, after rewriting the identity appLE.

The support theorem from the proper-base-change chapter is used as an existing tool
for the finite-cokernel Nakayama step, with no replacement of the Picard coherence
unit's bounded-model shortening argument. The unit record's realized arrays are
empty; this helper is below that unit, and the cancellation/shortening caller is
unchanged. The source references read for this route were Stacks
[056J](https://stacks.math.columbia.edu/tag/056J),
[00NX](https://stacks.math.columbia.edu/tag/00NX), and
[01B7](https://stacks.math.columbia.edu/tag/01B7).

## Second reading by C1

1. PASS: Diffed the sole delivered Lean module against the repository. The existing
   theorem signature is byte-for-byte identical, including every hypothesis and
   the `IsSplitEpi f` conclusion. No definition or public import changed; the added
   imports are proof-only. No other module or change record is delivered.
2. PASS: Independently compiled the module without errors or warnings (17.2 seconds).
   A scratch copy with explicit `#print axioms` for the target and both private
   helpers compiled; each uses exactly `propext`, `Classical.choice`, and `Quot.sound`.
   No sorry, forbidden declaration, or hollow definition occurs in the delivery.
   The right inverse is constructed from proved projectivity and epimorphism facts.
3. PASS: No statements were split off and no holes were added. Independently searched
   Lean sources and Loogle with finite-type/epimorphism and residue-surjectivity
   terminology. The existing public `sheaf_finiteType_of_epi` is still sorry, while
   the corresponding helpers in other files are private; retaining the completely
   proved local helper avoids introducing a sorry dependency. The residue argument
   uses no finiteness of the source. Zero targets and the empty affine scheme are
   covered: separation is valid even when there are no points.
4. PASS: Read the proof from its conclusion through affine projective splitting and
   residue detection of the finite-type cokernel. The existing proved support theorem
   supplies the Nakayama step. In scratch copies, removing FiniteDescent,
   QuasicoherentCokernel, or ModuleStalkFunctor caused missing-declaration errors;
   the support import supplies the theorem used directly. All added imports are
   needed. The No longer needed section accounts for the sole removed old proof
   dependency, Nakayama, without claiming its transitive pruning. Read the Picard
   coherence unit: its realized arrays are empty, and the bounded-model shortening
   route and caller are preserved.
5. PASS: Diffed the node records and checked each dependency's declaration or Mathlib
   match. Only proof, proof_deps, and proof_origin changed; the union of step uses
   equals proof_deps. The node follows the actual cokernel, support, affine sections,
   projectivity, and two naturality transport arguments. No new node is required
   for the completely proved private implementation helpers.

Second reading changed only this report by recording the independent checks.
The Lean proof and node record needed no repair. Closed holes: one, namely
`AlgebraicGeometry.Scheme.Modules.affine_isSplitEpi_of_residue_epi`; added holes: zero;
split-off statements: zero; whole modules pruned: none.
