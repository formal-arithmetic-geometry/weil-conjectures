## What changed

Replaced the sole sorry in `AlgebraicGeometry.exists_supported_koszul_unit_summand`
without changing its signature or any existing definition. The proof explicitly constructs
`E = Q.obj ⊞ A.obj`. It proves quasi-coherence using homology's biproduct comparison and
`Scheme.Modules.isQuasicoherent_biprod`; perfectness uses the split distinguished triangle
and `Scheme.isPerfect_two_out_of_three`. Support is proved directly by applying the additive
stalk-homology functor to `biprod.total`. Both summands have explicit retract diagrams.

The geometry is decomposed into two separate statements in new modules:
`SupportedKoszulRelativeDetector` constructs a perfect supported test object A, zero on U,
which detects only supported objects already zero on U. `SupportedOpenUnitConeProperties`
concerns a given unit triangle and supplies quasi-coherence, support on T, and vanishing of
its cone on U; it has no affine cover, generator, perfect object, or orthogonality hypothesis.
Neither new statement is the original statement renamed or its hypotheses repackaged.

The combining proof completes the specified unit to a distinguished triangle. It transfers
shifted orthogonality to A using the retract, uses exact restriction's shift comparison and
derived adjunction to prove orthogonality to R(L(K)), and uses integer shift equivalence to
prove orthogonality to K[1]. The triangle's exact coyoneda sequence gives orthogonality to
the cone. The relative detector makes that cone zero, and Mathlib's zero-cone criterion
makes the specified unit invertible. No alternative right adjoint is chosen in this proof.

All writes are in the item sandbox. Three Lean modules and three node files are delivered;
there are no interface changes, forced adaptations, change records, or new definitions.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_supported_koszul_unit_summand`
(node `lem-pc-supported-koszul-unit-summand`); its proof contains no sorry.

Added and left exactly `:= by sorry`:

- `AlgebraicGeometry.exists_supported_koszul_relative_detector`
  (`lem-pc-supported-koszul-relative-detector`, module
  `Sheaf.AlgebraicGeometry.SupportedKoszulRelativeDetector`).
- `AlgebraicGeometry.supported_open_unit_cone_properties`
  (`lem-pc-supported-open-unit-cone-properties`, module
  `Sheaf.AlgebraicGeometry.SupportedOpenUnitConeProperties`).

This is a decomposition: one upper hole closed and two strictly smaller geometric holes
added, not a complete sorry-free proof or a net hole-count improvement. The already stated
`Scheme.isPerfect_two_out_of_three` remains a dependency; it is not modified or counted as
an added hole. The new statement modules import the existing declarations their documented
proofs need so that the next work is explicit in the import closure.

Validation: all three modules compiled together in import order with lcompile.py. No sorry
occurs inside a definition or private declaration. The final delivery dry run supplies the
preflight and axiom probe. Empty U, empty T, empty X and redundant cover members are allowed.
For U top the relative detector may be zero, since every object restricting to zero is zero.
For U empty the cover makes X affine and the relative detector is ordinary affine supported
Koszul detection. The cone assertion allows all unbounded K and every specified right
adjoint; closedness of T is what makes direct image vanish on its open complement.

## No longer needed

Removed direct imports from the item's module:

- `Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact`
- `Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`
- `Sheaf.AlgebraicGeometry.KoszulOpenOrthogonality`
- `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition`
- `Sheaf.AlgebraicGeometry.SupportedOpenPushforward`

The first, second, and fifth are now dependencies of the appropriate smaller geometric
statements. KoszulOpenOrthogonality remains needed transitively by the existing affine
supported detector used in the new construction's proof plan. They are not claimed as
removed from the entire target closure.

The new route does not use node `lem-pc-ringed-spaces-derived-direct-image-composition`
or module `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition`: the relative
cone argument avoids the composition of pushforwards from W and U intersect V. This is the
pruned dependency of this item's argument; other targets may still need that module.

Added proof imports in the main module are precisely the two new statement modules,
PerfectTwoOutOfThree, Modules.QuasicoherentBinarySum, Mathlib.Topology.Sheaves.Abelian, and
Mathlib.Algebra.Category.Grp.Zero. Its original public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

No existing statement was found false, and no existing signature was changed. The original
DAG plan omitted explicit closure lemmas for perfectness and quasi-coherence of the sum.
The updated proof dependencies name PerfectTwoOutOfThree and QuasicoherentBinarySum.

The old plan passes through open direct-image composition. The implemented combination uses
the unit cone instead, with affine detection only for objects already zero on U. This is
below the unit level: `dag/units/sk-thm-picard-duality.json` has empty realized statement and
step lists, and none of its fixed statements or steps is bypassed or edited.

The existing affine-only `DerivedOpenUnitCone` does not apply to arbitrary qcqs X and does
not include support on an arbitrary closed T. `OpenRestrictionSupportTriangle` gives a
canonical triangle on the open subscheme, whereas the new cone statement concerns every
given over-site adjunction and given triangle, and additionally proves support on T. Its
proof plan explicitly uses that existing triangle and transports it by right-adjoint
uniqueness and triangle morphism isomorphisms; it does not duplicate its construction.

The local Stacks source files are absent on this machine. The official Stacks pages 0A9A,
09IR, 08D5, and 08DF were read online. Search with LeanFinder, Loogle, and grep found generic
triangle criteria and no complete matching theorem; LeanSearch returned Internal Server
Error. Library searches found the affine detector, canonical support triangle, sum closure,
and cover-isomorphism criterion, all retained where the argument needs them.

## New nodes

`lem-pc-supported-koszul-relative-detector` formalizes the supported Koszul construction on
the affine complement and its relative detection property. Its proof uses the existing
affine supported detector on S = T intersect (X minus U), supported open pushforward,
quasi-coherent derived direct image, exact extension-by-zero adjunction, restriction-zero
and two-open-cover detection. It never asserts invertibility of any global unit or adds Q.

`lem-pc-supported-open-unit-cone-properties` isolates the local homological/support facts
for an arbitrary specified open unit triangle. The existing canonical support triangle
provides quasi-coherence and vanishing on U after transport. Base change off the closed T
provides support on T. There is no detector or orthogonality conclusion in this node.

Both nodes have full Lean signatures, source places, proof steps, dependency lists, search
records, and edge cases. The existing node's proof, proof_deps and proof_origin agree with
the actual Lean proof. No change record is required.

## Second reading by H3

1. Compared the delivered item module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only imports, documentation, and the proof body changed. The two added modules and node files are new delivery artifacts.

2. Compiled all three modules with `lcompile.py --all`; compilation succeeds. The item theorem has no `sorry`; the only remaining sorries are the two explicitly named split-off theorems, each exactly `:= by sorry`. No definitions contain sorry, and no forbidden declarations were found.

3. Read both split-off statements and their nodes. The relative detector and cone-properties statements are strictly smaller than the item, have documented sources and complete proof plans, and are not duplicate restatements. Their signatures match the Lean declarations. No existing library theorem duplicating either statement was found by repository search.

4. Checked the proof route and pruning. The proof uses the relative detector, cone-properties lemma, perfectness two-out-of-three, and quasicoherent biproduct closure, while removing the five obsolete direct imports. The unit route remains the specified unit triangle and zero-cone criterion; no unit statement or step was edited. The main node proof and proof_deps match the implementation.

5. Checked edge cases recorded in the report and node documentation, including empty U, T, and X. The support and restriction hypotheses are used at their stated strength, and the resulting unit conclusion is unchanged. Verdict: accepted after the changes below.

Changed: added this second-reading record only; no Lean code, theorem statement, definition, node, or import was altered during review.
