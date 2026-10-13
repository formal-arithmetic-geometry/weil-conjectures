## What changed

Replaced the original hole in `GaloisCover.stalk_normalization_formal_zero_slice_split`
with a complete Lean proof from `GaloisCover.section_finiteEtale_generic_split` in the new
module `Sheaf.AlgebraicGeometry.Morphisms.SectionFiniteEtaleGenericSplit`. The original
signature and docstring are unchanged. The proof constructs the section over U, proves the
normalization comparison using Mathlib, proves restriction and iterated-pullback comparisons,
uses universal finite coproducts for the constant cover, and transports the section splitting
by base change. All projection equations are proved explicitly. The node copy records this route.

The false `zero_slice_split_core` and its malformed node from the prior attempt were removed;
they were not declarations of the repository baseline. No definitions, existing interfaces,
or other groups' modules were changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_formal_zero_slice_split`.
Its module now has zero sorries, including its five private comparison helpers.

Added one hole:
`AlgebraicGeometry.Scheme.GaloisCover.section_finiteEtale_generic_split`, node
`lem-sbc-section-finite-etale-generic-split`, in its own new module. This is a decomposition,
not a net decrease in holes. The remaining statement only splits the section pullback over U;
it has no normalization, stalk, minimality, formal variables or formal-test hypotheses.
The original theorem supplies the complete geometric and categorical assembly from it.

## No longer needed

Removed the direct proof imports of
`Sheaf.AlgebraicGeometry.Morphisms.GenericFibreActionExtension`,
`Sheaf.AlgebraicGeometry.Morphisms.NormalIntegralGenericHomFull`, and
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFormalPuncturedRestriction`.

`lem-sbc-generic-fibre-action-extension` and its module are unnecessary for this route:
the generic section fibre is already split by the original torsor identity, and that
isomorphism extends directly over U. This also removes this route's need for its
GenericFibreHomExtension and GenericFibreTorsorIdentity dependencies.
`lem-sbc-stalk-normalization-formal-punctured-restriction` and its module are unnecessary:
we base-change the splitting to the actual zero-slice base, without identifying its points
with a punctured spectrum or establishing finite étaleness of both formal restrictions.
These modules may remain reachable through other callers; no global deletion is asserted.

`lem-sbc-normal-integral-generic-hom-full` is still needed by the new section-splitting node
and remains imported there. `lem-sbc-relative-normalization-smooth-base-change` is used
through Mathlib's existing normalization API. Neither is pruned.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox's `zero_slice_split_core` asserted an isomorphism for arbitrary
scheme covers without hypotheses, which is false (for example an empty cover and the
identity cover over a nonempty scheme). It also merely moved the requested conclusion,
and the file named target.lean retained the original sorry. That explains the previous
no-original-declaration-proved rejection. Both problems are removed in this attempt.

The DAG's action-extension and punctured-point preparations are unnecessary for this
subproblem. Splitting the section cover over U first and base-changing that splitting
proves the stated slice result with the original hypotheses, including zero variables
and disconnected torsors. The unused minimality binders are preserved, with the unused
variable linter scoped off for this theorem. Extra elaboration heartbeats are scoped to
this theorem; there is no change to a mathematical definition to obtain them.

## New nodes

`lem-sbc-section-finite-etale-generic-split` records splitting the finite étale section
cover on U by extending its split generic fibre using normal generic full faithfulness
(Stacks 0EYJ and 0BQM). Semantic search found no matching scheme-level theorem; LeanSearch
was unavailable, and the library search located the private actual-section splitting
in RegularDivisorGaloisRootSplitting and the proved generic full-faithfulness theorem.
Its proof in words and exact Lean signature are supplied in the new module and node.
No change record is needed because no existing statement, definition or public import changed.

## Second reading by F4
1. I compared both delivered modules with the repository versions. The target theorem signature and docstring are byte-for-byte unchanged; only its proof and proof-only import changed. The added section-splitting declaration is in a new module and has a matching split node.
2. I compiled both modules with `lcompile.py --all`. They compile without errors. The target module has no `sorry`; the only remaining `sorry` is the named split theorem `GaloisCover.section_finiteEtale_generic_split`. No forbidden declarations or hollow definitions occur.
3. I checked the new statement against the construction and edge cases described in its docstring: the generic-point hypothesis makes U nonempty, and the argument handles disconnected torsors and the trivial finite group. It is strictly weaker than the target and has no extra smoothness or local hypotheses. Searches found no existing equivalent declaration.
4. I traced the target proof: it uses the new section-splitting theorem, the normalization comparison, pullback comparison helpers, and finite coproduct universality. The removed action-extension and punctured-restriction imports are unused; the unit route remains represented by the target node and its declared normalization dependency.
5. The target and new node records match the Lean declarations, proof dependencies, proof origin, module paths, and split status. The new theorem's proof is explicitly recorded as the sole remaining hole and its node supplies the required source and proof plan.

I changed only the proof imports and proof of the target, added the section-splitting module and node, and added this second-reading report section. No existing statement or definition was changed.
