## What changed

Replaced the single proof hole in
`AlgebraicGeometry.valuation_limit_qcoh_section_descent` by the Stacks 01Z0
argument. The supplied diagram and comparison map are unchanged. The proof constructs
the upper-tail structure-algebra functor, obtains its algebra colimit, and uses
`affine_pushforward_colimit` for the tensor colimit. It proves compatibility with the
specified transition and limit maps from their adjunction-unit equations, preserves
the tensor colimit under global sections on the qcqs base, and transports it to the
supplied diagram. Mathlib's concrete filtered-colimit criterion gives eventual zero.
The helper constructions and proofs are private. No definitions or signatures used by
consumers change, and no source-library module is edited.
The scope-command change record is
`coord/changes/valuation-limit-qcoh-section-descent-proof-scope.md`;
`tools/downstream.py --uses` found no existing consumer module to adapt.

The DAG proof now records the actual algebra-colimit construction and the direct
compact-open degree-zero sections theorem. The existing public imports are preserved;
new proof imports are private. The main declaration has a local heartbeat budget of
800000 for the dependent section-map conversions; the single-file wall-clock limit
remains 60 seconds. The repaired proof passed `lcompile.py` with exit code 0 in 41.9 seconds,
without errors or warnings. The public signature was compared byte for byte with
the current repository source and is unchanged; all Lean lines are at most 100
characters and the delivered module contains zero `sorry` tokens.
The first preflight requested a change record for `open MonoidalCategory`; that
record is retained with the unchanged signature and consumer check.

Repair of return at head `54558cde450`: removed the duplicate private
`AlgebraicGeometry.tensor_hom_ext` declaration. Both compatibility proofs now apply
the existing public `AlgebraicGeometry.tensorResolution_tensor_hom_ext`, imported
privately from
`WeilConjectures.AlgebraicGeometry.QCohTensorResolutionRestrictionTensor`.
The import-direction check accepts this dependency. The theorem named in the
return, `AlgebraicGeometry.Scheme.Modules.tensor_hom_ext` in
`TensorPowerOpenRestrictionAddition`, is private to its source module; the public
theorem used here has the same complete type. No upstream visibility is changed.

## Proved and sorry left

Closed: `AlgebraicGeometry.valuation_limit_qcoh_section_descent`
(node `lem-sc-valuation-limit-qcoh-section-descent`), one of one original holes.
Added holes: zero. Remaining holes in delivered Lean files: zero. Split-off theorems:
zero. The proof uses the existing statement `AlgebraicGeometry.affine_pushforward_colimit`,
whose own hole is unchanged and is not claimed closed by this delivery.

## No longer needed

Removed the private import
`WeilConjectures.AlgebraicGeometry.OpenModuleCohomologyDirectedColimit`.
Its node `lem-weil-pbc-qs-scheme-cohomology-directed-colimit` is not needed by this
proof: the proved `TopCat.abelianSections_preservesDirectedColimits` supplies exactly
the required degree-zero preservation, with no passage through derived functors.
This is a local pruning;
other consumers of the higher-cohomology theorem are unchanged.

The proof does not call `AlgebraicGeometry.exists_limit_affine_transition` separately:
affine projection and limit algebra information are already packaged by
`affine_pushforward_colimit`. The node `lem-weil-pbc-limit-affine-transition` remains
a statement dependency and is used below the retained affine-pushforward theorem;
it and its existing public import are therefore retained.

The duplicate private tensor-extensionality helper is also removed; its two uses
are supplied by the existing public theorem. No other module is withdrawn. The affine-pushforward, algebra-colimit and
filtered-colimit dependencies remain needed. No unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was necessary. The returned proof duplicated an
existing tensor-extensionality theorem; this repair reuses its public equivalent. The launcher's resumed reference clock
was reset in `.budget` (start 1792774377.2749622); the retained work and this delivery
continue the original claim from 2026-10-23, without modifying that metadata.
The former degree-zero step used a higher-cohomology interface unnecessarily; the direct proved sections-preservation
interface implements the same Stacks 01Z0 proof step. The source argument was checked
at `literature/stacks-project/limits.tex`, Lemma `lemma-descend-section`, and
`literature/stacks-project/sheaves.tex`, Lemma `lemma-directed-colimits-sections`(4).
Empty schemes, zero modules and non-antisymmetric directed preorders introduce no
extra assumptions: the proof uses a nonempty upper tail, compactness of the whole
base, and only preorder morphism identities.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
