## What changed

Replaced the sole proof hole in `Sheaf.Paper.TAdmissibleDualizableTruncations` by a
complete Lean assembly of all four conclusions, with the original signature unchanged. The docstring now follows the actual
proof route. The scalar argument proves finite presentation of perfect
cohomology and uses a finite Postnikov induction to prove perfection of scalar
truncations. The geometric argument transports truncations and cohomology through
exact realization and exact inverse image, uses the existing local-perfect-model
criterion in both directions, and constructs the induced standard t-structure.

Added `Sheaf.Paper.FlatCondensedScalarRealization`, with the actual composite
`ordinaryScalarRealization` and a complete proof of `flat_ordinaryScalarRealization`.
The proof detects exactness by lifting sections over affine w-contractible covers,
then constructs the comparison with the prescribed derived realization from its
counit on flat-term K-flat resolutions and descends it through localization. It
works on the ordinary unbounded derived categories, without regularity or a
geometric component assumption.

Added `Sheaf.Paper.CondensedScalarFinitePresentation` for the remaining comparison
of finite presentations in the ordinary and internal scalar-module conventions.
Its one theorem is a separate statement about ordinary degree-zero modules, without
t-admissibility or derived categories. Both new results have their own nodes.
The zero-object scope is local to three private helpers, leaving the item module
interface identical. LeanSearch was run in addition to LeanFinder, Loogle and grep.
No existing definition, public signature, source-library declaration or target was
changed. Proof-only imports are private. No other group's module was adapted.
The unit's route is kept.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.tAdmissible_dualizable_truncations`
(node `lem-zl-t-admissible-dualizable-truncations`). There are zero holes in the item
module. Its complete proof uses the remaining encoding lemma below, so this is a
decomposition, not a net hole closure.

Also proved the new theorem
`AlgebraicGeometry.ProEtale.CondensedRing.flat_ordinaryScalarRealization`
(node `lem-zl-flat-condensed-scalar-realization`) without any new proof holes.
Its definition is an actual functor composite, not data chosen from an existence
statement. All private helpers in both proved modules are completely proved.

Added exactly one hole:
`AlgebraicGeometry.ProEtale.CondensedRing.ordinaryScalarRealization_finitePresentation`
(node `lem-zl-condensed-scalar-finite-presentation`). It identifies the finitely
presented essential images of the two existing ordinary scalar-extension encodings.
It does not assert any truncation, t-structure, heart or dualizability conclusion.
The remaining work is the canonical terminal-object/scalar-ring transport, finite
free presentation transport, and normalized constant-extension comparison. Searches
found no existing theorem stating this comparison. A direct `rfl` test confirms that
the two scalar rings are not definitionally the same: one uses the explicit PUnit
profinite set and the other the category's chosen terminal object.

Hole counts in the packet: one original hole closed, one hole added, net zero.
The original theorem and the new exactness theorem are complete relative to their
named dependencies. Existing imported theorem holes are unchanged.

Validation: all three modules compiled together through `lcompile.py --all`; the
main module also compiled separately after removing unused imports. The final edits shorten the two reported long lines and synchronize the main
proof docstring with the updated node. No local Lake build was run.
The new statements were checked on zero rings, zero modules, empty schemes,
zero-sized presentations and arbitrary shifts; no uniform amplitude, rank, cover
member or finitely presented scalar module is required.

## No longer needed

Removed these original imports from the item module:

- `Mathlib.RingTheory.Flat.Basic`: flat exactness is encapsulated in the proved
  ordinary-realization theorem.
- `Sheaf.AlgebraicGeometry.ProEtale.SectionsConservative`: the new exactness proof
  proves the required local lifting detection directly from the affine cover.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: exact inverse image and
  its comparisons are already available through the actual local-model interface.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: no separate alpha
  coefficient isomorphism is needed for the already identified inverse image.
- `Sheaf.AlgebraicGeometry.ProEtale.WeaklyContractibleBasis`: the new proof uses the
  existing affine-cover theorem directly.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`: its definitions
  already come from the statement imports.
- `Sheaf.Paper.WContractibleCondensedScalarEvaluation`: the complete ordinary exactness
  proof uses `CondensedAffineOrdinaryScalarSections` instead of derived sections.

The main node no longer directly uses
`sk-thm-pe-weakly-contractible-basis`, `lem-zl-wcontractible-condensed-scalar-evaluation`,
`lem-weil-pbc-flat-tensor-exact`, `det-pe-sections-conservative`, or `lem-sfb-alpha-iso`.
Removed their obsolete top-level tool-use approvals, retaining the coherent-cohomology
and perfect-generator approvals in order. Flat tensor exactness is still used in the
new exactness node; affine covers replace the general basis and conservativity
route. These are dependency-edge removals, not withdrawals of those modules, which
other library declarations may still need. No Lean file is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned proof does not expose the comparison between the ordinary module
`scalarRing` used in derived realization and the internal module `scalarRingObj`
used in `HasScalarLocalModels`. They encode the same mathematics but use different
chosen terminal objects and different constant-module constructions. The new
finite-presentation node isolates precisely that missing comparison, without
changing either definition or asking for additional hypotheses.

The current blueprint Step 3 describes the perfect form of duality; the old node's
blueprint provenance calls its ancestor paragraph the field-stage projection
formula. New nodes cite the current perfect-duality step and the existing
`lem-zl-adic-hom-tensor-lisse-criterion` dependency chain. The blueprint unit and its
statement/step realization map are unchanged.

The generic exact-functor, internal-module/ordinary-module equivalence and normalized
internal/sectionwise scalar-adjunction nodes are used as mathematical tools. They do
not replace a smooth-proper-purity unit step. Any additional cross-unit approvals
are left for the maintainer; the packet does not add `tool_uses` entries.

## New nodes

`lem-zl-flat-condensed-scalar-realization`, module
`Sheaf.Paper.FlatCondensedScalarRealization`: the ordinary realization is exact under
flatness on extremally disconnected evaluations, and its termwise derived functor
is the already prescribed scalar realization. This theorem is fully proved.

`lem-zl-condensed-scalar-finite-presentation`, module
`Sheaf.Paper.CondensedScalarFinitePresentation`: finite-presentation essential-image
comparison between ordinary scalar modules and the existing internal finite
constant scalar models. This is the single remaining named theorem hole, with its
source and complete mathematical proof plan in its docstring and node.

No change records are needed: no existing statement or definition changed.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
