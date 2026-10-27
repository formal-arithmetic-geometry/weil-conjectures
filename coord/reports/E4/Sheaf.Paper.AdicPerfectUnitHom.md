## What changed

`Sheaf.Paper.AdicPerfectUnitHom` now constructs the comparison and proves every
clause of `AlgebraicGeometry.Scheme.adicPerfectUnitHom`, with its original
statement and public imports unchanged. The construction retains the A-action
on quotient sections. A section x of the quotient of Hom_A(M,N) defines the
linear map m ↦ H_n(ev_m)(x); transposition through the realization/sections
adjunction gives the comparison. Private proved lemmas establish additivity,
two-variable naturality, bijectivity for M=A, and the successor equation.

The rank-one proof uses the actual evaluation-at-one module isomorphism and
preservation of isomorphisms by H_n. The successor proof expands the lower
adjunction Hom equivalence using its unit, cancels the two balancing maps,
and uses naturality of the section insertion. These calculations are Lean
proofs in the item, independent of any finite-projective hypothesis.

The remaining geometric scalar calculation is stated separately as
`Sheaf.Paper.AdicPerfectQuotientSectionAdjunction`. Its single theorem asserts
an adjunction for the ordinary realization, identifies realization followed by
sections with constant sections of M/J^(n+1)M, and records the two scalar
successor normalizations. Its docstring specifies the right adjoints by actual
terminal sections and the transition by insertion of one. The theorem is used
only by eliminating its existential witnesses inside a proof; no definition
chooses arbitrary data from an unproved existence theorem.

The item's only new proof imports are this section-normalization module and
`WeilConjectures.Mathlib.CategoryTheory.Sites.Abelian`, whose proved linearity
of constant sheafification is needed. Both files compiled remotely. The final
item compile completed without warnings in 6.8 seconds; the new module compiled
in 10.5 seconds with its named theorem hole. No existing definition, public
signature, public import, instance or exported attribute was changed, so no
consumer adaptation or change record is needed.

## Proved and sorry left

Original holes: 1. Closed in the item's module:
`AlgebraicGeometry.Scheme.adicPerfectUnitHom`.

Added holes: 1, in the new module:
`AlgebraicGeometry.Scheme.adicPerfectQuotientSectionAdjunction`
(node `lem-sfb-adic-perfect-quotient-section-adjunction`). Its proof is exactly
`:= by sorry`. The item itself has zero remaining holes. This is a decomposition,
not a sorry-free proof of the geometric normalization: one original hole closed,
one smaller scalar-normalization hole added, net zero holes closed. Every
private helper is proved.

The new obligation is the scalar object/section identification from the old
node's first step, together with its scalar successor normalization. It makes
no assertion about the module of linear maps between two modules, constructs
no comparison t, and has no rank-one bijectivity or two-variable naturality
clause. The original Hom comparison and its three properties are derived by
the separate, proved evaluation/adjunction argument. Thus this does not rename
the original Hom-comparison obligation.

## No longer needed

No original Lean import was removed: both original public imports are needed
by the unchanged statement. The redundant private import
`Mathlib.CategoryTheory.Adjunction.Additive` was removed after testing; its
API is already available through the existing imports.

The item's direct proof dependencies are replaced by the section-adjunction
node. In particular:

- `lem-pur-site-constant-module-hom`, module
  `Sheaf.CategoryTheory.SiteConstantModuleHom`, is not used by this argument.
  Evaluation and transposition replace the internal-Hom comparison. This says
  nothing about its other users and does not withdraw that module.
- `lem-sfb-adic-constructible-finite-reductions`, module
  `Sheaf.Paper.AdicConstructibleFiniteReductions`, is not needed by the ordinary
  module calculation. No derived completeness, constructibility, finite
  cohomology or Noetherian hypothesis occurs here. The remaining scalar lemma
  uses ordinary tensor balancing, not that derived theorem.
- `lem-weil-pbc-site-constant-restriction` is no longer a direct dependency of
  the item's proof, but remains needed by the new scalar-normalization node.
  It is not globally pruned.

No module or DAG node is withdrawn. The new scalar node retains the existing
ordinary scalar-comparison APIs from
`lem-sfb-adic-finite-reduction-data` and
`lem-sfb-constant-realization-derived-scalar-extension`; their recorded
modules already provide the ordinary unit, balancing and tensor-normalization
statements. The unit route in `sk-lem-integral-models` is preserved.

## Where the brief, the DAG or earlier work was wrong

The old proof plan cited `adicConstructibleFiniteReductions` for an ordinary
scalar-extension calculation. That declaration concerns derived Noetherian
completion and finite constructible reductions, and does not directly supply
the arbitrary-module section normalization needed here. The original theorem
is unchanged. The missing ordinary scalar step is now explicit, with a precise
statement and source rather than an application of the unrelated derived
conclusion.

Searches found `constantSheafAdj`, `extendRestrictScalarsAdj`, the module
sheafification adjunction, `Adjunction.leftAdjointUniq`, and the algebraic
quotient tensor equivalence. Existing ordinary balancing helpers in
`AdicPerfectModelCompleteReduction` and `moduleComparison_tensor` in
`ConstantRealizationDerivedScalarExtension` are relevant to the remaining
normalization, but none of the read declarations supplies the complete section
identification with the fixed successor maps. The existing listed internal-Hom
theorem has a different role and is unnecessary for the proved evaluation
argument.

The new statement was checked on M=0, J=A, the zero coefficient ring and an
empty slice: quotient sections and realized sheaves are zero, and both scalar
identities are the unique zero maps. For J=0 the scalar quotient is A and the
construction is the ordinary constant-module/sections adjunction. Arbitrary
rings and ideals need no exactness or flatness of completion: the composite
coefficient map equals the quotient map by the limit cone identity, and tensor
associativity balances the two ordinary extensions directly.

## New nodes

`lem-sfb-adic-perfect-quotient-section-adjunction` is the ordinary scalar
realization/sections calculation preceding the total-Hom computation in Stacks
Tag 09C6 (`lemma-connected-adic-lisse`), using module sheafification (Tag 03CY)
and tensor extension (Tag 03EK). It belongs to the item's existing chapter and
unit. The whole current blueprint search for "quotient section adjunction"
found no duplicate; its provenance is the local model/quotient calculation in
`det-lem-integral-models-stacks`, via the original item. Its three recorded
Mathlib searches were run with the launcher search tool. The original node's
proof and proof dependencies now describe the actual evaluation/adjunction
argument. There are no change records because no shared interface changed.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
