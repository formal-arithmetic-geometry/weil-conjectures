## What changed

Replaced the sole proof hole of
`AlgebraicGeometry.ProEtale.DiagonalTrace.exists_diagonalTraceScalarComparisons`
without changing its signature or either public import. The combining proof is
complete: `squareOfAcyclic` proves a general comparison theorem for independently
sized localization categories, constructs the two right-derived units, and uses
`Functor.rightDerivedUnique` and `Functor.rightDerivedNatTrans_app` to prove the
full normalization on every cochain complex. Its auxiliary
`derivesOnKInjectives` proves the localizer criterion using homotopy equivalences.
Both helpers are private and proved.

The ordinary coefficient construction and the restricted-pushforward acyclicity
criterion are separated into two new modules. Neither new statement includes an
`ExactSquare`, a derived comparison isomorphism, or the conclusion of the original
theorem under another name. The acyclicity statement has no Chern data or
coefficient-cone conclusion, and applies to any normalized Restriction; the
ordinary statement has no right-derived models at all. The combining argument
constructs both full derived squares from these strictly smaller inputs.

Added private proof imports of the two new modules and
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`. The latter gives
Grothendieck abelianness of the completed module category, so its canonical
right-derived direct image supplies Rc without a further hole. No definitions,
instances, existing signatures, attributes, or other existing modules changed.

## Proved and sorry left

Original holes: 1. Closed original hole:
`AlgebraicGeometry.ProEtale.DiagonalTrace.exists_diagonalTraceScalarComparisons`
(node `lem-sfb-diagonal-trace-scalar-comparisons`). Its proof is complete relative
to the two named intermediate theorems below. There are zero sorries in the item
module. This is a decomposition, not a completed proof free of sorry axioms:
1 original hole closed and 2 smaller holes added, for a packet net of -1.

Every remaining hole added by this delivery:

- `AlgebraicGeometry.ProEtale.DiagonalTrace.exists_diagonalTraceOrdinaryScalars`,
  node `lem-sfb-diagonal-trace-ordinary-scalars`, module
  `Sheaf.Paper.DiagonalTraceOrdinaryScalars`: exact ordinary restrictions,
  coefficient/root cones and the two section-normalized ordinary squares.
- `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_restrictedPush_acyclic`,
  node `lem-sfb-diagonal-trace-restricted-push-acyclic`, module
  `Sheaf.Paper.DiagonalTraceRestrictedPushAcyclic`: invertibility of the destination
  derived units on scalar-restricted K-injectives, for varying and completed
  coefficients.

Both are public named theorems with exactly `:= by sorry`, a source and a full
natural-language proof. No data are chosen in a new definition from either
existence statement. The construction of Rc uses a proved canonical definition.

Validation: both new modules compiled in the server import-order run. After
fixing the combining proof, the item compiled in 34.1 seconds (exit 0). Its two
unused-variable warnings concern the original existential binder names
`varying_sections` and `completed_sections`; the unused-variable linter is
suppressed locally for this theorem so those published names remain unchanged.
The delivery command performs the final compile/preflight. The original public
statement is preserved verbatim. No new import or DAG dependency cycle reaches
the item; all Lean lines have at most 100 characters.

## No longer needed

No public import was removed; no existing Lean module was withdrawn. The parent
proof now uses the two smaller nodes, the canonical right-derived model and the
ringed-site K-injective-resolution theorem directly. The following former direct
proof dependencies are absent from its new proof route:

- `lem-pur-twist-sheaf-locally-free` / `Sheaf.Paper.PurTwistSheafLocallyFree`:
  scalar extension along the base-field coefficient isomorphism suffices; no
  local freeness of the Tate line is required. In fact its theorem assumes l is
  invertible on the scheme, which is not an assumption of the item.
- `lem-pur-coefficient-system-derived-comparison` /
  `Sheaf.Paper.CoefficientSystemDerivedComparison`: the new derived-square proof
  uses acyclicity on whole systems and uniqueness of right derivation directly,
  rather than finite-level evaluation or etale/pro-etale comparison.

The old `lem-coef-semilinear-derived-sections` and
`det-sp-coefficient-towers-abelian` dependencies are retained in the ordinary
construction node. The old ringed-topos derived-composition dependency is retained
in the acyclicity node, together with the more directly applicable proved
`lem-pur-continuous-scalar-resolution`. Consequently these are relocated
requirements, not pruned mathematics. Existing transitive imports, including
upstream declarations and their proofs, are unchanged; no claim of global
module pruning is made.

## Where the brief, the DAG or earlier work was wrong

No statement change is proposed. The original node's direct appeal to
`pur_twist_sheaf_locally_free` would need an invertibility hypothesis unavailable
here, but the ordinary coefficient isomorphisms do not need that theorem.
The derived comparison needs scalar-restricted K-injectives to be acyclic for the
next direct image; it does not need restriction to preserve K-injectives. The
new proof isolates exactly the weaker unit-invertibility condition and proves
the rest of the comparison, including the normalization on all complexes.

Read the node, the latest blueprint trace proof paragraph (1), all six original
proof-dependency statements, the canonical derived model, and the ringed-topos
composition and continuous scalar-resolution statements. Also examined the proved
`nativeConstantRestriction_push_quasiIso`: it confirms the sequence-site route,
but its native coefficient restriction and constant-ring-module targets are not
the arbitrary normalized Restriction and fixed-module-sheaf presentation here.
It is not a direct application without additional presentation identifications.

The edge cases checked for both new statements are empty sites, identity
morphisms, the zero complex, and the first positive quotient n=0. No flatness of
the quotient map, finite-level K-injectivity, Milnor acyclicity, or invertibility
of l is assumed. The new acyclicity proof uses the existing ringed-topos
composition/K-flat resolution result for nonflat maps. The unit route is kept;
no realized blueprint unit statement or proof step is bypassed.

Mathlib searches were actually run through msearch (recorded in searches.jsonl):
LeanSearch found ordinary sheaf restriction, Loogle found generic restriction and
right-derived APIs, and grep found ordinary sheaf change-of-rings definitions.
None constructs this diagonal normalized coefficient package. These actual search
records are used in the two new nodes.

## New nodes

`lem-sfb-diagonal-trace-ordinary-scalars` is the underived part of the scalar
comparison construction in trace paragraph (1). It has no derived comparison
conclusion. Its module is `Sheaf.Paper.DiagonalTraceOrdinaryScalars`.

`lem-sfb-diagonal-trace-restricted-push-acyclic` is the ringed-site acyclicity step
for deriving the ordinary squares. It has no coefficient-cone construction or
derived-square conclusion. Its module is
`Sheaf.Paper.DiagonalTraceRestrictedPushAcyclic`.

Both nodes remain in chapter `sec-six-functors-basics`, unit
`sk-prop-diagonal-tower`, and have a blueprint source, complete proof steps,
verbatim Lean attachments and three kinds of actual Mathlib search. No change
record is needed: only the item proof/node and new modules/nodes changed.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
