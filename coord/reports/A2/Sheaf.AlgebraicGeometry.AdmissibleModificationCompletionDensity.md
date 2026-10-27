## What changed

Proved `AlgebraicGeometry.completionPowerQuotientMap_square` by functoriality of Spec;
the resulting ring-map equality is definitional after unfolding the quotient map.
The definitions and all existing public signatures and public imports are unchanged.

Reduced `AlgebraicGeometry.admissibleModification_completion_density` to two genuine
geometric steps: the canonical isomorphism of infinitesimal blowup fibres, with both
projection identities, and bijectivity of the actual strict-local comparison at one
index. These have separate new modules and source-backed proof plans.

Added and proved `CommRingCat.colimit_quotientMap_bijective`. It constructs the inverse
using the colimit universal property and proves both inverse identities. It needs
neither filteredness nor finite generation. In the item, directed domination from the
existing admissible-system declaration identifies the stage structural maps with the
specified sourceBaseMap. Applying the new colimit theorem proves the second clause;
Ideal.map_pow and Ideal.span_singleton_pow prove the principal-ideal clause without
any nonzerodivisor assumption. Pullback extensionality proves the first clause from
the new fibre isomorphism.

Validation: `lcompile.py --all` compiled all four files cleanly: fibre statement 2.7 s,
strict-local statement 3.2 s, proved colimit comparison 3.6 s, assigned module 5.2 s.
The dependency IDs, new-node names, proof-dependency unions and 100-column limit
were also checked.

Only the assigned existing module and its own DAG node change; three new modules and
three new DAG nodes are added. No definitions are repaired and no consumer is adapted.

## Proved and sorry left

Original holes closed:

- `AlgebraicGeometry.completionPowerQuotientMap_square` (original node
  `lem-per-admissible-modification-completion-density`): proved outright.
- `AlgebraicGeometry.admissibleModification_completion_density` (same node): reduced
  to the following two strictly smaller statements, with a complete Lean assembly.

New holes, and the complete list of sorries left in this delivery:

- `AlgebraicGeometry.admissibleCompletion_fiber_iso`, node
  `lem-per-admissible-completion-fiber-iso`: only the infinitesimal-fibre assertion.
- `AlgebraicGeometry.admissibleCompletion_strictLocal_congruence`, node
  `lem-per-admissible-completion-strict-local-congruence`: a single-stage strict-local
  congruence, before taking colimits or specializing the exceptional ideal.

`CommRingCat.colimit_quotientMap_bijective` and both private helper lemmas are proved
without sorry. There are zero holes in the assigned module, two original holes closed,
and two new holes added: net zero. The main theorem is a decomposition, not an outright
proof of its remaining geometric inputs. Neither new hole is a renamed copy of the
main theorem, and neither includes its colimit or principal-ideal conclusions.

## No longer needed

Removed the proof import `Sheaf.RingTheory.FilteredColimitFiniteData`, the proof-dependency
edge to `lemma-nagata-filtered-colimit-finite-data`, and its obsolete top-level tool-use
approval. The actual colimit proof uses stage quotient inverses and coprojection
extensionality; it does not choose elements or equations at a filtered stage. This
module and node are not needed by this proof, though other parents may still use them.

The item's direct proof imports of `Mathlib.RingTheory.AdicCompletion.Completeness`,
`WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange`,
`WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples`,
`WeilConjectures.RingTheory.EtaleResidueTriplesLocalizedStrictHenselization`,
`Sheaf.RingTheory.StrictHenselizationSurjectiveQuotientCore`, and
`Sheaf.RingTheory.StrictHenselizationPresentationIn` are also removed. Their mathematical
roles belong to the geometric sublemmas' plans and to the existing admissible-system
lemma; they are not claimed globally unnecessary. In particular, the completion,
Rees, Proj and strict-henselization nodes in the original proof remain needed
transitively. No module is withdrawn, and no unit statement or unit proof step is
bypassed. The existing admissible-system node remains needed for common domination.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The DAG's finite-data colimit argument can be replaced
by a shorter universal-property argument. The supplied finite-data interface is for
preorders, whereas the actual index is an induced category of domination morphisms;
this difference creates no issue for the new proof, which only uses common domination
to identify structural maps and works over an arbitrary category thereafter.

Edge cases were checked in the source argument: n=1, I=0 or nilpotent, empty blowups,
and non-separated completion maps. The generic colimit theorem also covers an empty
index category, zero rings and the unit ideal. The new strict-local assertion uses
the selected geometric point, so its local rings are nonzero. The principal case
uses ideal powers only and does not require the generator to be regular.

## New nodes

`lem-per-admissible-completion-fiber-iso` records original proof steps 1–3, using the
existing canonical Rees-reduction declaration and arbitrary Proj base change. Both
projection equations specify the actual map and allow a direct pullback-extensionality
application in the parent.

`lem-per-admissible-completion-strict-local-congruence` records original proof steps
4–5 at a single blowup. Its proof plan uses the fibre isomorphism, the existing
geometric/algebraic strict-henselization dictionary, the surjective quotient theorem,
and pointed uniqueness. It states the quotient of S.comparison.app J itself.

`lem-per-colimit-quotient-comparison` records the proved universal-property replacement
for original step 6. Its complete Lean proof is in
`Sheaf.RingTheory.ColimitQuotientComparison`. The parent now cites the two geometric
nodes, this proved node, and the existing admissible-system node. Every new node
preserves the existing chapter, unit and historical blueprint ancestry. No change
record is required because existing statements, definitions and interfaces do not
change.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
