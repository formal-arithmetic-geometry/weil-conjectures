## What changed

Proved `AlgebraicGeometry.Etale.abelianHigherDirectImage_core_comp` in
`Sheaf.AlgebraicGeometry.AbelianHigherDirectImageCoreComp`, with its original signature.
The proof follows the original adjunction / single-complex / homology route.

Added proof-only imports of
`WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc` and
`WeilConjectures.SixFunctors.BaseChange.DerivedComparison`. The former supplies the
proved derived pullback associativity theorem; the latter identifies transported
composition comparisons with `eqToIso` followed by `upperStarPlusComp`.

The seven private generic single-complex calculations are reused from
`Sheaf.AlgebraicGeometry.EtalePullbackSingleComp`; the proved derived transition
composition calculation is specialized from
`Sheaf.AlgebraicGeometry.LowerStarPlusTransitionComp` to abelian-group sheaves.
Their public statements only cover module coefficients, so those two modules are
not imported. Added a concrete private derived transition, its proved naturality,
and an expansion lemma. The final proof assembles these calculations and applies
homology. No public definitions or signatures changed. Generic binders are explicit on
the private lemmas, so the module adds no namespace, variable or option commands.
The local axiom probe passed in the first dry run.

Updated the existing node's proof and proof origin to describe the completed Lean
calculation, and made its derived-composition coherence dependency explicit.
The unit `sk-lem-failure-field` and its route are unchanged.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.abelianHigherDirectImage_core_comp`
(node `lem-sbc-abelian-higher-direct-image-core-comp`).

Holes closed: 1. Holes added: 0. Sorries left in the delivery: none.
The complete module compiled cleanly with `lcompile.py` in approximately 40 seconds.
Every private helper is proved; the private transition is constructed directly
from the adjunction unit, pullback comparison and counit, without witness choice.
This is a proof, not a decomposition into new holed statements.

## No longer needed

None. No original import or proof dependency was removed. The original public
import of `AbelianHigherDirectImageMap` is needed for the statement.
The ring-specific comparison modules considered during search are not needed by
this proof and were never imported; no claim of pruning their other users is made.

## Where the brief, the DAG or earlier work was wrong

The original statement and mathematical proof plan are correct. The original
proof-dependency list did not explicitly name derived composition associativity;
the updated node cites `lem-weil-pbc-derived-inverse-image-composition`, whose
coherence clause is realized here by the already proved source theorem
`upperStarCompDerivedPlus_assoc`.

The closest proved public lemmas have `ModuleCat` coefficients, while their
single-complex helpers are private. This is an API limitation, handled here with
local proved calculations rather than a changed dependency interface.

A first expansion through composite natural-isomorphism components exceeded the
single-file compile limit. The private transition now writes those components
explicitly; the expansion proof substitutes the structure-map equality before
using functoriality. No tool or timeout setting was changed.

Checked the original unrestricted hypotheses throughout: identity scheme maps,
zero sheaves and p = 0 are covered by the generic functor and adjunction equations.
No geometric hypothesis or restriction on p was introduced. Tag 09Z1 provides the
canonical comparisons in its colimit statement; the adjunction coherence details
are the categorical elaboration recorded by the original node, completed here.

## Second reading by U3

1. Interface: read the whole repository/sandbox diff and compared the existing
   `abelianHigherDirectImage_core_comp` signature byte for byte with a script.
   Verdict: identical, including universes, arbitrary scheme arrows, both structure-map
   equalities, every natural degree p, and the comparison coefficient morphism.
   `AbelianHigherDirectImageMap` and all public definitions are unchanged. The only
   added definition is private and constructs a morphism directly from unit, comparison,
   and counit; it chooses no witness of an existence theorem.
2. Proof: compiled the delivered file cleanly with `lcompile.py` (39.9 seconds).
   A scratch copy with `#print axioms AlgebraicGeometry.Etale.abelianHigherDirectImage_core_comp`
   compiled (52.3 seconds) and printed exactly `propext`, `Classical.choice`, `Quot.sound`.
   Searched the delivered Lean for sorry and forbidden declarations: none.
   Read the degreewise calculations, localization factorization identities, faithful
   plus inclusion, adjunct naturality, and homology assembly. In the transition
   composition, `ht₂` is the inverse hom-equivalence applied to its own adjunct;
   `ha'` is derived associativity and `hn'` moves the counit past the inverse comparison.
   The final proof cancels that inverse with its hom and uses transition naturality
   at the a-single comparison. Verdict: a kernel-checked proof, no inherited sorryAx.
3. Split statements: none; holes closed 1, holes added 0. No new modules or nodes.
   Checked the private complex calculations at i = n and i ≠ n, including the zero
   object; exactness hypotheses are available for both étale pullbacks. Substitution
   of h' and h'' imposes no extra condition beyond wa and wb. Identity arrows and
   p = 0 remain covered by the same equations. Verdict: no decomposition or restatement.
4. Route and pruning: read `EtalePullbackSingleComp`, `LowerStarPlusTransitionComp`,
   `HigherDirectImageTransitionCoreComposition`, the upstream `ExactFunctor` APIs,
   `UpperStarCompAssoc`, and `DerivedComparison`. The public ready-made single and
   transition lemmas require ModuleCat coefficients; the generic helpers are private.
   An independent LeanFinder search for exact-functor comparison with a complex
   concentrated in one degree returned `mapDerivedCategorySingleFunctor` and its
   factorization APIs, not composition coherence. A pinned-Mathlib/upstream grep for
   single-comparison composition/naturality found no replacement. The local proof
   uses the available factorization lemmas and proved upstream associativity directly.
   Both added imports are proof-only and used; the original public import supplies
   the statement's definition. Every old proof dependency remains used, so
   `## No longer needed` is complete. Read `dag/units/sk-lem-failure-field.json`:
   its fixed route and realized record are untouched. Read
   [Stacks Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1): it is the higher-direct-image
   colimit application; the coherence identity here is the categorical elaboration,
   not an additional geometric assertion from that tag. Verdict: route retained.
5. DAG: compared the node with the repository version. Its three proof steps match
   the single-complex comparison, derived transition composition, and homology
   assembly in Lean. The four proof dependencies are exactly the union of step uses;
   the added derived-composition node includes the coherence clause supplied by the
   proved upstream theorem. Source and proof-origin attribution distinguish the
   colimit application from the completed categorical calculation. Verdict: consistent.

Second reading changed no Lean proof. Restored the existing node's `mathlib_searches`
field to the repository version because stage 3 does not own that field; the independent
search evidence is recorded above and in the sandbox search log. Added this review.
