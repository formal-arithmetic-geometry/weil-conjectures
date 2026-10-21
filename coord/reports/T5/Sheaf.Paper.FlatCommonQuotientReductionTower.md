## What changed

Implemented `SheafOfModules.CommonQuotientReduction.nonempty_comparison` from an
ordinary module-sheaf quotient lemma. The proof constructs the derived restriction,
uses the universal derived counit to construct the natural comparison, proves its
components invertible on K-flat representatives, and explicitly assembles the strict
transition maps, tower isomorphism, quotient cones, epi and kernel formulas.

Private proved helpers reuse the existing exact restriction API and establish
flat-term K-flat representatives,
exact scalar extension under the flatness hypothesis, and preservation of K-flatness
by flat restriction. The latter uses the existing tensor comparison and cancellation
isomorphisms, including their total-complex compatibility. Ordinary braiding orders the cancellation
so the proof directly tests F tensor Res(P), avoiding signed total-complex symmetries.

Added `Sheaf.Paper.OrdinaryCommonQuotientTower` for the separate underived quotient
calculation: normalized ordinary comparisons and scalar transitions.
The quotient units are explicitly constructed from the presheaf extension unit
and the sheafification adjunction; their naturality is proved and transported
to the prescribed ordinary models. They are no longer chosen fields of the structure.
Its statement has no flatness or complex hypotheses and no derived or strict-complex
conclusion. Proved `OrdinaryCommonQuotientTower.unit_epi`, `.unit_transition` and
`.unit_kernel` independently: none of those conclusions is a field of the retained
holed structure. The kernel proof uses the locally bijective map R/ker(q)→S,
tensor descent through sheafification, and Mathlib's quotient-tensor equivalence.
Also proved `.unique`: the section normalizations and epic units determine every
comparison, unit and transition map uniquely. The retained choice of ordinary
data therefore satisfies the project's determinacy requirement. The main theorem supplies the missing homological and tower argument;
it does not simply apply a renamed copy of its original statement.

Removed two unused public imports advised by the statement reviewer, and the unused
direct private import of `LeftDerivedFromResolvingClass`. Optional structure generators
are disabled and `monoidalCategory` is locally irreducible to avoid unnecessary expansion.
The pure-section construction is kept irreducible while elaborating the specification,
then restored for the supporting proofs. Flatness predicates stay locally irreducible
and are unfolded explicitly only where their conditions are used. Exact restriction
instances are supplied explicitly rather than registered as local search rules.
See `coord/changes/T5-flat-common-quotient-imports.md`.

## Proved and sorry left

Closed the original hole in
`SheafOfModules.CommonQuotientReduction.nonempty_comparison` (one original hole).
All private helper proofs are complete. No `sorry` remains in the item module.
Constructed `SheafOfModules.commonQuotientPresheafUnit`, `commonQuotientUnit`
and `commonQuotientModelUnit`, and proved `commonQuotientUnit_naturality`
and the unit section formulas.
The new public theorems `SheafOfModules.OrdinaryCommonQuotientTower.unit_epi`,
`.unit_kernel`, `.unit_transition` and `.unique` are fully proved.

Added one hole in `SheafOfModules.nonempty_ordinaryCommonQuotientTower`, node
`lem-weil-pbc-ordinary-common-quotient-tower`. This is the ordinary quotient-tensor
calculation from original steps 2–3 and the ordinary maps in step 5. More precisely,
the remaining hole constructs only the natural ordinary isomorphism and the
transition maps with their pure-section formulas. The units are actual constructions.
Epimorphy, transition
compatibility, and the complete local ideal-product kernel formula are now proved
from those formulas and local quotient surjectivity, not assumed in that hole.
The full local-lift, balancing and quotient proof is recorded in its docstring and node. The edge cases
of zero and unit kernel ideals, zero module, and empty site obey the same formulas;
there is no pointwise or global-surjectivity assumption.

Thus this delivery is a decomposition (one upper hole closed, one lower hole added),
not a net hole-count improvement. No definition contains `sorry`, and no arbitrary
existence witness is used for data: the normalized pure-section formulas determine
ordinary comparison and transition maps (formally proved by `.unique`), and the universal counit equation
determines the derived comparison.

## No longer needed

Removed `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` and
`Sheaf.Paper.RingedTopoiTensorSections` (unused public imports), and the direct private
import `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`.
The latter may still be reached through the existing derived-change-of-rings proof;
no declaration or dependency from that source module is removed or claimed pruned.

The item's proof does not use the black-box node
`lem-weil-pbc-flat-scalar-restriction-kflat`: its required K-flat clause is proved
privately from tensor cancellation. It also does not separately invoke
`lem-pur-left-derived-from-kflat-class`: the existing cochain model already provides
the universal property needed for the lift. Removed that node from the item's
`tool_uses`, and updated `proof_deps` and proof steps to the actual argument.
The full flat-term restriction conclusion is unnecessary; flat terms are only required
over B by the representative field. No blueprint unit realization is bypassed.

The node `def-weil-pbc-ringed-tensor-section-calculus` is not needed as a proof lemma:
the normalized formulas use the actual `changeOfRingsPresheaf` and `toSheafify` directly.
It remains in the original statement dependencies; those are unchanged.
No module is withdrawn and all existing DAG parents are retained.

## Where the brief, the DAG or earlier work was wrong

The declared dependency `Sheaf.Algebra.Homology.FlatScalarRestrictionKFlat` is absent
from the readable source and the compile server has no object for it. There is no
rework row restoring it. Rather than restate that dependency or weaken the item,
the required K-flat restriction clause is proved here using existing tensor APIs.

Original step 1 asked for flat R-terms as well, but no field of `Comparison` needs
that stronger assertion. Original step 6 proposed a new resolving-class descent;
the cochain model's existing universal derived property supplies the exact lift and
normalization more directly, without a second resolution construction.

The tensor-quotient calculation in original steps 2–3 was described as elementary,
but its local-surjectivity and sheafification glue has no existing Lean declaration.
The kernel calculation has now been proved using tensor local bijectivity and
Mathlib quotient tensors. The normalized ordinary comparison and coefficient transition construction
remain separated as one genuine underived result. Quotient units, including their
naturality in module maps, have been constructed directly. Local scalar lifts are essential:
sectionwise surjectivity was not introduced.

## New nodes

`lem-weil-pbc-ordinary-common-quotient-tower` records the normalized underived quotient
tensor comparison, transitions and quotient units. Its source is the sheaf tensor
construction in Stacks 03EK and the elementary quotient-tensor calculation used in
099L. The node cites the same current blueprint ancestor as the item and preserves
the proper-base-change unit route. Searches found ordinary module quotient tensor
lemmas but none with the required sheafified local kernel and pure-section formulas.

Change record: `coord/changes/T5-flat-common-quotient-imports.md`.

Validation: both delivery modules passed the compile phase of `deliver3.py`.
The main proof also compiled in 36.4 seconds before removing one unused simp argument.
A direct comparison verified all original public definitions, the entire `Comparison`
structure, and the item theorem signature unchanged. The current direct importer,
`DerivedFiniteQuotientCoherence`, explicitly imports the tensor-section module itself;
it does not refer to `CommonQuotientReduction.Comparison`. Both DAG dependency lists match
the union of their proof-step dependencies. No source-library module or target was edited. The initial split-off gate requested
continued work; the subsequently proved quotient-kernel and epi results further
reduced the retained obligation.

## Second reading by T5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
