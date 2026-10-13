## What changed

Proved `exists_adjoin_singleton_finite_split_algebra` with its signature and visibility unchanged.
Added two proof-only imports, `Sheaf.RingTheory.MonogenicResiduePolynomialModel` and
`Sheaf.RingTheory.MonogenicRelationFiniteSplitting`. The former supplies a monic residue relation
in a localized monogenic presentation; the latter splits that relation by a finite coefficient
extension. The final proof composes the finite map with the presentation isomorphism and uses
`Ideal.map_map` to identify the extended ideal.

Four new modules each contain one fully proved public theorem:

- `MonogenicResidueLeadingRelation`: Zariski's lemma over the fraction field of the contracted
  quotient, descent of algebraicity, and a degree-preserving polynomial lift give a relation with
  leading coefficient outside the maximal ideal. This works for an arbitrary commutative algebra.
- `MonogenicPrincipalLocalizationModel`: localize at a nonzero coefficient, lift that coefficient
  ring to the required universe, use its fraction field, and construct the monogenic presentation
  by an injective, surjective localization lift. Surjectivity is proved by adjoin induction.
- `MonogenicResiduePolynomialModel`: map the residue relation to that presentation and multiply
  by the inverse leading coefficient. Explicit leading-coefficient, degree and evaluation
  calculations prove monicity, positive degree and ideal membership.
- `MonogenicRelationFiniteSplitting`: use Mathlib's actual splitting field and integral closure,
  the existing Nagata-domain N-2 and finite-Nagata lemmas, and a surjective tensor-product map to
  prove finiteness of the extended monogenic algebra. Root integrality descends splitting, and
  functorial evaluation transports ideal membership.

All five modules compile cleanly using `lcompile.py --all`. No existing interface, definition,
public import, target, or other claimed module was changed. The two original proof steps remain:
residue relation after coefficient localization, then finite splitting and integral closure.
`dag/units/sk-thm-p1.json` does not designate this node as a unit statement or step realization.
The source was read at https://stacks.math.columbia.edu/tag/0334 because this clone has no local
`literature/stacks-project/algebra.tex`.

## Proved and sorry left

Closed the item's one hole: `exists_adjoin_singleton_finite_split_algebra`
(node `lem-weil-pbc-monogenic-finite-split-algebra`).

The following new declarations are also fully proved, with no direct `sorry`:

- `exists_monogenic_residue_leading_relation`
  (`lem-weil-pbc-monogenic-residue-leading-relation`).
- `exists_monogenic_principal_localization_model`
  (`lem-weil-pbc-monogenic-principal-localization-model`).
- `exists_monogenic_residue_polynomial_model`
  (`lem-weil-pbc-monogenic-residue-polynomial-model`).
- `exists_monogenic_relation_finite_splitting`
  (`lem-weil-pbc-monogenic-relation-finite-splitting`).

No `sorry` remains in any delivered module, and none was added. This is a proof from existing
library declarations, not a decomposition into unproved intermediate statements. The imported
project Nagata theory retains its existing transitive proof dependencies; this delivery does not
claim to close those dependencies.

## No longer needed

No original import was removed: the original public imports belong to the unchanged interface.
The planned dependency `lem-weil-pbc-finite-algebra-is-integral` is no longer used by this node's
argument; finiteness is proved directly via the tensor-product map, and root integrality follows
from the monic polynomial. No module of that node was imported. The other old dependencies remain
used transitively through the new proved lemmas, or as definitions in their statements:
Zariski's lemma, Nagata localization, the Japanese condition, normality of finite-extension
integral closure, finite Nagata ascent, integral closure, and finite modules. They are not pruned.
The target's `proof_deps` now names the two new lemmas actually applied in its proof.

## Where the brief, the DAG or earlier work was wrong

No statement correction or forced adaptation was needed. The original DAG plan was usable but
omitted the Lean glue: extending the contracted quotient to its fraction field, preserving
polynomial degree during lifting, building the principal-localization monogenic isomorphism,
transporting universes, and proving the monogenic extension finite. These steps are now proved.
The construction uses `Frac(R)` as the splitting-field base to keep the output universe controlled,
and uses `ULift(R_a)` with its fraction field for the localization model. These implement the
source's constructions without selecting data for any definition from an unproved existence lemma.

The edge cases were checked in the argument: the zero residue generator has a positive-degree
relation (X); a constant nonzero polynomial cannot annihilate a residue element because the
contracted quotient embeds injectively in the residue field; the chosen leading coefficient is
nonzero because its image is outside the proper maximal ideal; repeated or inseparable roots
are allowed by Mathlib's splitting field; and no primality assumption on the ideal is used in
transporting evaluation through the finite splitting map.

## New nodes

`lem-weil-pbc-monogenic-residue-leading-relation`, module
`Sheaf.RingTheory.MonogenicResidueLeadingRelation`: the residue relation with nonvanishing
leading coefficient, proved using Zariski's lemma and Mathlib polynomial lifting.

`lem-weil-pbc-monogenic-principal-localization-model`, module
`Sheaf.RingTheory.MonogenicPrincipalLocalizationModel`: a compatible monogenic presentation
after principal localization, proved using localization, fraction-field uniqueness and ULift.

`lem-weil-pbc-monogenic-residue-polynomial-model`, module
`Sheaf.RingTheory.MonogenicResiduePolynomialModel`: the normalized monic residue relation,
proved by combining the preceding two lemmas and computing evaluation and leading coefficient.

`lem-weil-pbc-monogenic-relation-finite-splitting`, module
`Sheaf.RingTheory.MonogenicRelationFiniteSplitting`: finite split coefficient extension of a
given relation, fully proved. It uses the existing `lem-weil-pbc-nagata-domain-n2` as a tool;
that lemma is in the same unit and does not depend on this item.

All four nodes have source, proof steps, actual Mathlib search records, and exact Lean signatures.
There are no change records because no existing interface changed.

## Second reading by W2

1. **Interface comparison.** Compared `AdjoinSingletonFiniteSplitAlgebra.lean` with the repository version. The theorem signature, universes, hypotheses, conclusion, visibility, and existing declarations are byte-for-byte unchanged; only proof-only imports and the proof body were added. Verdict: pass.

2. **Compilation and proof hygiene.** Compiled all five delivered modules with `lcompile.py --all`; all compiled without errors or warnings. Searched the delivered sources for `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, and `extern`; none occur. The four auxiliary declarations and the target are complete proofs. Verdict: pass.

3. **Statements and nodes.** Checked each auxiliary theorem against its DAG node, including exact Lean signatures, source, proof steps, dependencies, and blueprint/unit metadata. The statements are strict reductions used by the target proof and do not duplicate the target. Edge cases described in the prior review (zero generator, nonzero leading coefficient, repeated roots, and arbitrary ideals) are respected by the constructions. Verdict: pass.

4. **Route and pruning.** The target follows the unit route: normalized residue relation, then finite splitting and ideal-map composition. The target's proof dependencies are exactly the two auxiliary declarations it applies. The old finite-algebra-is-integral dependency is not used; no import was removed because all original public imports remain part of the interface. Verdict: pass.

5. **Axioms and visibility.** Proof-only imports are plain `import`; public imports are limited to declarations needed by exported statements. No delivered definition contains postponed data. The compiled declarations use only the permitted foundational axioms (with any transitive `sorryAx` confined to pre-existing imported open theorems). Verdict: pass.

I changed only this second-reading report section; no Lean source, node statement, or existing interface required repair.
