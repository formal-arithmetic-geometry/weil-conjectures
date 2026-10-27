## What changed

Replaced the proof hole of `AlgebraicGeometry.Scheme.adicResidue_cech_quotient_cone`
with a comparison of universal arrows. The original public signature and imports stay
unchanged. Added private proofs that finite quotient restrictions are locally complete,
that a reflector's complete objects are closed under products, and that quotient Roos
limit points are complete by exact internal Hom and the Roos triangle. Milnor exactness
lifts the specified compatible scalar units. The two mapping bijections then construct
inverse comparison maps and transport the homotopy-limit cone, retaining every unit leg.

The residual mapping-property assertion is in the new module
`Sheaf.Paper.AdicResidueQuotientUnitUniversal`. It mentions only the specified quotient
tower, a Roos cone and its normalized unit; it has no Cech model, augmented complex,
chosen reflector, or assertion that the cone point is complete. The latter assertion is
proved here rather than assumed. Thus the new statement is the mapping-property step,
not the original cone comparison under a new name.

## Proved and sorry left

Closed the original named hole `AlgebraicGeometry.Scheme.adicResidue_cech_quotient_cone`
(node `lem-sfb-adic-residue-cech-quotient-cone`) by a complete proof from the listed
inputs. Added one hole: `AlgebraicGeometry.Scheme.adicResidueQuotientUnit_universal`
(node `lem-sfb-adic-residue-quotient-unit-universal`). No other hole is added or left
in either delivered module. This is a decomposition: one original hole closed, one
strictly smaller mapping-property hole added, net zero. It is not reported as a net proof.
All private helper proofs are complete. No definitions contain holes.

Validation: `lcompile.py --all` compiled both delivered modules against the current
server overlay, with no errors (9.4 s for the residual statement module and 34.9 s
for the main module). The original theorem signature was compared verbatim, and
all Lean lines are at most 100 characters.

## No longer needed

The original module had no private proof imports to remove. All three original public
imports are retained. The direct Koszul-to-Cech calculation is replaced by the existing
Cech reflector's universal property and a formal comparison of universal arrows.

The original node's ordinary ring derived-change-of-rings dependency
`lem-pur-derived-change-of-rings` / `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`
is not needed: no ordinary ring scalar-extension functor is used here.
The original `lem-weil-proetale-countable-products-exact` /
`Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact` is not needed: products are
taken in the derived category, whose existence uses K-injective resolutions, not
exactness of products of sheaves. The original weakly-etale localization theorem
`lem-weil-proetale-weakly-etale-localization` /
`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization` is not needed: all arguments
are on the given slice site and its actual restricted coefficient sheaves.
The original `lem-weil-derived-countable-products-core` /
`WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore` is also
unneeded: termwise product preservation requires exact products, whereas the proved
`DerivedCategory.hasLimitsOfShape_discrete` instance gives the existence used here.
The strict-tower theorem is not used by the completed main proof; it remains in the
residual mapping-property node's plan for the Koszul/quotient comparison.
These are local dependency removals, not claims that other parents no longer need those
modules. No module is withdrawn and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement correction. The existing proof plan did not expose a declaration
identifying its strict quotient presentation with the specified counit-transpose tower
on the slice. That compatibility and its mapping property remain the explicit smaller
obligation; the plan's other completeness and comparison steps are now Lean proofs.

Checked the source proof of Stacks Tag 099M (`proetale.tex`, lemma-naive-completion),
Tag 0A0E (`algebraization.tex`, lemma-derived-completion-koszul), and the unit's current
blueprint route. Edge cases of the residual assertion: J=0 gives the identity completion
and constant quotient tower; J=A gives zero finite quotients and zero complete targets;
the zero ring is included. No boundedness, finite Tor dimension, perfectness or
Mittag--Leffler assumption was added. The residual theorem quantifies all normalized
lifts: the proof in words explains why different lifts differ by a finite-reduction
identity endomorphism of the reflector, which is invertible by derived Nakayama.

## New nodes

`lem-sfb-adic-residue-quotient-unit-universal` records the residual mapping-property
half, with the exact Lean signature, Stacks sources, proof in words, actual LeanSearch,
LeanFinder and grep searches, and the inherited integral-models unit route. The main
node's proof and dependencies now match the completed formal comparison.

The Cech reflector, complete-elements ideal, section-completeness restriction, and
exact internal-Hom statements are used as generic ringed-site tools. They supply
completeness on the fixed slice, while the residual Koszul/quotient comparison keeps
the integral-models unit route.

No existing definition or statement changes, no forced adaptations, and no change
record is required.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
