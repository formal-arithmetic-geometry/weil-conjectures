## What changed

Proved `AlgebraicGeometry.Etale.integral_etale_direct_image_exact` with its statement,
universes and public imports unchanged. The private, fully proved helper
`preservesFiniteColimits_integral_ab` transports the existing module-coefficient exactness
result through the equivalence between abelian groups and modules over `ULift ℤ`.
The induced coefficient functors on sheaves are left adjoints. Their composite around
module direct image is naturally isomorphic to abelian direct image by the coefficient
counit; the proof checks naturality and transfers finite-colimit preservation.

The other two conclusions use the existing exact-functor higher-derived vanishing theorem
and `Functor.isIso_rightDerivedFunctorPlusUnit`. Five proof imports were added:
`WeilConjectures.SixFunctors.Integral.Exact`,
`WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering`,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact`,
`Mathlib.Algebra.Category.Grp.ZModuleEquivalence`, and
`Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`.

Updated the item's proof route and removed obsolete tool approvals. Two new DAG records
attach already proved source declarations; they introduce no Lean module, declaration or
proof obligation. No definition, public interface, target or other group's module changed.
The unit record has no realization at this node; the universal-datum unit is unaffected.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.integral_etale_direct_image_exact`
(node `sbc-lem-integral-etale-direct-image-exact`). The private coefficient-transport helper
is fully proved. No holes were added, split off or left in the delivery: 1 of 1 closed,
0 added, 0 remaining. Both new source attachments refer to existing proved declarations.

The complete file compiled through `lcompile.py` without errors or warnings (8.3 seconds
with an explicit axiom check). `#print axioms` reported exactly `propext`,
`Classical.choice`, and `Quot.sound`. Its proof
works for every integral morphism, including empty schemes and nonsurjective morphisms;
coefficient equivalence imposes no finiteness, torsion or characteristic hypothesis.

## No longer needed

Removed these eight direct proof imports:

- `WeilConjectures.SixFunctors.Finite.Exact`
- `Mathlib.CategoryTheory.Sites.EpiMono`
- `Sheaf.Paper.IntegralEtaleCoverDisjointRefinement`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleDisjointCover`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`

The finite theorem does not imply the integral theorem; the completed integral theorem
is used instead. Its completed geometric proof supplies the local lifting, disjoint-cover
gluing and stalk argument, so this item need not import or prove the separate
`lem-sbc-integral-etale-cover-disjoint-refinement` module. Standard sheaf instances supply
enough injectives, without calling `etaleModule_enoughInjectives`.

Removed as direct proof dependencies:
`def-weil-pbc-direct-image`,
`lem-weil-pbc-abelian-sheaf-epi-locally-surjective`,
`lem-sbc-integral-etale-cover-disjoint-refinement`,
`lem-weil-pbc-disjoint-etale-sections-product`,
`def-weil-pbc-etale-site`,
`lem-weil-pbc-module-sheaves-enough-injectives`,
`lem-weil-pbc-exact-functor-derived-factorization`,
`lem-weil-pbc-exact-functor-bounded-below`,
`lem-weil-pbc-exact-functor-derived-functor`, and
`lem-weil-pbc-etale-composition-cancellation`.
The statement definitions remain available through the unchanged public imports.
Local surjectivity, disjoint gluing and the two exact-functor localization tools remain
recorded under the source results where appropriate; this is direct-dependency pruning,
not a claim that all their modules leave the targets' complete import closure.

Withdrew the six obsolete direct `tool_uses` entries for local surjectivity, disjoint
sections, enough injectives, derived factorization, bounded-below preservation, and the
general exact-functor derived theorem. Kept left exactness and higher-derived vanishing.
No Lean module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original proof plan did not reuse the complete integral module direct-image proof in
`WeilConjectures.SixFunctors.Integral.Exact`, or the exact bounded-below comparison instance
in `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact`.
The former has a coefficient-universe parameter requiring `ULift ℤ`, rather than `ℤ`;
restriction along the ring equivalence and the integer-module equivalence resolve this.
No statement or mathematical error was found. The current blueprint still asks for the
same three conclusions and is respected.

## New nodes

`src-sbc-integral-module-direct-image-exact` attaches the existing theorem
`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom` in
`WeilConjectures.SixFunctors.Integral.Exact`. It records its complete source proof and its
use with universe-lifted integer coefficients. No hole or duplicate declaration is added.

`src-sbc-exact-functor-plus-unit` attaches the existing instance
`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit` in
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact`. It records
the canonical comparison through the bounded-below exact functor factorization and the
uniqueness of right derived functors. No hole or duplicate declaration is added.

No change record is needed: existing signatures, definitions and visibility are unchanged.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
