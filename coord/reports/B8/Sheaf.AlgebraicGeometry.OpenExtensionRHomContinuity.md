## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek_rhom_continuity`
with its original statement and chosen integer bound. All six public imports are preserved.
The proof uses the existing evaluation-normalized open internal-Hom formula,
exact pullback, and bounded-below qcqs pushforward continuity. Private helpers prove
naturality of `colimit.post`, invariance under natural isomorphisms, preservation of
quasi-isomorphisms by exact termwise colimits, and composition through a genuine
complex model. The model is constructed from the existing functorial K-injective
replacement and cochain internal Hom. No arbitrary witness of existence defines data.

The full single-file proof compiled through `lcompile.py` in 54.7 seconds.
Its sole unused-tactic warning was removed before delivery preflight.

The DAG proof and dependency list follow this argument. The unit's statement and
realized route are preserved. Sources read: Hemo--Richarz--Scholbach, Lemma 5.3 and
its proof, PDF p. 14; Bhatt--Scholze, Lemmas 6.3.14 and 6.8.12; the current blueprint
unit and the proof of `lem-sfb-dc-hom-preserves`.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek_rhom_continuity`
(node `lem-sfb-rhom-continuity-open-extension`). There were 1 and there are 0 holes
in the assigned module. Added 0 holes and split off 0 statements. Every private
helper is proved. Imported declarations retain their own proof dependencies.
The original theorem signature was checked token-for-token, including universes,
binders and conclusion; all six original public imports are unchanged.

## No longer needed

Removed these direct proof imports:

- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`
- `Sheaf.CategoryTheory.SheafTensor`
- `WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian`
- `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`
- `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono`
- `Sheaf.Paper.CondensedModuleDerivedPushpull`
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`

The proof does not directly need these planned dependencies:

- `sk-def-sfb-sheaf-tensor`: native closed module structures are already the
  structures of the existing derived Hom and its adjunction.
- `det-prop-sfb-module-pullback-exact-main` and
  `def-sfb-module-upper-lower-adjunction`: use the canonical exact `supportPullback`
  and its adjunction from the open Hom formula's existing module.
- `lem-sp-grothendieck-enough-injectives`,
  `lem-weil-pbc-complex-injective-resolution-mono`, and
  `lem-weil-pbc-bounded-below-injectives-kinjective`: existing negative vanishing
  and total/bounded-below compatibility already give the pushforward bound.
- `def-weil-pbc-internal-abelian-sheaf-module-equivalence`: the current qcqs
  pushforward continuity theorem is stated on internal modules themselves.
- `sk-def-sfb-module-derived-pushpull`: the proof uses the native
  `lowerStar.rightDerivedFunctor` directly, without its named abbreviation.

Removed obsolete top-level tool approvals for
`det-prop-sfb-module-pullback-exact-main`, `lem-sp-grothendieck-enough-injectives`,
`lem-weil-pbc-complex-injective-resolution-mono`, and
`lem-weil-pbc-bounded-below-injectives-kinjective` for the reasons above.

These are removals from this proof's direct route, not withdrawals of declarations.
Shared transitive dependencies remain available. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The earlier plan is mathematically valid but does not need a fresh bounded injective
resolution for the lower bound. Its existing bounded-below derived-functor API
already proves the bound. The plan's section-action transport is unnecessary for
the current internal-module statement of pushforward continuity. The proof makes
the representative and original-cocone compatibility explicit, rather than assuming
that arbitrary diagrams in a derived category admit strict lifts. Concrete-functor
unfolding initially exceeded the single-file limit. The model isomorphism calculation
is now generic, and local irreducibility keeps the main argument on the established
functor APIs. These are local proof-context changes, with no public attribute changes.

The generic tools from `lem-weil-pbc-kinjective-functorial-existence`,
`lem-weil-pbc-exact-functor-bounded-below`,
`lem-weil-pbc-derived-functor-negative-vanishing`,
`src-right-derived-functor-plus-compatibility`, and
`det-lem-formal-closed-support-adjunction` provide reusable construction and
comparison APIs; they do not replace the unit's finiteness route. No statement,
public definition, source-library declaration, or consumer is changed.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
