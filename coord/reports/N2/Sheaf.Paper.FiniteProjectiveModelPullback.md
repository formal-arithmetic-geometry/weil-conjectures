## What changed

Filled all six existing theorem holes in
`Sheaf.Paper.FiniteProjectiveModelPullback`. Every public signature, public import,
and non-theorem body is unchanged. All new Lean declarations are proved private
helpers in the item module.

The normalized model comparison follows from explicit constant-module and
scalar-extension adjunctions and uniqueness of left adjoints. The resulting
comparison exists for every scalar module. Its hom-equivalence equation gives
the normalization on generators; restriction extends that equation from a
terminal object to every object. Injectivity of the hom-equivalences proves
uniqueness. Linearity gives the basis formulas, and naturality gives the specified
retract and differential equations.

For flatness, realize a Mathlib finite-projective splitting and use the proved
constant-unit/scalar-extension-unit isomorphisms and preservation of finite
products. The finite-free retract lemma gives flat terms. The bounded-above flat
complex theorem gives K-flatness. The existing canonical ordinary good-complex
counit theorem supplies quasi-isomorphism preservation on the good resolving
class. The resolving-class theorem and uniqueness of derived functors transfer
its computation to the arbitrary derived-category universe, LF and epsilon of
the public statement. Localization then preserves the complex comparison.

Proof imports added: `Mathlib.RingTheory.Finiteness.Projective`,
`Sheaf.Paper.ScalarPerfectFiniteFree`, and
`Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients`. Proof-only `import all`
accesses proved private helpers from the scalar finite-free, strict-perfect, and
ordinary integral construction modules. Local irreducibility settings prevent
expensive unfolding of the tensor restriction construction and chosen pullback.
Proved private local instance wrappers cache the standard sheafification and
sheaf-composition propositions, reducing repeated generic typeclass inference.
The DAG proof and dependencies now follow this argument.

Returned-delivery repair (head ef99a3c01): removed the redundant private theorem
`proofCommWeakSheafify` and its local instance registration. Mathlib's existing
`HasSheafify` to `HasWeakSheafify` instance now supplies the proposition from
`proofCommSheafify`, so the duplicate in `AdicCoefficientDatum` is not reproved.

The two private `ScalarAdjunction.tensorHomEquiv_naturality_left/right` statements
now explicitly bind the site, category, universes and sheafification hypotheses,
and their `f` binders explicitly name `scalarPerfectExtensionFunctor`.
The older `CoefficientOrdinaryProof` and `ScalarReductionProof` statements have
`f` in their private `tensorFunctor`, built from `changeOfRingsPresheaf`.
Here it is built from `changeOfRingsPresheafOfUniverses`, whose explicit restriction
maps are used by the actual scalar realization. Thus the short unqualified texts
previously matched while denoting different constructions; the repair exposes
that distinction in the binders, as requested. No existing library declaration
or public signature has changed.

Validation: the repaired module compiled through `lcompile.py` in 42.8 seconds
with exit code 0. Its sole line-length warning was corrected before delivery.

## Proved and sorry left

Closed six of six original holes, all in namespace
`WeilConjectures.FiniteProjectivePullback`:

- `model_additive`.
- `comparison_existsUnique`.
- `comparison_free`.
- `comparison_retract`.
- `comparison_differential`.
- `finiteProjectiveModelPullback`.

There are zero `sorry` occurrences left in the item module and zero new holes
or new Lean statements elsewhere in this delivery. This is a proof from existing
stated dependencies, not a decomposition into newly holed statements.

The existing dependency
`WeilConjectures.ordinaryIntegralPullComplexCounit_isIso` in
`Sheaf.Paper.OrdinaryCompletedIntegralPullback` remains `sorry` in the shared
library. It is neither changed nor newly introduced here. The new ownership node
`lem-tw-ordinary-integral-good-complex-counit` records precisely that independent
computation theorem, rather than the later constructible-completeness theorem.
Other existing dependency holes, including the published derived-functor
existence instance, remain the responsibilities of their items.

## No longer needed

The returned repair also removes the redundant `proofCommWeakSheafify` helper;
Mathlib's existing `HasSheafify.isRightAdjoint` instance replaces it.

Removed proof imports `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage` and
`Sheaf.CategoryTheory.SiteInverseImageTensor`. The comparison uses the explicit
adjunctions of the actual scalar realization and ordinary pullback, so it needs
neither the separate constant inverse-image comparison nor the site inverse-image
tensor theorem. Consequently removed the direct proof dependencies and obsolete
top-level tool approvals `lem-pe-constant-left-module-inverse-image` and
`lem-weil-pbc-left-exact-site-inverse-image-tensor`.

The direct proof dependency `def-weil-pbc-constant-sheaf` is subsumed by the actual
constant-module package in `def-weil-pbc-strict-perfect-coefficient-package`.
No module is withdrawn: these declarations may still have other consumers.
The strict-perfect pullback module remains needed for its proved finite-free
retract flatness helper, but its full computation theorem is not applied.

## Where the brief, the DAG or earlier work was wrong

The proposed direct application of the generic strict-perfect ringed-pullback
computation theorem does not match the published ordinary pullback interface:
the generic theorem asks for explicit algebraic inverse-image data and object/map
identifications with its tensor construction. The ordinary pullback is supplied
as a left adjoint by sheafified Kan extension. Adjunction uniqueness avoids those
identifications for the normalized comparison.

The original DAG co-owned the early canonical good-complex counit theorem with
the later ordinary constructible-completeness theorem in the same Lean module.
The latter depends on finite-projective models; the former's statement and
source proof are independent of them. A separate existing-declaration attachment
records that early theorem, preventing a spurious dependency cycle. It uses
neither the later completeness theorem nor any conclusion of this item.
There is no change to a blueprint unit's realized statement or proof steps.

The duplicate-statement return exposed ambiguous unqualified private types. The
repaired naturality statements explicitly show the site and actual extension functor.

The older scalar-extension adjunction implementation uses a different tensor
presheaf construction. Its formulas were adapted privately to the actual
independent-universe scalar extension used by `model`, rather than assuming
those definitions are identical.

## New nodes

`lem-tw-ordinary-integral-good-complex-counit` records the already published theorem
`WeilConjectures.ordinaryIntegralPullComplexCounit_isIso`, with `existing: true`.
It introduces no Lean module, declaration or hole. Its self-contained statement
is computation on flat-term K-flat complexes, with no constructibility,
boundedness or completeness assumptions. Its proof specializes ordinary ringed
pullback computation and uses uniqueness of the universal counit. This is the
independent property used to transfer computation to arbitrary LF and epsilon.
The zero complex, zero coefficient ring, arbitrary non-flat structural maps and
unbounded good complexes satisfy the stated hypotheses without additional
assumptions. The preflight conservatively classifies the added proof-scope commands as an
interface change. The required record is
`coord/changes/N2-finite-projective-model-proof-scopes.md`; it documents the local
attributes, private generic variables, unchanged public definitions and signatures,
and the absence of current Lean consumers. No consumer adaptation is needed.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
