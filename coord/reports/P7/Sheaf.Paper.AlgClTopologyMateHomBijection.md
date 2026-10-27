## What changed

Filled both theorem proofs in Sheaf.Paper.AlgClTopologyMateHomBijection without changing
any existing signature, definition or public import. Added private proof imports for
InternalScalarPullbackNormalization, NormalizedScalarRestrictionPush (including its
proved normalized_inverse helper), ConstantModelTorAmplitude, the section-module
Grothendieck construction, PullbackFiniteConstantLocalModel and Mathlib Hom congruence.
Updated the existing DAG proof
to follow these proofs. No other Lean module is changed.

Theta invertibility follows from a normalized comparison b: the existing
normalized_inverse calculation identifies b.inv with exactly the specified mate.
The first and third scalar Hom bijections come from the recorded equivalences on the
full constant-model constructible subcategories. Exact pullback preserves boundedness;
a proved private stratification argument (following the existing RationalRestrictionGlue
proof) preserves the required constant-model notion for arbitrary commutative coefficients.
Naturality of sigma and geometric Hom adjunction identify the five-factor equivalence
with postcomposition by the prescribed chi. No properness, coefficient flatness or
constructibility of the B-pushforward is assumed.

Proof context record: coord/changes/P7-algcl-topology-mate-proof-context.md.

## Proved and sorry left

Filled 2 of 2 original theorem holes. The complete module compiled cleanly in 31.3 seconds
with lcompile.py (a second complete run passed in 33.4 seconds):
- AlgebraicGeometry.ProEtale.algClTopologyPullbackTheta_isIso.
- AlgebraicGeometry.ProEtale.algClTopologyMate_hom_bijection.

Added 0 holes and split off 0 statements. No sorry remains in the delivered Lean module.
Existing imported theorem holes remain with their original owners, particularly
constructible_algCl_topology_comparison and internal_scalar_pullback_normalization;
this packet does not add or relocate them.

Private proved generic helpers keep derived functor constructions closed while checking
scalar normalization, homology transport, fully faithful Hom maps and mate naturality.

## No longer needed

Removed private imports:
- Sheaf.Paper.ModuleRingedToposDerivedComparison: use the existing normalized internal
  scalar-pullback comparison directly, with its exact mate identification.
- Sheaf.CategoryTheory.ExactFunctorDerivedFunctor: the already available canonical
  left-derived/termwise comparison and homology API suffice.
- Sheaf.AlgebraicGeometry.CondensedModulePullbackExact: exactness instances already come
  from the retained public pullback imports; its theorem need not be applied separately.

The tested coefficient-specific PullbackConstantModelConstructible import is unnecessary:
the generic stratification argument from RationalRestrictionGlue, reproduced as a proved
private helper using pullback_finiteConstantLocalModel, gives the preservation directly.
Removed direct dependency and
tool approval lem-sfb-pullback-constant-model-constructible; no withdrawal is claimed.

Removed direct proof dependencies det-prop-sfb-module-pullback-exact-main,
lem-weil-pbc-exact-functor-derived-functor and
lem-sfb-kflat-scalar-comparison-normalization. The latter still supplies the mate definition
through a retained public import and is used transitively by normalization; it is not
withdrawn. Removed lem-sfb-adjunction-transpose-square: Mathlib's direct
homEquiv_naturality_left gives the needed specialization with no extra square theorem.
Their obsolete tool_uses entries were removed. No module is withdrawn, and no transitive
closure pruning is claimed for dependencies still reached elsewhere.

## Where the brief, the DAG or earlier work was wrong

The plan is mathematically valid. A shorter existing API for the first hole is the
proved normalized_inverse helper together with internal_scalar_pullback_normalization;
this avoids repeating transport through the entire ringed-topos K-flat construction.
The exact-functor and transpose-square assembly can also use the existing canonical
comparison and direct Mathlib adjunction naturality. The generic stratification argument
is a shorter route than specializing the coefficient-specific
pullback-preservation statement. The source helper in RationalRestrictionGlue was not
available in the published build, so its short proof is reproduced privately here.
PullbackFiniteConstantLocalModel supplies its existing public local-model theorem. The constant-model constructibility
notion is preserved as requested; the different locally finitely presented notion
was not substituted. Empty schemes, zero complexes and identity maps introduce no
extra cases in the proof, since all steps are functorial and equivalences are used
on ambient Hom types. No source-library file or target statement changes.

## Second reading by P7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
