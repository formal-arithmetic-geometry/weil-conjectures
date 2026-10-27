# Finite compatibility and canonical comparison interfaces

The item `Sheaf.Paper.SfImmersionCompletedPullbackComparison` is held by N1.
The delivery proves its original finite_compatibility theorem, without adding holes.
No target statement, hypothesis, conclusion or universe is changed.

## The functor type (productComparison unchanged)

Reviewer fix (2026-10-26): productComparison keeps its published Pi.lift body, and the
coherence import stays a plain `import`. The delivered rewrite of that body forced a new
statement dependency on the item node, which a stage-3 node change with a changed proof
cannot carry. The private generic theorem roos_product_comparison_formula proves that
the published lift equals roosProductComparison for any evaluation-equality proof;
roosIso_exists now rewrites by it and applies the generic uniqueness theorem.

modulePull's body is unchanged. Its result type is now explicit, using
pbcModules and pbcAdicCompletion, exactly as the strict-tower statements do.
That type is definitionally equal to its former inferred type. This prevents
repeated conversion between the two presentations of the same coefficient ring.
The abstract category used in roosRlim_exists uses that same alias. A local
irreducibility attribute keeps the chosen limit object behind its API.

Every theorem statement is unchanged. The only interface change is the explicit,
definitionally equal result type of modulePull; its data is unchanged.
No shared Roos-model definition or adopted WeilConjectures file is changed.

The downstream tool's name search finds 35 textual users of modulePull; 32 refer
to other namespaces or fields. The actual consumers of this module's modulePull
are IntegralImmersionPullbackNormalization and IntegralStratumChartRestrictionsData.
The latter is also the only external user of this module's productComparison, whose
body is unchanged. All fields and all definitions of both consumers retain the same
functor, with a definitionally equal type. Both consumers are
checked from unchanged sources against this delivery. No adaptation is intended.

## Existing evaluation-interchange API

Sheaf.CategoryTheory.ExactTowerAugmentedCounitEvaluation was unclaimed when edited.
Its already proved private theorem
CategoryTheory.ExactTowerAugmentedCounit.interchange_transition is made public,
with a source docstring. Its full statement and proof are unchanged. All existing
public signatures, attributes, imports and data definitions of that module are
unchanged. The existing owning node records the additional public Lean attachment.
This adds no mathematical assertion, construction or hole and changes no meaning.

The item uses an ordinary proof import of that module. Its finite evaluation
comparison follows from the existing public pbc_reduction_adic_tower_laws, so it
also uses an ordinary import of LevelwiseAdicTruncations. That module is unchanged.
The only existing direct importer of ExactTowerAugmentedCounitEvaluation is
Sheaf.Paper.SfCompletedPullbackMateFactorization. It uses the existing public API,
not the formerly private helper, and is checked from its unchanged source.

There are no forced adaptations. The item also shortens moduleObj_eq by evaluating
the existing functor equality and replaces a componentwise transport calculation
by a proved generic equality-isomorphism lemma. These change proofs only.

Validation: the item compiles cleanly in 57.2 seconds; the API owner compiles in
31.1 seconds. All three named consumers compiled from unchanged sources against
the changed interfaces. Their temporary sandbox copies were removed after these
checks, so they are not delivered as changes. No forced adaptation is present.
