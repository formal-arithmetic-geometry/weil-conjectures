## What changed

Replaced the sole sorry in `AlgebraicGeometry.finite_duality_derived_hom` by a complete
Lean reduction. Its signature and existing docstring are unchanged. Added two independent
intermediate modules, each with one public named theorem and a matching DAG node:
`Sheaf.AlgebraicGeometry.AffineDerivedHomEvaluationCounit` and
`Sheaf.AlgebraicGeometry.FiniteAffineAdjointCounitComparison`.

The first intermediate constructs an ambient scalar right adjoint, a natural identification
RHom(O_Y,-) with the identity, and the evaluation counit formula for every derived object.
It is affine, does not require Noetherian schemes or boundedness, and makes no assertion
about the geometric right adjoint. The second compares the geometric and scalar adjoints
at a bounded-below quasi-coherent object, with boundedness of its geometric adjoint image
as an explicit input. It makes no internal-Hom identification or evaluation assertion.
Neither intermediate restates the original theorem.

The main proof obtains boundedness from `finiteTwistedInverse_boundedBelow`. It constructs
the Hom identification for the specified rhoR by applying scalar restriction to the
component of `adjA.rightAdjointUniq adjH`, then composing with the first intermediate's
identification. Associativity and Mathlib's `rightAdjointUniq_hom_app_counit` prove the
required evaluation equation. It combines this with the independently obtained geometric
counit equation. Thus the combination includes actual transport of the specified
adjunction, rather than merely applying a renamed copy of the statement.

Added three proof imports (the two intermediate modules and Mathlib adjoint uniqueness),
retained the boundedness lemma, and removed the four unused direct proof imports listed
below. All existing public imports remain as on the base. Updated the original node's
proof, proof_deps and proof_origin to agree with this route. No existing definition or
statement changes; no change record is required.

## Proved and sorry left

Proved by reduction: `AlgebraicGeometry.finite_duality_derived_hom`
(`lem-sc-finite-duality-derived-hom`), 1 of the item's 1 original sorries.
Its module contains no sorry. The reduction still depends on the named theorem
`finiteTwistedInverse_boundedBelow` and on the two new statements below; this is not
an assertion that the theorem is closed under the project's axiom criterion.

Every sorry added in this delivery:

- `AlgebraicGeometry.exists_affine_derivedHom_evaluation_counit`, node
  `lem-sc-affine-derived-hom-evaluation-counit`, in
  `lean/Sheaf/AlgebraicGeometry/AffineDerivedHomEvaluationCounit.lean`.
- `AlgebraicGeometry.finite_affine_adjoint_counit_comparison`, node
  `lem-sc-finite-affine-adjoint-counit-comparison`, in
  `lean/Sheaf/AlgebraicGeometry/FiniteAffineAdjointCounitComparison.lean`.

Both have proof exactly `:= by sorry`, a source, and a complete proof in words.
The mathematical checks include zero objects, arbitrary shifts, the identity morphism,
and transport under arbitrary specified adjunction/comparison isomorphisms. The first
statement imposes no unjustified quasi-coherence claim for general K. The second uses
quasi-coherence only with finite/Noetherian and bounded-below hypotheses.

## No longer needed

Removed direct proof imports from the item's module:

- `Sheaf.AlgebraicGeometry.FiniteAffineDerivedEquivalence`
  (`lem-sc-finite-affine-derived-equivalence`).
- `Sheaf.AlgebraicGeometry.FinitePushforwardDerivedHomQCoherent`
  (`lem-sc-finite-pushforward-derived-hom-qcoherent`).
- `Sheaf.AlgebraicGeometry.FiniteSheafHomAffineAdjoint`
  (`lem-sc-finite-sheafhom-affine-adjoint`).
- `Sheaf.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint`
  (`lem-pc-noetherian-derived-direct-image-right-adjoint`).

The first three remain in the natural-language proof plans of the new intermediates;
they are relocated dependencies, not mathematical pruning from the whole route.
The Noetherian existence theorem and its module are genuinely unnecessary on this
route: R, a, comparison and adj are already inputs, so their existence is never used.
No other existing node or module is claimed to be pruned.

## Where the brief, the DAG or earlier work was wrong

The previous attempt stopped without a reduction. The existing plan is mathematically
usable but its Lean declarations do not expose all its required comparison coherence.
`finite_affine_derived_equivalence` gives comparisons after quasi-coherent inclusions,
whereas the conclusion requires c on the entire derived category. The existing affine
Hom adjunction gives an existential derived restriction functor L and an underlying
Hom isomorphism, but does not tie that isomorphism to the specified derived restriction
and the displayed evaluation morphism from `derivedInternalHom`. These localization
and coherence tasks are isolated in the two new items rather than abandoned.

`finite_pushforward_derivedHom_qcoherent` also has an extra family of local
HasDerivedCategory instances and uses a different algebra-valued Hom presentation.
The new comparison item's proof plan explicitly requires transporting the exact scalar
restriction, underlying Hom comparison, and quasi-coherent membership; those steps
are not treated as definitional equalities or asserted proved here.

The unit `sk-thm-picard-duality` has no realized nodes in its statement or proof-step
lists; the finite-duality argument and its sources are retained. No fixed unit or
chapter route is bypassed. The local Stacks TeX checkout is absent on this machine;
the cited source was read at the official pages for Tags 0BUZ, 0BV0, 0AX2 and 0AX3.
LeanSearch was attempted but returned an Internal Server Error; its search record says
unavailable. LeanFinder, Loogle and local rg were used instead.

## New nodes

`lem-sc-affine-derived-hom-evaluation-counit`: source Stacks 0BUZ/0BV0 and 0AX3.
This is the derived scalar-Hom adjunction with evaluation at one, independently of any
geometric adjoint. Its three-step plan transports exact scalar restriction, computes
Hom on K-injective resolutions, and descends the underived evaluation map. Its own
module contains one remaining theorem sorry.

`lem-sc-finite-affine-adjoint-counit-comparison`: source Stacks 0AX2 and 0AVW.
This is the comparison of the geometric and scalar right adjoints, independently of the
internal-Hom evaluation formula. Its four-step plan constructs the global pushforward
comparison, transports the affine equivalence, uses finite
pseudo-coherence and affine cohomology to locate the two representing objects in the
bounded-below full subcategory, and applies pointwise counit-preserving uniqueness. Its own module contains
one remaining theorem sorry. It requires boundedness only at the fixed object K; its
proof plan uses Yoneda uniqueness of the two representing objects, without assuming
that the given geometric adjoint already restricts globally. No change records were added.

## Second reading by H2

1. **Existing declarations unchanged — PASS.** Read all three delivered modules and
   diffed the existing module against the repository. The sole existing theorem's
   signature is byte-for-byte identical (checked by extracting the text from `theorem`
   to `:= by`); its docstring is unchanged. There are no definition changes or change
   records. Only its proof, proof imports, and local heartbeat option changed.
2. **Proof and axioms — PASS as a reduction.** All three files compile locally in
   import order without errors or warnings (10.6, 8.2, and 26.5 seconds after repair).
   A scratch module printed the axioms of all three delivered theorems: each uses only
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The main theorem has no
   local sorry; the only two delivered sorries are exactly the public named intermediate
   theorems listed above. No forbidden declaration, hollow definition, or hidden sorry
   occurs. This does not claim closure under the final axiom criterion.
3. **Split statements and reuse — PASS.** Independently read the affine adjunction,
   affine equivalence, finite Hom quasi-coherence, and boundedness declarations. Read
   the official Stacks sources [0BUZ](https://stacks.math.columbia.edu/tag/0BUZ),
   [0BV0](https://stacks.math.columbia.edu/tag/0BV0),
   [0AX2](https://stacks.math.columbia.edu/tag/0AX2), and
   [0AX3](https://stacks.math.columbia.edu/tag/0AX3). The first split is the ambient
   scalar-Hom adjunction and its evaluation formula, without any geometric comparison;
   the second is the geometric comparison, without any internal-Hom or evaluation
   conclusion. Neither restates the item. Checked zero objects, identity morphisms,
   shifts of arbitrary degree, and changes of the specified adjunction/comparison by
   automorphisms: counit-preserving uniqueness absorbs those changes. Both docstrings
   give complete mathematical constructions, and both have matching nodes. Independent
   msearch LeanFinder queries used “sheaf modules derived restriction of scalars right
   adjoint evaluation unit” and “derived direct image affine scheme equivalence
   quasicoherent modules scalar restriction comparison counit”; they returned underived
   scalar coextension, sheafification, and pushforward adjunctions, not either split.
   Loogle on `CategoryTheory.Adjunction.rightAdjointUniq` confirmed the existing
   counit lemma used by the main proof. Local rg of Sheaf and upstream Lean found no
   shorter derived comparison theorem. The substantial localization and geometric
   coherence arguments cannot be closed in a few minutes from the existing APIs.
4. **Route and pruning — PASS after repair.** The main proof first constructs the
   evaluation identification for H, then uses `adjA.rightAdjointUniq adjH` in the correct
   direction (rhoR to H) and `rightAdjointUniq_hom_app_counit`; the geometric equation
   is independently combined with it. Every old proof dependency removed directly
   from the item is listed in `## No longer needed`. Three remain mathematical proof
   dependencies of the intermediates; only the Noetherian right-adjoint existence
   node is pruned from this route, since the adjunction is given. The unit record has
   `realized.statement = []` and `realized.steps = [[]]`; no realized unit node or fixed
   unit step is bypassed. Found and repaired missing proof imports in the two new
   modules: without these imports the queue would incorrectly drop the relocated
   dependencies despite their being needed by the documented plans. All added imports
   are plain `import`; existing public imports remain needed for signatures/instances.
5. **DAG agreement — PASS.** The existing node changes only `proof`, `proof_deps`, and
   `proof_origin`. Its steps follow the actual Lean reduction and dependencies. Checked
   that `proof_deps` equals the union of each node's step uses for all three nodes.
   The new nodes specify sources, complete plans, searches, created/item/group/date,
   blueprint origin, chapter/unit, and Lean records. Their hypotheses, conclusions,
   universes, and named sorries agree with their Lean declarations.

Second-reading changes: added the planned proof imports to the new modules
(`FiniteSheafHomAffineAdjoint` and `DerivedRHomAlgebraModule` in the evaluation module;
`FiniteAffineDerivedEquivalence`, `FinitePushforwardDerivedHomQCoherent`,
`FiniteSheafHomAffineAdjoint`, `DerivedRHomAlgebraModule`, and `AffineDerivedCohomology`
in the comparison module). Removed trailing whitespace in the main proof. No statement,
definition, theorem proof, or node field required a mathematical correction.
