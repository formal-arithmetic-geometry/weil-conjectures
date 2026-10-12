## What changed

Completed the earlier sandbox proof of
`AlgebraicGeometry.finiteDuality_degreeZero_counit_action` without changing its signature.
The proof obtains the algebra-valued Hom model and its evaluation/action formulas from
`sheafHom_affine_rightAdjoint`, proves its exactness, and uses an A-linear degree-zero
lift. Scalar restriction of the lifted isomorphism composed with iH gives e; its
composition with the underived counit gives epsilon. Evaluation at one is the underived
counit formula. A-linearity and the action formula specialized to the identity inclusion
of U prove the multiplication identity. The identity restriction was repaired using
`CategoryTheory.Functor.map_id`.

Added `FiniteAlgebraHomExact.lean`, with a complete proof: form the natural tensor-dual
Hom isomorphism from `dual_tensor_hom_iso`; transfer finite-limit and finite-colimit
preservation using `finiteLocallyFree_tensorLeft_exact`; scalar restriction reflects
isomorphisms through the unchanged abelian sheaf and hence reflects finite limits and
colimits. Apply Mathlib's preservation-through-reflection lemmas. The recorded
`sheafAlgebraRestrictScalars_preservesFiniteLimits` and colimit theorem supply the
restriction exactness, using standard derived categories only locally in this proof.

Added `FiniteExactHomDegreeZeroLift.lean` for the remaining derived comparison and
A-linear lifting argument. This is strictly part of the original argument: it assumes
an exact underived right adjoint, produces an A-linear lift and its counit equation, and
asserts neither evaluation at one nor the sectionwise action identity. Both sectionwise
clauses are proved in the original module. Updated its node to follow this assembly.

All three sandbox modules compile cleanly through lcompile.py in import order. No data
definition, target signature, or existing auxiliary signature was changed. No push is
requested or performed.

Repair of return C3/C4/E5: replaced the existential affine-adjoint comparison route
with a direct construction for the prescribed gamma. Updated the lift's proof-plan
imports, docstring, node proof[1], node proof[3], proof_deps, and second-reading point 5.
All theorem signatures remain unchanged. The repaired lift compiles cleanly.

Repair of return X-0952c: the earlier delivery passed review but landing failed on
missing unrelated module `Sheaf.CategoryTheory.CycleBoundaryTowerStep`. The current
import-pruning checker skips downstream paths that are no longer files. This repair
refreshes the delivery base from current `sheaf-dag` using deliver3.py and enables
its server-compilation checks with `WEIL_SERVER_COMPILE=1`. No unrelated library
file is added or adapted; all delivered signatures and proof routes are preserved.
The server-enabled dry run passed on refreshed base sheaf-dag (commit
`7c4338488`); nothing was pushed. A combined scratch-file server check also
validates the assembly with both newly declared intermediate results present.

## Proved and sorry left

Closed the original module's sole hole:
`AlgebraicGeometry.finiteDuality_degreeZero_counit_action`
(node `lem-sc-finite-duality-degree-zero-counit-action`).

Also proved the new intermediate declaration
`AlgebraicGeometry.finite_algebraHom_exact`
(node `lem-sc-finite-algebra-hom-exact`); it contains no sorry.

Added exactly one named hole:
`AlgebraicGeometry.finite_exactHom_degreeZero_lift`
(node `lem-sc-finite-exact-hom-degree-zero-lift`). Its proof is exactly `by sorry`, in
its own module, with a source and a complete proof in words. Consequently this delivery
is a decomposition (one original hole closed, one lower hole added), not a claim that
the target's axiom closure is already sorry-free. Existing imported declarations may
still depend on sorry, as intended in this stage.

## No longer needed

Removed `Sheaf.AlgebraicGeometry.FiniteAffineAdjointCounitComparison` from the lift,
and its node `lem-sc-finite-affine-adjoint-counit-comparison` from the lift's proof plan.

Removed these direct proof imports from the original module:

- `Sheaf.AlgebraicGeometry.FiniteDualityDerivedHom`
- `Sheaf.AlgebraicGeometry.FiniteSheafHomAffineAdjoint`
- `Sheaf.AlgebraicGeometry.FiniteAffineDerivedEquivalence`
- `Sheaf.AlgebraicGeometry.ExtEvaluation`
- `Sheaf.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact`
- `Sheaf.AlgebraicGeometry.AffineSinglePushforwardUnitIso`
- `Sheaf.AlgebraicGeometry.DerivedCategory`
- `Sheaf.AlgebraicGeometry.DerivedRHomAlgebraModule`

The first three are not needed as direct imports by the assembly. The exact Hom lift
uses `lem-sc-finite-affine-derived-equivalence` and
`lem-sc-finite-scalar-right-adjoint-qcoh` to construct phi for the prescribed canonical
gamma; it no longer uses `lem-sc-finite-affine-adjoint-counit-comparison`. Evaluation and tensor exactness remain needed through
`FiniteAlgebraHomExact`, and the canonical single-pushforward unit remains needed in the
remaining lift's proof plan. The affine derived equivalence remains directly in the
lift's plan. Thus removal of direct imports is not a claim that every listed
module becomes globally unreachable.

The assembly no longer directly uses nodes
`lem-sc-finite-duality-derived-hom`, `lem-sc-finite-sheafhom-affine-adjoint`,
`lem-sc-finite-affine-derived-equivalence`, `lem-sc-ext-evaluation`,
`lem-sc-ext-tensor-exact`, `def-pc-derived-rhom-algebra-module`,
`lem-sc-affine-single-pushforward-unit-iso`, or `def-pc-derived-category` as proof
steps. The node's actual proof dependencies are exactly the underived Hom adjunction,
proved Hom exactness, and the degree-zero lift. The corresponding foundational nodes
are retained wherever their intermediate proofs need them. Unit statements and steps
were not bypassed; the unit record's realized fields are empty.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt had no DAG records for its two new intermediate modules
and no report. Its action proof failed to compile at a placeholder used as the receiver
of map, then at the unqualified `Functor.map_id` (resolved to the core Functor theorem).
Both were repaired. The earlier Hom-exactness hole could be closed using existing
results, so it is proved rather than left as a second new hole.

The returned plan incorrectly treated an existential factorization and its phi as
compatible with a subsequently prescribed canonical gamma. That public statement
supplies neither equality nor compatibility. The repaired plan constructs gamma before
phi and proves the latter is an isomorphism by the adjunction hom equivalences and
full faithfulness, so its transpose equation uses that same gamma throughout.

The arbitrary underlying Hom isomorphism alone does not normalize a derived counit.
The lift intentionally retains the specified underived adjunction and the canonical
comparison hypothesis hc; sectionwise compatibility is then proved using the same iH
and adjH returned by the underived Hom theorem.

The new lift was checked mathematically for the identity morphism and for twists of the
specified geometric or underived adjunction: right-adjoint uniqueness changes j to
compensate, preserving the counit. Empty schemes and the zero algebra cause no exception;
all objects on the empty side are zero and the lifting uses full faithfulness, not
cancellation. The action calculation works also for a=0 and b=0. The exactness lemma
does not assume a nonzero or constant local rank.

LeanSearch was unavailable (HTTP Internal Server Error), recorded as unavailable;
LeanFinder, Loogle, logged Mathlib grep, local library searches and blueprint searches
were performed. The full Stacks checkout is absent from this clone; the cited original
Stacks pages 0BUZ, 0AX2, 0AX3 and 0AVW were read on the official site. The existing
library node sources already name these documents; no new external source is required.

## New nodes

`lem-sc-finite-algebra-hom-exact`: exactness of any algebra-valued Hom model naturally
identified after scalar restriction with Hom from a finite locally free module. Its
Lean proof is complete; it depends on the existing tensor/evaluation and scalar
restriction declarations. Module `Sheaf.AlgebraicGeometry.FiniteAlgebraHomExact`.

`lem-sc-finite-exact-hom-degree-zero-lift`: the A-linear lift and canonical derived
counit equation for a supplied exact underived right adjoint. The remaining argument is
the derived adjunction, finite affine derived equivalence, quasi-coherence of the
specified scalar right adjoint, canonical single-pushforward unit, and lifting through
the fully faithful single functor. It has exactly one sorry
and does not restate the sectionwise conclusions of the original theorem. Module
`Sheaf.AlgebraicGeometry.FiniteExactHomDegreeZeroLift`.

No change records are needed: all existing statements and definitions are unchanged.


## Earlier second reading (a previous round; superseded)

1. Compared all delivered modules with their repository counterparts. Only the item
   already exists. Its complete theorem signature, including hc and both sectionwise
   clauses, is byte for byte unchanged; no existing definition or auxiliary statement
   changes. Removed an accidental extra space before its proof separator. The two new
   modules declare the two new node statements; no change record is needed.

2. Compiled all three modules locally in import order after the repairs: no errors or
   warnings. Searched all delivered Lean for forbidden declarations and sorry: the
   sole sorry is finite_exactHom_degreeZero_lift, exactly by sorry. There are no data
   definitions or hidden holes. Explicit scratch-copy #print axioms probes for
   finite_algebraHom_exact, finite_exactHom_degreeZero_lift, and
   finiteDuality_degreeZero_counit_action each list only propext, Classical.choice,
   Quot.sound, and sorryAx. The exactness proof has no local hole but still uses open
   imported results; this delivery does not claim any sorry-free axiom closure.

3. Read the new statements, their proofs in words, and the recorded dependencies.
   Exactness uses dual_tensor_hom_iso naturally, tensor exactness for the locally free
   dual, and reflection through unchanged underlying abelian sheaves. It requires
   only the stated finite local freeness, including rank zero and variable rank.
   The remaining lift asserts an A-linear isomorphism and its derived counit equation,
   with the exact right-adjoint model explicitly supplied. It neither asserts nor
   hides either sectionwise clause. It is strictly the derived-comparison part of the
   original argument, not a renamed restatement. The identity morphism, empty scheme,
   zero module, and twists of the specified adjunctions all preserve this statement:
   right-adjoint uniqueness adjusts j to the specified counit. No cancellation or
   arbitrary data definition is used. Read Stacks Tags 0BUZ, 0AX2, and 0AX3 on the
   official site: they give the underived adjunction, finite derived right-adjoint
   comparison, and trace/counit compatibility respectively. The Noetherian hypotheses
   supply pseudo-coherence and quasi-compactness; eL and e0 supply bounded-below
   objects. The exact H comparison and full faithfulness of the A-module single
   functor account for the lift rather than an extra geometric hypothesis.
   Fresh searches used Loogle for rightAdjointUniq, LeanFinder for lifting degree-zero
   derived isomorphisms, and Mathlib grep for fully faithful single functors and
   derived-composite/counit comparisons. Local library searches also found
   finiteLocallyFree_derivedInternalHom_single and locallyFreeHomAbelianFunctor_exact;
   neither supplies the A-linear lift or its counit equation, and neither replaces
   the proved reflection argument for arbitrary H. The lift requires substantial
   localization compatibility work, so it was not closed in this reading.

4. Read the proof from the top: sheafHom_affine_rightAdjoint supplies the action and
   evaluation formulas, finite_algebraHom_exact proves exactness, and the lift gives
   j and the first conjunct. heval evaluated at j(omega) gives the second. The third
   uses map_smul, haction at Over.mk(identity), and Functor.map_id. These calculations
   work at zero sections and on empty opens. No shorter existing theorem found in
   the searches gives the complete result. Removed the unused proof import
   Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification from the exactness
   module and recompiled. All public imports serve signatures. Added plain proof-plan
   imports to the open lift for Derived.Adjunction, DerivedRHomAlgebraModule,
   FiniteAffineDerivedEquivalence, FiniteScalarRightAdjointQCoh,
   AffineSinglePushforwardUnitIso, and FiniteAffineDerivedFactorization; their
   dependencies remain needed. The previous
   No longer needed section names every old proof dependency absent from the item.
   The unit sk-thm-picard-duality has no realized statement or step nodes; its route
   is unchanged.

5. Compared the three node records with the Lean statements and actual assembly.
   The lift repair removes the existential `finite_affine_adjoint_counit_comparison`
   route. It now imports `FiniteAffineDerivedEquivalence` and
   `FiniteScalarRightAdjointQCoh`, constructs the same canonical gamma from exact
   restriction, the inverse derived-composite comparison, and `g_* ⋙ T = f_*`, and
   uses that gamma both to define beta/phi and in the final counit equation. The
   docstring and node proof[1] explicitly establish essential-image membership and
   the full-faithfulness argument making phi an isomorphism; proof[3] explicitly
   reuses this same gamma. No theorem signature changed.

Second reading changed proof-plan imports, removed one unused import, clarified the
new lift's canonical-comparison argument and matching DAG step, restored whitespace
at the original proof separator, and added this review. One original hole is closed
and one lower hole added: decomposition, with net zero holes closed. The additional
exactness theorem is proved locally without adding a hole.

The refreshed repository baseline also added direct DerivedCategory and
DerivedRHomAlgebraModule proof imports while this reading ran. Both are now listed
above as removed direct imports; their foundational declarations remain reachable
through the retained signature imports and exactness/lift modules.

## Earlier second reading (a previous round; superseded)

1. PASS. Independently diffed the original module and compared its theorem signature
   as bytes through the proof separator: unchanged, including hc and all three
   conclusions. The only existing node changes are proof, proof_deps, proof_origin.
   Both additional modules are new; no existing data definition changes.
2. PASS. Compiled all three modules in scratch-copy import order, with explicit
   #print axioms probes. Each reports only propext, Classical.choice, Quot.sound
   and sorryAx. The only delivered sorry is finite_exactHom_degreeZero_lift, a
   public named theorem with proof exactly by sorry. No forbidden declaration or
   data definition is introduced. Initial full compilations timed out under machine
   load; subsequent single-file and full scratch-copy compilation passed (main
   module 38.3 and 42.2 seconds). Reduced its heartbeat allowance to 500000.
3. PASS. Read both new signatures and proof docstrings. Exactness follows from
   the natural tensor-dual comparison and reflection through the unchanged
   underlying abelian sheaf; rank zero needs no exception. The open lift retains
   the specified adjunction and canonical hc, and supplies only the A-linear
   derived comparison, leaving evaluation and action to the assembly. It is a
   strict subargument, not a restatement of all original conclusions. Checked
   identity f, zero modules, empty schemes, and adjunction twists: right-adjoint
   uniqueness adjusts j and preserves the specified counit. Fresh Loogle search
   for CategoryTheory.Adjunction.rightAdjointUniq found the uniqueness/counit
   APIs, not this lift. Fresh local/upstream searches for degreeZero/lift and
   locallyFreeHomAbelianFunctor_exact found no duplicate A-linear comparison.
   Read the official Stacks pages [0AX2](https://stacks.math.columbia.edu/tag/0AX2),
   [0AX3](https://stacks.math.columbia.edu/tag/0AX3), and
   [0BUZ](https://stacks.math.columbia.edu/tag/0BUZ): the Noetherian, bounded-below,
   affine, and quasi-coherence assumptions needed by their comparison arguments
   are supplied here. The open lift requires substantial localization work and
   was not closed in this reading.
4. PASS. Read the assembly downward: underived Hom adjunction, exactness, lift,
   then heval at j(omega) and haction after map_smul and identity restriction.
   No cancellation is used. All public imports support signatures; the new
   proof imports support the exactness proof or the documented open lift plan.
   The No longer needed section covers every former item proof dependency absent
   from its new proof_deps. The unit sk-thm-picard-duality has empty realized
   fields, and its route is unchanged.
5. PASS. Read all three node files and the public statements of the cited affine
   equivalence, scalar-right-adjoint quasi-coherence, and factorization modules.
   The equivalence supplies full faithfulness and essential-image identification;
   the quasi-coherence theorem applies to the specified derived right adjoint at
   K, bounded below by eL. The lift constructs gamma from canonical comparisons,
   rather than choosing an unnormalized existential factorization. Its step 4
   uses the same gamma for the canonical counit identity. The assembly node's
   three dependencies match its actual calls; the exactness node matches its
   tensor and reflection proof.

Second reading changed only the main module's heartbeat allowance from 1200000
to 500000 and this report. No mathematical statement, definition, proof route,
node statement or import was changed. One original hole closed, one strictly
smaller hole added; net zero, a decomposition.

## Second reading by N3

1. PASS. Independently diffed the item against the repository and compared the
   existing theorem signature as bytes, from `theorem` through the proof separator:
   identical, including both derived-category universes, canonical comparison hc,
   and all three conclusions. The other two modules are new. The existing node
   differs only in proof, proof_deps and proof_origin. No definitions, existing
   interfaces or target statements change; no change record is required.

2. PASS. Compiled all three delivered modules in import order through lcompile.py:
   clean, at 33.1, 21.6 and 47.2 seconds. Scanned their full texts for forbidden
   declarations and holes. The only sorry is the public named theorem
   finite_exactHom_degreeZero_lift, exactly `by sorry`; no data definitions are
   introduced. Regenerated scratch copies with explicit #print axioms for all
   three declarations and compiled them in import order: each lists exactly
   propext, Classical.choice, Quot.sound and sorryAx. The sorryAx comes from
   the named remaining hole and existing open dependencies; this
   delivery is a decomposition, not a sorry-free closure proof.

3. PASS. Read both new statements and their complete proof docstrings, then the
   public statements of finite_affine_derived_equivalence,
   finite_scalar_right_adjoint_qcoh, affine_singlePushforward_unit_isIso,
   and finite_affine_derived_factorization. Exactness uses the natural dual-tensor
   identification, tensor exactness and reflection through the identical abelian
   sheaf. The lift supplies the A-linear comparison and counit equality, leaving
   both sectionwise clauses to the item. For identity f, twisting either specified
   adjunction changes the comparison j to compensate; for zero modules, rank-zero
   A and empty schemes the same full-faithfulness argument works. Arbitrary
   choices in these existential proof arguments create no public data definition.
   Read official Stacks Tags [0BUZ](https://stacks.math.columbia.edu/tag/0BUZ),
   [0AX2](https://stacks.math.columbia.edu/tag/0AX2) and
   [0AX3](https://stacks.math.columbia.edu/tag/0AX3). The Noetherian hypotheses
   give pseudo-coherence and quasi-compactness; eL supplies boundedness below.
   Fresh logged searches used Loogle for rightAdjointUniq_hom_app_counit,
   LeanFinder for lifting degree-zero isomorphisms compatibly with counits, and
   Mathlib grep for singleFunctor/isomorphism APIs. They found categorical
   infrastructure, not a duplicate A-linear sheaf comparison. Also searched
   local and upstream Lean for degreeZero/lift and locallyFreeHomAbelianFunctor_exact.
   The latter does not prove arbitrary algebra-valued H exactness or its counit
   comparison. The remaining lift requires localization compatibility work and
   cannot be closed by a short application of these results.

4. PASS. Read downward: obtain the underived Hom model and its formulas; prove
   its exactness; apply the lift; define e and epsilon; apply heval at j(omega);
   apply map_smul and haction at the identity object and eliminate the identity
   restriction with Functor.map_id. All sectionwise claims are actual proofs.
   Signature imports remain public and proof imports plain. The report lists
   all old item proof dependencies absent from its current proof_deps and
   distinguishes direct-import removal from global pruning. The unit
   sk-thm-picard-duality has empty realized statement/step fields, left unchanged.

5. PASS after clarification. Compared the nodes with signatures and proof calls:
   the item uses exactly the underived Hom theorem, exactness and lift; exactness
   uses tensor evaluation/exactness and scalar-restriction infrastructure. The
   lift constructs its prescribed gamma directly from canonical comparisons,
   rather than choosing the existential factorization theorem's arbitrary iso.
   Found one missing justification in step 3: the cited affine single-pushforward
   theorem is for a scheme morphism, whereas g has the direct-image algebra as
   codomain ringed space. Added the argument that exact derived scalar restriction
   takes the canonical g comparison to the canonical f comparison via the same
   gamma; exact restriction reflects isomorphisms through cohomology and the
   unchanged abelian sheaf. Thus the g comparison is invertible. Updated the new
   lift docstring and matching node step, including its dependency citations.
   No signature, mathematical statement, import or proof body changed.

Second reading changed the lift's written proof and corresponding node step to
justify the algebra-valued canonical single comparison, and added this review.
One original hole closed, one strictly smaller hole added: net zero, decomposition.
The new exactness theorem is proved without a local hole.
