## What changed

Reduced `AlgebraicGeometry.flat_telescope_normalization_unshifted_isIso` to the strictly
smaller stage-sum obligation in the new proof-only import
`Sheaf.AlgebraicGeometry.FlatTelescopeSumComparisonIsIso`. The original public
signature, universes, hypotheses, and public imports are unchanged.

The original plan calls for a morphism of distinguished triangles using the normalized
translated-unit map. That is unnecessary. Extract the existing triangulated shift structure
from `exists_derivedPullback`. Transport alpha on the sum representative and its translate.
Use the given normalized shift equation only to prove invertibility of the translated
component, not to identify it with the existing triangulated shift structure. Naturality
then gives a commutative five-term exact-sequence diagram. Three proved private helpers
provide the five lemma, transport of naturality, and transport across functor shift
isomorphisms. The last step proves invertibility of the literal cone component.

Updated the item's DAG proof and introduced one matching node for the sum-only obligation.
No definitions, existing signatures, other held modules, or target statements changed.
The unit record sk-thm-picard-duality has empty realized statement/step arrays; the route
change is below that level and keeps the parent's finite-stage/sum/cone argument.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.flat_telescope_normalization_unshifted_isIso`
(node `lem-sc-flat-telescope-normalization-unshifted-is-iso`). Its module now has no sorry.

Added one named hole:
`AlgebraicGeometry.exists_flat_telescope_sum_comparison_isIso`
(node `lem-sc-flat-telescope-sum-comparison-is-iso`), whose proof is exactly `by sorry`.
It asserts an invertible comparison only on a representative of the sum of bounded-flat
stages. It has no transition maps, no cone comparison, no shifted-unit isomorphism, and
no shift equation. It is strictly part of the original argument, not the original theorem
under another name. The caller proves the translation and arbitrary transition-cone steps.
This is a decomposition: one upper hole closed, one lower hole added, net zero holes.

The private `cone_five_lemma`, `transport_naturality`, and `shifted_transport_comm` are
fully proved. No sorry was put in any definition or private helper. Destructing the
existential sum presentation occurs inside the proposition proof; no data definition
chooses an arbitrary witness from the unproved lemma.

## No longer needed

Removed the item's proof import `Sheaf.AlgebraicGeometry.FlatTelescopeStageMapRefinement`:
node `lem-sc-flat-telescope-stage-map-refinement` and its common arrow/tower refinements
are not used by this proof. Naturality already applies to every homotopy morphism between
representatives, and the literal cone is available by destructing isFlatTelescope.

Removed the item's direct proof import `Sheaf.Algebra.Homology.KFlatTelescopeClosure`.
The cone argument uses exactness of functors, not a separate K-flatness proof. The new
sum node still needs the flat-coproduct clause of `lem-pc-kflat-closure`; that node is
therefore not claimed globally pruned, and its proof import will be needed when the
sum-only lemma is proved. The proof does not need common flat refinements, a normalized
triangle-image theorem for the arbitrary supplied e, or a proof that the fourth vertical
map is the shift of the first. Definitions used in the unchanged public signature stay.

No assertion is made that the removed refinement module is unreachable from every other
target branch; pruning here records that this item's route no longer needs it.

## Where the brief, the DAG or earlier work was wrong

The original proof dependencies do not state the sum-comparison obligation. In particular,
KFlatTelescopeClosure states K-flat/flat closure, not existence of a split homotopy telescope
presentation with invertible alpha. That missing step is now a named, documented node.

The original plan's triangle morphism is more than the hypotheses immediately provide:
the supplied normalized translated-unit comparison need not be the particular triangulated
shift structure extracted from derived pullback's specification. The five-term proof avoids
that identification entirely. Its fourth vertical component is allowed to be independent
of the shift of its first, and naturality at the shifted endomorphism gives the final square.

Checked the new statement on a zero tower, the empty scheme, a constant bounded tower,
and a tower with bounds increasing without a uniform bound. The split finite-partial-sum
construction and coproduct argument apply to each; only finite maxima are taken.

Mathlib searches used leanfinder, loogle, and grep. LeanSearch returned HTTP 500 and is
recorded as unavailable, not as a negative search. Blueprint searches for telescope and
direct sum found no duplicate of the restricted sum-comparison theorem. The Stacks pages
06YS and 06YJ were read: they supply flat-resolution and derived-exactness context;
the restricted alpha/presentation argument is explicitly marked as an agent expansion of
the parent's step 1, not as a literal statement of those tags.

## New nodes

`lem-sc-flat-telescope-sum-comparison-is-iso` is stated in
`lean/Sheaf/AlgebraicGeometry/FlatTelescopeSumComparisonIsIso.lean`.
It isolates only the finite-partial-sum presentation and invertibility-on-sums part of
parent step 1. Its docstring and node describe the explicit split augmentation, constant
telescope models of the bounded stages, coproduct preservation, and componentwise inverse.
There are no change records or forced adaptations.

## Second reading by E1

1. Compared the delivered normalization module with the repository version. The public theorem signature and its public imports are byte-for-byte unchanged; only proof imports, private helpers, and the proof body changed. Verdict: pass.

2. Both delivered modules compile with lcompile.py --all. The normalization theorem has no sorry; the only remaining sorry is the named public sum-comparison theorem. No forbidden declarations or hollow definitions occur. The five-term helper proves the necessary Yoneda exactness argument with an independently invertible fourth component. Verdict: pass.

3. The sum statement is a strict intermediate: it has a family of bounded-above flat complexes and proves existence of a telescope representative with invertible comparison. It omits transition maps, shifted-unit data, and the arbitrary cone conclusion. The finite partial-sum/tail splitting works for zero towers, empty schemes, constant bounded stages, and varying bounds. Independent leanfinder, loogle, Mathlib grep, and local library searches found no duplicate. TelescopeColimit gives only a quasi-isomorphism; FilteredFreeKProjectiveAssembly concerns filtered free ModuleCat complexes, not this sheaf-complex homotopy equivalence. Closing the new hole requires formalizing this splitting and coproduct transport; it is not a few-minute application. Verdict: pass.

4. The proof uses the existing triangulated derived pullback structure and a direct five-term argument below the unit level. Generic triangle two-out-of-three requires a shifted-component identity unavailable here, so it does not shorten this proof. Both removed proof dependencies are listed under No longer needed; all remaining public imports serve the unchanged statement. The new module imports exactly its statement dependencies. Verdict: pass.

5. The normalization DAG proof and dependencies match the Lean proof. The new node records the sum-only obligation, source expansion, complete proof, and searches. The unit route remains unchanged; its realized arrays were already empty. No definition is introduced, and existential witnesses are eliminated only within the proposition proof. Verdict: pass.

Changed the new sum lemma's docstring to give the explicit summand-tail splitting, including its finite partial-sum inverse, and corrected its bounded-stage wording from B_n to E_j. Removed two unused shift-definition stmt_deps from the new node and added independent search results. The existing theorem docstring is preserved; its original triangle-morphism/refinement narrative is superseded by the proof and DAG route described above.

Sources reread: https://stacks.math.columbia.edu/tag/06YS (flat resolutions) and https://stacks.math.columbia.edu/tag/06YJ (exactness of derived pullback). The new node correctly labels the restricted comparison argument as an agent expansion rather than a literal statement of these tags.

Axiom probes: cone_five_lemma and shifted_transport_comm use only propext, Classical.choice, and Quot.sound; transport_naturality is axiom-free. The main theorem and new sum theorem use those permitted axioms plus sorryAx from open obligations. The probe copy reported one docstring line-length warning, repaired in the delivered source before the final clean compile.
