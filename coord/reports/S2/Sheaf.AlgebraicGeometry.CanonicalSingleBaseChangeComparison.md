## What changed

Proved AlgebraicGeometry.Scheme.Modules.canonicalSingleBaseChangeComparison with its original
signature and public imports unchanged. The proof uses derivedBaseChange_unit_compatibility,
left-derived counit naturality, right-derived unit naturality, and cancellation of the
adjunction-preserving tensor-to-ordinary pullback comparison. The final calculation states the local composites explicitly and applies a proved generic
category lemma for functoriality and cancellation under the two functors.

Added Sheaf.AlgebraicGeometry.HomotopySingleBaseChangeComparison, with a proved public theorem
and two proved private helpers. The main module also has three proved private helpers
for naturality and functorial cancellation. The helpers prove the single-complex equation for arbitrary
additive functors by degree-zero extensionality, then apply the homotopy quotient. Specializing
to the natural transformation moduleBaseChangeMap gives the ordinary equation used above.
Both node records now describe the completed proofs. No existing interface changes or forced
adaptations are needed.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.Scheme.Modules.canonicalSingleBaseChangeComparison
(lem-sc-canonical-single-base-change-comparison).

Also proved the new theorem AlgebraicGeometry.Scheme.Modules.homotopySingleBaseChangeComparison
(lem-sc-homotopy-single-base-change-comparison); its two private helpers are proved.
No sorry remains in either delivered module. Holes closed: 1; holes added: 0; split off: 0.
The existing sorry AlgebraicGeometry.derivedBaseChange_unit_compatibility is used unchanged,
as intended by the assigned node's original plan. Thus the delivery closes a local hole;
it does not claim that the transitive axiom closure is already sorry-free.

## No longer needed

No original import, node or module is pruned. The three original proof dependencies remain
used through the comparison definitions and derived unit compatibility. No invertibility,
flatness, acyclicity, cartesianness or nonemptiness assumption is added. The new ordinary
comparison theorem is proved in this delivery, so it creates no further proof item.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox claimed completion of the main proof, but its final broad simp exceeded
the single-file compile limit. Explicit local composites and proved generic category calculations now replace that simp. Its proposed
ordinary homotopy hole has also been proved: generic additive-category helpers avoid costly
scheme-category alias reduction inside the quotient calculation. The earlier new node's Lean
statement used pushforward aliases whereas its module used RingedSpace.moduleDirectImage;
the record now matches the actual declaration verbatim.

The original node's Tag 08HY is the general derived mate construction, rather than an explicit
single-complex compatibility theorem. The single-complex calculation is the formal termwise
argument described in the node; Mathlib's single and quotient constructions supply its proof.
The unit sk-prop-av-cube and its realized statement and steps are unchanged.

## New nodes

lem-sc-homotopy-single-base-change-comparison, in
lean/Sheaf/AlgebraicGeometry/HomotopySingleBaseChangeComparison.lean, records the proved ordinary
homotopy exchange identity. It assumes additive tensor pullback and contains no derived-category
hypotheses or derived units/counits. It is strictly the ordinary part of the parent's argument.
Its direct parent and precise proof step are recorded in blueprint.from, retaining the earlier
sandbox ancestry. Zero modules and empty schemes satisfy the generic degree-zero calculation.
Searches found single-complex comparison component formulas and quotient functor definitions,
but no existing scheme exchange identity with these comparisons. No change record is needed.

## Second reading by S2

1. Compared the main module with the repository version and checked the existing
   theorem signature byte for byte. Verdict: unchanged; no target, definition,
   public import, or existing visibility changes. The added module contains only
   proved theorems and private proof helpers.
2. Read every proof. The ordinary helper postcomposes with a single-map
   isomorphism, uses to_single_hom_ext, and checks degree zero; its next helper
   maps that equality through the quotient. The main proof applies the recorded
   derived unit compatibility, naturality, functoriality and cancellation of
   t_g.hom followed by t_g.inv. No derived comparison is inverted. There is no
   sorry, axiom, unsafe, opaque, implemented_by, extern or hollow definition in
   either delivered file. Local compilation and the delivery axiom probe are
   required below; transitive sorryAx from existing open dependencies is allowed.
3. No statements remain split off with sorry. The new proved ordinary statement
   has precisely the four morphisms, commutative-square equation, arbitrary
   module and additive tensor-pullback instances used in the proof. It has no
   derived-category or geometric assumptions. Zero modules and empty schemes
   are included: the generic argument works in any additive categories with
   zero objects, by degree-zero extensionality. Repeated searches with Loogle
   (to_single_hom_ext), LeanFinder (homotopy quotient single-object exchange),
   and rg on both library roots and Mathlib found component and quotient
   comparison lemmas, but no existing scheme comparison of this type.
4. Read the original proof plan and the sk-prop-av-cube unit record. The proof
   keeps the derived-unit route and all three original proof dependencies;
   no old dependency becomes unnecessary. The unit's realized record is
   unchanged (its existing statement/step lists are empty). The new theorem
   proves the ordinary termwise part, not a restatement of the derived item.
   The new module's public import supplies moduleHomotopyBaseChange in its
   signature; the main module's new import is proof-only and plain import.
5. Compared both node signatures with the Lean text verbatim and checked the
   proof steps, proof_deps, proof_origin, ancestry, source, searches, created,
   unit and chapter fields. Verdict: they describe the actual argument. The
   ordinary node's proof dependencies provide base-change naturality and the
   adjunction comparison; the imported homotopy-exchange definition is a
   statement dependency, not an appeal to the still-open derived theorem.

Changed the main proof's elaboration: infer the ordinary comparison's type
instead of repeating it, specify the right-unit naturality objects and generic
helper categories, and prove the final definitional alias equality explicitly.
The first author's version exceeded the 60-second compile limit. No mathematical
statement or proof route was changed; no holes were added. Both Lean files also
satisfy the 100-character line limit. Final compiler and preflight results are
recorded after the required dry run.

Validation: both modules compiled cleanly in the required dry run and preflight
printed OK (CODEX because it adds the proved ordinary node/module). A scratch
#print axioms check reports [propext, Classical.choice, Quot.sound] for
homotopySingleBaseChangeComparison and those plus the existing sorryAx for
canonicalSingleBaseChangeComparison. No new sorry is introduced. The delivery
probe also passed. The existing theorem signature and both recorded Lean
signatures were checked byte for byte; neither Lean module has overlong lines.
