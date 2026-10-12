## What changed

Completed the earlier sandbox reduction of
`Sheaf.AlgebraicGeometry.IntegralConstantModulePushforwardColimit`.
The original theorem signature and docstring are unchanged. Its proof chooses the existing
finite approximation, reverses its small cofiltered index, constructs the direct-image diagram
and its canonical cocone, supplies identity stage isomorphisms, and applies the limit-comparison
lemma. Affineness and qcqs instances are inferred from the finite approximation and integral
morphism. The combination is complete Lean and compiles.

Added two modules, `Sheaf.AlgebraicGeometry.ConstantModulePushforwardFunctoriality` and
`Sheaf.AlgebraicGeometry.ConstantModulePushforwardLimit`. Their definitions contain no sorry;
functor and cocone laws refer to the named functoriality obligation. Both new modules explicitly
disable autoImplicit. Updated the original node's proof, proof_deps and proof_origin to match
this reduction. No existing statements or definitions were changed.

Checked the source finite-approximation proof, the canonical constant-sheaf comparison,
existing planned dependency signatures, and Stacks Tags 09Z1 and 09Z6. Repeated LeanFinder,
Loogle and source searches found no direct result with this interface. All three modules compile
locally in dependency order.

## Proved and sorry left

Proved, from recorded obligations:
`AlgebraicGeometry.Etale.exists_filtered_colimit_finite_lowerStar_constant`
(node `lem-weil-pbc-integral-constant-module-pushforward-colimit`).
The item's one original sorry is gone. The delivery leaves exactly these two named sorries:

- `AlgebraicGeometry.Etale.constantModulePushforwardMap_id_comp`, in
  `Sheaf.AlgebraicGeometry.ConstantModulePushforwardFunctoriality`, node
  `lem-weil-pbc-constant-module-pushforward-functoriality`.
- `AlgebraicGeometry.Etale.isColimit_constantModulePushforwardCocone`, in
  `Sheaf.AlgebraicGeometry.ConstantModulePushforwardLimit`, node
  `lem-weil-pbc-constant-module-pushforward-limit`.

These are genuine parts of the argument. The first supplies identity/composition coherence
for all modules and scheme morphisms, without integral or finite approximation hypotheses.
The second asserts the universal property of a specified cocone for a given affine inverse
system, without producing a finite approximation or finite stages. The main proof constructs
all witnesses from the separate finite-approximation theorem. The delivery does not claim an
axiom-free closure while these obligations remain open.

Edge checks: the general comparison covers zero modules, empty schemes and a singleton index.
The cofiltered hypothesis excludes the empty index. On a singleton index, the scheme limit
projection is an isomorphism, so the indicated cocone is a colimit. Constant pullback
comparisons and forgetting coefficients work for arbitrary modules; no finite-module
assumption is needed in either new lemma.

## No longer needed

No imports were removed from the original library module; its four public imports support
its unchanged statement. The two added imports are proof-only.
Removed the earlier sandbox helper's unused public import
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence`: the constructions already have
all required definitions through `WeilConjectures.ConstructibleSheaf.Defs`.

The new limit node uses the existing Mathlib leaf
`lem-weil-pbc-filtered-category-exists-directed-final`
(`CategoryTheory.IsFiltered.exists_directed`) directly. It does not need
`lem-weil-pbc-filtered-category-directed-cofinal` or
`Sheaf.CategoryTheory.ExistsDirectedReindexing` as a dependency.

The original top-level dependencies `sbc-lem-higher-direct-image-limit`,
`lemma-constructible-pullback-constant`, `def-weil-pbc-category-colimit`, and
`def-weil-pbc-direct-image` have moved into the new obligations or their statement
imports; they are not globally pruned. The unit's own statement and realized steps stay.
No other existing node or module is claimed to be globally unnecessary.

Second reading removed the redundant public import
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` from the new limit module.
The public functoriality import already supplies its statement types and instances;
the whole delivery compiles without this extra import.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt had compiling Lean and nodes but no report or successful dry run.
Its limit node cited the weaker directed-reindexing statement while invoking finality
and transferring a colimit back. The node now cites Mathlib's actual directed final-functor
existence theorem, which gives preservation and reflection in both directions.

The planned higher-direct-image result is for abelian sheaves indexed by a directed preorder
and returns a derived-degree comparison. The item is an existential statement for module
sheaves indexed by an arbitrary small filtered category. Applying the existing theorem
requires reindexing, degree-zero identification, constant-sheaf coherence and coefficient
comparison. These are recorded in the new limit obligation, not hidden inside a definition.
Likewise, `ModuleSheavesColimitsForgetful` is stated for `SheafOfModules` over a ring sheaf,
whereas this item uses `Sheaf ... (ModuleCat Λ)`; the coefficient comparison is still part of
the recorded obligation. Existing `lowerStarConstantSheafMapOfOver` functoriality concerns
the monoidal unit Λ, not arbitrary M, so it does not directly discharge the new coherence
statement. No mathematical counterexample to the statements was found.

## New nodes

`lem-weil-pbc-constant-module-pushforward-functoriality`: canonical transition maps between
constant-module direct images preserve identities and composition. The module defines the
maps using actual adjunction and comparison morphisms and leaves only their laws as a
named theorem. Source: Stacks Tag 09Z1 and Tag 09Z6's finite approximation paragraph.

`lem-weil-pbc-constant-module-pushforward-limit`: the canonical cocone of constant-module
direct images for an affine cofiltered inverse system with qcqs structure maps is a colimit.
Its proof in words records final directed reindexing, constant pullback identification,
Tag 09Z1 in degree zero and transfer of the universal property to module sheaves.
Source: Stacks Tag 09Z1 and Tag 09Z6's finite approximation paragraph.

No change records are needed: no existing signature or definition changed.


## Second reading by S1

1. Compared the delivered original module with the repository by diff. The only
   changes are two plain, proof-only imports and the body of
   `exists_filtered_colimit_finite_lowerStar_constant`. Its signature and docstring
   are byte-for-byte unchanged. Compared the existing node as parsed JSON: only
   `proof`, `proof_deps`, and `proof_origin` differ. No existing definition, target,
   or other module is changed. Verdict: pass.
2. Compiled all three modules in dependency order through lcompile.py, with no
   errors or warnings. Searched the complete delivered sources: the two listed
   named theorem obligations are the only sorries, with no forbidden declarations
   or implementation attributes. A scratch copy with #print axioms for the map,
   its coherence theorem, diagram, cocone, colimit theorem, and original theorem
   showed only propext, Classical.choice, Quot.sound, and (except for the map)
   sorryAx. The map itself uses only the standard three axioms. The diagram and
   cocone have concrete data; their law proofs use the named coherence theorem.
   Verdict: pass as a reduction with two open obligations, not an axiom-free proof.
3. Read etale-cohomology.tex, label lemma-relative-colimit (Tag 09Z1), and
   Tag 09Z6's finite approximation paragraph, lines 12999–13008. The new limit
   lemma retains the affine-transition and qcqs-stage and qcqs-limit hypotheses
   of 09Z1. Constant coefficients are a genuine special case of its sheaf system;
   passing to arbitrary modules uses the sectionwise linear structures and
   sheafification, not a finite-module assumption. Checked singleton indexing
   (the projection is an isomorphism), zero M, and empty schemes. Cofilteredness
   excludes an empty index. The coherence equalities have the correct reversed
   composition order. Both new theorems have source/docstring proofs and matching
   nodes. Independently searched via LeanFinder for direct-image continuity,
   Loogle for constantCommuteCompose, and grep for adjunction/restriction/transition
   results, plus rg over the project and upstream. Read ConstantSheafMap.lean:
   its theorem is for the monoidal unit, not arbitrary M. Read the existing
   HigherDirectImageLimitSystem and ModuleSheavesColimitsForgetful interfaces:
   their derived/abelian and ring-sheaf interfaces require the adaptations
   recorded in the new limit obligation. No exact duplicate or few-minute
   discharge was found. Verdict: both obligations are true proper parts of the
   argument; neither supplies the original finite-approximation witnesses.
4. Read the original reduction from its first obtain to its final exact. The
   finite approximation supplies the small cofiltered category, finite stages,
   affine transitions, compatible projections, and limit proof; reversing the
   category and taking Iso.refl gives the exact required existential witnesses.
   The remaining comparison is strictly the second part of this construction.
   All four old proof dependencies removed from the top node are explicitly
   accounted for in No longer needed; they remain in statement dependencies or
   the new obligations, so no global pruning is claimed. Read sk-thm-p1.json:
   neither the unit statement nor any realized step is bypassed or changed.
   Removed the redundant QuasiSeparated import from the new limit module and
   recompiled the entire delivery. Verdict: pass.
5. Checked each node's Lean statement verbatim against its theorem, each
   proof_deps list against the union of proof-step uses, and the new-node source,
   creation, blueprint, chapter/unit, search, status, and Lean records. The
   original node records the finite approximation and the two actual obligations;
   the new nodes explain coherence and continuity respectively. The coefficient
   and degree-zero adaptations remain explicitly open, as the report says.
   Verdict: DAG and Lean agree at the level of this partial reduction.

Changed only the redundant import and this review/pruning documentation.
