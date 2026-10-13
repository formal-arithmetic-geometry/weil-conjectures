## What changed

Completed the three-clause proof of
`ModuleCat.finitePresentation_descent_directedColimit` in
`Sheaf.Algebra.FinitePresentationColimit`, using three new proof-only imports. The second reading additionally proves the finite
tensor-vanishing helper from the existing directed base-change elementwise theorem.
The object proof takes Mathlib's finite free presentation, constructs the stage
module as an explicit lifted quotient by the relation-map range, proves its finite
presentation, and identifies the final extension by the quotient-kernel equivalence.
The map proof uncarries the given map, lifts it, constructs both comparison
isomorphisms from Mathlib's `extendScalarsComp`, and proves the commuting square
on unit tensors. The equality proof uses finite generators, differences of their
images, eventual tensor vanishing, span extensionality, and the adjunction bijection.
The private, proved `exists_comparison` helper constructs the comparison isomorphisms.

Corrected the intermediate theorem's accidentally unconstrained module universes.
Each clause independently uses a common module universe containing the ring universe:
`max u v`, `max u w`, or `max u z`. The algebraic hypotheses and conclusions are
unchanged. No target of `Challenge.lean`, nor any definition used by a target, changes.
The change record is
`coord/changes/finitePresentation_descent_directedColimit-universes.md`.

Read the node, its elementwise-colimit dependency, and the unit record
`dag/units/sk-thm-picard-semicon.json` (no realized statements or steps are bypassed).
The local literature checkout omits the downloaded Stacks source; read the official
texts at https://stacks.math.columbia.edu/tag/05N7 and
https://stacks.math.columbia.edu/tag/05LI. Mathlib searches were run through msearch
and additionally rg across Mathlib, WeilConjectures, Sheaf, and the DAG. LeanSearch
returned HTTP 500 and is recorded as unavailable, never as no match. LeanFinder,
Loogle, and source searches supplied finite presentations, adjunctions, tensor
right exactness and tensor/direct-limit constructions, but no exact descent theorem.

The four delivery modules compile without warnings using lcompile --all. All seven
unchanged direct importers compile against the changed module. The largest importer,
`Sheaf.AlgebraicGeometry.FinitePresentationModuleMapDescent`, initially exceeded the
60-second overlay limit, then passed its baseline check in 11.8 seconds and its
overlay recheck in 53.1 seconds. Its source is unchanged. No forced adaptations are
included. The delivery dry run passed; nothing was pushed.

## Proved and sorry left

Closed the hole in `ModuleCat.finitePresentation_descent_directedColimit`, after the
explicit universe correction described above, by a complete Lean proof from three
strictly smaller statements, one of which is now proved. This is a decomposition, not a sorry-free proof of the
whole descent theorem: one upper hole is replaced by two lower holes (net -1).
No sorry remains in the item's module; the private comparison helper is proved.
The original malformed universe instance is not claimed to be proved.

The delivery adds exactly two remaining holes, each in its own new module:

- `ModuleCat.exists_stage_finite_relation_cokernel`, node
  `lem-pc-finite-relation-cokernel-colimit`, module
  `Sheaf.Algebra.FiniteRelationCokernelColimit`: descend a specified finite relation
  map's quotient, without any module finite-presentation assumption or conclusion.
- `ModuleCat.exists_stage_restricted_hom`, node
  `lem-pc-fp-restricted-hom-colimit`, module
  `Sheaf.Algebra.FinitePresentationRestrictedHomColimit`: lift a map whose domain is
  the original stage module into a stage tensor target, without a finite-presentation
  assumption on the target. Construction of the scalar-extended map and its
  comparison square are proved in the item, rather than assumed in this lemma.
The new `ModuleCat.exists_stage_finite_tensor_vanishing`, node
`lem-pc-finite-tensor-vanishing-colimit`, is proved in the second reading from
`TensorProduct.directedColimitBaseChangeElementwise`, with explicit tensor
transition maps and finite-set induction. It adds no hole. This helper
depends only on standard axioms; the combined descent theorem still has sorryAx
through its object and map clauses. Those two clauses still use
the two holes listed above.

Both remaining holed proofs are exactly `:= by sorry`, in named public theorems with source,
proof in words, and blueprint tags. No data definition has sorry, and no exported
definition selects an arbitrary witness of an unproved existence theorem. Local
existential witnesses occur only inside the proof of the descent existence result.

Edge cases checked for the new statements: m=0 and n=0 in the relation presentation;
empty generating or relation sets; zero source and target modules; empty vanishing
set (j=i suffices); constant and singleton systems; noninjective transition maps;
and a zero final ring. The restricted-Hom and vanishing lemmas need no finiteness
of the target, in agreement with Tag 05LI. Directedness is used only for finitely
many upper bounds and eventual equations.

## No longer needed

No original import is removed. Removed the unnecessary public import of
`Mathlib.Algebra.Module.FinitePresentation` from the new cokernel and vanishing
modules: their signatures do not use finite presentation. No node or module is
claimed pruned. The former
direct proof dependency `lem-pc-filtered-colimit-commrings-elementwise` remains
needed below the new lemmas; the item's updated proof_deps lists its three actual
proof modules instead. The target's finite-presentation hypothesis on N is retained,
although the map and equality assembly does not use it. This is not import pruning.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox had no proof edits, only search logs. The original natural
language node is correct, but the Lean signature adds an unintended universe-size
requirement: its final module can lie in max(u,v) while its existential stage model
must lie in v, even when v does not contain the ring universe. For a constant diagram
of a field K which is not Small in v, take the finitely presented regular module K.
A nonzero stage model small in v would admit an injection K into its carrier by
scalar multiplication of a nonzero vector, contradicting non-smallness of K. Thus
that inferred signature is not the source theorem. Explicit common module universes
and real ULift quotient constructions fix it. The node's statement_change records
the size convention, source, old statement and all mathematical citers. The change
record contains old and new signatures and all import dependents and their holders.
A repository-wide search finds no Lean application outside the item, so no existing
proof needs adaptation.

The planned finite-presentation condition on the target is stronger than needed
for map descent and eventual equality: Tag 05LI proves the corresponding assertions
for an arbitrary target. The new helpers exploit this without changing the item's
algebraic hypotheses or bypassing the unit route.

## New nodes

`lem-pc-finite-relation-cokernel-colimit` formalizes the finite relation matrix and
cokernel step of Tag 05N7 (1). It has an explicit matrix-sized input and concrete
quotient output, leaving the finite-presentation proof and identification with the
original module to the item. The module-universe lift is canonical, not chosen from
an unproved existence assertion.

`lem-pc-fp-restricted-hom-colimit` formalizes the finite generator and relation
lifting argument of Tag 05LI (3) as an uncurried map. Its proof plan uses the
existing ring-element representation criterion and the finite tensor vanishing
node. The item's adjunction and comparison-isomorphism assembly supplies the
scalar-extended map demanded by the original theorem.

`lem-pc-finite-tensor-vanishing-colimit` formalizes the finite element equality step
used in Tag 05LI (1). Its proved implementation uses the existing directed
base-change elementwise theorem to detect each zero at a later stage, and
synchronizes those finitely many stages by induction. The item proves the passage from this statement to
map equality on the span of finite generators.

Each new node records actual searches, including LeanSearch's
unavailability. Blueprint ancestor is `lem-pc-rf-perfect-base-change`, via
`lem-pc-fp-module-map-descent-affine`. The finite-set vanishing statement is a proved corollary of the existing directed
base-change elementwise node; the two remaining holed statements have no exact
match in the searched library. Change record:
`coord/changes/finitePresentation_descent_directedColimit-universes.md`.


## Second reading by V4

1. Compared every delivered module with the repository. Three helper modules are
   new. The only existing public declaration is the descent theorem; its only
   signature edits are the explicit common module universes declared in the change
   record. The old and new signatures in that record match the respective source
   signatures byte for byte. Independently compiled the original with
   `pp.universes`: its object clause really requests a Type v stage model for a
   Type (max u v) final module. The constant large-field counterexample validates
   the correction. All algebraic hypotheses, conclusions and comparison equations
   stay unchanged. No Challenge statement or definition changes. Repository-wide
   name search finds no application outside this module; all seven direct users
   only import it. Verdict: pass with the declared intermediate statement repair.

2. Independently compiled all four modules with lcompile, without errors or
   warnings. Scanned the sources: no forbidden axiom, unsafe, opaque, extern or
   implemented_by; no definition or partial proof contains sorry. Scratch-copy
   `#print axioms` verifies the private comparison helper uses only propext,
   Classical.choice and Quot.sound. The descent theorem uses those plus sorryAx
   from exactly the two remaining public helper holes. The now-proved vanishing
   helper uses only the three allowed axioms. Verdict: valid decomposition, not a
   sorry-free proof of the descent theorem.

3. Read the two holed statements and all their docstrings and nodes, checking
   zero rows/columns, empty relation sets, zero modules, constant diagrams,
   noninjective transition maps, and zero final ring. The cokernel statement
   descends concrete finite relation data and leaves the finite-presentation and
   quotient-kernel assembly to the item. The restricted-Hom statement needs finite
   presentation only of the source and leaves the adjunction and commuting-square
   assembly to the item. Both are true strict parts of the argument. Re-read Stacks
   Tags 05N7 and 05LI online. Independent LeanFinder, Loogle and msearch grep queries
   used tensor/direct-limit and linear-map vocabulary; additional rg searches read
   the existing sheaf-Hom, algebra tensor-colimit and directed base-change modules.
   This found a shorter route for finite tensor vanishing, now proved. No exact
   existing declaration supplies either remaining hole. Verdict: pass after repair.

4. Read the proof top down: finite free presentation, explicit ULift quotient,
   finite generation of the relation range, quotient-kernel equivalence; adjunction
   and canonical comparison isomorphisms; generator differences and span
   extensionality. Every import of the item and every public helper import is
   needed by a signature or the proof; proof dependencies are plain imports.
   The old direct ring-elementwise dependency is replaced by the three actual
   helpers, and remains below the two open helpers. No module is claimed pruned.
   Read sk-thm-picard-semicon and its realized fields (empty statement and step
   lists); no realized node or unit step is bypassed. Verdict: pass.

5. Checked all four node Lean signatures verbatim against the module sources and
   checked proof_deps against uses. The item's three proof steps match the actual
   proof. Updated the vanishing node to cite the existing directed base-change
   elementwise node and describe the proved finite-set induction; retained source,
   blueprint ancestry, created metadata and searches. New nodes have all fields
   required by brief-stage3 section 3. Verdict: pass after dependency repair.

Changed in this second reading: proved
`ModuleCat.exists_stage_finite_tensor_vanishing` using the existing
`TensorProduct.directedColimitBaseChangeElementwise`, explicit linear tensor
transition maps and finite-set induction; added its plain proof import; updated
its docstring, DAG proof and proof_deps, and this report. Retained the required
`statement_change.by = "V4 stage 2"` schema label; preflight requires that form
for statement repairs even in stage 3.
No other proof or signature was rewritten. Final accounting: one original hole
repaired/decomposed, two new holes, one new helper fully proved; net -1 hole.
