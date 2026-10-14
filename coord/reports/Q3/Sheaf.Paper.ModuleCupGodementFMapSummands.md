## What changed

Retained and checked the inherited proof of
`AlgebraicGeometry.Scheme.Modules.moduleCup_godement_fmap_summands` without changing
its signature or original docstring. Added two proof-only imports:
`Sheaf.Paper.ModuleCupGodementFMapModels` and
`Sheaf.Paper.ModuleCupCosimplicialFMapSummands`.

The first new module states only the augmented cosimplicial Godement coordinate
construction and its degreewise tensor square. The second constructs the three
extended chain maps explicitly, proves their differential equations using additive
pushforward and coface naturality, and proves their front/back section identity.
The original module evaluates the augmentation morphism equations on pure tensor
sections and cancels the degree-zero extension isomorphisms to assemble the result.
This is a reduction with substantial completed complex-level work, not a full proof
of the Godement construction. No data are chosen into definitions from an unproved
existence theorem: the private chain-map definitions are explicit and fully proved.

Updated the original DAG node's proof, proof_deps and proof_origin to record this
route. Added matching records for both new modules. Checked the existing attempt,
compiled all three modules again, removed the redundant public FunctorCategory import
from the new Godement module, and added proof comments explaining the negative-degree
boundary case and the front/back naturality calculation.

## Proved and sorry left

Closed the original module's one direct hole:
`AlgebraicGeometry.Scheme.Modules.moduleCup_godement_fmap_summands`
(node `lem-sc-module-cup-godement-fmap-summands`). Its proof is complete relative to
the new Godement construction theorem below. No sorry remains in this module.

Fully proved, with no direct sorry:
`AlgebraicGeometry.Scheme.Modules.moduleCup_cosimplicial_fmap_summands`
(node `new-module-cup-cosimplicial-fmap-summands`). The private helpers
`app_inv_hom`, `crossComponent_nat`, and `crossComponent_comm` are also proved;
`crossComponent` and `crossMap` are actual constructions, not chosen witnesses.

Added one remaining hole:
`AlgebraicGeometry.Scheme.Modules.moduleCup_godement_fmap_models`
(node `new-module-cup-godement-fmap-models`), whose whole proof is `:= by sorry`.
Its docstring and node describe the semilinear stalk maps, unit and multiplication
checks, iteration, transport to the six given models, and coordinate tensor square.
It asserts neither extended chain maps nor Alexander–Whitney summand compatibility.
Thus one upper hole is closed and one lower hole is added: a decomposition, net zero
holes, rather than a claim of a sorry-free proof of the original theorem.

Validation: all three single-file compiles in sandbox import order pass, with times
13.1, 4.4 and 7.0 seconds respectively on this resumed run. The delivery dry run
printed OK, passed the axiom and static checks, and left only the second reading
for the independent reader. Nothing was pushed. The original theorem signature
was compared verbatim with the repository and is unchanged; the three node
proof_deps lists each equal the union of their proof-step uses. Empty schemes, zero coefficients,
degree (0,0), and degree -1 were checked in the argument: coordinate assertions are
vacuous for empty schemes, zero maps preserve zero families, the degree-zero simplex
inclusions are identities, and the negative source complex term is zero. No flatness
or exactness hypothesis is introduced.

## No longer needed

No original public import was removed: both
`Sheaf.Paper.ModuleCupGodementCodegeneracies` and
`Sheaf.Paper.ModuleCupAWComponents` occur in the unchanged statement.
Removed the redundant `public import Mathlib.CategoryTheory.Monoidal.FunctorCategory`
from the new Godement module; its remaining statement imports already expose it.

Second reading replaced the new models module's public AWComponents import with
ModuleCupGodementCosimplicialInput: only the complex, tensor and zero-pair definitions
are needed there. No existing node or module is claimed pruned from the targets' import closure.
The original direct proof dependencies
`def-sc-module-cup-godement-model`,
`def-sc-module-cup-godement-codegeneracies`,
`new-module-cup-godement-beta-exists`,
`new-module-cup-godement-iterate-pairings-canonical-exists`,
`new-module-cup-godement-iterate-pairings-canonical-collapse`, and
`lem-sc-module-cup-godement-model-pairing-pairing`
are now needed only in the lower Godement construction's statement or proof plan;
`def-sc-module-cup-aw-components` is needed in the generic summand proof.
`lem-sc-module-cup-godement-relations` is not used by this route: the six cosimplicial
objects are already given, so constructing new objects from the free simplex quiver
is unnecessary. Its module may remain reachable elsewhere; no global pruning claim
is made. None of these dependency modules is imported merely to record a plan.

## Where the brief, the DAG or earlier work was wrong

The sandbox inherited from the earlier attempt already contained the Lean proofs,
node records, and report, but its session ended without a READY answer. This resumed
run checked the statements against the concrete model and codegeneracy definitions,
read the existing pairing and coefficient-model interfaces, compiled the complete
set, and obtained a successful dry run. The two-part reduction is retained.
A fresh Loogle search for AlgebraicTopology.map_alternatingCofaceMapComplex
returned an unknown identifier, so it supplies no shorter route. Source grep
found no existing cross-scheme replacement.

The same-scheme `moduleCup_godement_coefficient_models` and
`moduleCup_cosimplicial_aw_natural` cannot supply the required cross-scheme maps;
they have codomains in a single module category. The existing pairing-for-models
lemma supplies pairings individually, but does not assert compatibility of a
simultaneous choice across f. The remaining construction therefore explicitly uses
coordinate pairings on both schemes, rather than taking arbitrary independent
witnesses from those existence statements.

Read Stacks Tags 0FKR and 0FKU. They give the Godement construction and naive cup
products; the cross-scheme coordinate extension and its detailed compatibility
argument are agent-written, as recorded in proof_origin. Searches of Mathlib and
both library roots found no theorem providing this cross-scheme result. LeanSearch
returned an internal server error and is recorded as unavailable; LeanFinder,
Loogle and source grep were actually run and logged. Imported blueprint search for
Godement returned no matching node. The unit record `sk-prop-av-cube` has no realized
nodes in either its statement or step; this reduction stays below that unit and
changes none of its steps or the chapter route.

## New nodes

`new-module-cup-godement-fmap-models`, in
`dag/nodes/sec-abelian-varieties/new-module-cup-godement-fmap-models.json`, states
the remaining augmented cosimplicial coordinate construction in
`lean/Sheaf/Paper/ModuleCupGodementFMapModels.lean`. It is strictly a part of the
original argument: it ends before taking alternating cofaces or proving any
front/back summand identity. The completed generic theorem and the final assembly
supply those remaining steps.

`new-module-cup-cosimplicial-fmap-summands`, in
`dag/nodes/sec-abelian-varieties/new-module-cup-cosimplicial-fmap-summands.json`,
records the fully proved theorem in
`lean/Sheaf/Paper/ModuleCupCosimplicialFMapSummands.lean`. It applies to arbitrary
paired cosimplicial objects with compatible pushforward transformations and has
no Godement or augmentation hypotheses. The chain-map construction is explicit.

No change record is needed: no existing definition, signature, visibility, public
import or elaboration option changes, and there are no forced adaptations.


## Second reading by Q3

1. Interface: compared the original module with the repository using diff. Only two
   plain imports and the proof body changed; the original theorem signature, visibility,
   options, definitions and docstring are byte-for-byte unchanged. The two other modules
   and their declarations are new. No target or existing public interface changed. Pass.
2. Proof: compiled all three files in import order and inspected every proof and private
   construction. The only direct sorry is the whole named theorem
   `AlgebraicGeometry.Scheme.Modules.moduleCup_godement_fmap_models`. Scratch-copy
   `#print axioms` gives only propext, Classical.choice and Quot.sound for
   `moduleCup_cosimplicial_fmap_summands`; the models theorem and original theorem
   additionally use sorryAx. No forbidden declaration or data choice occurs. In particular
   crossComponent uses explicit components (zero in negative degrees), and crossMap uses
   the proved differential equation, rather than an arbitrary existence witness. Pass as
   a decomposition: one original hole closed, one lower hole added, net zero.
3. Split statements: read the actual Godement object, germ unit, map, insert, multiply
   and collapse definitions, and both model predicates. The separate witnesses for term
   equalities agree by proof irrelevance, so transport does not introduce arbitrary
   coordinates. Read Stacks 0FKR and 0FKU: the cross-scheme extension is an agent-written
   coordinate argument, not a theorem claimed verbatim from those pages. At x′, the map
   uses the germ image of the f(x′) coordinate; evaluation at that same coordinate gives
   multiplication compatibility. Common-neighbourhood representatives and hχ give the
   tensor square, without flatness. Empty schemes give empty products; zero coefficients
   give zero maps; identity f gives the ordinary Godement comparison. In cosimplicial
   degree zero the terms are T(F), not F: the first iterate of the unit/tensor identities
   gives the stated augmentation equations. The generic theorem checks (0,0) via identity
   simplex maps, and degree -1 via the zero source term. The remaining construction is
   strictly before extended complexes and summand compatibility; the latter work is
   actually proved, so this is not a renamed copy of the item. Its docstring supplies the
   full coordinate argument and its node matches. Fresh LeanFinder query
   "cosimplicial object alternating coface complex commutes with additive functor"
   finds the same-category AlternatingCofaceMapComplex.map and the face-complex additive
   comparison, but no cross-scheme construction. Fresh Loogle query "Godement" gives
   no hits. Mathlib grep for skyscraper tensor / alternating-coface map finds only the
   usual map definition. Repository and upstream grep for cross-scheme Godement and
   cosimplicial f-maps finds no duplicate. The remaining construction cannot be closed
   in a few minutes with the available interfaces. Pass.
4. Route and pruning: followed the top proof: obtain augmented cosimplicial maps and
   pairings, use the fully proved generic transport, evaluate two morphism identities
   on pure tensors, and cancel degree-zero extension isomorphisms for the three squares.
   The generic proof sums coface naturality and uses front/back naturality directly;
   it needs no totalization or quasi-isomorphism. Existing same-scheme pairings do not
   provide simultaneous compatibility with f. Both original public imports are needed
   by the unchanged signature. Narrowed the new models module from AWComponents to
   ModuleCupGodementCosimplicialInput, which provides its tensor, complex and zero-pair
   definitions; it uses no AW summand. All eight old direct proof dependencies are
   accounted for in No longer needed: seven remain below or in signatures, while
   GodementRelations is unnecessary because the cosimplicial objects are already given.
   The unit sk-prop-av-cube has empty realized statement and step arrays; no realized
   node or unit step is bypassed or changed. No global module pruning is claimed. Pass.
5. Nodes: opened all three JSON records. The original changes only proof, proof_deps
   and proof_origin. Every dependency list equals the union of the step uses. The
   original records the two theorem applications and augmentation cancellation; the
   generic node records the signed differential and front/back calculation; the models
   node records the remaining coordinate construction and its pairing dependencies.
   Both new nodes have source, created, blueprint, chapter/unit, searches and verbatim
   Lean signatures. No statement or definition change record is required. Pass.

Second reading changed only the new models module's import (AWComponents replaced
by the narrower GodementCosimplicialInput), added explicit source/blueprint references
in both new module docstrings, and appended this review. No proof needed repair.
No additional hole was closed or added by the second reading.
