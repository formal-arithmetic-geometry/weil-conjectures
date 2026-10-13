## What changed

Reduced `AlgebraicGeometry.schemeGlobalHom_baseChange_exchange` to two strictly
partial statements in new modules:
`Sheaf.AlgebraicGeometry.InternalHomBaseChangeExchange` and
`Sheaf.AlgebraicGeometry.GlobalSectionsBaseChangeMate`. Both imports in the item
are proof-only. All existing signatures, visibility, definitions and docstrings
are unchanged.

The internal statement is an equality in the sheaf derived category on Y', before
any global sections or scalar identifications. The Leray statement concerns
arbitrary sheaf complexes E,E' and a map a, with no Hom or tensor-Hom input.
They isolate the two numbered steps in the original node plan. Their conjunction
is combined by real Lean: two private categorical lemmas prove how Leray and an
adjunction Hom equivalence transport postcomposition and precomposition. The
internal exchange equality is then substituted inside the transpose, and the
expanded definitions give the original four-factor global square.

Updated the item's node proof, proof_deps and proof_origin accordingly. Each new
statement has its own module, complete proof in words, source and node. No new
data is selected from an existence theorem; p in the internal statement and item
is an explicit local evaluation-mate expression.

Read the source constructions at [08I3](https://stacks.math.columbia.edu/tag/08I3)
(pullback of evaluation), [08HY](https://stacks.math.columbia.edu/tag/08HY)
(counit base-change mate), [0B6I](https://stacks.math.columbia.edu/tag/0B6I)
(passage to global Hom), and the final diagrams of
[0AA8](https://stacks.math.columbia.edu/tag/0AA8). The source .tex and blueprint
markdown are not materialized in this clone; the unit JSON was read and the
source tags were read online. This decomposition supplies the details of the
parent's formal exchange argument; it does not use the isomorphism conclusion
or the additional hypotheses in the statement of 0AA8.

The target and new statement modules compile locally. The target uses the two
new declarations with their exact stated types; the private transport lemmas
contain no sorry. Final delivery validation is the deliver3.py dry run.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.schemeGlobalHom_baseChange_exchange`
(node `lem-sc-global-hom-base-change-exchange`). No sorry remains in the item.
The private `globalMate_postcomp` and `globalMate_exchange` lemmas are fully proved
using adjunction naturality, functor map_comp and Leray naturality.

Added exactly two named holes, one in each new module:

- `AlgebraicGeometry.schemeInternalHom_baseChange_exchange`
  (node `lem-sc-internal-hom-base-change-exchange`).
- `AlgebraicGeometry.schemeGlobalSections_baseChange_mate`
  (node `lem-sc-global-sections-base-change-mate`).

This is a decomposition, not a completed proof from standard axioms: one upper
hole closed and two lower holes added, for net minus one at this step. Existing
sorry-bearing dependencies are retained and were not changed.

Edge cases were checked mathematically before stating the lemmas. Both equations
remain well-typed for zero objects, empty schemes and zero a. Identity squares
reduce to naturality of evaluation or Leray. Neither lemma cancels beta_M,
beta_N or a, and neither requires those maps to be invertible. For a general
nonflat base-change square the same counit construction and triangle identities
apply; no base-change isomorphism theorem is used.

## No longer needed

None. No existing import was removed, and no original dependency node or module
is declared pruned. The original dependencies remain in the two child arguments
or supply the definitions of the unchanged statement. The new internal-Hom
module imports GlobalHomAdjunctionIso directly, since it does not use the global
pullback comparison or scalar-square definitions. The item's original public
import GlobalHomPullbackComparison is required by its unchanged signature.
The original unit route is retained; its realized fields are unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The existing node's plan
leaves the tensor-composition and Leray-composition coherences in prose, so
neither is supplied by a directly applicable existing exchange declaration.
These are the two remaining new items, rather than anonymous holes in the proof.
The recorded adjunction and Leray existence theorems do supply the pinned data
needed to formulate them. The standard adjunction naturality lemmas supply the
combining proof, but do not supply these two coherence results themselves.

LeanSearch was unavailable (HTTP Internal Server Error), recorded as unavailable
with no inference of absence. LeanFinder and grep searches ran through msearch.py
and found generic adjunction/pullback tools but no exact result. Local searches
of both library roots and the full blueprint for internal Hom and Leray found
no duplicate statement. The ancestor helper returns None for this item's module-
named creation chain; the new nodes inherit the existing parent's explicit
blueprint ancestor `lem-sc-finite-duality` and extend its via path.

## New nodes

`lem-sc-internal-hom-base-change-exchange` states the first step, the sheaf-level
exchange for pinned evaluation-mate comparisons. Its source is the final diagram
argument of 0AA8 with 08I3 and 08HY. Its proof transposes evaluation, expands the
base-change counit mate, and compares tensor paths on K-flat representatives.
It contains no derived global sections or restriction of global scalars.

`lem-sc-global-sections-base-change-mate` states the second step independently
of Hom, for an arbitrary morphism LgX^*E to E'. It isolates compatibility of
canonical Leray/scalar identifications with the base-change adjunction mate.
The proof expands the units and counits, then uses the right-derived-unit
characterization of the Leray comparisons. There are no change records and no
forced adaptations.

## Second reading by E1

1. **Interfaces: pass.** Compared the item with the repository using diff and
   separately compared the complete existing theorem signature byte for byte.
   Only two proof-only imports, two private proved helpers, and the original
   theorem's proof were added. Its signature, visibility and docstring are
   unchanged. There are no changed definitions, target statements, or forced
   adaptations; the other two modules are new statements.
2. **Proof and trust: pass as a decomposition.** Compiled all three delivered
   modules in import order through lcompile.py: no errors or warnings. Read the
   two private transport proofs and the final substitution/definition expansion.
   No forbidden declaration or hollow definition occurs. The only two sorry
   tokens are the complete bodies of the two reported public child theorems.
   A separate scratch import audit with #print axioms reports only propext,
   Classical.choice, Quot.sound and sorryAx for all three public theorems.
   The chosen direct-image comparison is uniquely determined by its evaluation
   equation (take alpha to be the identity and use the tensor-Hom equivalence).
   No arbitrary existence witness is introduced by this delivery.
3. **Split statements: pass.** Read both complete statements, docstring arguments,
   nodes, and the pinned evaluation, adjunction and Leray constructions they use.
   The internal-Hom identity is the sheaf-level part, without global sections;
   the Leray identity is for arbitrary E, E' and a, without internal Hom. Neither
   restates the global target. Zero inputs and a=0 give zero paths; identity
   squares give evaluation/Leray naturality, with the canonical unit comparisons.
   The formal mate argument requires neither flatness nor cancellation of beta.
   Checked the cited Stacks Tags 0AA8, 08HY and 08I3; the extra hypotheses of
   0AA8 are used for invertibility, not these formal comparison identities.
   Independent msearch LeanFinder search for derived-global-sections comparison
   under composition/adjunction units and grep for tensor mates, exchange and
   conjugation returned general naturality tools but no matching statement.
   Also searched both local library roots for Beck-Chevalley, Leray and Hom
   exchange, and inspected the direct-image/pullback composition and nearby
   global-Hom modules. No duplicate or closure available in a few minutes found.
4. **Route and pruning: pass.** The item really combines both child equations
   using adjunction naturality, Leray naturality and functoriality; it is not a
   renamed application of the original hole. Its public import is needed by
   the original signature; both new imports are proof-only and used. Each new
   module's public import supplies its statement data. No import is unused.
   All six old proof dependencies remain as definitions expanded in the item
   or in the child statements/arguments: derived base change, global RHom,
   global pullback comparison, global-Hom adjunction, tensor-Hom bijection and
   pullback tensor comparison. None is pruned from the import closure. Read
   sk-thm-picard-duality's realized record; this delivery changes no unit step
   or realized entry and keeps the parent's two-step exchange route.
5. **DAG: pass.** Only proof, proof_deps and proof_origin of the existing node
   differ. Verified the dependency union of each node against its proof steps,
   and the new nodes' Lean statement records against the actual signatures.
   New nodes have their sources, proof arguments, searches, creation records,
   chapter/unit and blueprint provenance. The parent record describes the
   actual two-child reduction and the categorical combining proof.

Changed only this report to record the independent reading and verification.
No Lean repair or node repair was needed. One original hole is closed, two
strictly partial holes are added, and no modules are pruned: this remains a
net-minus-one decomposition, not a proof from the standard axioms alone.
