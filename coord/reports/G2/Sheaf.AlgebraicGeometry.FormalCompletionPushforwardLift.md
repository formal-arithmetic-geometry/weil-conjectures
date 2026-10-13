## What changed

The signature and visibility of AlgebraicGeometry.formalCompletion_pushforward_lift are
unchanged. Its proof now constructs beta = lim.map gamma followed by the inverse of
lim.map kappa, reconstructs alpha, proves its composite equation on limits, and cancels
each epimorphic source limit projection to obtain the equation of natural transformations.
This is a compiling decomposition, not a complete proof of the formal-functions theory.

Three new modules make the missing interfaces explicit:

- FormalCompletionPushforwardLimitIso states the isomorphism of limit sheaves induced by
  the canonical comparison. It contains no G, gamma, or lift conclusion.
- CoherentFormalModuleLimitFull states reconstruction of a map between two coherent
  formal systems from an arbitrary map between their limit sheaves. It contains no
  proper morphism, pushforward, kappa, or comparison equation.
- CoherentFormalModuleLimitProjectionEpi proves the limit projections epic. Coherence
  gives quasi-coherence; the defining quotient isomorphisms make transitions epic;
  the affine cokernel/image formula makes their affine section maps surjective;
  evaluation and the initial tail k -> n+k reduce to Mathlib's sequential-limit
  surjectivity theorem. The existing affine-cover criterion proves the projection epic.

The item's three new imports are proof-only. All four modules compile with lcompile.py
in import order, without warnings. No existing definition, signature, public import,
or target statement changes. No other group's module is adapted.

## Proved and sorry left

Closed the original hole in AlgebraicGeometry.formalCompletion_pushforward_lift
(lem-weil-pbc-formal-completion-pushforward-lift), by decomposition into the following
two strictly separate arguments. The item's module has no remaining sorry.

Added exactly two named holes, with complete source-backed proofs in their docstrings:

- AlgebraicGeometry.formalCompletion_pushforward_limit_isIso:
  lem-weil-pbc-formal-completion-pushforward-limit-iso.
- AlgebraicGeometry.coherentFormalModule_limit_full:
  lem-weil-pbc-coherent-formal-module-limit-full.

Also proved AlgebraicGeometry.coherentFormalModule_limit_projection_epi
(lem-weil-pbc-coherent-formal-module-limit-projection-epi) and its private affine
surjectivity helper, without any new sorry. This projection proof does not assume either
of the two new holed statements. Existing dependencies can still contain upstream
sorries; no claim of a standard-axiom-only final theorem is made. Delivery hole accounting:
one original hole closed, two new holes added, net -1; this is decomposition.

Edge cases checked mathematically: for J=0 coherent formal systems are constant;
for J=1 they are zero; zero sheaves and the empty scheme give zero limits. No individual
kappa_n is assumed invertible or monic. Maps between limit sheaves descend because
A-linearity preserves I^(n+1)N, not because arbitrary level lifts are unique.

## No longer needed

Removed these five direct proof imports from the item's module:

- Sheaf.AlgebraicGeometry.TheoremFormalFunctions
- Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
- Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
- Mathlib.AlgebraicGeometry.Modules.Tilde
- Sheaf.AlgebraicGeometry.FormalSystemsPullback

The first four remain ingredients of the new helper modules and their proof plans;
their corresponding nodes are still needed below the reduction. The broad theorem
lem-weil-pbc-formal-systems-pullback and its module
Sheaf.AlgebraicGeometry.FormalSystemsPullback are not used by this proof or the new
helper proof plans. Reconstruction only needs restriction of the coherent formal
object conditions, supplied by CoherentFormalModulesRestrictionObjects, and affine
quotient descent. Other targets may still reach FormalSystemsPullback, so this is
pruning from this item's route, not a claim that the whole library can delete it.

No unit statement or realized unit step is bypassed. The new lemmas inherit sk-thm-p1;
the item's node is not itself among that unit's realized statements or steps.

## Where the brief, the DAG or earlier work was wrong

The planned affine argument is mathematically usable, but its recorded declarations
lack the global sheaf-limit interfaces needed to compose the map and reconstruct alpha
without repeating the affine transport and gluing. The delivery exposes these as two
independent proof obligations, and proves the needed projection cancellation lemma
from existing declarations and Mathlib. The source's uniqueness step requires coherent
system limit projections, not monicity of the individual comparison components.

No statement was found false or weakened. The repository copy lacks
literature/stacks-project/coherent.tex, so the source paragraphs were checked on the
Stacks pages for tags 088B, 087W and 02OC. The explicit sheaf-limit formulations and
categorical assembly are marked as agent-written in proof_origin.

The blueprint_refs.py ancestor command follows created.item identifiers, and printed
None for this node because the existing node's created.item is a module name. New nodes
therefore preserve the existing explicit blueprint ancestor thm-weil-pbc-finite-etale-lifting
and its via chain, prepending the item node, instead of fabricating a new ancestor.

## New nodes

lem-weil-pbc-formal-completion-pushforward-limit-iso isolates the formal-functions
comparison on limits, with no source formal object or gamma. Source: Stacks 02OC,
degree zero, and 088B's first half. It is a named public theorem with sorry in
FormalCompletionPushforwardLimitIso.lean.

lem-weil-pbc-coherent-formal-module-limit-full isolates quotient descent, reconstruction,
and gluing for maps between limits of two coherent formal systems. Source: Stacks 087W's
projection kernel formula and 088B's reconstruction/uniqueness paragraph. It is a named
public theorem with sorry in CoherentFormalModuleLimitFull.lean.

lem-weil-pbc-coherent-formal-module-limit-projection-epi proves the cancellation interface
for source projections, by affine transition surjectivity, initial tails and Mathlib
sequential limits. Source: the surjective tower argument in 087W, the local-surjectivity
criterion in QuasicoherentKernel.lean, and Mathlib concrete-category sequential limits.
It has no sorry in CoherentFormalModuleLimitProjectionEpi.lean.

All three have their statements, source places, complete proof steps, Lean signatures,
blueprint references and three search kinds recorded. LeanSearch was attempted but
returned Internal Server Error; Loogle/LeanFinder and source searches were available.
No change record is necessary: all existing signatures and visibility are unchanged.

## Second reading by G2

1. **Interfaces: pass.** Compared the delivered item with the repository by diff.
   The complete declaration signature, visibility, universes, hypotheses and conclusion
   are byte for byte unchanged. The differences are proof-only imports, the proof and
   its natural-language explanation. The other three modules are new; no existing
   definition, target statement or other group's module is changed. No change record
   is needed.
2. **Proof and axioms: pass as decomposition.** Independently compiled all four
   modules in import order through lcompile.py, with no errors or warnings. Inspected
   all declaration bodies: no hollow definitions, arbitrary witness constructions,
   forbidden declarations or hidden holes. Exactly the two named public theorems
   listed above retain `:= by sorry`. A scratch copy with explicit `#print axioms`
   showed only propext, Classical.choice and Quot.sound for
   AlgebraicGeometry.coherentFormalModule_limit_projection_epi; the item and the
   two split theorems additionally use sorryAx. The original hole is closed by a
   real inverse-limit construction and projection cancellation, not by restating it.
   One hole closed and two added is a decomposition, net -1, not completion.
3. **Split statements: pass.** Read all three helper signatures and source-backed
   docstring arguments against Stacks 087W, 088B and 02OC. The comparison theorem
   isolates formal functions and contains no G or gamma. The reconstruction theorem
   isolates descent between two coherent systems and contains no proper morphism,
   comparison or pushforward. An arbitrary A-linear map preserves I^(n+1)N, so no
   omitted continuity hypothesis is needed. Tested zero/unit ideals, zero sheaves,
   empty schemes and the constant-system case. Read the existing affine equivalence,
   restriction-object theorem and globalSections_formal_functions signatures.
   Independent searches used “A-linear maps between inverse limits of finite adic
   quotient modules descend”, “limit of pushforward quotients”, and local rg over
   both Lean roots. LeanFinder returned module-level completion lifts and general
   sheaf isomorphism criteria, not either helper. Loogle attempts were unavailable
   for the indexed identifiers; local source inspection supplied the actual concrete
   sequential-limit theorem. No duplicate or short global reconstruction proof was
   found. Both remaining obligations require substantial affine transport/gluing,
   so neither can be closed by a few-minute application of an existing theorem.
4. **Route and pruning: pass after repair.** The item uses exactly its three new
   helper imports. Both Sheaf.Limits public imports are needed by the new limit
   signatures; Proper is needed by the comparison signature. Removed the redundant
   direct Tilde import from CoherentFormalModuleLimitFull: the imported affine module
   already publicly exports it. The five old proof dependencies are accounted for:
   lem-weil-pbc-theorem-formal-functions and
   lem-weil-pbc-ideal-times-quasi-coherent-affine-sections remain below the comparison;
   lem-weil-pbc-coherent-formal-modules-affine and
   lem-weil-pbc-affine-tilde-gamma-adjunction remain below reconstruction;
   lem-weil-pbc-formal-systems-pullback is unused by the new route. Read the unit's
   realized statement and steps: none is bypassed. Replaced the final manual local
   lift in the projection proof with epi_of_surjective_app on all affine opens,
   using the already established quasi-coherence and affine section surjectivity.
5. **Nodes: pass after repair.** Compared all Lean signatures with their node records,
   checked each proof_deps list against the union of step uses, and read the cited
   declarations. The original node changes only proof, proof_deps and proof_origin.
   Each new node records source, searches, creation, unit, chapter, blueprint chain,
   Lean signature and agent-written proof origin. Updated the projection node's final
   step to name the exact affine-cover criterion now used in Lean. Corrected the
   comparison node's source URL from 087W to the cited formal-functions tag 02OC.

Second reading changed the projection proof's last step and matching explanation,
removed one redundant helper import, corrected one source link, and recorded this
independent review. No signature changed and no further hole was added or closed.
