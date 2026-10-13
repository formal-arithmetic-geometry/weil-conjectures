## What changed

Replaced the proof of `AlgebraicGeometry.Etale.tailOpenCohomologyCoconeLeg_naturality`
with an explicit coefficient-square and cohomology composition argument. Added proof-only
imports of `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial` and
`WeilConjectures.SixFunctors.BaseChange.Pasting`. Kept all existing signatures, definitions,
and public imports unchanged. Copied two already-proved private helpers into this module;
no new public statements or assumptions were introduced. Updated the existing node's
proof and dependencies to record square pasting.

## Proved and sorry left

The sole original hole, `AlgebraicGeometry.Etale.tailOpenCohomologyCoconeLeg_naturality`
(node `lem-weil-pbc-tail-open-cohomology-leg-naturality`), has a complete Lean proof in
the sandbox source. No `sorry` remains in the delivered module and no holes were added.
The missing shared compiled dependency is now available. The prescribed full-module
compilation succeeded against the shared build in 55.2 seconds, without a sandbox
compiled overlay. No error or warning was printed. The delivery dry run printed OK: full-module compilation, the axiom probe, and
preflight passed. Its review class is CODEX because the node proof was updated.
Nothing was pushed.

## No longer needed

No imports, nodes, or modules are pruned. The proof uses the arrow definition from
`TailOpenCohomologyArrowLaws`, but does not invoke its holed laws theorem. It uses the
open-square definitions from `EtaleLimitOpenCohomologyCocone`, but does not invoke its
holed cocone existence theorem. Neither theorem's extra identity/composition assumptions
are needed for the naturality statement. Their modules remain necessary for definitions.

## Where the brief, the DAG or earlier work was wrong

The node's planned square-pasting step has a proved library declaration,
`AlgebraicGeometry.Etale.squareUpperStarIso_paste_vert_hom`, recorded by
`lem-weil-pbc-square-iso-pasting`; this dependency has been made explicit.

Earlier attempts were blocked because the shared compiled library lacked
`Sheaf.AlgebraicGeometry.TailOpenCohomologyArrowLaws.olean`. On this retry the artifact
became available through the shared build refresh. Full-module compilation now passes;
no dependency was rebuilt, duplicated, or supplied from a scratch overlay.

## Earlier second reading (a previous round; superseded)

1. Compared every sandbox Lean module with the repository by diff. The existing
   public theorem signature and the entire cocone-leg definition are byte for byte
   unchanged. The only module edits are two proof-only imports, two new proved private
   helpers copied from existing private helpers, a local elaboration option, and the
   replacement of the original sorry. No change record or interface change is needed.
   The extra arrow-law module was byte for byte identical to the repository and has
   been moved out of the delivery into scratchpad.
2. Static inspection finds no sorry, axiom, unsafe, opaque, implemented_by, extern,
   or hollow definition in the item. The initial compile succeeded in 20.7 seconds
   using an existing sandbox .lbuild overlay. After moving that overlay into
   scratchpad, the prescribed compile fails before elaboration because the shared
   library lacks TailOpenCohomologyArrowLaws.olean. Thus the required full-module
   baseline compile and axiom check are NOT verified; no overlay-only success is
   accepted as delivery evidence. No dependency was rebuilt during this reading.
3. There are no split-off statements or new holes to review. The two private helper
   statements are strictly smaller coherence assertions, fully proved, and coincide
   with existing private helpers in EtaleLimitOpenRestrictedSystem and
   EtaleCohomologyOpenRestrictionNaturality. They cannot be used through public
   imports there. The coefficient helper uses equality of composites, naturality,
   and square pasting; the cohomology helper uses coefficient naturality and
   composition. Identity transitions, singleton diagrams, empty opens, degree zero,
   and zero coefficients introduce no extra assumption into either argument.
4. Read the proof from the desired naturality equality downward: restricted map
   composition comes from monomorphism cancellation and c.w; the coefficient leg
   equation comes from L.w and hG; square pasting then identifies coefficients;
   cohomology functoriality gives the result. Searches of lean/ found the two existing
   private helpers and the public square-pasting theorem used here, with no direct
   public replacement for the whole argument. Both added imports are proof-only
   and used. No original dependency is pruned: the cocone module supplies actual
   open and coefficient definitions, inverse-image composition supplies the
   comparisons, and cohomology functoriality supplies composition. Read
   dag/units/sk-thm-p1.json realized: this local coherence calculation bypasses no
   realized unit statement or step, and makes no unit change.
5. Compared the node JSON: only proof, proof_deps, and proof_origin differ. The
   new square-pasting dependency names the node whose Lean declarations include
   squareUpperStarIso_paste_vert_hom; proof_deps equals the union of step uses.
   The other dependencies and the statement/Lean signature agree with the proof.
   No new node is present or needed.

Second reading changed no proof. It clarified that the two private helpers were
new to this module, excluded the unchanged arrow module from the delivery, moved
existing compiled sandbox artifacts into scratchpad so they cannot mask the missing
baseline import, and recorded the unverified compile/axiom gate. Delivery remains
blocked by the missing shared compiled import, not by a known mathematical fault.

The second reader reran deliver3.py --no-push after these checks. It exited 1 with
COMPILE FAILED (local), nothing pushed, naming the same missing
Sheaf.AlgebraicGeometry.TailOpenCohomologyArrowLaws.olean. The push command was not
run because the required dry run did not print OK.

## Second reading by V3

This is the current independent second reading; it supersedes the earlier blocked
reading above. The shared compiled dependency is available in this round.

1. **Interfaces: pass.** Diffed the sole delivered Lean module against the current
   repository. Independently compared the full existing
   `tailOpenCohomologyCoconeLeg` definition and the signature of
   `tailOpenCohomologyCoconeLeg_naturality` byte for byte: both are unchanged.
   The hypotheses still include the arbitrary cone c, coefficient transitions φ,
   functor G, object comparisons eG, transition equation hG, and arbitrary cocone L.
   The conclusion is the same naturality equality on every tail arrow and every
   natural-number degree. No coefficient identity/composition, colimit, or scheme
   limit hypothesis has been added. No change record or forced adaptation is needed.
2. **Proof and axioms: pass.** Recompiled the delivered module using lcompile.py
   against the shared build, without a sandbox .lbuild overlay: clean exit 0 in
   24.7 seconds. A full scratch copy with explicit #print axioms checks also compiled
   cleanly in 24.4 seconds. The existing leg definition, the naturality theorem, and
   both new private helpers depend only on propext, Classical.choice, and Quot.sound;
   none depends on sorryAx. Static inspection found no sorry, axiom, unsafe, opaque,
   implemented_by, extern, or kernel-check bypass in the delivered source. The leg
   is the original explicit construction, not data chosen from an existence theorem.
3. **Split statements: pass, none.** The delivery closes precisely the original
   naturality hole and adds zero holes. There are no split-off statements or new
   nodes. Read both proved private helpers and their existing private counterparts:
   the coefficient helper is identical to that in EtaleLimitOpenRestrictedSystem;
   the cohomology helper is identical to that in EtaleCohomologyOpenRestrictionNaturality.
   Both are inaccessible from those other modules because they are private. Searches
   with rg for transported composition, coefficient composition, cohomology naturality,
   and square pasting in lean/Sheaf, lean/WeilConjectures and the upstream checkout
   located these helpers and the general public laws, but no public replacement that
   shortens the argument. The helper hypotheses are just commuting squares and
   composite equalities, or composable scheme and coefficient maps. Identity maps,
   empty opens, degree zero, and zero coefficients require no extra assumptions.
4. **Route and pruning: pass.** Read downward from the final equality: hr cancels
   the monomorphic stage-open inclusion and applies c.w; h₁, h₂, h₃ are restriction
   identities; he precomposes L.w by eG_j.inv, substitutes hG and cancels eG_j.
   The coefficient helper specializes vertical square pasting, cancels the inverse
   composition comparison, and applies naturality to φ. The cohomology helper uses
   cohomologyMap_map, the composition clause of cohomologyPullbackFunctorial, and
   Sheaf.H.map_comp_apply. Rewriting hp and he gives the original leg definition.
   Each of the three imports supplies declarations used in the signature or proof;
   the two new imports are correctly proof-only. No old proof dependency can be
   removed: the open-cocone module supplies the open maps and coefficient definition,
   inverse-image composition supplies comparisons, and cohomology functoriality is
   used explicitly. The open-cocone existence theorem and arrow-laws theorem are
   not applied. Read dag/units/sk-thm-p1.json, including every realized entry: this
   local coherence calculation changes no unit route or realized step. Square pasting
   is a proved tool from sk-def-exchange, not a replacement for a unit-level argument.
5. **DAG: pass.** Diffed the delivered node and verified programmatically that only
   proof, proof_deps and proof_origin differ. Its recorded Lean signature exactly
   matches the unchanged theorem signature. proof_deps is precisely the union of
   the proof step's uses. Read the inverse-image composition and square-pasting
   nodes and the actual declarations: squareUpperStarIso_paste_vert_hom is recorded
   by lem-weil-pbc-square-iso-pasting and applies to arbitrary commuting squares,
   without a cartesian assumption. The other dependencies supply the definitions
   and composition law used as described. No new nodes are required.

Second reading changed no Lean proof, interface, import, or node. It added this
independent review and current compilation/axiom evidence to the report. The net
change in holes for this delivery is one closed and zero added; nothing is pruned.

The current second reader's deliver3.py --no-push run printed OK: compilation,
axiom probe and preflight passed (dry-run commit 3ffe583ade). Review class is CODEX
because the existing node's proof record changes. The reader then invoked the
prescribed push delivery command.
