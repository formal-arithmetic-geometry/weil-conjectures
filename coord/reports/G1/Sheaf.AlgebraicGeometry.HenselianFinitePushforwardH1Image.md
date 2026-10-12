## What changed

Corrected the helper `finite_pushforward_H_one_lift_of_henselianLocalRing` so its witness z is used in a genuine lifting equality: the restricted image of x equals the canonical restriction of H¹(ψ)(z), with the module/abelian inverse-image comparison made explicit. The lifting helper applies to arbitrary destination module sheaves, without an injectivity hypothesis. Removed the circular dependency of the helper on the target. Added the named injective-module H¹ vanishing theorem and used it to finish the target proof.

## Proved and sorry left

`finite_pushforward_H_one_image_eq_zero_of_henselianLocalRing` is proved. The helper `finite_pushforward_H_one_lift_of_henselianLocalRing` remains sorry in node `lem-weil-pbc-henselian-finite-pushforward-h1-lift`. The acyclicity helper `subsingleton_H_one_of_injective_module_sheaf` remains sorry in node `lem-weil-pbc-henselian-finite-pushforward-h1-injective-vanishing`.

## No longer needed

No module is globally pruned and no public import is removed. The following former DIRECT target proof dependencies have moved into the two helper plans; they remain transitively needed:
`lem-weil-pbc-finite-morphism-permanence`, `lemma-weil-pbc-finite-exchange`,
`lemma-constructible-pullback-constant`, `lem-weil-pbc-finite-pushforward-cohomology`,
`lem-weil-pbc-edge-map-base-change`, `thm-weil-pbc-finite-etale-lifting`,
`lemma-weil-pbc-h1-torsor-comparison`, `lem-weil-pbc-constant-module-sheaf-underlying`,
`lem-weil-pbc-injective-module-abelian-acyclic`, `lem-weil-pbc-cohomology-pullback-functorial`,
and `prop-weil-pbc-inverse-image-modules-exact`.

## Where the brief, the DAG or earlier work was wrong

The returned helper statement was a zero-factorization restatement of the target and created a dependency cycle. It did not use its witness z. The helper now states the actual lifting equality, and its blueprint ancestry is `prop-weil-pbc-p1-acyclicity` at the strict-henselian base proof step. The target depends on the helper and the separately named injective-acyclicity result.

## Earlier second reading (a previous round; superseded)

Read the target and both helper declarations hypothesis by hypothesis. The target uses the same henselian local ring, proper morphism, cartesian residue-fibre square, coefficient ring, injective module sheaf, finite locally finitely presented cover, finite coefficient module, map ψ, and class x as the source Lemma 0A5H. The lift helper preserves every hypothesis and supplies z on the total finite pushforward; its conclusion relates the restricted image of x to the restriction of H¹(ψ)(z), through the canonical comparison required because module inverse image and underlying abelian inverse image are distinct objects. The target then applies the injective module H¹ vanishing helper to H¹(ψ)(z), and functoriality of zero gives the required vanishing. Empty covers and zero modules are included by the unchanged quantified statement. The helper dependency route is one-way: target → lift and injective vanishing; the lift has no target dependency. The correction removes the circular edge and restores the intended Stacks 0A5H proof route.

## New nodes

`lem-weil-pbc-henselian-finite-pushforward-h1-lift` records the lifting step. `lem-weil-pbc-henselian-finite-pushforward-h1-injective-vanishing` records the separately open injective-module H¹ vanishing step and is realized by `Sheaf.AlgebraicGeometry.InjectiveModuleSheafH1`.

## Earlier second reading (a previous round; superseded)

1. **Interface and accidental changes.** Compared the delivered target module with the repository version. The target theorem statement is byte-for-byte unchanged; only its proof and proof-only imports were added. The two helper modules are new modules and their declarations match their corresponding DAG `lean.statement` fields.

2. **Proof and axioms.** Compiled all three modules with `lcompile.py --all`; they compile without errors or warnings. The target's axiom report contains only the standard axioms plus `sorryAx` originating from the two explicitly named open helper theorems. No `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definition was introduced.

3. **Split-off statements.** The lifting helper has a witness and a concrete naturality equality, so it is a strict intermediate factorization rather than a restatement of the zero conclusion. The injective-module helper states the needed degree-one subsingleton result. Both have source docstrings, matching nodes, and no duplicate declaration was found in the repository.

4. **Pruning and route.** The target proof uses exactly the lifting and injective-vanishing helpers, and the unit route remains represented by the target node and its two proof dependencies. The helper imports are public only where their signatures require the corresponding structures; the target's helper imports are proof-only. No old proof dependency became unused beyond the dependencies recorded in the updated target node.

5. **DAG agreement.** Checked the target, lifting, and injective-vanishing nodes against the Lean declarations and proof calls. Their statements, proof dependencies, sources, and `blueprint` ancestry agree with the delivered code; the two unresolved statements remain explicitly marked `split`.

Changes made in this second reading: added this audit section and retained the worker's corrected lifting equality and one-way dependency structure. No Lean statement or definition required repair.

## Earlier second reading (a previous round; superseded)

1. **Interfaces.** Diffed the target against the repository: its complete theorem
   signature and existing docstring are byte-for-byte unchanged. Only two proof-only
   imports and the proof body changed. Neither helper module exists in the repository;
   both are new declarations, so no existing interface or definition changes.

2. **Kernel proof.** All three modules compile through `lcompile.py --all`, without
   errors or warnings. The target obtains a lifting witness, applies total-space
   injective acyclicity, and uses additivity to send zero to zero. Exactly two named
   helper theorems remain `sorry`; there is no hollow definition or forbidden axiom,
   unsafe declaration, opaque declaration or alternate implementation. The scratch
   `#print axioms` check covers all three declarations: only standard axioms and
   `sorryAx` from the explicitly open helpers occur. This is a reduction, not a
   completed axiom-free proof of the target.

3. **Split statements.** Removed `[Injective J]` from the NEW lifting helper. Keeping
   that assumption makes its right side necessarily zero by the other helper and
   disguises a restatement of the target. For arbitrary J, lifting and naturality
   are a distinct part of the argument: instantiate J with the finite pushforward
   and ψ with its identity to recover actual surjectivity of restriction. The
   docstring proves this by finite base change, the finite pushforward edge
   isomorphism, henselian lifting of finite M-torsors, and naturality. Checked the
   source at https://stacks.math.columbia.edu/tag/0A5H: its lifting argument does not
   use injectivity until the subsequent vanishing step. Empty V and zero M have
   only the zero class, with z = 0. For i an identity the lift is z = x. The
   arbitrary-J version does not assert vanishing for noninjective J.
   Checked injective-module acyclicity against
   https://stacks.math.columbia.edu/tag/03FD: it is true without requiring the
   underlying abelian sheaf to be injective, and includes J = 0 and the zero ring.
   Real searches with leanfinder, loogle and grep are in searches.jsonl;
   LeanSearch was also tried and returned Internal Server Error (recorded as
   unavailable, with no absence verdict); also
   searched repository and upstream Lean. Mathlib's subsingleton instance requires
   an injective ABELIAN sheaf, which is insufficient. The existing node
   `lem-weil-pbc-injective-module-abelian-acyclic` uses SheafOfModules, a small-universe
   ring and rightDerived evaluation; it does not supply the required arbitrary-ring
   ModuleCat-valued Sheaf.H conclusion directly. Its presentation/cohomology bridge
   remains part of the separately open helper, rather than being claimed proved.

4. **Pruning and unit.** All public imports provide objects or classes in the
   signatures; the two helper imports into the target are plain imports. The old
   target proof dependencies listed above are removed from its DIRECT proof_deps
   only: they remain in the helper plans, so no transitive dependency or module is
   declared globally pruned. Removed injective abelian acyclicity from the lifting
   node, since lifting no longer uses it; it remains under injective vanishing.
   Read dag/units/sk-thm-p1.json, including realized: the strict henselian step (ii)
   still uses finite torsor lifting followed by injective acyclicity, and no
   realized unit node is bypassed or edited.

5. **DAG.** Checked all three lean.statement signatures against the Lean, including
   the generalized NEW helper. Updated the lifting title and self-contained
   statement, added the missing statement dependencies and their citations to both
   new nodes, and replaced their unverified search summaries with recorded real
   searches. The target proof text now describes its actual two-helper reduction.
   The helper has no dependency on the target, and the two source proof plans are
   acyclic and match the docstrings. Both new nodes have source, proof, proof_deps,
   proof_origin, searches, status split, created, blueprint ancestry, chapter, unit
   and lean records.

Changes: generalized the new lifting lemma to arbitrary destination module sheaves;
corrected the helper DAG metadata, source-route dependencies and search evidence;
clarified that the delivery closes one original theorem by reduction, leaves two
new helpers open, and prunes no module globally. Existing Lean statements and
all definitions are unchanged. The earlier second-reading sections above are
superseded by this audit.


## Second reading by G1

1. Compared every delivered Lean module with the repository. The original theorem's
   signature and docstring are byte-for-byte unchanged; its only changes are two
   plain proof imports and its proof body. The two helper modules are new. There
   are no changes to existing definitions, hypotheses or conclusions.

2. Compiled all three modules using `lcompile.py --all`. All compile without errors
   or warnings. Compiled the scratch axiom audit for all three declarations: only
   `propext`, `Classical.choice`, `Quot.sound` and `sorryAx` occur. The latter remains
   in precisely the two named, documented helper theorems listed above. No hollow
   definition or forbidden declaration appears. The target is closed by reduction;
   this delivery does not claim an axiom-free proof of its dependency closure.

3. Read the helper signatures and source arguments at
   https://stacks.math.columbia.edu/tag/0A5H and
   https://stacks.math.columbia.edu/tag/03FD. Lifting uses properness of V over A,
   finite base change, the finite pushforward cohomology comparison, torsor lifting,
   and naturality. It does not require injectivity of J and is a strict part of the
   argument. Taking J to be the finite pushforward and ψ its identity tests actual
   lifting rather than a zero-factorization restatement. Empty V and zero M admit
   the zero lift; zero J makes the naturality equality zero on both sides. The
   vanishing lemma holds also for the zero ring and zero J; it does not assert that
   the underlying abelian sheaf is injective. Repeated leanfinder searches using
   restriction of scalars and finite-group torsor extension, loogle searches for
   Sheaf.H with Injective and for cohomologyMap, and grep for surjective
   cohomologyMap/subsingleton cohomology found no direct replacement. Searches are
   recorded in searches.jsonl. Read the existing InjectiveModuleAbelianAcyclic
   module: its small-ring, SheafOfModules/rightDerived statement requires genuine
   representation, universe and cohomology comparisons to apply here, so neither
   helper can be closed in a few minutes. Both have source proof docstrings and nodes.

4. Reviewed the proof from the target downward: obtain the lift, kill its image
   using injective vanishing, then use map_zero for restriction and comparison.
   The helper imports into the target are plain imports. Public imports supply
   signature objects and instances. Checked every old direct proof dependency
   against No longer needed: all eleven are listed, and remain in the helper plans.
   Read sk-thm-p1.json including realized; the finite torsor lifting step remains
   below the strict henselian comparison, and no realized unit node is bypassed.
   No module is globally pruned.

5. Checked normalized Lean signatures against all three node lean.statement fields;
   all agree. Each proof_deps is exactly the union of its proof steps' uses. The
   target plan describes its actual proof; the two open helper plans agree with
   their source docstrings, have no edge back to the target, and include the required
   source, origin, searches, created, blueprint, chapter, unit and lean records.

Changes in this reading: fixed the new lifting docstring's article ("an module"
→ "a module"), clarified the current report's arbitrary-J lifting and direct-only
pruning claims, and added this independent audit. No Lean proof or statement repair
was necessary. Prior audit sections are historical and are superseded by this one.
