## What changed

Closed `AlgebraicGeometry.Scheme.picardRankMatch_baseChange_stalk_finrank_eq` without changing its signature or public imports. Added proof-only imports of `FiniteLocallyFreeStalkFinrank`, `Modules.LocallyFreeRank`, Mathlib `PullbackCarrier`, and `import all` for `Modules.RestrictionStalkExtensionIso` and `PicardUniversalRankMatchConjunction`. All new helpers are private and proved. Updated the existing node's proof, proof dependencies and proof origin to match the Lean.

The local-rank helper pulls a fixed-rank frame back before taking stalks, then transports finrank along the semilinear open-restriction stalk comparison. The iterated direct image is identified with the composite base change via associativity, pushforward composition and the unit of the adjunction along an isomorphism. On a nonempty fibre, a point in the common reference fibre product compares its two ranks. Outside the proper image, the empty-cover sheaf condition proves both direct-image stalks zero.

## Proved and sorry left

Closed the one original hole in `AlgebraicGeometry.Scheme.picardRankMatch_baseChange_stalk_finrank_eq` (node `lem-sc-picard-base-change-stalk-finrank-eq`). No holes added or split off; no `sorry` remains in the delivered module. Private helpers are complete proofs. Existing dependencies retain their existing status.

Validation: the final module compiles with `lcompile.py` without errors or warnings. The theorem's signature and all four public imports are unchanged. The proof treats zero rank and empty fibres explicitly; empty test schemes contain no point to check. No new data is selected from a mere unproved existence theorem: selected natural isomorphisms identify the specified functors, and all point choices occur only in proofs.

## No longer needed

The planned dependency `lem-weil-pbc-module-stalk-pullback`, module `Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk`, is not needed by this proof. No import of it is added. Pulling back fixed-rank frames before taking stalks avoids the general tensor-pullback stalk formula and `Module.finrank_baseChange`. Existing public imports are retained because they support the existing signature and visibility. Every added proof-only import is used. No other planned nodes are pruned. The unit record has empty realized statements and steps, so no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The returned delivery correctly identified three duplicate private theorems. The earlier delivery and second reading overlooked that `import all` allows these existing private declarations to be reused. The DAG's stalk-scalar-extension step admits a shorter implementation using pulled-back local frames and open-restriction stalk transport. The proof supplies the previously implicit empty-fibre vanishing argument directly from properness and the sheaf condition. The associativity helper is adapted from the proved private construction in `PicardBaseChangeStalkFiniteBases`; the open-restriction semilinearity helpers are adapted from `Modules.RestrictionStalkExtensionIso`, and now reused via proof-only `import all` of the two modules named in the return.


Repair: removed `Scheme.Modules.inverse_stalkMap_germ`, `Scheme.Modules.restriction_stalk_smul`, and `Scheme.tensorRankComp`. The local-rank proof calls `AlgebraicGeometry.restriction_stalk_smul` directly; the reference-rank comparison calls the imported `AlgebraicGeometry.Scheme.tensorRankComp`. Removed the now-unused private `Scheme.tensorComparison`. No dependency interfaces or other modules are changed. Both added imports pass the import-direction check. The repaired module compiles without errors or warnings. The previous second reading covered the pre-repair version; a fresh independent reading is required.

## Second reading by Y2

1. **Interface: pass.** Read the repository and sandbox modules and their full diff.
   The sole existing theorem, `AlgebraicGeometry.Scheme.picardRankMatch_baseChange_stalk_finrank_eq`,
   has a byte-for-byte identical signature and docstring. In particular, flatness, properness,
   local finite presentation, finite local freeness, universal rank matching, the disjunction
   `F = E ∨ F = Modules.dual E`, and the two specified stalk finranks are unchanged.
   All four existing public imports remain unchanged; the five additions are proof-only imports.
   No target, existing definition, other module, or change record is altered.
2. **Proof and axioms: pass.** Compiled the delivered module with `lcompile.py --all`:
   no errors or warnings. Refreshed the scratch copy from the repaired module and compiled
   `#print axioms AlgebraicGeometry.Scheme.picardRankMatch_baseChange_stalk_finrank_eq`:
   exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   Scanned the delivered source for `sorry`, forbidden axioms and implementation escapes:
   none. Read each private helper, including the actual construction of the associativity
   direct-image isomorphism. Its choices are adjunction/composition identifications of
   specified functors; no arbitrary existence witness supplies new mathematical data.
3. **Split statements and edge cases: pass.** No new public statements, nodes or holes
   are split off. The local-rank helper pulls the frame back along the restricted morphism,
   uses fixed-rank pullback preservation, and transports stalk rank through the additive
   equivalence semilinear over the inverse open-immersion stalk-ring map. No flatness of
   `h` is assumed. On a nonempty fibre, the maps `ar` and `bs` identify both reference
   ranks on the same pulled-back `E`; `Scheme.Pullback.exists_preimage_pullback` supplies
   a point with exactly the required compatibility. On an empty fibre, the complement
   of the proper projection's image is open, every germ is represented on a smaller open
   with empty inverse image, and the empty-cover sheaf condition makes its section zero.
   The composite projection has empty fibre too, by `Scheme.Pullback.range_snd`.
   Thus the rank witnesses themselves become zero, rather than an unjustified comparison
   on an empty scheme. Rank zero uses no nonempty basis; empty test schemes have no `t`.
4. **Route, reuse and pruning: pass.** Searched `lean/Sheaf`, `lean/WeilConjectures`, and
   Mathlib's algebraic-geometry/module-sheaf files for stalk finrank and subsingleton
   stalk results. Read `FiniteLocallyFreeStalkFinrank`, the fixed-rank pullback instance
   in `Modules.LocallyFreeRank`, and Mathlib's pullback-carrier point and range lemmas.
   The proof uses the existing fixed-rank stalk calculation rather than restating it.
   Read the three helpers named in the return: the two restriction helpers in
   `Modules.RestrictionStalkExtensionIso` and `tensorRankComp` in
   `PicardUniversalRankMatchConjunction`. The repaired module contains none of their
   duplicate theorems and calls the existing semilinearity and rank-composition helpers.
   The local frame route avoids the general tensor-pullback stalk theorem; the report's
   sole removed old proof dependency is exactly `lem-weil-pbc-module-stalk-pullback`.
   Each added import supplies a used theorem or instance. The associativity construction
   also exists privately in `PicardBaseChangeStalkFiniteBases`; importing that whole module
   solely for its definition would add its separate finite-basis route to this numerical
   argument, so the existing correct local construction is retained. Read unit
   `sk-prop-av-cube`: its realized statement is empty and its one realized step is empty;
   no realized unit step or chapter route is bypassed.
5. **DAG: pass.** Compared the whole node diff and read the statements and Lean records
   of all old and new proof dependencies. Only `proof`, `proof_deps`, and `proof_origin`
   differ. The three steps record the local-frame calculation/associativity, comparison
   at a common reference point, and proper-image empty-fibre vanishing in the actual
   proof. The two newly cited module nodes provide the existing private helpers through
   `import all`; their stronger public conclusions are not assumed. The dropped tensor
   stalk formula is not called. Node statement, source, unit, chapter and Lean signature
   record remain unchanged; there are no new nodes to validate.

Second-reading changes: refreshed the scratch axiom check to use the repaired source and
added this independent review. No correction to the repaired Lean proof or node was needed.
