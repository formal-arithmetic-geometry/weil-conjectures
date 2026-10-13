## What changed

Proved `AlgebraicGeometry.Scheme.affine_principal_cover_quasiIso_detection` in the assigned
module, keeping its signature, universes, public imports and visibility unchanged.
Four proved private helpers establish tilde exactness, the principal-open localization
comparison, the relative open-cover isomorphism criterion, and its homology application.
The comparison reuses `Scheme.Modules.tildePullbackIso` from the source library.
Added proof imports of `WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde` and
`Mathlib.CategoryTheory.Sites.LocalProperties`. Updated the existing node's proof,
proof dependencies and proof origin to match the Lean proof. No other module is adapted.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.Scheme.affine_principal_cover_quasiIso_detection`
(node `lem-sc-affine-principal-cover-quasi-iso-detection`).
No sorry remains in the assigned module, and no hole was added or split off.
The private helpers `tilde_preservesHomology`, `principalOpen_localized_quasiIso`,
`isIso_over_of_cover`, and `quasiIso_over_of_cover` are all proved.
The consolidated module compiles through lcompile.py; the delivery dry run additionally
checks the maintainer's axiom probe and server preflight.

## No longer needed

Removed the proof import `Sheaf.Topology.SheafIsomorphismLocalOpenCover` and the dependency
`lem-weil-pbc-sheaf-isomorphism-local-open-cover`: the proof applies Mathlib's
`Sheaf.isIso_of_coversTop` directly to the localized site over U.
The node `lem-weil-pbc-quasi-coherent-module-kernel` is unnecessary for tilde exactness:
localization preserves injectivity, and the left adjoint preserves cokernels.
Its module `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` stays imported
because its proved `preservesLimitsOfSize_restrictFunctor` instance supplies exactness
of ordinary restriction. Its corresponding restriction-limits node is now a dependency.
The affine tilde/Gamma adjunction and tilde construction remain used; no unit-level
statement or step is bypassed (`sk-thm-picard-duality.realized` has no assigned nodes).
These are proof-specific pruning claims; other targets may still need the named modules.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The planned principal-open comparison already follows from
the proved source-library pullback/scalar-extension isomorphism. The planned route through
quasi-coherent kernels was longer than the direct injectivity proof for tilde.
The local-isomorphism theorem in the planned import concerns a cover of a whole ringed
space; the private relative-site argument directly handles an arbitrary open U.
The proof handles r=0, empty U, the zero ring, zero elements and units without extra
hypotheses or an added derived-category universe instance. The two added restriction
nodes and the affine pushforward sections node are existing proved tool results from
another unit, used only for the ordinary localization comparison, with no change to the
unit route. No new nodes or interface changes are required.

## Second reading by E3

1. Compared the only delivered Lean module with the repository by diff, and checked
   the existing theorem signature byte for byte. Universes, hypotheses, conclusion,
   public imports and visibility are unchanged. There are no definition changes,
   adapted modules or change records. Verdict: pass.
2. Read all four private helpers and the main proof. There is no sorry, axiom,
   unsafe, opaque, implemented_by, extern or hidden data choice in the module.
   A scratch copy of the complete repaired module compiled with a #print axioms
   probe for affine_principal_cover_quasiIso_detection: only propext,
   Classical.choice and Quot.sound. All four helpers occur in that proof's closure.
   The standalone tilde_preservesHomology probe gives the same permitted axioms.
   Verdict: pass, subject also to the delivery tool's exact-file checks.
3. No statement was split off, no new public statement was introduced, and no hole
   was added. Checked the private lemmas against empty U and the empty index type,
   zero rings, a=0 and units: the range identification and localized-site covering
   proof require no nonemptiness or unit-ideal assumption. Verdict: pass.
4. Searched the library independently for tilde exactness and local quasi-isomorphism
   criteria. Read AffineDerivedTildeHomologyComparison and
   AlternatingCechSheafLocalContraction: their relevant helpers are private, and
   their public statements do not replace this relative principal-open argument.
   Read PullbackTilde and reused its proved natural comparison as the worker did.
   Every remaining import supplies a signature, comparison, exactness instance or
   the local isomorphism criterion; proof-only additions use plain import.
   Both former proof dependencies no longer used are listed above. The unit's
   realized record is unchanged and has no assigned statement or step nodes.
   Verdict: pass.
5. Compared the node JSON with the repository: only proof, proof_deps and
   proof_origin differ. Checked that proof_deps is exactly the union of uses,
   and read the existing declarations for the affine adjunction, tilde construction,
   affine pushforward sections and restriction limits/colimits. These match the
   argument, including the dependencies inside the source pullback comparison.
   Verdict: pass.

Second-reading repair: the initial exact-file compile exceeded 60 seconds.
Removed the three unnecessary backward.isDefEq.respectTransparency.types overrides,
then changed the five local comparison isomorphism bindings ep, ec, eqp, eqpc and
eqo from let to have to avoid unnecessary unfolding during proof checking.
Also unpacked the concretely constructed Spec(A_a) ≅ D(a) together with its
inverse factorization into local e and heinv, so later steps use the isomorphism
abstractly rather than unfolding its full construction. This existential is proved
by the existing explicit isoOfRangeEq construction, with no unproved witness choice.
The complete repaired proof and axiom probe compiled in 49.7 seconds; no mathematical
argument or interface changed. No imports or nodes were additionally pruned.
