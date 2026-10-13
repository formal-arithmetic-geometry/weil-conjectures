## What changed

Replaced the hole in `Sheaf.RingTheory.IntegerApproximationFlatPointStage` by a
complete Lean reduction. The proof establishes Noetherianity of both original
stage ring diagrams using `Algebra.FiniteType.isNoetherianRing`, obtains localized
diagrams from `Algebra.exists_localized_noetherian_approximation`, transports the
assumed flatness through an R-linear equivalence and the localization flatness
criterion, and applies the existing `RingTheory.exists_flat_stage`. At its chosen
stage it uses the localization criterion again and a concrete module linear
equivalence to obtain precisely the original conclusion. The signature and
visibility of the original theorem are unchanged.

Added proof imports of `Mathlib.RingTheory.FiniteType` and
`Sheaf.RingTheory.NoetherianApproximationLocalizedDiagrams`. The new module states
only the localized-diagram construction, without a flatness hypothesis or a
flat-stage conclusion. Its witnesses are destructured exclusively inside the
proof: no definition chooses arbitrary data from an unproved existence theorem.

The existing named nondependent forall binders `hmodel` and `hq` trigger Lean's
unused-variable syntax linter even when the introduced hypotheses are used in the
proof. A three-theorem scratch experiment reproduces this for `forall (h : True),
True`, with both tactic and lambda proofs. A declaration-scoped
`linter.unusedVariables false` preserves the existing signature while suppressing
these two syntax warnings; no kernel or proof checking is disabled.

## Proved and sorry left

Closed the original hole:
`Algebra.exists_flat_integer_approximation_stage_at_prime`
(node `lem-weil-pbc-integer-approximation-flat-point-stage`). There are no sorries
left in the assigned module.

Added one hole:
`Algebra.exists_localized_noetherian_approximation`
(node `lem-weil-pbc-noetherian-approximation-localized-diagrams`), in the new module
`Sheaf.RingTheory.NoetherianApproximationLocalizedDiagrams`.
Its proof is exactly `by sorry`; its docstring and node give the construction in
five steps. This is a decomposition, not a sorry-free proof: one original hole
closed, one construction hole added, net zero. The remaining hole asserts no
flatness and chooses no flat stage. The final Noetherianity, flatness transport,
and stage selection are proved in Lean rather than moved to that hole.
The imported `RingTheory.exists_flat_stage` is already proved from its own named
lower dependencies; those dependencies are unchanged.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrime` from the assigned
module. It remains a proof import and a planned dependency of the new localized
construction module, so this does not prune that module from the import closure.

No mathematical dependency is pruned. Original construction dependencies
`lem-weil-pbc-filtered-colimit-localization-at-prime`,
`def-weil-directed-colimit-abelian-groups`,
`lem-weil-pbc-localization-tensor-product`, and
`lem-weil-pbc-localization-tensor-over-base` are now dependencies of the new node.
The original node directly keeps
`lem-weil-pbc-finite-type-algebra-noetherian`,
`lem-weil-pbc-flat-over-localization`, and
`lem-weil-pbc-colimit-eventually-flat`, together with the new construction node.
No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The original plan requires a localized
module-colimit construction and localized tensor comparisons that are not
supplied together by the existing Lean declarations. These are isolated as a
construction lemma rather than asserted implicitly by a flat-stage lemma.
The finite-type-to-Noetherian part and the selection and scalar restriction part
can be proved directly from Mathlib and the existing stage theorem.

The local `literature/stacks-project/algebra.tex` is absent on this machine.
Read the source at Stacks Tags 00RC, 00R6 and 00QX, and downloaded the current
Stacks algebra.tex into the sandbox scratchpad. The first reduction paragraph
of `theorem-openness-flatness` explicitly localizes the supplied approximation
and then separately applies `lemma-colimit-eventually-flat`. The source label
for 00QX is `lemma-limit-module-essentially-finite-presentation`.
LeanSearch returned HTTP Internal Server Error and is recorded as unavailable.
LeanFinder, Loogle and Mathlib grep ran through msearch.py; the search log is
in the sandbox. Library grep found the existing stage theorem but no theorem
constructing this combined localization interface.

## New nodes

`lem-weil-pbc-noetherian-approximation-localized-diagrams` records the
flatness-independent construction used by steps 1-3 of the original plan. Its
input is a supplied compatible approximation with Noetherian stages, finite
stage modules, and transition tensor isomorphisms. Its output gives local
Noetherian diagrams with the hypotheses of `RingTheory.exists_flat_stage`, plus
actual prime-localization maps and module linear equivalences at the limit and
every stage. It does not assume or conclude flatness. Source: Stacks Algebra,
00RC first reduction paragraph and the displayed system of 00QX.

Edge cases checked in the statement: the index is nonempty but need not have a
least element; ring maps need not be injective; R,S,M may occupy different
universes; the zero module is allowed; and the presence of q excludes a zero
limit top ring. For a singleton system the output is ordinary localization at
the contracted primes. If a stage top ring were zero, its unital map to the
limit top ring would contradict the presence of q, so no nonexistent prime is
required there. All localization comparisons keep the original restricted
scalar actions. No changes to definitions or existing statements, and no change
records or forced adaptations.

## Second reading by A3

1. **Interface: pass.** Compared both delivered modules with the repository. The
   only existing declaration is
   `Algebra.exists_flat_integer_approximation_stage_at_prime`; its entire signature
   is byte-for-byte identical, including its universe lifts, hypotheses, scalar
   instances and contracted prime. Its docstring and visibility are unchanged.
   The new construction module has no repository counterpart. No definitions,
   targets or externally visible imports of the existing module changed; no
   change record or forced adaptation is required.
2. **Proof: pass.** Both modules compile locally without errors or warnings.
   The only explicit sorry is the reported named construction theorem, with
   exactly `:= by sorry`. There are no data definitions, arbitrary choices from
   an unproved existence theorem in a definition, forbidden declarations or
   kernel-checking overrides. The existential diagrams are eliminated only in a
   proposition proof. Checked the two directions of the localization flatness
   criterion and the orientations of both module linear equivalences; they
   transport flatness with exactly the scalar actions in the original signature.
   Axiom probes in scratch copies check both declarations separately.
3. **Split statement: pass as a decomposition.** The new lemma is the
   flatness-independent localization construction, not the original conclusion
   under another name. Its proof in words constructs the diagrams on the original
   index and explains representatives, eventual equality, scalar compatibility,
   local transition maps and tensor comparisons. In particular the localized
   ring tensor comparison requires further localization, not an unjustified
   isomorphism. Tested singleton and constant systems, the zero module,
   noninjective stage maps (including quotient maps), and directed indices with
   no least element. A prime of S contracts to genuine primes at every stage,
   so zero stage rings cause no counterexample. The arbitrary supplied module
   actions remain compatible by the stated semilinearity hypotheses.
   Independently searched LeanFinder for compatible prime localization and
   filtered ring/module diagrams, Loogle for `IsLocalization, TensorProduct`,
   and Mathlib grep for localized-module direct limits and localization
   diagrams. These found component results (including `IsLocalization.tensor`,
   `moduleTensorEquiv`, and module filtered-colimit representatives), not this
   combined construction. Library grep and reading
   `FiniteTypeApproximationFlatPoint` found no replacement: that theorem assumes
   global flatness and additional limit tensor comparisons. Read the source
   paragraphs of 00RC and the system in 00QX in the supplied algebra.tex. Closing
   the combined construction is not a few-minute proof. One upper hole closed
   and one lower hole added remain a net-zero decomposition.
4. **Route and pruning: pass.** The proof directly uses Mathlib's finite-type
   Noetherianity and localization flatness, then the already supplied
   `RingTheory.exists_flat_stage`. Proof-only additions use plain imports.
   Public imports supply types and instances used by signatures; the retained
   localization-colimit proof import of the new holed module follows its
   documented construction plan. Checked all seven old direct proof dependencies:
   four construction dependencies move below the new node, and the three
   Noetherianity/flatness/stage-selection dependencies remain direct.
   `## No longer needed` accounts for each of these; no module is actually
   pruned from the closure. Read `dag/units/sk-thm-p1.json`: none of its realized
   statement or step nodes is bypassed or changed.
5. **Nodes: pass.** Only `proof`, `proof_deps`, and `proof_origin` change in the
   existing node. For both nodes, dependency lists equal the union of step uses
   and the stored Lean statements match the actual signatures verbatim. Checked
   the new node's source, parent route, chapter/unit, creation metadata, search
   records and complete Lean record. Its source proof and the existing node's
   updated four-step assembly agree with the delivered modules.

Second reading changed only this report: added the independent five-point
review and search evidence. No mathematical repair was needed.
