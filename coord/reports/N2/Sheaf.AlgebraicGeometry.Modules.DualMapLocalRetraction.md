## What changed

The existing theorem `AlgebraicGeometry.Scheme.Modules.exists_local_retraction_dualMap_of_epi`
keeps its signature byte for byte. Its proof obtains a local section and then applies
transpose compatibility. The two intermediate statements are now in their own new modules,
`Sheaf.AlgebraicGeometry.Modules.LocalSectionOfEpi` and
`Sheaf.AlgebraicGeometry.Modules.DualRetractionOfLocalSection`. They are imported privately
because only the target proof needs them. The original public Dual import remains necessary
for the target statement. The local-section module publicly imports only the scheme-module
and finite-locally-free definitions it needs.

The second reader corrected the composition in both new statements: a right inverse satisfies
`s ≫ restrict(f) = id_Q`, not `restrict(f) ≫ s = id_P`. The erroneous versions were never
existing declarations of the repository. No existing definition or statement changed, and no
change record or forced adaptation is needed. All three delivered modules compile locally.

## Proved and sorry left

Closed original hole: `AlgebraicGeometry.Scheme.Modules.exists_local_retraction_dualMap_of_epi`.

Added holes:
- `AlgebraicGeometry.Scheme.Modules.exists_local_section_of_epi`, node
  `new-sbc-local-section-of-epi`, in `LocalSectionOfEpi`.
- `AlgebraicGeometry.Scheme.Modules.isSplitMono_restrict_dualMap_of_local_section`, node
  `new-sbc-dual-retraction-of-local-section`, in `DualRetractionOfLocalSection`.

This is a decomposition, not a complete axiom-free proof: one upper hole closed, two strictly
smaller lower holes added, net holes closed minus added = -1. The item itself has no textual
sorry, but its proof still depends on both named holes. Each lower theorem has a source and a
complete natural-language proof. No hole was added inside a definition. The scratch axiom
checks show only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; deliver3 also runs
its declaration probe. The attempted proof of transpose compatibility did not close within
the short repair pass and is excluded from the delivery.

## No longer needed

No original import removed and no module pruned. The old target proof dependencies
`def-sc-finite-locally-free-sheaf`, `def-weil-sheaf-of-modules-category`,
`def-pur-sheaf-hom`, and `def-pur-localized-ringed-site` are no longer direct proof dependencies
of the target: its proof now uses the two intermediate declarations. All four remain necessary
in those intermediate nodes, so none is claimed as pruned from the target import closure.
The unused proof-only InternalHomOver import from the unsuccessful repair attempt was removed.

## Where the brief, the DAG or earlier work was wrong

The first worker's local-section theorem used the wrong composition. On Spec(k), the
projection k^2 → k is an epimorphism with a finite free target but cannot have a left inverse:
its nonzero kernel precludes `f ≫ s = id_(k^2)`. The first worker's transpose theorem was also
false as written: the inclusion k → k^2 has a left inverse, but its dual k^2 → k is not
monic. Both new statements now use the genuine section identity.

The new nodes had empty statement/proof dependency lists, copied review stamps, an incorrect
finite-basis proof attached to transpose compatibility, and non-verbatim Lean signatures.
These have been repaired. The target node's proof metadata was missing from the sandbox;
it now records the actual two intermediate applications. The original report incorrectly
called this a proof without stating its negative hole balance.

## New nodes

`new-sbc-local-section-of-epi`: the finite-basis local lifting step, in new module
`Sheaf.AlgebraicGeometry.Modules.LocalSectionOfEpi`. Its equation is now the correct
right-inverse equation. Local surjectivity and the universal property of a free sheaf are
available, but no exact local-section theorem was found.

`new-sbc-dual-retraction-of-local-section`: contravariant internal-Hom functoriality and open
restriction, in new module `Sheaf.AlgebraicGeometry.Modules.DualRetractionOfLocalSection`.
It has no epimorphism or finite-freeness assumption: a supplied section suffices.
`SheafOfModules.overHomObjIso` supplies the restriction isomorphism, but the full scheme-module
transpose/restriction compatibility is not already stated in the searched library.

LeanSearch was attempted and returned Internal Server Error; this is recorded as unavailable
without a mathematical search verdict. Independent successful searches used leanfinder for simultaneous local lifting, loogle for preservation
of split monomorphisms, and grep for overHomObjIso/freeHomEquiv. The actual search results are
recorded in both new nodes. Repository searches included local splitting, local lifts,
restriction of internal Hom, and existing local sections. The existing
`exists_openCover_split_shortExact` has additional finite-rank hypotheses on all terms and
cannot handle arbitrary P here. The source Tag 0EKP was read: these two steps expand its
omitted details in the (2) to (3) dual-surjection construction.

## Second reading by N2

1. PASS after repair. Diff checked against the repository: the existing target signature is
   byte for byte identical. No existing definition, attribute, visibility or public import
   changed. Only the target proof and two proof-only imports changed; new statements have
   their own modules. No other held module is touched.
2. PASS with the two declared open statements. Every delivered module compiled individually
   in dependency order via lcompile.py. No prohibited declaration or implementation mechanism
   occurs, no definition was added, and each remaining sorry is the entire proof of its named
   public theorem. The scratch #print axioms checks and the delivery probe check the allowed
   axioms; sorryAx is expected from the two explicit open statements.
3. PASS after repairing two false compositions. A section is a right inverse. Tested rank
   zero, zero source/target, the empty scheme/open, and ordinary finite-dimensional vector
   spaces. The local lifting step only uses finite freeness of Q, not quasi-coherence of P.
   The transpose step only uses the supplied section. Both are strict parts of the original
   two-step argument, not restatements of its final conclusion. Each has a full proof docstring
   and node. Searches with different terms found useful APIs but no duplicate exact theorem.
4. PASS as a decomposition. The route preserves finite-basis local lifting followed by taking
   duals on an open; no chapter or unit step is bypassed. The pre-existing realized lists in
   dag/units/sk-prop-input-spreading.json are empty and unchanged; this delivery makes no claim
   to fill them. Imports are needed for statements or the two actual proof applications.
   Every old proof dependency is accounted for above; no module pruning is claimed.
5. PASS after repair. The target proof and proof_deps now match its Lean applications. Both
   new nodes have definition dependencies, appropriate self-contained statements, matching
   verbatim Lean signatures, corrected proof text, source, search evidence, creation fields,
   chapter/unit and blueprint ancestry. Copied review stamps were removed from new nodes.

Changes by this second reader: corrected both new composition equations, moved intermediates
to separate modules, minimized local-section imports, completed natural-language proofs,
repaired all three node records, and rewrote the progress report to call this a decomposition.
