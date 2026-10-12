## What changed

Reduced the sole remaining hole `moduleCohomologyFMap_comp` to the common-target
section-homology diagram `moduleCohomologyFMap_comp_data` in the new module
`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapCompData`. The main module proves the
resolution transport and inverse cancellation from its three squares using private,
proved category-theoretic helpers. Existing signatures and visibility are unchanged.
Also refactored the already-proved independence cancellation through an abstract
private helper: rewriting concrete homology maps caused expensive unfolding.
Updated the parent proof plan and added the diagram node.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_comp` (the only one
of the six public theorems that still contained `sorry` on the baseline).
Added one hole, `AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_comp_data`,
node `lem-weil-pbc-module-cohomology-fmap-comp-data`. This is a decomposition:
one hole closed, one added, net zero. Its conclusion contains only homology of
section complexes and three comparison squares, with no derived cohomology,
resolution isomorphisms, or equality of cohomology f-maps. The parent proves their
combination and transport. The main module and all its private helpers have no holes.

## No longer needed

No existing proof-dependency import, node, or module is pruned. Removed the saved
sandbox copy of `ModuleCohomologyFMapComparison.lean`: it was unchanged and is now
available in the shared compiled cache; its library import remains needed.
The earlier attempted fixed-choice composition statement was never delivered and
has been replaced, rather than retained as another hole.

## Where the brief, the DAG or earlier work was wrong

The saved fixed-choice composition lemma was a restatement, not a strict part of
the argument. The saved report also improperly included the second reader's section;
it has been removed. The saved node had an incomplete signature, no searches, and
an invalid blueprint ancestry format; these are repaired.
The previous comparison-module cache absence has resolved. The original inverse
cancellation rewrites unfolded concrete sheaf/homology constructions and exceeded
the 60-second compiler limit; abstract private cancellation helpers and explicit
associativity simplification avoid that unfolding.
The literature source files are absent on this machine. Sources were verified at
[01FB](https://stacks.math.columbia.edu/tag/01FB),
[01F8](https://stacks.math.columbia.edu/tag/01F8),
[013P](https://stacks.math.columbia.edu/tag/013P), and
[013S](https://stacks.math.columbia.edu/tag/013S). The diagram's assembled proof is
marked agent-written, since Stacks does not state this exact diagram. Edge cases
p=0, identity scheme maps, zero modules, and empty schemes need no extra hypotheses:
the construction uses only nonnegative injective replacement, identity descents,
and invertibility of sections comparison for complexes of injectives.

## New nodes

`lem-weil-pbc-module-cohomology-fmap-comp-data` states the common-target diagram for
homology of section complexes. Its complete proof describes injective replacement
of k_*Ch.K, two quasi-isomorphism lifts, homotopy uniqueness after augmentation,
and application of global sections/homology. Resolution transport and cancellation
are deliberately performed in the parent Lean proof. It stays inside the existing
unit route. No public interface change or forced adaptation is delivered.

## Second reading by G2

1. PASS: compared the delivered main module with the repository using `diff -u`.
   Every existing declaration signature, visibility, definition body, and docstring
   is byte-for-byte unchanged. The only added import is plain `import` of CompData,
   needed only by the composition proof. No target or existing interface changes.
2. PASS: both delivered modules compile locally through lcompile.py. The first
   main-file run timed out on a heavily loaded machine; the unchanged retry passed
   in 53.7 seconds. A scratch copy with explicit `#print axioms` passed in 39.9 seconds.
   Independence and the two new abstract cancellation helpers use only propext,
   Classical.choice and Quot.sound. Composition, its auxiliary theorem, and the four
   downstream public clauses additionally use sorryAx from the documented diagram
   hole. No forbidden declarations or data holes; the sole textual sorry is the
   whole proof of the public named `moduleCohomologyFMap_comp_data`. The choices in
   the final proof are from the already-proved `moduleCohomologyFMapData_nonempty`.
3. PASS: read the new statement against its node, ModuleCohomologyFMapData fields,
   and Stacks [01FB](https://stacks.math.columbia.edu/tag/01FB),
   [01F8](https://stacks.math.columbia.edu/tag/01F8),
   [01EZ](https://stacks.math.columbia.edu/tag/01EZ),
   [013P](https://stacks.math.columbia.edu/tag/013P) and
   [013S](https://stacks.math.columbia.edu/tag/013S).
   Ch.K supplies termwise injectivity for the sections isomorphism; Z.Modules has
   enough injectives for replacement. Ck.lambda and Cc.lambda are quasi-isomorphisms
   and L is bounded below injective, so 013P applies without requiring those maps
   to be monic. The augmentation of Cc.J is a quasi-isomorphism, giving the beta
   homotopy by 013S. The inverse pushforward comparison has source (kh)_*Ch.I,
   hence is applied after the identity descent, not before it. All three displayed
   squares have exactly the directions used by the parent proof. At p=0 the same
   augmentation argument applies; identity maps, zero modules and empty schemes
   do not invalidate replacement, homotopy uniqueness, or sections invertibility.
   Repeated searches with msearch leanfinder (derived global sections for different
   ringed spaces), loogle (fully qualified InjectiveResolution.descCompHomotopy),
   and grep (pushforwardComp / sections quasi-isomorphism), plus rg of lean/Sheaf,
   found no existing diagram. descCompHomotopy works in one category and compares
   resolutions of objects; it does not give the cross-scheme comparison. The
   remaining diagram construction cannot be closed by a short application of it.
4. PASS: the parent gives a real reduction: resolutionSectionsIso_naturality supplies
   three resolution squares and composition_diagram_cancel proves inverse
   cancellation before the result is expanded to the original cohomology maps.
   The remaining theorem asserts only the common-target homology diagram, not the
   parent equality under a new name. This remains a one-for-one decomposition,
   with net zero holes closed, not an axiom-free proof of composition. The imports
   are needed by definitions, basic properties, comparison, diagram, and the local
   enough-injectives instance. No old proof dependency is unused. Read
   dag/units/sk-thm-p1.json `realized`: no unit-level realization is bypassed or
   edited; this reduction is below that level, on the same f-map route.
5. PASS after repair: the parent node records exactly the diagram application,
   naturality and cancellation now written in Lean, and retains its old proof
   dependencies. The new node has its full Lean signature, docstring argument,
   source, searches, creation record, ancestry, chapter and unit. Its proof_deps
   are the union of its steps' uses. Added the omitted SchemeModulesEnoughInjectives
   dependency to the replacement step. Corrected the order/direction of the inverse
   successive-pushforward comparison in the new docstring and node proof. Clarified
   the parent proof_origin's obsolete reference to V2's then-open composition hole.

Second reading changed only the new docstring and DAG proof bookkeeping, and added
this independent review. No Lean proof, existing signature or definition changed.
