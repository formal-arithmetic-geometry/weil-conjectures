## What changed

Proved both declarations in `Sheaf.Algebra.Homology.RingPseudoCoherentSummand` without
changing their signatures or public imports. Added proof imports of
`Sheaf.RingTheory.MPseudoCoherentVanishingBase` and
`Sheaf.RingTheory.PseudoCoherentIffAllM`. Updated the item's DAG proof and docstrings.

The fixed-degree proof descends simultaneously in degree for both summands, starting
above the cohomology bound of the original witness. Its step uses the existing
triangle lemma on the two ordinary split biproduct triangles. Private proved helpers
transport witnesses along suitable cohomology maps, raise their degree, and extend the all-degree
criterion from representatives to derived objects. No new data definition is introduced.
The all-degree clause applies that criterion and the fixed-degree result.

LeanFinder found no pseudo-coherence summand result; Loogle found Mathlib's
`CategoryTheory.Pretriangulated.binaryBiproductTriangle_distinguished`; the Mathlib grep
for pseudo-coherence summands returned no hits. Library search found the existing
vanishing-base and all-degree criterion used here. Local single-file compilation passes.

Repair of the returned delivery: generalized the private transport helper in place as
`DerivedCategory.mPseudoCoherent_of_homology_map`. Its argument is now any morphism
whose homology maps are isomorphisms above `m` and epi at `m`, rather than an
isomorphism of derived objects. The three former isomorphism calls now apply this
stronger result to the isomorphism's hom or inv with inferred homology conditions.
No import or public signature changed. The retained second reading below concerns
the pre-repair version; the independent reading of the repaired version is recorded below.

## Proved and sorry left

Closed both original holes:
- `DerivedCategory.mPseudoCoherent_summand`
- `DerivedCategory.pseudoCoherent_summand`

No sorry remains in this module and no new hole was added. Both declarations have node
`lem-pc-ring-pseudo-coherent-summand`. Scratch-copy `#print axioms` checks of both declarations show exactly `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx` in their transitive closures.

## No longer needed

No import was removed and no existing proof-dependency node or module was pruned.
The planned shifted double-summand construction and shift descent are unnecessary:
ordinary split triangles and simultaneous degree descent suffice. The original triangle
dependency stays, and the existing vanishing-base and all-m criterion are now explicit
DAG dependencies. The unit has empty realized statement/step lists, so this replacement
bypasses no realized unit statement or proof step.

## Where the brief, the DAG or earlier work was wrong

The original proof text inlined the vanishing base and the all-degree criterion instead
of recording their existing nodes as dependencies. The new proof records them explicitly.
The all-degree criterion's Lean signature concerns `Q.obj C`; essential surjectivity and
witness transport bridge this to arbitrary derived objects without changing any interface.
The existing docstrings cited Tag 064T for the all-m criterion, whereas its landed node
and declaration identify Tag 064U; corrected the docstrings. No statement correction,
forced adaptation, or new node was needed.


The landing check correctly found that the old private helper duplicated
`DerivedCategory.pseudoCoherent_of_iso` in `Sheaf.RingTheory.MPseudoCoherentShift`.
That existing declaration is private and unavailable to an importer. The repair takes
the requested generalization option: it proves transport for arbitrary morphisms with
only the required homology properties. This is strictly more general, since no inverse
or homology condition below `m` is required. Composing the finite-free witness with
such a morphism proves the result directly. All three applications remain ordinary
isomorphisms, which automatically satisfy the generalized assumptions.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered Lean module with the repository version. Both existing theorem
   signatures are byte for byte identical; existing public imports and definitions are
   unchanged. Only proof bodies, proof imports, and explanatory docstrings changed. PASS.
2. Compiled the module locally with `lcompile.py` without errors or warnings. Scanned for
   forbidden declarations and holes: none. Compiled a scratch copy with `#print axioms`
   for both public theorems: each uses only `propext`, `Classical.choice`, and `Quot.sound`.
   Witness transport composes maps or isomorphisms; representative selection uses the
   localization's representative isomorphism, not an undetermined existence witness. PASS.
3. No statements or holes were split off. Reviewed the three private proved helpers:
   transport preserves witness conditions; monotonicity handles equality and strict
   inequality separately; the all-degree criterion transports along an actual isomorphism.
   Checked boundary degrees `n = m`, `B > m`, and the final descent index, as well as zero
   summands and unrestricted negative integer degrees. PASS.
4. Read the imported vanishing-base, triangle, and all-degree results and searched the
   library for alternative isomorphism, monotonicity, criterion, and summand declarations;
   a fresh Mathlib grep for `IsMPseudoCoherent|IsPseudoCoherent` found no matches. No shorter
   existing summand result was found. All imports are needed: the original public imports
   supply the statements and biproduct notation, and the three private imports supply the
   used results. The sole old proof dependency remains used, so `No longer needed` is
   complete. Unit `sk-thm-picard-duality` has `realized` statement `[]` and steps `[[]]`;
   no realized statement or step is bypassed. PASS.
5. Compared the delivered node with its repository version and the Lean proof. Only
   `proof`, `proof_deps`, and `proof_origin` changed. The three dependency nodes exactly
   match the zero-witness base, triangle descent, and all-degree criterion used in Lean;
   proof-origin text describes the actual simultaneous degree descent. No new node is
   needed. PASS.

Second reading changed only this report: recorded the independent checks and replaced
its cautious axiom-closure wording with the verified, sorry-free axiom results. No Lean
or DAG repair was necessary.


## Second reading by U2

1. Compared the delivered module with the repository using `diff`, and separately
   compared each existing theorem signature as text. Both signatures are byte for byte
   identical. Existing public imports are unchanged; the two added imports are private
   proof imports. No existing definition, statement, visibility, or target changed. PASS.
2. Compiled the delivered module through `lcompile.py`: no errors or warnings. Scanned
   the delivery for holes and forbidden declarations: none. Compiled a fresh scratch
   copy with `#print axioms` for all three private helpers and both public theorems:
   each has exactly `propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`.
   There is no new data definition or selection from an unproved existence theorem.
   The representative of an arbitrary derived object comes with the localization's
   actual representative isomorphism and is used only inside a proof. PASS.
3. No statement was split off and no hole was added. Reviewed the repaired homology-map
   helper directly: composing the bounded finite-free witness with `g` preserves its
   data, gives compositions of isomorphisms above `m`, and compositions of epimorphisms
   at `m`. No inverse or conditions below `m` are needed. Its former isomorphism-only
   analogue in `MPseudoCoherentShift` is private and strictly less general. Reviewed
   monotonicity at `n = m` and `n > m`, zero summands, arbitrary negative degrees,
   `B = max m b + 1`, the descent base and successor, and the endpoint
   `B - (B - m).toNat = m`. All boundary cases are covered. PASS.
4. Read the definitions and the imported triangle, vanishing-base, and all-degree
   declarations. Fresh searches with retract/finite-free-approximation vocabulary in
   LeanFinder, the split-triangle declaration in Loogle, and Mathlib grep found no
   shorter pseudo-coherence result. Searched the upstream and project sources for
   transport, monotonicity, all-degree, summand and retract results. The generalized
   helper is not an existing statement under another name. Each proof import supplies
   a result used by the proof; public imports supply statement definitions and biproduct
   notation. The sole old dependency, the triangle node, remains used, so the pruning
   list is complete: none. Unit `sk-thm-picard-duality` has `realized.statement = []`
   and `realized.steps = [[]]`; no realized route is bypassed. PASS.
5. Compared the node records structurally: only `proof`, `proof_deps`, and
   `proof_origin` differ. The proof records the bounded vanishing base, simultaneous
   degree descent through the two split triangles, generalized witness transport,
   and representative transport for the all-degree criterion exactly as in Lean.
   Its three dependencies match the three imported library results. No new nodes
   or change records are required. PASS.

This second reading changed only the report, recording the independent checks of the
repaired version and marking its previously pending reading complete. No Lean or DAG
repair was necessary. Holes closed: `DerivedCategory.mPseudoCoherent_summand` and
`DerivedCategory.pseudoCoherent_summand` (2 of 2); holes added: none; split off: none.
