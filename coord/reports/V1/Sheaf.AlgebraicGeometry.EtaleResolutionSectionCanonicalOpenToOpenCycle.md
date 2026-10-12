## What changed

Proved `AlgebraicGeometry.Etale.resolutionSection_canonical_open_to_open_cycle`
in `Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalOpenToOpenCycle`, with
its original signature and visibility unchanged. Added proof-only imports of
`Sheaf.AlgebraicGeometry.EtaleOpenFreeSheafUnitCoherence` and
`Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison`.

A proved private helper `sectionsEquiv_precomp` gives free-sheaf sections
naturality in the represented object, directly from the two adjunctions and
`uliftYonedaEquiv_naturality`. The main proof takes the inverse sections equivalence
of the cycle's image under `iCycles`, proves it is a Hom cocycle using `iCycles_d`,
and identifies the restricted representative using `cyclesMap_i`. It then applies
both `open_cocycle` normalizations and `InjectiveResolution.mk₀_comp_extMk`.
Mapping and associating Ext compositions, applying the exact-functor composition
comparison, cancelling its inverse at G, and using identity-generator coherence
close the equality. This follows the existing node's route and uses every planned
proof dependency; no DAG route or public interface changes are needed.

The module compiles cleanly through `lcompile.py`. The proof is uniform in q and
in the opens: it has no positive-degree, nonempty-open, or strict-inclusion
hypothesis. In particular q = 0, equal opens, and the empty open are included.

Sources read: Stacks [0A50](https://stacks.math.columbia.edu/tag/0A50), its proof by
section complexes of an injective resolution, and
[03F3](https://stacks.math.columbia.edu/tag/03F3), the comparison by localization
and restriction of that resolution. The named comparison/coherence declarations
and their DAG records were read. Searches through msearch's LeanFinder, Loogle,
and grep, and local rg, found the Ext representative-composition formula and the
adjunction/Yoneda naturality tools, rather than a ready-made theorem for this
normalized comparison.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.resolutionSection_canonical_open_to_open_cycle`
(node `lem-weil-pbc-etale-resolution-section-canonical-open-to-open-cycle`).
One of one original sorries proved; zero sorries left in the delivered module,
zero holes added, and zero statements split off. The private sections-naturality
helper is also proved. This is a proof from existing library declarations, not
a decomposition into new obligations. The second reader
confirmed that this theorem and its private helper have only the three permitted
axioms, with no transitive `sorryAx` dependency.

## No longer needed

None. No imports were removed. All five planned nodes remain used: the canonical
comparison definition, open-comparison data (sections equivalence and its
coefficient naturality), open-object cohomology map definition, free-sheaf unit
coherence, and exact-functor composition comparison. No planned node or module
has been bypassed or proposed for pruning. The unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found. The cited local Stacks source files
are absent on this machine, so the two cited statements and proofs were read at
the official URLs above. The elementary free-representable precomposition
naturality needed for the cocycle calculation was not a public library lemma;
it is now proved privately in the item's module, with no new obligation or node.

## Second reading by V1

1. Interface: compared the complete delivered module with the repository using
   `diff -u`, and independently compared the original theorem signature through
   `:= by` byte for byte. The signature, visibility, universe, arbitrary scheme X,
   sheaf G, resolution I, normalized comparison c, nested opens A and B, degree q,
   cycle z, and both sides of the equality are unchanged. No existing definition
   was changed and no change record is required. Verdict: pass.

2. Proof: compiled the delivered file with `lcompile.py`, without errors or
   warnings. A scratch copy with `#print axioms` for
   `AlgebraicGeometry.Etale.sectionsEquiv_precomp` and
   `AlgebraicGeometry.Etale.resolutionSection_canonical_open_to_open_cycle`
   compiled and printed exactly `propext`, `Classical.choice`, and `Quot.sound`
   for each. There is no `sorryAx`, local hole, forbidden declaration, or data
   chosen from an unproved existence theorem. The inverse `sectionsEquiv` is an
   explicitly constructed equivalence, not an arbitrary witness. Verdict: pass.

3. New obligations: none were split off. The private helper is proved by two
   applications of adjunction naturality and `uliftYonedaEquiv_naturality`.
   Searching the library with `rg` found related private precomposition lemmas in
   `Sheaf.Paper.FreeRepresentableHomotopyHomology` and
   `Sheaf.CategoryTheory.InjectiveResolutionCohomologyPresheafData`; neither is a
   public replacement for this helper using the specified sections equivalence.
   An independent Loogle search confirmed
   `CategoryTheory.Adjunction.homEquiv_naturality_left`. No duplicate public
   statement was added. The argument needs neither q > 0 nor a nonempty or proper
   open inclusion: q = 0, equal opens, and the empty open remain covered.
   Verdict: pass.

4. Route and pruning: read the proof from its conclusion downward. The chosen
   f is the inverse sections image of `L.iCycles q z`; coefficient naturality and
   `iCycles_d` prove it is a cocycle. Represented-object naturality and
   `cyclesMap_i` identify its precomposition with the restricted cycle. Both
   `c.open_cocycle` equations apply with precisely those representatives.
   Mathlib's `InjectiveResolution.mk₀_comp_extMk` identifies their Ext classes.
   The remaining calculation maps and associates Ext compositions, applies
   `exactFunctorCompositionComparison` with e : FA ≅ FB ⋙ T, cancels e at G,
   and uses `etaleOpenFreeSheafUnit_coherence B A h` at the source. The direction
   of the isomorphism agrees with the inverse in `openCohomologyRestriction`.
   Each of the three imports is needed: the public one supplies the statement,
   and the two plain imports supply the comparison/coherence proof. Every old
   `proof_deps` node remains used, so `## No longer needed` is complete.
   Read `dag/units/sk-thm-p1.json`, including `realized`: the item is below its
   fixed statement and steps, and bypasses none of them. Read the official
   [Stacks 0A50](https://stacks.math.columbia.edu/tag/0A50) resolution-section
   argument and [Stacks 03F3](https://stacks.math.columbia.edu/tag/03F3), part (2),
   for localization. These give the source context; the explicit normalized
   cocycle calculation is supplied by the Lean argument just checked.
   Verdict: pass.

5. DAG: read the item's node and its five dependency records/modules, including
   the canonical comparison structure, the sections adjunction, the explicit
   object-cohomology map, unit coherence, and Ext composition comparison.
   The existing proof step describes the calculation actually implemented;
   `proof_deps` is exactly its five-node union, and `proof_origin` records the
   source of that existing cocycle route. No new node or metadata repair is
   needed. Also checked the landed additive construction record
   `coord/changes/etaleOpenObjectCohomologyMap.md`; the proof uses its explicit
   construction and does not alter its interface. Verdict: pass.

Second-reading changes: appended this independent review and clarified the axiom
result in `## Proved and sorry left`. No Lean proof, import, statement,
definition, or DAG change was necessary. One original hole closed, no holes
added, no split-off statements, no pruning.
