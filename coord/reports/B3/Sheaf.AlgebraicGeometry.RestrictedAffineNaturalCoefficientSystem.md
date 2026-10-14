## What changed

Proved `AlgebraicGeometry.Etale.exists_restricted_affine_natural_coefficient_system`
in `Sheaf.AlgebraicGeometry.RestrictedAffineNaturalCoefficientSystem` without changing
any signature or definition. Added proof-only imports of
`Sheaf.AlgebraicGeometry.RestrictedAffineSingleTransitionLaws`,
`Sheaf.AlgebraicGeometry.RestrictedAffineSingleConeNaturality`,
`Sheaf.AlgebraicGeometry.RestrictedAffineSingleConeLeg`, and
`Sheaf.AlgebraicGeometry.RawAffineRestrictedCohomologyMapFormula`.

The witnesses are the actual `restrictedAffineDiagram`, `restrictedAffineCone`,
`restrictedAffineK`, `restrictedAffineSingleTransition`, `restrictedAffineG`,
`restrictedAffineSingleConeIso`, and `restrictedAffineL`. Their existing geometric,
colimit, transition-law, and cone-naturality results supply the corresponding fields.
Mathlib's `HomologicalComplex.isZero_single_obj_X` proves both negative-degree claims.
The cohomology comparisons are `eqToIso` of proved definitional object equalities.
A private equality-transport naturality lemma proves their compatibility without
repeatedly reducing the large cohomology structures. The explicit cone-leg lemma
reduces the cone equation to the generic `rawAffineRestrictedCohomologyMap_formula`;
the existing concrete stage-naturality theorem supplies the stage equation.

Updated the main node's proof, proof dependencies, and proof origin to describe this
assembly. Added a generic, proved raw-map formula API in its own module. No existing
public signature or shared definition changed. Proved
private helpers identify the concrete coherence witnesses and cohomology objects;
private comparison isomorphisms use those named equality proofs. A proved private
assembly lemma packages the existential with abstract witnesses; the public theorem
supplies the concrete witnesses, negative-degree proofs, and both comparison equations.
The complete module compiled cleanly in 59.0 seconds; the formula API module also
compiled cleanly. No compile limit was increased and no proof was left unfinished.

Searches: Lean Finder returned `HomologicalComplex.isZero_single_obj_X` and related
single-complex support lemmas; Loogle confirmed its exact signature. Local ripgrep
found the explicit transition laws, cone naturality, and cone-leg theorems. No generic
Mathlib theorem supplies the full etale coefficient-system construction.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.Etale.exists_restricted_affine_natural_coefficient_system`
(node `lem-sbc-restricted-affine-natural-coefficient-system`).
The already-proved `AlgebraicGeometry.Etale.restricted_affine_stage_naturality`
keeps its signature and is derived from a proved private heterogeneous version
of the same definitional equality. No sorry remains in either delivered module; no holes were added or split off.
Also proved `AlgebraicGeometry.Etale.rawAffineRestrictedCohomologyMap_formula`
(node `lem-sbc-raw-affine-restricted-cohomology-map-formula`). This is a proof,
not a decomposition.

## No longer needed

No existing import or proof-dependency node was removed. All original dependencies
are used, and the three explicit coherence results and generic raw-map formula are now additional
dependencies.
No pruning is claimed. The existential wrapper modules `RestrictedAffineSingleCoherence`
and `RestrictedAffineCoefficientSystem` are unnecessary for this proof and were not
imported; this does not assert that other target branches stop using them.

## Where the brief, the DAG or earlier work was wrong

The existing node described the main construction as still open and said the
transition-law, cone-naturality, and cone-leg results were not applied. These are now
applied to the concrete constructions, and its proof record has been updated.
The previous stage-naturality correction is respected: the proof uses the concrete
transition and canonical equality comparisons throughout, never arbitrary witnesses from an
existential coefficient-system theorem. No statement correction is needed.

## New nodes

`lem-sbc-raw-affine-restricted-cohomology-map-formula` records the proved formula
`AlgebraicGeometry.Etale.rawAffineRestrictedCohomologyMap_formula` in
`Sheaf.AlgebraicGeometry.RawAffineRestrictedCohomologyMapFormula`. It applies to any
triangle of schemes over S, any abelian etale coefficient morphism, any degree p,
and any etale U; it has no directedness or geometric hypotheses. The formula follows
by reflexivity from the existing raw-map definition. This supplies an explicit API
so stage and cone comparisons can keep the raw map folded, avoiding repeated
expansion of derived cohomology structures. No new sorry or change record is needed.

The whole blueprint search for “canonical cohomology map” found no matching
blueprint node. The new node inherits the item's blueprint ancestor
`sbc-lem-higher-direct-image-limit` and records the intervening nodes. LeanSearch
was attempted but returned an unavailable-service error; Lean Finder, Loogle,
and source grep supplied the remaining recorded searches.

## Second reading by B3

1. Compared the complete module with the repository version and extracted both existing
   theorem signatures: each is byte-for-byte identical. The existing public import is
   unchanged; all four added imports are proof-only. No existing definition, visibility,
   hypothesis, or conclusion changed. Read the earlier stage-naturality repair record:
   this proof retains the prescribed concrete transitions and comparison isomorphisms.
2. Compiled both delivered modules together through lcompile.py: clean, 17.0 seconds
   for the formula module and 55.7 seconds for the main module. Read all private helpers
   and both public proofs. No sorry, axiom, unsafe, opaque, extern, implemented_by,
   kernel-check bypass, or raised compile limits occurs in either delivered source.
   Explicit #print axioms checks of the main theorem, stage theorem, and new formula
   compiled cleanly in a scratch copy (55.9 seconds); each uses only propext,
   Classical.choice, and Quot.sound, with no sorryAx.
   Both private comparison definitions are eqToIso of named, proved reflexive equalities.
   The coherence existential is proved with actual constructions and retains HEq to
   those constructions; no arbitrary witness is chosen from an unproved existence result.
3. No statements were split off and no holes were added. Checked the new proved formula
   against rawAffineRestrictedCohomologyMap's definition: its composite is exactly that
   definition, and reflexivity proves it uniformly, including zero coefficients,
   degree zero, and identity maps. Its node's Lean statement is byte-identical to the
   theorem signature. Independent Lean Finder search for inverse-image coefficient
   morphisms and cohomology of single complexes returned group-cohomology results,
   not this library-specific formula; source search found no existing formula API.
4. Read the concrete construction, single-transition laws, cone naturality, and cone-leg
   API used in the proof. The assembly uses these proved components directly and
   Mathlib's isZero_single_obj_X for negative degrees. The generic private transport
   lemma is a short equality-induction proof; Loogle's eqToHom_naturality is instead
   formulated for a morphism family over one index equality. No shorter full construction
   was found. Every added import has an explicit proof use; the public SingleMaps import
   is required by the existing stage theorem's signature. All old proof dependencies
   remain used, so No longer needed is complete and no pruning is claimed. This item
   and its ancestor are below the unit level; no realized unit statement or step is
   bypassed or changed. The unit's pre-existing empty realized arrays are unchanged.
5. Checked all delivered nodes' proof_deps against the union of their proof-step uses;
   they agree. Existing nodes change only proof, proof_deps, and proof_origin. The new
   formula node has its source, complete proof, searches, origin, blueprint ancestry,
   creation record, and matching Lean record. The first worker omitted updating the
   already-proved stage theorem's node after replacing its direct unfolding proof with
   the formula-based private HEq helper. Repaired that node's proof description,
   dependency list, and origin to match the actual Lean proof.

Second-reading changes: updated only the stage-naturality node and this report.
No Lean proof, declaration, definition, or import required repair. The delivery closes
one original hole and adds none: proved 1 of 1; split off 0; pruned none.
