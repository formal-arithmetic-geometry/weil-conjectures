## What changed

Proved `AlgebraicGeometry.Scheme.Modules.cechRefinement_composition_naturality`
in `Sheaf.Paper.CechCupPullbackCompat`, preserving every existing signature and
public import. Added the proof-only import
`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial`.

The proof evaluates the unit-normalized composition isomorphism on sections,
commutes units and coefficient maps with restrictions, and proves equality of
the cochain maps tuple by tuple. Homology functoriality and naturality of the
forgetful homology comparison identify the composite homology map. The composite
comparison square uses the first conjunct of the existing
`cechCupPullbackCompat`, specialized to the auxiliary pair F,F in degrees p,0;
the existing existence theorems supply its comparison and cup-product arguments.
Finally `moduleCohomologyPullback_comp` gives the cohomology-pullback equality.
The comparison-square part therefore still rests on the existing main theorem's
hole, as intended by stage 3; the cochain calculation introduces no assumption.

`tensorPullback` and `tensorPullbackObj` are locally irreducible throughout the
file, avoiding unnecessary unfolding of their concrete constructions. The
scheme-module scalar instance has local priority 2000, following the existing
`EtaleTensorSections` pattern. These local attributes do not change any
definition body or imported interface. The scoped heartbeat
budget matches the two other substantial proofs in the module. The intermediate
cover hypothesis is explicitly cleared: only the original and final covering
hypotheses enter the comparison square. The unused-variable linter is scoped off
for this declaration because the original intermediate-cover binder must stay
unchanged. No hypothesis or signature is removed.
Updated only `proof`, `proof_deps`, and `proof_origin` of the existing node.
No definition or statement changed and no module was adapted. The local
elaboration controls are recorded in
`coord/changes/CechCupPullbackCompat-local-elaboration.md` because the static
preflight flags attribute commands even when the attributes are local. Its users
table contains the complete downstream inventory; no public setting is exported.

Repair H10: replaced backward rewriting of the pushforward-composition naturality
square with cancellation of its inverse. Replaced refinement-formula rewriting
with explicit equality compositions whose degree, cochain and tuple arguments are
specified. The section restriction and coefficient-naturality calculations likewise
compose their equations directly, avoiding dependent rewrite motives. Removed the expanded intermediate homology-naturality restatement;
the proof uses Mathlib's equation directly. All three conclusions and the complete
signature are unchanged. No helper declaration, hole, module or import was added
by this repair. Unification now respects the existing local irreducibility attributes
for the unit and section calculations; the homology-transport block retains the original
normalization setting. The logical route and node dependencies are unchanged.

Validation of the final repair:

- Module compilation with `.olean`, private/server companions and IR artifacts succeeds
  under the unchanged 60-second per-compiler-process timeout. The wrapper's displayed
  69.5-second elapsed total includes waiting for a compile slot.
- The unchanged direct importer
  `Sheaf.AlgebraicGeometry.PicardExternalCupLeftComparisonComplexes` compiles against
  the delivered module artifacts (13.4 seconds).
- The unchanged direct importer
  `Sheaf.AlgebraicGeometry.PicardExternalCupRightCechDiagram` compiles against the
  delivered module artifacts (9.0 seconds).
- `#print axioms cechRefinement_composition_naturality` completes against those artifacts
  (6.9 seconds): `propext`, `Classical.choice`, `Quot.sound`, and the existing transitive
  `sorryAx` dependency from the main compatibility theorem. No additional axiom appears.
- Existing declaration signatures are unchanged, no new hole is present, and every Lean
  line is at most 100 characters. The final dry run runs the complete source axiom probe
  and delivery preflight; no push is requested.

The compiler wrapper and its timeout settings are unchanged. Consumer copies and the
axiom-check module are diagnostic files under scratchpad, excluded from the delivery.
The stale second-reading marker and review text were removed so this repair receives
an independent new second reading.

Searches: Lean Finder returned group-cohomology functoriality lemmas rather than
Cech cup comparisons; Loogle found `HomologicalComplex.homologyMap_comp`;
Mathlib grep found no Cech cup-product result. Searches of both local library
roots found `moduleCohomologyPullback_comp` and the existing normalized
`tensorSectionsComp`. This shorter route needs no new resolution theory for
composition. The unit record `sk-prop-av-cube` has empty realized lists; its
statement and route are unchanged. The cohomology-fmap functoriality node is used
as a general composition tool; it supplies the normalized-unit composition law
needed here, which no node of the cube unit supplies.

## Proved and sorry left

Closed one of the four original holes:
`AlgebraicGeometry.Scheme.Modules.cechRefinement_composition_naturality`.
Added zero holes and zero intermediate statements.

The three existing holes remain unchanged, all attached to
`lem-sc-picard-cech-cup-pullback-compat`:

- `AlgebraicGeometry.Scheme.Modules.cechCupPullbackCompat`;
- `AlgebraicGeometry.Scheme.Modules.moduleCup_coefficient_naturality`;
- `AlgebraicGeometry.Scheme.Modules.moduleCup_pullback_naturality`.

The three already completed naturality declarations and their helpers are
preserved. The new composition proof is complete Lean from existing declarations,
including the main compatibility theorem still awaiting proof; it is not a new
sorry-free transitive proof of the node.

## No longer needed

None. No baseline import, node, or module is pruned. All five original public
imports still supply statement interfaces or the existing proved cochain
naturality calculations. The new proof-only functoriality import is used.
No whole-library or target-closure pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The existing DAG text said successive-refinement composition remained unproved;
the node now records its proof and the exact existing dependencies. The original
resolution-diagram plan is unnecessary for its cohomology-pullback conjunct:
`moduleCohomologyPullback_comp` already proves that law under the unit equation.
The generic Cech comparison naturality theorem is coefficient naturality on one
scheme, not cross-scheme refinement; this proof does not apply it as the latter.
It uses its existence clause only and obtains the cross-scheme square from the
main compatibility theorem's existing first conjunct.

The other three holes need the resolution comparison and multiplicative model
arguments described in their docstrings. The dependency definitions and
cochain identities alone do not supply these arguments. They were left in their
original declarations rather than renamed as equivalent new holes.

The previous delivery was returned as H10 because module-artifact compilation and
the axiom probe timed out. Its earlier successful source-only compilation was
insufficient evidence. This repair explicitly checks artifact generation, the
axiom probe and both unchanged direct importers against the delivered artifacts.

## Second reading by R3

1. **Statements unchanged.** Compared the delivered module with the repository version and
   `original.lean.txt`. All existing declaration signatures, including the three remaining
   holes and the completed naturality declarations, are byte-for-byte unchanged. Verdict: pass.
2. **Proof validity.** Compiled `lean/Sheaf/Paper/CechCupPullbackCompat.lean` with
   `lcompile.py`; it succeeds with no errors. The only remaining `sorry`s are the three
   pre-existing declarations listed above; no new sorry, axiom, unsafe, opaque, or hollow
   definition was added. Verdict: pass.
3. **New statements and searches.** No intermediate theorem or split-off statement was
   added. The proof uses existing declarations and the proof-only functoriality import;
   recorded searches found no duplicate Mathlib or library result. Verdict: pass.
4. **Pruning and route.** The added import is used by the composition proof, while all
   existing public imports remain required for declarations or proof dependencies. The
   successive-refinement route in the unit record is preserved, and no old dependency or
   module can be pruned. Verdict: pass.
5. **DAG agreement.** The node proof, proof dependencies, and proof origin describe the
   tuplewise composition, homology transport, and `moduleCohomologyPullback_comp` route
   implemented in the file. The unit's realized route and target statement are unchanged.
   Verdict: pass.

I changed only this report by adding the present second-reading record. The delivered Lean
module, node, and local elaboration change record required no further repair.
