## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.exists_finite_etale_extension_of_regular_integral_divisor` by a complete Lean assembly, preserving its signature and visibility. Added two proof-only imports and two new statement modules. Private proved helpers establish etaleness on the union of two opens and restrict an isomorphism over a larger open to a smaller open, including its composition identity. Updated the item node to match this proof.

The proof follows the trait purity step of unit `sk-prop-input-spreading`: adjoin W, which contains the divisor's generic point, then extend across the remaining regular codimension-two boundary. Source pages read: Stacks Tags 0EYE, 0EYJ, 00NU, 0H2W, 0BMA, 0EY7 and 0EY6(2). No unit or target statement changes.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.Scheme.exists_finite_etale_extension_of_regular_integral_divisor` (node `lem-sbc-regular-integral-divisor-etale-purity`). No sorry remains in the assigned module.

Added two holes, a decomposition rather than a complete proof of classical purity:
- `AlgebraicGeometry.Scheme.regular_dim_ge_two_outside_divisor_generic_neighbourhood` (node `lem-sbc-regular-integral-divisor-boundary`), in `Sheaf.AlgebraicGeometry.Morphisms.RegularIntegralDivisorBoundary`.
- `AlgebraicGeometry.Scheme.exists_finite_etale_extension_of_regular_codimension_two_boundary` (node `lem-sbc-regular-codimension-two-etale-extension`), in `Sheaf.AlgebraicGeometry.Morphisms.RegularCodimensionTwoEtaleExtension`.

Both have whole named public theorem proofs `:= by sorry`, source citations, proof docstrings and matching nodes. The first statement involves no cover and proves only regularity and dimension of the remaining boundary. The second involves no divisor, integral scheme or generic-point neighbourhood and extends a cover of an open across an already known regular codimension-two boundary. The combination, union-locality and restriction calculation are proved in Lean. Net holes: one closed, two added.

Edge cases checked mathematically: a point divisor in a curve has no boundary after adjoining W; a line divisor in a plane leaves only dimension-two closed points outside a generic-point neighbourhood; W=top makes the boundary condition vacuous. Empty covers extend by the empty cover. If V is empty, the boundary condition forces L empty, since any nonempty locally Noetherian scheme has a generic point with dimension-zero stalk. Singularities inside V are allowed; regularity is required only at missing points. No normality of N, global regularity of L, quasi-compactness or quasi-separatedness was added.

All three delivered modules compile via lcompile.py. The assigned module compiles without any sorry. Its proof still depends on the two named new holes, so its transitive axioms still include sorryAx until these items are proved.

## No longer needed

No original imports or modules pruned. All four original public imports are needed by the unchanged signature. In the new codimension-two extension module, the second reader replaced the unnecessarily broad `WeilConjectures.AlgebraicGeometry.Regular` import by `Mathlib.AlgebraicGeometry.Noetherian` and `Mathlib.RingTheory.RegularLocalRing.Defs`, which supply exactly the local Noetherianity and regular-local-ring predicates used in its statement. The broad module remains needed by the divisor statements, so this is not global module pruning. Removed from the assigned node's direct `proof_deps`: `def-nagata-effective-cartier-ideal`, `def-weil-regular-scheme`, and `def-pc-integral-scheme`. Their direct geometric argument is now carried by `lem-sbc-regular-integral-divisor-boundary`. The original definition dependencies remain statement dependencies and are used by the new statements; none is claimed globally unnecessary. No independent DVR construction, normalization of N, or finite-normal comparison module is imported: adjoining W removes every codimension-one boundary point directly.

## Where the brief, the DAG or earlier work was wrong

The item's original proof_deps listed only definitions, although its proof used substantive geometric and purity inputs. Those definitions cannot supply either the Cartier stalk regularity/dimension calculation or existence of an extension. The delivery supplies two independently scoped statement nodes for these missing inputs. Mathlib searches found the ring dimension-drop lemma but no scheme-level boundary calculation or finite-etale purity extension. LeanSearch returned Internal Server Error; this is recorded as unavailable, not as a negative search.

The ancestor tool returned None for this newly created item; the new nodes use the item's recorded ancestor `sbc-thm-spreading-finite-etale-galois`. Blueprint searches for 0BMA, 0EY7, 00NU, regular integral, purity regular, Cartier and codimension found no identical blueprint node. Existing depth-two/trait cover extension modules either require additional smooth/local-base hypotheses or are ancestors importing this item, so cannot close this proof.

## New nodes

`lem-sbc-regular-integral-divisor-boundary`: the geometric calculation in the first step of the item's original proof. It is independent of any cover; its source is 00NU and the regular-divisor calculation used in 0EYE/0EYJ.

`lem-sbc-regular-codimension-two-etale-extension`: classical extension after all codimension-one boundary points have already been removed. It is the final step of 0H2W, using local purity 0BMA and extension 0EY7, with the locally Noetherian gluing via depth-two uniqueness (0EY6(2)) made explicit in the proof docstring. This keeps the unit's purity route.

No change records or forced adaptations: no existing interface was changed.


## Second reading by M2

1. **Interface comparison: pass.** Read the repository/sandbox diff of
   `RegularIntegralDivisorEtalePurity.lean`. The existing declaration's entire signature,
   universes, namespace, public visibility and docstring are byte-for-byte unchanged;
   only two private proved helpers, two plain proof imports and its proof body were added.
   No existing definition or target changed. Both other modules are new statements,
   with no definitions or choice of data from unproved existence.

2. **Proof and axioms: pass, conditional on the two reported holes.** Compiled all three
   modules in dependency order through `lcompile.py`, with no errors or delivery-file
   warnings. The target uses the boundary lemma, target-local etaleness on `U ⊔ W`,
   the codimension-two extension, and restriction of an isomorphism over nested opens.
   In the last helper `hfac` gives equality over L, `hpre` identifies the inverse images
   of U, and cancellation of the monomorphism `U.ι` gives the required identity over U.
   A scratch-copy `#print axioms` check of all three public theorems showed exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. There is no sorry in the
   assigned module, and exactly one whole named theorem hole in each new module.
   No forbidden axiom, opaque/unsafe declaration, extern or implementation override
   occurs. This closes one original hole and adds two: decomposition, net minus one.

3. **Split statements: pass.** Read Stacks 00NU, 0EYE, 0EYJ, 0BMA, 0EY7, 0EY6(2),
   and 0H2W against both new statements. The boundary lemma uses the Noetherian ambient
   stalk, Cartier nonzerodivisor and regular quotient; integrality makes every
   nongeneric divisor stalk have dimension at least one. W excludes the only possible
   divisor-generic boundary point. It has no cover hypothesis or extension conclusion.
   The other lemma assumes the resulting regular dimension-at-least-two boundary
   directly, with no divisor or generic neighbourhood. Local purity (0BMA), extension
   on Noetherian affine patches (0EY7), and unique extension on overlaps by the
   depth-two identity (0EY6(2)) justify the locally Noetherian gluing; 0H2W uses precisely
   this final purity step. Neither statement is a renaming of the item. Checked a point
   divisor in a regular curve (no remaining boundary), a line in a plane (remaining
   boundary stalk dimension two), W=top, V=top (take the given cover), the empty cover,
   and V empty (a nonempty locally Noetherian scheme would have a generic dimension-zero
   stalk, contradicting the boundary hypothesis). Singularities in V are permitted.
   Repeated msearch with different wording about restriction equivalences and excluded
   regular stalks, and Loogle `IsRegularLocalRing, "quotient"`; no exact theorem found.
   A first Loogle query using `Ideal.Quotient` was rejected as an unknown identifier,
   and is not counted as a negative result. Direct rg of Mathlib geometry/regular local
   rings and both project roots found no boundary/extension theorem closing these holes.
   The upstream regular-quotient generators lemma already assumes ambient regularity,
   so cannot supply the boundary lifting step; the scheme-level Cartier stalk calculation
   is also missing. Existing trait/smooth depth-two extension modules have extra local
   base/smoothness hypotheses or depend on this item. No hole could be closed in a few
   minutes by an available theorem. Both docstrings give sourced complete mathematical
   arguments and both nodes match their statements.

4. **Route and pruning: pass after report repair.** The Bool-indexed cover helper
   proves union-locality from Mathlib's target-local property; the restriction helper
   uses existing `preimageIso` and `isoOfLE`, without a new hole. All original public
   imports support the unchanged signature; both new imports of the item are proof-only.
   Replaced the broad Regular import of the new codimension-two module by the narrower
   Mathlib definition modules. Explicitly listed all three old direct proof dependencies
   no longer used directly, retaining them as statement/geometric dependencies.
   No module is claimed globally pruned. Read `dag/units/sk-prop-input-spreading.json`:
   its section/generic-point step still invokes regular-divisor purity, and this delivery
   supplies its classical codimension-two last step rather than bypassing that route.
   The unit's existing `realized.statement` and seven `realized.steps` arrays are empty;
   this delivery leaves them unchanged and does not claim to repair that existing
   bookkeeping omission. No unit statement or step was removed.

5. **DAG agreement: pass.** The assigned node's first step uses the new boundary node;
   its second step records target-locality and finite base change; its third step uses
   the new extension node and the proved restriction calculation. `proof_deps` is
   exactly the union of those steps' `uses`, and `proof_origin` records the source route.
   Compared the existing node with the repository: only permitted proof fields changed.
   Read both new records, including chapter/unit, source, statement dependencies,
   proof steps, searches, `status: split`, creation/blueprint ancestry and Lean records.
   The normalized recorded Lean signatures agree with the declaration signatures.
   No change record or forced adaptation is needed.

Second-reading changes: narrowed the new codimension-two module's imports, made the
old direct proof-dependency removals explicit in `## No longer needed`, and added this
independent reading. No theorem signature, proof body, definition or DAG route changed.
