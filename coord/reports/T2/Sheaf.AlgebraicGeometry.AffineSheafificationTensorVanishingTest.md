## What changed

Proved `AlgebraicGeometry.Scheme.affine_sheafification_tensor_vanishing_test` with its
original signature and docstring. Added a fully proved private helper
`restriction_totalTensor_iso`: transport the existing pullback monoidal structure to
ordinary open restriction, form its natural bidegree tensor comparisons, and totalize.
The main proof restricts the actual K-flat witness along `isoSpec.inv ≫ U.ι`, transports
zero homology by exactness, and identifies the restricted test with `G` using the
open-immersion counit. It constructs the affine representing isomorphism explicitly
from the over equivalence, restriction composition, and the exact-functor localization
factorizations, with the spectrum localization universe `wX` kept independent.

Added proof-only imports of `Sheaf.AlgebraicGeometry.Modules.IsKFlatRestriction`,
`WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal`,
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`, and
`WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap`. Public imports and all
existing declarations' interfaces are unchanged. Updated the item's DAG proof and
proof dependencies to this direct argument. No other existing module is adapted.

Validation: the final single-file compilation is clean (no errors or warnings).
The proof treats arbitrary unbounded complexes and arbitrary test sheaves. Empty opens
and zero rings require no case split: the comparisons are functorial for all open
immersions and isomorphisms.

## Proved and sorry left

Closed the sole original hole in
`AlgebraicGeometry.Scheme.affine_sheafification_tensor_vanishing_test`
(node `lem-pc-affine-sheafification-tensor-vanishing-test`).

No `sorry` remains in the item, and no new holes or modules are added. The private
helper `restriction_totalTensor_iso` is proved in full. This is a proof from existing
library declarations, not a decomposition into new postponed statements.

## No longer needed

The direct argument does not use the following original planned proof dependencies:

- `lem-pc-derived-tensor-open-restriction-universes`, module
  `Sheaf.AlgebraicGeometry.DerivedTensorOpenRestrictionUniverses`;
- `lem-pc-open-restriction-kflat-model`, module
  `Sheaf.AlgebraicGeometry.OpenRestrictionKFlatModel`;
- `lem-pc-open-restriction-total-tensor`, module
  `Sheaf.AlgebraicGeometry.OpenRestrictionTotalTensor`;
- `lem-pc-affine-localized-site-derived-transport`, module
  `Sheaf.AlgebraicGeometry.AffineLocalizedSiteDerivedTransport`.

None of these modules was imported by the original item, and none is added. The DAG
edges to them are removed. This is pruning of this proof's dependency edges; it does
not assert that other target branches stop reaching those modules. Both original
public imports remain necessary for the theorem's statement. Temporary redundant
proof imports of `Sheaf.Algebra.Homology.KFlat` and
`Mathlib.Algebra.Homology.ShortComplex.ExactFunctor` were removed after checking that
the retained imports provide their declarations and instances.

## Where the brief, the DAG or earlier work was wrong

The original module had no imports of its planned proof-only dependencies. No
mathematical statement was changed or disputed. The existential equivalence provided
by `affine_localized_site_derived_transport` gives its comparison with tilde but does
not name a comparison with the specific restriction functor used on the K-flat model.
Constructing the inverse affine transport explicitly avoids needing that additional
interface and follows the same exact-restriction argument.

Care is needed with the two category presentations: `X.Modules` has a separately named
category instance from `SheafOfModules (moduleRings X.toRingedSpace)`. The derived
transport functors are explicitly typed on the latter shared carriers; additivity and
exactness instances are transported by `change` from the ordinary restriction functor.
This preserves the given localizations and avoids selecting a second derived category.

The generic tools `lem-pc-kflat-open-restriction`,
`lem-pc-scheme-pullback-monoidal-existing`, and
`lem-weil-pbc-module-restriction-open-immersion-limits` are used as tools. They preserve
the unit's route; no unit statement or realized step is bypassed. The item's unit
`sk-thm-picard-duality` has no realized node for this auxiliary transport statement.

Searches: LeanFinder for open-immersion derived tensor vanishing returned only ordinary
restriction and composition lemmas; Loogle found the exact counit comparison
`Modules.restrictFunctorAdjCounitIso`. Repository and Mathlib `rg` searches found the
existing K-flat restriction, pullback monoidal, restriction limit, and totalization
comparisons used here, but no theorem already combining this specific affine test.

The earlier dry runs used a fetched baseline missing the assigned module and node.
On retry, the baseline includes both. Preflight then identified the added file-level
open, options, and local-instance attributes as an interface change. The proof now
keeps the original file-level commands, scopes its elaboration options to each theorem,
and uses namespace-qualified names in the main proof. The additional local-instance
attributes were removed. The static interface comparison is empty; no change record
or false new-node attribution is needed.

## Second reading by T2

1. **Interfaces — pass.** Compared the sole delivered Lean module against the
   repository with `diff`. The existing public theorem signature is byte for byte
   identical, including all three derived-localization assumptions and the independent
   spectrum universe `wX`. Its original docstring, public imports, namespace, and
   file-level commands are unchanged. No definitions or other existing modules change;
   no change record is required.
2. **Proof and axioms — pass.** Independently compiled the delivered file with
   `lcompile.py`: exit 0, no warnings, 33.8 seconds. Compiled a scratch copy with
   `#print axioms` for both `restriction_totalTensor_iso` and
   `affine_sheafification_tensor_vanishing_test`: each uses only `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Scanned the module for
   forbidden declarations and kernel-bypass mechanisms; none occur. There are no
   local holes or hollow definitions. All complexes, functors, and comparison maps
   are constructed explicitly; the K-flat complex is the witness supplied by the
   hypothesis, not a new arbitrary object chosen from a postponed existence theorem.
3. **Split statements and edge cases — pass.** No statements are split off and no
   public helpers or nodes are added. Read the fully proved private helper: inverse
   tensorator naturality gives both bicomplex differential squares; preservation of
   coproducts permits totalization for arbitrary unbounded complexes. Read the main
   proof from its conclusion backwards: its K-flat witness has the required derived
   representing isomorphism and zero tensor homology. Empty opens, zero rings, zero
   complexes, and arbitrary test sheaves introduce no omitted hypothesis. The
   open-immersion counit applies to all module sheaves, not just quasi-coherent ones.
4. **Shortest route, imports, and pruning — pass.** Searched independently with
   Loogle query `"mapBifunctor", "Iso"`, Mathlib grep query
   `mapTotalIso|Monoidal.*map.*[Cc]omplex|mapBifunctor.*[Ii]so`, and repository searches
   for tensor restriction and bifunctor comparisons. Found graded-object and
   totalization tools, but no direct replacement for this affine vanishing theorem.
   Read `openRestriction_totalTensor_iso`; it concerns the over-site composite for
   a literal open inclusion, whereas this helper handles the actual composite open
   immersion from the spectrum. Retaining the direct argument is justified.
   Tested deleting each of the four added proof-only imports in separate scratch
   copies: all four deletions fail, respectively at `isKFlat_restrict`,
   `pullbackMonoidal`, finite-limit preservation for restriction, and `mapTotalIso`.
   The two public imports supply the existing signature. Compared old and new
   `proof_deps`: all four removed edges are listed under `No longer needed`; no
   removed physical import or globally pruned module is claimed. Read
   `dag/units/sk-thm-picard-duality.json`: its `realized.statement` and sole
   `realized.steps` entry are empty, so this auxiliary node is not a fixed realized
   step. The generic monoidal, restriction, and K-flat results remain tools.
5. **DAG agreement — pass after repair.** Read the node and each of its six new
   proof dependencies, including their recorded Lean declarations. The three proof
   steps accurately describe K-flat restriction, tensor/homology transport, and the
   explicit affine representing comparison used by the Lean proof. `proof_deps` is
   exactly the union of the steps' `uses`; `proof_origin` identifies this argument.
   Restored stale `reviewed` and `reviewed_proof` metadata from the repository;
   after repair the only changed node fields are `proof`, `proof_deps`, and
   `proof_origin`. No statement, statement dependencies, unit, or source changed.

Second reading changed only the stale node review metadata and appended this review.
The Lean proof required no repair. Closed 1 original hole, added 0 holes; the main
statement and private helper have no postponed dependencies according to their axiom
checks. Delivery validation is recorded by `deliver3.py`.
