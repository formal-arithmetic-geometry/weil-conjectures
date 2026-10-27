## What changed

Restored the assigned archived module and replaced its one postponed theorem with a
complete Lean proof assembling three strictly smaller constituent theorems. The
orientation is explicitly the existing `finiteSmoothOmegaCoordinates`; the proof
substitutes the three factor equations and derives the precise adjunct equation
using Mathlib's `homEquiv_symm_rightAdjointUniq_hom_app`,
`rightAdjointUniq_inv_app`, functoriality and naturality. It preserves the original
theorem statement, including its separate factor equalities and every unbounded K.

Moved the original 16 constructions, with their signatures and bodies unchanged,
to `Sheaf.Paper.FiniteSmoothGammaConstructions` and publicly reexported that module
from the original owner. This permits lower constituent lemmas to import those
constructions without importing their conclusion. The original six public imports
are retained, so every existing consumer sees the same API and instances. No
existing consumer requires adaptation. The corresponding ownership node follows
the existing definitions; a second definition node records the remaining factors.

The change record is `coord/changes/R3-finite-smooth-gamma-constructions.md`.

Validation: `lcompile.py --all` accepted all five delivery modules with exit code 0 and no diagnostics. A byte comparison verifies the unchanged theorem signature and all 16 construction declarations. The unchanged direct consumer `Sheaf.Paper.FiniteSmoothPurityMaps` also compiled against the changed owner module with exit code 0 and no diagnostics; its temporary sandbox copy was deleted afterward. The server used its normal private overlay for unpublished dependency repairs. The overlaid DAG has every direct reference needed by the new records and no dependency path back to any changed node. An unrestricted traversal also encountered pre-existing upstream cycles and the missing record `def-weil-pbc-ideal-module-product-stalk`; those are outside this delivery and were not altered.

## Proved and sorry left

The input had one direct hole, in
`AlgebraicGeometry.Etale.finite_smooth_gamma_normalization`
(`lem-pur-finite-smooth-gamma-normalization`). That hole is closed by a complete
assembling proof, but this is a decomposition, not a net proof: 1 hole closed,
3 holes added, net -2. There are zero direct holes in the item module and zero in
the relocated construction module. The final sum-counit equation is proved from
adjoint uniqueness rather than split off.

The three remaining holes are the entire proofs of these public theorems, each
in its own module with a complete source-based proof in words:

- `AlgebraicGeometry.Etale.finiteSmoothDiagonal_coordinates`, node
  `lem-pur-finite-smooth-diagonal-coordinates`, in
  `Sheaf.Paper.FiniteSmoothDiagonalNormalization`: only the exceptional diagonal
  factor's coordinate equation (original Steps 1 and 3).
- `AlgebraicGeometry.Etale.finiteSmoothDeformation_coordinates`, node
  `lem-pur-finite-smooth-deformation-coordinates`, in
  `Sheaf.Paper.FiniteSmoothDeformationNormalization`: actual rank-zero Rees data,
  specialization coordinates and identity-trace coordinates (Steps 2 and 4--7).
  It asserts neither the diagonal equation nor any tensor-map conclusion.
- `AlgebraicGeometry.Etale.finiteSmoothTensor_coordinates`, node
  `lem-pur-finite-smooth-tensor-coordinates`, in
  `Sheaf.Paper.FiniteSmoothTensorNormalization`: only the canonical tensor mate at
  the already specified sum-adjunction unit orientation (Steps 8--9). It has no
  Rees datum or geometric orientation existence conclusion.

These are independent constituent obligations, not a repackaging of the input.
The public constructions contain no `sorry` and no newly chosen data.
The main proof takes the geometric witness only in a theorem proof.

Edge cases were checked against the formulas: empty X gives the unique maps in
the zero sheaf category; identity and open-immersion maps have an empty
complement or a clopen diagonal component; a finite fold map has one normal
component per sheet and the actual evaluation counit. K=0 and arbitrary unbounded
K are included. The coefficient unit lies in degree zero, so the symmetry used
in the tensor transpose contributes no sign. No nonempty-source or positive
relative-dimension assumption was introduced.

## No longer needed

No existing module or declaration is withdrawn. No global pruning is claimed:
other targets may still use every dependency independently. The main assembling
proof now directly uses only the three new constituent lemmas and the categorical
adjoint-uniqueness API. Its old mathematical dependencies are retained as proof
dependencies of the appropriate constituent nodes, rather than imported merely
because they appear in the former plan.

The following unused private proof imports were removed from the original module
(and are not needed by the unchanged construction block):

- `Sheaf.AlgebraicGeometry.DiagonalRegularPureCodimension`
- `Sheaf.AlgebraicGeometry.EtaleSumFlatKFlat`
- `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry`
- `Sheaf.AlgebraicGeometry.ShriekTensorComposition`
- `WeilConjectures.Compactification.NagataCompactification`
- `Mathlib.CategoryTheory.Adjunction.Unique`
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`
- `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact`
- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`
- `WeilConjectures.SixFunctors.BaseChange.Etale`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`

In particular, `lem-pur-diagonal-regular-immersion` is not used: its positive
codimension interface does not prove the rank-zero assertion. The new deformation
node uses the direct clopen diagonal computation and its empty regular sequence.
The general vector-bundle purity theorem is also unnecessary for this rank-zero
factor: the published definition already transports the identity-adjunction trace.
The public imports of `VectorBundleIntegration` and `VectorBundlePurity` are
preserved at the original module for consumer compatibility; the relocated
constructions use their explicit identity-adjunction trace formula and do not
need those two imports themselves.

The old top-level tool-use approvals are removed from the assembling theorem's
node because its new direct proof dependencies are the three constituent nodes.
Their mathematical uses, where still needed, remain in the constituent proofs.
The removed approval entries are:

- `def-amb-vector-integration`
- `def-sbc-smooth-morphisms`
- `def-weil-pbc-etale-shriek-base-change-map`
- `def-weil-pbc-etale-sum-extension`
- `lem-amb-etale-adjoint-locality`
- `lem-kun-tensor-sym`
- `lem-pod-separated-finite-type-base-change`
- `lem-pur-diagonal-regular-immersion`
- `lem-pur-etale-sum-flat-kflat`
- `lem-pur-etale-support-map-compatibility`
- `lem-sfb-quasifinite-compact-support-exact`
- `lem-weil-pbc-etale-base-change-finite-limits`
- `lem-weil-pbc-etale-composition-cancellation`
- `lem-weil-pbc-etale-section-clopen-immersion`
- `lem-weil-pbc-etale-underived-exchange-restriction`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-locally-noetherian-quasi-separated`
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`
- `prop-asd-smooth-base-change`
- `thm-amb-etale-exceptional-adjoint`
- `thm-amb-vector-bundle-purity`
- `thm-asd-smooth-tensor`
- `thm-nagata-compactification`
- `lem-amb-shriek-tensor-composition`

Existing cross-unit tools cited by the new constituent nodes are the original
support-comparison, sum-flatness and tensor-symmetry tools. They are used for the
same local calculations as the accepted parent proof plan. No unit statement or
realized unit step is bypassed or changed.

## Where the brief, the DAG or earlier work was wrong

The rework row says the item was quarantined for an import of
`Sheaf.AlgebraicGeometry.SfP1ProjectionTraceFalseTail`. At inspection time the
archived and restored current item source were identical and neither directly
imported that module. The reason is transitive: one source path runs through
`VectorBundlePurity`, `VectorIntegrationMate`, ordinary smooth duality and the
projective-line trace transport modules to `SfP1ProjectionTraceFalseTail`. The
server compile accepts the restored item and its lower construction
module. This delivery preserves all archived constructions and its theorem,
rather than interpreting quarantine as withdrawal. The substantive change is the
compiled decomposition of the theorem, not a no-op restoration.

The old Step 2 cited a positive-codimension regular-immersion theorem at dimension
zero. The existing stage-2 review already warned about this. The new constituent
plan uses the clopen section and empty regular sequence directly. The rest of the
three-factor route is preserved. Mathlib searches found the categorical counit
API but no theorem giving these specified geometric or tensor normalization
maps directly. The existing declared dependencies provide the ingredients, but
not the missing constituent coordinate equations as ready-to-apply statements.

## New nodes

`def-pur-finite-smooth-gamma-constructions` records the unchanged Rees-data,
normal-coordinate, rank-zero-trace and tensor-map definitions in the lower
construction module. The existing coordinate-owner node is updated only in its
Lean attachment. No definition meaning changes.

`lem-pur-finite-smooth-diagonal-coordinates` isolates the exceptional diagonal
coordinate calculation from Steps 1 and 3.

`lem-pur-finite-smooth-deformation-coordinates` isolates the actual clopen Rees
geometry and its normalized specialization and rank-zero integration calculation.

`lem-pur-finite-smooth-tensor-coordinates` isolates the unbounded sum-projection
and evaluation calculation at the fixed unit orientation.

All new nodes have the original chapter and unit, source-based proof steps,
actual Mathlib searches, and Lean attachments. The blueprint ancestor query
reports `None`; searches for rank-zero deformation, etale tensor counit and
diagonal adjunction coordinates found no existing blueprint nodes stating these
constituent normalization equations. No new tool approvals are invented.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
