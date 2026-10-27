## What changed

Replaced the sole sorry in
`WeilConjectures.ExceptionalIntegralReconstruction.exceptionalIntegralReconstruction`
by a complete assembly: prove the universal actual reconstruction restriction, choose
its source and target witnesses, construct the exceptional systems in the prescribed
lifted coordinates, restrict the system adjunction, choose compatible realization
transport shifts, and package the unchanged conclusion.

`ExceptionalIntegralReconstructionInterfaces` owns all previous data declarations,
verbatim, with the same public imports; it also adds the proved field-copying
`SystemAdjunction.withTransport` construction. The assigned module publicly reexports it.
`ExceptionalIntegralReconstructionEquivalence` proves restriction of the actual
reduction/limit adjunction, preserving precisely the common cohomological and Tor
intervals and the actual unit/counit equations. It retains the calculus coherence,
sequence resolutions and reduction/limit shifts from existing declarations.
`ExceptionalIntegralSystemExistence` repeats the proved generic system-transport
construction for the exact lifted valuation ring used by this theorem; it retains
the existing ordinary adjoint, site comparisons, evaluations and quotient mates.
No arbitrary object is defined by choosing a witness of a new admitted existence
statement.

The two remaining subarguments are each in a separate module with its source and
complete natural-language proof. Their declarations are strictly parts of the
argument: normalized stability/adjunction, and geometric integral realization of
already supplied reconstruction and adjunction data. The latter chooses a replacement
transport record on the same ordinary adjoint, sites and proper/open comparison,
because arbitrary transport shift fields are not asserted to be cochain-normalized.
The restricted adjunction fields do not use those shift fields;
`SystemAdjunction.withTransport` explicitly copies them to the updated record parameter.

The original theorem signature and all old declaration bodies except that proof are
unchanged. No source-library file, target, other existing module or other node changes.
Change record: `coord/changes/Z7-exceptional-integral-reconstruction-interfaces.md`.

Validation: lcompile.py compiled both construction lemmas cleanly (8.4 s for the
reconstruction equivalence and 17.6 s for fixed-coordinate system existence). The
interface and both residual theorem signatures also compiled. The final assembly
also compiled cleanly in the ordered set (52.4 s including server setup);
delivery preflight is recorded by deliver3.py. The extracted original declarations were checked byte-for-byte
against the original block; the only additional declaration copies the adjunction fields. Direct-importer search over both Lean
roots finds no current importers of the assigned module; its DAG users are retained.
Edge cases checked in the subarguments: zero input and empty schemes preserve the
[0,0] intervals; the identity word reduces to reconstruction/site triangle identities;
cochain signs cover zero and negative shifts. Absolute separatedness is never added.

## Proved and sorry left

Original module: one hole closed, in
`WeilConjectures.ExceptionalIntegralReconstruction.exceptionalIntegralReconstruction`.
This is a decomposition, not a dependency-free proof: two lower holes are added.
The original module now has zero sorry expressions. Net local hole change: 1 closed,
2 added. Existing admitted dependencies are used as intended by stage 3.

New proved declarations, with no local holes:

- `WeilConjectures.ExceptionalIntegralReconstruction.exceptionalIntegralReconstructionEquivalence`
  (`lem-sf-exceptional-integral-reconstruction-equivalence`).
- `WeilConjectures.ExceptionalIntegralReconstruction.exceptionalIntegralSystemExistence`
  (`lem-sf-exceptional-integral-system-existence`).

Every sorry left in this delivery:

- `WeilConjectures.ExceptionalIntegralReconstruction.exceptionalIntegralNormalizedAdjunction`
  (`lem-sf-exceptional-integral-normalized-adjunction`): normalized preservation,
  common bounds, origins and the specified restricted transpose.
- `WeilConjectures.ExceptionalIntegralReconstruction.exceptionalIntegralRealizationAssembly`
  (`lem-sf-exceptional-integral-realization-assembly`): coherent integral realization
  and primitive map normalization after choosing compatible transport shifts.

Each has exactly `:= by sorry`, in its own module and matching new DAG node. There
are no holes in definitions, instances or private helpers.

## No longer needed

No module is withdrawn. The original argument's geometric steps remain in the
two residual subarguments or the two proved construction lemmas. The old direct
citation `lem-weil-integral-ctf-triangulated` (module
`Sheaf.Paper.IntegralCtfTriangulated`) is not used here: it concerns the legacy
`integralCtfProperty`. The unchanged interface instead uses the already proved
modern finite-Tor helper, owned by `lem-pur-integral-ctf-shift-closure`, for the
actual predicate of this statement. This is a local citation replacement; no
claim is made that the legacy module is globally unused.
The original direct proof-dependency list is replaced by the four actual assembly
lemmas; their own nodes record the corresponding underlying declarations. No module
is withdrawn, and no old dependency is claimed globally unnecessary.

The following direct public imports are now supplied transitively by the unchanged
public imports of the extracted interface:

- `Sheaf.Paper.FiniteFieldFiber`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`.
- `WeilConjectures.Compactification.RefinementCategory`.
- `Sheaf.Paper.SfIntegralConstructible`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`.
- `Sheaf.Paper.QcqsCompactSupportRealization`.
- `Sheaf.SixFunctors.IntegralSystemOperations`.
- `Sheaf.SixFunctors.IntegralSystemExpressionDomain`.
- `Sheaf.SixFunctors.IntegralSystemCanonicalBridge`.
- `Sheaf.Paper.ExceptionalSystemInterfaces`.
- `Sheaf.Paper.StrictEtaleSystemInterfaces`.
- `Sheaf.Paper.StrictEtaleExceptionalAdjointInterfaces`.
- `Sheaf.Paper.ExceptionalProEtaleRealization`.
- `Sheaf.Paper.ExceptionalDerivedSiteRealization`.
- `Sheaf.Paper.ExceptionalFiniteSupportRealization`.
- `Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange`.
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`.
- `Sheaf.Paper.IntegralExceptionalInverseImage`.
- `Sheaf.Paper.SequenceAdjointShiftInterfaces`.
- `Sheaf.SixFunctors.IntegralOperationShiftData`.
- `Sheaf.Paper.PurReductionLimitShiftAdjunction`.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData`.

These are import consolidation only, not mathematical pruning. The assigned theorem
uses four private proof imports. The interface owns the existing API and no new
proof-dependent public import is introduced.

## Where the brief, the DAG or earlier work was wrong

The planned generic system-transport theorem takes a coefficient field in Type (u+1)
and its own valuation ring, while this theorem fixes ULift O_E for E in Type u. Its
existence result is therefore not directly the required Systems value. The delivery
uses its proved ring-parametric construction helpers with the prescribed lifted
ring, then repeats its origin-adjunction/evaluation argument. No existing statement
is changed or assumed at a mismatched universe.

The existing unrestricted reconstruction theorem suffices for the first step:
common intervals can be transferred across the actual counit rather than adding a
separate effectivity hypothesis or a compatible-origin witness to normalized.

An inductive SystemAdjunction retains its full Systems parameter even though its
fields do not use the transport shifts; a field-copying construction is necessary
to move to an updated record.

The shift fields of a supplied Systems.transport record do not themselves assert
cochain-model normalization. The residual realization theorem therefore chooses
compatible transport shifts on its same underlying data. It does not infer that
arbitrary exact shift structures equal the primitive realization shifts.

The current blueprint unit is unchanged. The source PDF was read at Lemma 5.22,
Proposition 5.24, Construction 5.25, Proposition 5.26, and the uniform-bound references
2.29 and 3.16. The new proof descriptions specialize those steps to schemes and the
existing recorded strict-system interfaces.

## New nodes

- `def-sf-exceptional-integral-reconstruction-interfaces`: exact former data block,
  moved to prevent an import cycle. The proof-step statements cite this interface; the parent retains its original
  statement and statement dependencies.
- `lem-sf-exceptional-integral-reconstruction-equivalence`: proved restriction of the
  actual reduction/limit adjunction to common finite-Tor bounds, with its maps and shifts.
- `lem-sf-exceptional-integral-system-existence`: proved generic system construction
  in the precise lifted coefficient coordinates and at the given compactification.
- `lem-sf-exceptional-integral-normalized-adjunction`: residual normalized restriction,
  step 2 of the original plan.
- `lem-sf-exceptional-integral-realization-assembly`: residual realization and primitive
  normalization, steps 3--9, with a compatible choice of transport shifts.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
