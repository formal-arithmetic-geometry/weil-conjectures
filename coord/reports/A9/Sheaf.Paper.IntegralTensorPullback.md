## What changed

Filled six existing helper proofs in `Sheaf.Paper.IntegralTensorPullback`.
All existing declaration signatures, attributes, definitions and public imports stay
unchanged relative to the current shared source, including the derived-monoidal
public import added during this session. Three proved private helpers establish compatibility of quotient units,
their inverse images, and their termwise tensor products.

The strict Roos augmentation condition follows by product projections and naturality
of the tower augmentation. The constant coefficient commutativity and monoid-map
proofs reuse the existing proved lemmas in
`Sheaf.Paper.FiniteConstantModelResolution`; the definitions of the two constant
coefficient constructions coincide. Both tower unit compatibility proofs reduce
to the consecutive quotient-unit identity. Linearity of the constant unit is the
multiplication identity of the coefficient monoid morphism.

The only added private proof import is
`Sheaf.Paper.FiniteConstantModelResolution`. No public API or definition repair
is part of this delivery.

## Proved and sorry left

Closed six of the original eight holes, all in namespace
`AlgebraicGeometry.ProEtale.IntegralTensorPullback`:

- `augmentation_condition`
- `constantRing_isCommMonObj`
- `constantToIntegral_isMonHom`
- `towerUnit_compatible`
- `constantUnit_linear`
- `constantTowerUnit_compatible`

Two original holes remain unchanged, both under node
`det-lem-int-tensor-pullback`:

- `AlgebraicGeometry.ProEtale.IntegralTensorPullback.restrictionPullback_existsUnique`
- `AlgebraicGeometry.ProEtale.IntegralTensorPullback.preserves_and_completed`

Their existing sources and full proofs in words remain in their docstrings.
No holes were added or split off. This is a partial delivery of six helper proofs,
not a proof of the main preservation/completion theorem.

## No longer needed

Removed unused private proof imports:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`
- `WeilConjectures.ConstructibleSheaf.Pullback`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.Paper.CondensedOpenClosedRecollement`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.Paper.IntegralTensorShriek`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.PbcQbarCompletedPullback`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Paper.IntegralConstructibleHeart`

Kept by the reviewer (2026-10-25), though the present partial proof does not use them:
`Sheaf.Paper.CartesianCoefficients`, `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`
and `Sheaf.Paper.IntegralModels` carry the realized statements of units
(sk-prop-sfb-cartesian-coefficients, sk-prop-sfb-qlbar-colimit-x, sk-lem-integral-models) on the
route of the still-open `preserves_and_completed`. Under brief-stage3 §1 their modules stay imported.

No DAG node or module is withdrawn: the open main theorem still needs its planned
proof dependencies. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing scalar coefficient helpers in `FiniteConstantModelResolution` already
prove exactly the commutativity and multiplicativity identities required here.
The current helper proofs need no separate sheafification argument.

For the unfinished main theorem, the declared strict normalization interface
`Sheaf.Paper.IntegralPullbackStrictRoosNormalization` is formulated using
`SheafOfModules` over completed and constant sheaves of commutative rings, whereas
this module uses internal module objects over pulled-back condensed rings.
A transport of the quotient towers, their units and the Roos comparisons between
these presentations remains to be written before that interface can be applied.
Moreover, its `GoodR` representative includes termwise flatness, whereas this
module quantifies over every K-flat representative. Passing from the former to
the latter needs representative independence. These are remaining proof tasks;
this delivery changes neither interface nor the main theorem's hypotheses.

The attempted scalar-comparison proof established normalization using
`CondensedRing.comapUpperStarIso` and the proved forgetful normalization from
`IntegralResiduePullOrdinaryUnit`. Its uniqueness calculation still incurred
expensive definitional comparisons of module-object wrappers; the final attempt
exceeded the fixed 60-second limit. That attempted proof and its imports are not
included. The original named theorem and hole are preserved for subsequent work.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
