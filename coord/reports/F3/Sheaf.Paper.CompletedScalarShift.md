## What changed

Implemented the signed mapping-cocone shift and its product comparison, proved the
strict completed-scalar chain equation using the native Roos coordinate API, and constructed
normalized descent through the retained localization comparison. Cancelling that comparison
on good representatives gives the derived comparison square. Naturality and a flat-term
K-flat resolution transport it to every derived object. The homotopy-counit helper
is generic over abelian categories and their derived models, which avoids expanding
the completed coefficient construction during the categorical proof. Native tower
evaluation and adjacent transitions are generic over the underlying category;
the additive assumptions enter the Roos construction itself. The chain helper
constructs the fixed canonical product comparison directly, eliminating an unused
arbitrary-comparison parameter and its equality hypothesis. Its actual product
isomorphism has a named definition, and the assigned proof rewrites its definitional
equality with the original completedScalarShiftProductIso explicitly.

The coefficient category abbreviation in IntegralReductionTowerUnrestricted now uses
the forgetful presentation of the same completed commutative-ring sheaf as the
change-of-rings witness. The original presentation retains its standard localization
instance. The definition repair and its consumers are recorded in
coord/changes/F3-integral-tower-coefficient-presentation.md.

## Proved and sorry left

Closed: WeilConjectures.completedScalarComparison_commutesWithShift (one assigned hole).
Added holes: none. No definition contains sorry. All five new helper modules are
fully proved: completedScalarChainShift, completedScalarShiftDescent,
ProductShift.productCommShift, SignedCoconeShift.coconeCommShift, and
RoosShift.commShift, together with their coordinate and coherence APIs.

The forced-adaptation module retains its two pre-existing holes, unchanged:
WeilConjectures.integralScalarTransition_existsUnique and
WeilConjectures.integralScalarExtensionWellDefined. They supply stated dependencies
of this item; their proofs are not part of this delivery.

All eight delivered modules have passed compilation against the standard instances.
The final generic tower-evaluation API and the unchanged chain proof pass together
in scratchpad/chain-generic-level-api.log (5.2 s and 41.2 s respectively).
The final fixed-comparison interface passes in scratchpad/chain-fixed-product.log
(chain 39.2 s). The assigned proof with an explicit product-equality rewrite passes
in scratchpad/chain-fixed-functor-definition.log (41.3 s); the slower functor-definition
experiment is excluded, and the original private abbreviation is retained. Nineteen of the
21 unchanged textual-consumer copies also compile. The last isolated check of
IntegralOperationsScalarComparisons passes at 43.8 s (scratchpad/scalar-comparisons-isolated.log),
and PointSectionsTensorShift passes at 18.3 s (scratchpad/point-tensor-standard.log).
No additional adaptation was needed. All unchanged test copies were removed before delivery.

The unchanged CompletedTensorShiftRight and IntegralOperationsPreserveConstructible
consumers exceed 60 s both with the repaired definition and in isolated compiles
against the published baseline (scratchpad/shift-right-baseline.log and
scratchpad/preserve-baseline.log). These are pre-existing baseline failures; neither
file is adapted in this packet. The finite tensor-shift consumer passed at 56.2 s;
a repeated batch reached 60 s. The successful runs and that timing variation are
retained in scratchpad/all-standard-consumers.log, remaining-standard-consumers.log,
and unverified-standard-consumers.log.

## No longer needed

Removed proof imports from the item: DerivedChangeOfRingsCochainModel, KFlat,
SiteDerivedTensorDescentIndependentCoefficients, IntegralScalarExtensionUniverses,
IntegralScalarExtensionWellDefined, and KFlatIndependentCoefficients. The corresponding
interfaces needed by this argument are already provided transitively, or the argument
uses the retained localization comparison directly. This removes import edges only;
no adopted-source declaration or whole module is withdrawn.

The direct tensor-complex sign calculation from def-pc-tensor-complex-sheaves is
replaced by Mathlib's mapBifunctorShift₂Iso. The abstract derived-category shift
convention is supplied by Mathlib's existing shift interface. Their statement
dependencies remain as recorded. The site-derived tensor descent dependency remains
needed inside CompletedScalarShiftDescent; removing its direct import from this item
does not prune that module or its node. The well-definedness node also remains needed
by CompletedScalarChainShift for transition uniqueness. The removed
def-weil-abstract-derived-category proof edge is covered by the existing Mathlib shift
interface; it remains a statement dependency. These are changes of direct proof edges,
not withdrawals of any of those four nodes.

## Where the brief, the DAG or earlier work was wrong

The first preflight found metadata omissions: LeanFinder and Loogle are one search
kind, so each new node now also records an actual LeanSearch query. The three
CommShift definition signatures now use the declaration parser's form without the
noncomputable modifier. The change-record Users table now explicitly includes the
new chain and descent helpers. That metadata correction did not change Lean source. A subsequent compile-limit
failure was repaired by making the private homotopy-counit helper generic over
abelian categories and proving its final identity composition explicitly. The final
assigned module compiles without development options in 32.8 s
(scratchpad/main-final-generic.log). Its public definitions and statement remain verbatim. The chain helper
subsequently exceeded the limit in delivery; generalizing native tower evaluation
and adjacent transitions to arbitrary target categories removes unnecessary
abelian-instance conversions and gives a 41.2 s clean chain compile. The final
helper removes the unused general product-comparison argument and passes in 39.2 s;
the corresponding main proof uses an explicit equality of the two canonical
product constructions. All seven original definitions and the assigned theorem
statement match the current source exactly under the declaration parser.

The universal change-of-rings witness uses the forgotten commutative-ring presentation
of completed coefficients, while integralTowerModules originally used the recorded
ring-limit presentation. They are definitionally equal, but repeated conversion of
their module and derived-category structures made elaboration expand the coefficient
construction. The generic native Roos API packages its two coordinate equations as
ConeFormula; the concrete theorem uses that unchanged property instead of repeatedly
expanding the signed cocone at coefficient categories. The definition repair aligns the
coefficient presentations without changing their mathematical meaning. Target signatures
and the item's existing definitions remain verbatim.

The cone sign is proved on mapping-cocone inclusions. The generic cone shift alone
has the wrong common scalar; multiplying by (-1)^m gives coefficient one on the first
inclusion and (-1)^m on the second.

## New nodes

- lem-weil-product-comm-shift: degreewise product shifts and coherence, fully proved.
- lem-weil-signed-mapping-cocone-shift: signed cocone shifts and coherence, fully proved.
- lem-weil-roos-comm-shift: the native strict Roos functor shift and coordinate API, fully proved.
- lem-weil-completed-scalar-chain-shift: the actual strict chain comparison, fully proved.
- lem-weil-completed-scalar-shift-descent: normalized descent on good complexes, fully proved.

Definition repair: coord/changes/F3-integral-tower-coefficient-presentation.md.

## Forced adaptations

Sheaf.Paper.IntegralScalarExtensionWellDefined is currently held by U2 (formerly W5).
Only the proof of integralScalarChainAction_existsUnique changes. Against the repaired abbreviation,
the original local CommRing annotation caused failure to synthesize SMulCommClass
between the completed-ring carrier and the forgetful-presentation carrier. Its original
naturality rw also failed to find the canonical-ring restriction map in a target
containing the forgetful presentation. The local CommRing and scalar annotations now
use the coefficient presentation of the module, and that rw is erw. The original
signature, visibility, scalar function, and every other declaration are unchanged.
The original errors are `failed to synthesize SMulCommClass` between those two ring
presentations, and `Tactic rewrite failed: Did not find an occurrence` of the
canonical-ring restriction applied to integralScalarConstant. The changed proof lines
are its local CommRing annotation, the explicitly typed scalar c, and rw changed to erw.
The adapted module compiles; the original compiler diagnostics are retained in
scratchpad/FinalOriginalW5.log and the successful adapted standard-instance compile
in scratchpad/standard-abelian-proof.log. The clean standard-instance rebuild of all
proof dependencies and the assigned theorem succeeds in scratchpad/clean-standard-proof.log
(chain lemma 46.7 s; earlier assigned proof 43.9 s). The final private-helper
optimization passes in 32.8 s in scratchpad/main-final-generic.log.

## Forced adaptations

### Sheaf.Paper.IntegralScalarExtensionWellDefined
Original against changed dependencies failed:
```
st✝¹ : Algebra ℚ_[l] E
inst✝ : FiniteDimensional ℚ_[l] E
Y : AlgebraicGeometry.Scheme
a : ↥(Padic.coefficientExtensionIntegers l E)
M : integralTowerModules l E Y
U V : Y.ProEtᵒᵖ
f : U ⟶ V
x : ↑(M.val.obj U)
⊢ integralScalarConstant l E Y V a • (ConcreteCategory.hom (M.val.map f)) x =
    (ConcreteCategory.hom
          ((SheafOfModules.derivedChangeRingIndependentCoefficients (AlgebraicGeometry.Scheme.ProEt.topology Y)
                  (completedIntegralCommRingSheafUnrestricted l E Y)).obj.map
            f))
        (integralScalarConstant l E Y U a) •
      (ConcreteCategory.hom (M.val.map f)) x

Note: The target expression is not type-correct under the `implicit` transparency level, which may have triggered the failure. This is usually caused by unfolding of semireducible definitions in prior tactic steps. Use `set_option linter.tacticCheckInstances true` to investigate the source of the issue.
Full error:
  Application type mismatch: The argument
    RingCat.instRingObjForgetRingHomCarrier
  has type
    Ring
      ((forget RingCat).obj
        ((SheafOfModules.derivedChangeRingIndependentCoefficients (AlgebraicGeometry.Scheme.ProEt.topology Y)
                (completedIntegralCommRingSheafUnrestricted l E Y)).obj.obj
          V))
  but is expected to have type
    Ring ↑((completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj V)
  in the application
    @ModuleCat.instModuleCarrierObjRestrictScalars
      (↑((SheafOfModules.derivedChangeRingIndependentCoefficients (AlgebraicGeometry.Scheme.ProEt.topology Y)
                (completedIntegralCommRingSheafUnrestricted l E Y)).obj.obj
          U))
      (↑((completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj V)) RingCat.instRingObjForgetRingHomCarrier
      RingCat.instRingObjForgetRingHomCarrier
  
  Note: The following definitions were not unfolded because their definition is not exposed:
    getLimitCone ↦ 13

(with the modules compiled into /tmp/forced-adaptation-_58u8aax/.lbuild) [16.2 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
