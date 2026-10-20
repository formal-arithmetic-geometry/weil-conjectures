# WeilConjectures.integralOperationsWellDefined

## Reason

The completed proof adds private lemmas, proof sections and local elaboration commands.
The static interface checker records commands such as `open`, `variable`, `section`
and local `attribute` changes even when they export no new mathematical interface.
This record documents that command change and the three new fully proved public
coefficient results. Every original declaration, including all instances and
construction bodies, retains its exact interface and defining module. All ten
public imports are unchanged. There is no definition or statement repair.

Local irreducibility avoids expanding coefficient and product constructions while
elaborating proofs. The attributes are file-local (with product opacity further scoped to proof
sections) and do not change reducibility for importers. Proof-only imports supply the actual declarations
needed by this route; their additions and removals are listed in report.md.

## Old

The original nondeclaration commands, as read by the interface checker, are:

```lean
@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 512
universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.isDefEq.respectTransparency false
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
```

The three independent-coefficient modules did not exist. The main theorem had
its present statement and an unproved proof. Original public definitions and
instances are reproduced unchanged, rather than extracted into a new module.

## New

The added commands open private proof sections and install local irreducibility
for coefficient and product constructions. The independent coefficient helpers
use `backward.isDefEq.respectTransparency.types true` so Lean respects these
boundaries when comparing types. This keeps sheafification from expanding while
checking naturality. No command exports a new global instance or attribute.

The good-complex localization is proved privately for a generic ringed site and
then specialized. A private tensor-total instance lemma reuses the existence of
the required totals. Private abstract lemmas turn preservation of quasi-isomorphisms into
preservation of acyclicity and apply this to the core K-flat predicate. Local
opacity of constant sheaves, monoidal structures and operation functors avoids
repeated large definitional comparisons; explicit functor equations identify the final Roos values. Local caches share
flat-subcategory coproduct and complex tensor instances. Explicit categories and
tower families in the derived-limit transport avoid expensive inference through
the coefficient limit. Within the private proof part, a local priority of 3000
for the existing `integralTowerHasDerivedCategory` instance avoids repeatedly
matching the commutative-ring presentation against completed modules. This
priority is not exported.

The Roos quasi-isomorphism argument is first proved privately for an arbitrary
abelian category with exact countable products. Its specialization supplies the
same statement used by the operation proofs. The finite tensor proof uses the acyclic mapping-cone characterization of
quasi-isomorphisms. K-flatness kills the tensor of the cone; signed flip and
braiding handle the second variable. The two tensor maps compose to the desired
map. These generic private proofs are adapted from the existing site tensor
module. They replace the former derived-category comparison entirely and avoid
its missing-instance failure.

The proof of the existing `integralOperationsDerivedCountableProducts` uses
`derivedCategory_countableProducts_core` in place of the stronger general
`derivedCategory_countableProducts_and_towerLimit` theorem. Its statement is
unchanged and the discarded tower-limit conclusion was never needed.

The added coefficient theorem signatures are recorded verbatim in the lean records
of `lem-pur-change-of-rings-tensor-cancellation-independent`,
`lem-pur-kflat-change-of-rings-independent`, and
`lem-pur-coefficient-pullback-exact`. All three are fully proved. No original
signature or definition changes. A textual comparison with the current source
confirms the unchanged ten public imports, original construction bodies and
instances, and final theorem statement. The only other original proof changed
is the countable-products theorem described above.
This packet restores G1's rolled-back proof from the repair note. R9 replaces
the finite derived-category comparison by the direct K-flat cone argument,
removing the source of the three instance failures reported by the global build. Compilation evidence for
this restored packet is recorded in report.md.

## Users

The current direct-source importers are listed below. Every existing signature,
public import, construction body and public instance is preserved. The change is
proof code, proof-only imports and local elaboration commands. No downstream
adaptation is required and no module held by another group is edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.MilnorTower | unclaimed | Existing interface preserved. |
| Sheaf.AlgebraicGeometry.ProEtaleMilnorSequence | unclaimed | Existing interface preserved. |
| Sheaf.Paper.IntegralDerivedOperations | unclaimed | Existing interface preserved. |
| Sheaf.Paper.IntegralLineTensorComparison | unclaimed | Existing interface preserved. |
| Sheaf.Paper.IntegralScalarExtensionWellDefined | unclaimed | Existing interface preserved. |
| Sheaf.Paper.RationalSliceCompletedEvaluation | unclaimed | Existing interface preserved. |
| Sheaf.SixFunctors.CompletedTensorShiftRight | unclaimed | Existing interface preserved. |

## Status

landed 20261020T211821-L-3505934 2026-10-20 (merge of deliver/R9/Sheaf.Paper.IntegralOperationsWellDefined)
