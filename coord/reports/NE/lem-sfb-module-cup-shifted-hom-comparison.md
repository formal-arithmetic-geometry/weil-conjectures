## Worker report

Delivered `lean/Sheaf/AlgebraicGeometry/ModuleCupShiftedHomComparison.lean`, module
`Sheaf.AlgebraicGeometry.ModuleCupShiftedHomComparison`. It fully defines the proposition
`AlgebraicGeometry.SchemeModuleCupShiftedHomComparison` and states
`AlgebraicGeometry.scheme_module_cup_shifted_hom_comparison` with `sorry`. This is the
only postponed theorem. The proposition constructs no unspecified mathematical data:
it asserts existence of the family of additive equivalences together with its complete
resolution normalization and the other required identities.

Source read: `literature/stacks-project/cohomology.tex`, section-cup-product, the
Hom(O,-)=Gamma paragraph preceding lemma-second-cup-equals-first, that lemma and its sign
footnote; the node's seven proof steps. These give the target-shift version of the usual
source-shift construction. The declaration docstring gives the complete resolution,
comparison, naturality, augmentation and tensorator proof plan.

Hypothesis and clause correspondence (names below refer to the body of the defined
proposition, so its installed instances do not escape into the theorem signature):

| Node clause | Lean rendering |
| --- | --- |
| Any scheme X | `X : Scheme.{u}`; no geometric property instance is assumed. |
| All O_X-module sheaves | `A := SheafOfModules.{u} (moduleRings X.toRingedSpace)`, and every F,G ranges over A. In particular the category instance is the shared SheafOfModules instance. |
| D(O_X), with K-flat tensor | The shared `HasDerivedCategory.{w}` binder, `schemeDerivedTensorMonoidal X`, and the exact auxiliary instances used by `SchemeSingleTensorAugmentationCoherence`; w is independent of u. |
| U=O_X, sF=F[0] | `U := SheafOfModules.unit ...`, `s := DerivedCategory.singleFunctor A 0`. |
| Right-derived global sections | `H := RingedSpace.moduleCohomology X.toRingedSpace`, `ΓX := RingedSpace.globalSectionsFunctor X.toRingedSpace`. No abelian-sheaf cohomology is substituted. |
| For every n>=0 an additive equivalence | `∃ e : ∀ (F : A) (n : ℕ), (H n).obj F ≃+ (s.obj U ⟶ (s.obj F)⟦(n : ℤ)⟧), ...`. |
| Canonical normalization in every injective resolution | The first conjunct universally quantifies F, `I : InjectiveResolution F`, n, a global cycle a, and a module cocycle map φ. Evaluation `φ.val.app (op ⊤) 1 = ...iCycles n a` implies that e of the canonical class is `(I.extMk φ (n+1) rfl hφ).hom`. The class is transported by `(I.isoRightDerivedObj ΓX n).inv`, not an existentially chosen comparison. Mathlib's `InjectiveResolution.extMk_hom` expands the right side into the localized cocycle map followed by the inverse localized augmentation, including localization/shift comparisons. This holds for every I and every representative, and uniquely fixes e. |
| Coefficient naturality | The second conjunct states `e G n ((H n).map φ a) = e F n a ≫ (s.map φ)⟦(n : ℤ)⟧'` for every coefficient map and every class. |
| Degree zero sends a section to its module map | For every v and every φ taking 1 to v, the third conjunct identifies e of `(ΓX.toRightDerivedZero.app F) v` with `s.map φ` followed by the canonical inverse zero-shift isomorphism. A map from U is uniquely determined by that value, including on all opens by O-linearity and restriction. |
| Class of one gives identity | The fourth conjunct uses `(ΓX.toRightDerivedZero.app U) 1` and the inverse zero-shift comparison on sU. After identifying sU[0] with sU, this is exactly the identity. |
| Ordinary unsigned cup | The last conjunct quantifies a bilinear `cup` satisfying the recorded `Scheme.Modules.IsModuleCupProduct F G p q cup`. The dependency proves unique existence, so this quantification is precisely the ordinary cup, not an arbitrary operation. |
| All p,q and all classes | `p q : ℕ`, followed by every a in `(H p).obj F` and b in `(H q).obj G`; neither flatness nor a restriction on either degree is added. |
| Canonical augmentation m | `m F G := μ Q (t.obj F) (t.obj G) ≫ Q.map (DerivedCategory.moduleCup_singleTensorIso F G).hom`, exactly the fixed map in `SchemeSingleTensorAugmentationCoherence`. |
| Specified signed comparison | `schemeSignedDerivedTensorShift X (s.obj F) (s.obj G) p q`, which extracts the second shift first. Its defining total-model formula gives (-1)^(q*i) on shifted first-factor degree i. The following `eqToHom` only identifies the integer cast of p+q with the sum of the casts. |
| Cup identity | The final equality is e(cup a b) equal to the transported inverse left unitor, then `(e F p a ⊗ₘ e G q b)`, the signed comparison, and `(m F G)⟦p+q⟧'`, in Lean's left-to-right composition order. |
| Source unitor | `inv (ε Q) ≫ (λ_ (s.obj U)).inv ≫ (ε Q ⊗ₘ 𝟙 (s.obj U))` is the inverse left unitor after identifying the derived tensor unit with sU by the normalized localization unit map ε. It has source sU and target sU tensor sU. This avoids silently assuming those units are definitionally equal. |

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the transparent
  abbreviation for Mathlib's `SheafOfModules`; on this scheme we use that exact carrier.
- `WeilConjectures.Topology.RingedSpaceModuleCohomology`:
  `RingedSpace.globalSectionsFunctor`, `moduleCohomology`, `globalSectionsComplex`.
- `Sheaf.Paper.ModuleCohomologyCupProduct`: `Scheme.Modules.IsModuleCupProduct` and
  `exists_unique_moduleCupProduct`, including its re-exported resolution data and class map.
- `WeilConjectures.AlgebraicGeometry.DerivedTensorStructure`:
  `schemeModule_hasFunctorialFlatResolution` and `schemeDerivedTensorMonoidal`.
- `Sheaf.AlgebraicGeometry.SingleTensorAugmentationCoherence`:
  `SchemeSingleTensorAugmentationCoherence`, `scheme_single_tensor_augmentation_coherence`,
  and its exact definition of m using `DerivedCategory.moduleCup_singleTensorIso` from
  `WeilConjectures.AlgebraicGeometry.ModuleCupCanonicalHZeroIdentification`.
- `Sheaf.Paper.ShiftedTensorMorphismCalculus`: `shiftedTensorComplexComparison`,
  `IsCanonicalShiftComparison`, `shiftedTensorCanonicalComparison`, and the calculus.
  Its comparison convention is implemented for the actual shared scheme tensor by
  `Sheaf.AlgebraicGeometry.LocalizationTensoratorSignedShifts`:
  `schemeSignedTotalTensorShift`, `schemeSignedDerivedTensorShift` and
  `localization_tensorator_signed_shifts` remain in that original module. The new definition
  node `def-sfb-signed-derived-tensor-shift` records the existing plain comparison with
  `existing: true`. The item cites that definition node in stmt_deps and publicly imports
  its existing module; the localization theorem remains in proof_deps only.
- Mathlib's `CategoryTheory.InjectiveResolution.extMk`, `extMk_hom`, and
  `CategoryTheory.Abelian.Ext.hom` supply the cocycle-to-localized-morphism normalization.
  `InjectiveResolution.isoRightDerivedObj` supplies the canonical class transport;
  `Functor.toRightDerivedZero` supplies the degree-zero class.
- `CategoryTheory.RingedDerivedNative.localization_isIso_ε` supplies invertibility of
  localization's specified unit comparison. No independently selected unit is used.

Proof imports are `LocalizationTensoratorSignedShifts`, `DerivedInjectiveResolutionNaturality`,
`ModuleCupPairingExists` and `ModuleCupResolutionExistence`. Other proof dependencies are publicly re-exported through
the statement imports or Mathlib's injective Ext API. One proof import is deliberately
omitted: `Sheaf.Paper.ModuleCupResolutionAugmentation` publicly imports the retired duplicate
`Sheaf.Paper.ModuleCupCanonicalHZeroIdentification`, which clashes with the canonical upstream
module supplied by SingleTensorAugmentationCoherence. The first compiler probe diagnosed the
exact duplicate `DerivedCategory.moduleCup_canonical_hzero_identification`. The upstream
augmentation module also exposes a duplicate upstream resolution-data carrier while the
recorded cup declaration uses the Sheaf resolution-data module. No library source or
non-owned dependency record was edited; the augmentation lemma remains in the documented
proof plan. This is an import compatibility issue, not a change to the mathematical assertion.

Searches for an existing statement, all on 2026-10-24:

- msearch.py LeanFinder: "Module sheaf cohomology is canonically shifted derived Hom from
  the structure sheaf with cup product given by derived tensor". Eight hits, including
  `CategoryTheory.Sheaf.H`, scheme module Hom/category declarations and sheaf cohomology
  presheaves. None states this normalized module-cohomology/tensor comparison.
- msearch.py LeanSearch: "Module sheaf cohomology is derived Hom from the structure sheaf
  with tensor cup product". Eight hits, including `Sheaf.H`, `SheafOfModules` and scheme
  module declarations; no match.
- msearch.py Loogle: `InjectiveResolution.isoRightDerivedObj, DerivedCategory.singleFunctor,
  unitHomEquiv`. No hit; Loogle reports the first short identifier unknown.
- msearch.py grep in Mathlib/Algebra/Category:
  `cup.*[Hh]om|[Hh]om.*cup|extEquivCohomologyClass`. No hits.
- rg in both live `lean/WeilConjectures` and `lean/Sheaf`: cohomology/Hom equivalences,
  normalized Hom, the item id, and the proposed declaration names. Found the different
  `ModuleResolutionHomologyExtEquiv` and scalar-module homology representability/evaluation
  modules; read those interfaces. They supply ingredients, not the present theorem.
  A final exact-name/item-id search found no existing declaration.

Edge cases checked against the statement and constructions: p=0, q=0 and p=q=0 include
zero-shift comparisons; zero sheaves and zero classes are included by additive equivalences;
the empty scheme and zero global ring are not excluded. Arbitrary nonflat coefficients
use a comparison m, never its inverse. No quasi-coherence, flatness, properness,
separatedness, finiteness or characteristic assumptions occur. The localization universe
w is independent of u; the Ext carrier is small in u and `Ext.hom` transports to the given
localization universe. The repaired delivery adds one definition node reusing the existing
comparison, documented below; it requires no mathematical statement correction or dependency
module change.

Initial validation: scompile.py compiled both the sandbox module and its named library
module cleanly (6.3 and 6.5 seconds), with no errors or non-sorry warnings. Current repair validation compiles the item and checks the existing comparison through its
original module, without any relocation or added declaration. During drafting,
explicit Ext universes and the canonical SheafOfModules category fixed elaboration failures;
no mathematical hypothesis was added.

## Second reading by NE

This is the author's separate second reading, as required by the direct-worker protocol;
the maintainer supplies independent review. Reopened the node and the completed file and
checked the five conjuncts against all its sentences. The first fixes e on every resolution
and every evaluated cocycle, rather than merely asserting an arbitrary additive equivalence.
The second is exactly coefficient naturality. The third and fourth retain both degree-zero
sections and the specific class of one, with the necessary zero-shift comparison. The final
conjunct uses the recorded unsigned cup predicate, the exact augmentation, and the comparison
with the specified extraction order; it quantifies all nonnegative degrees and arbitrary
classes and coefficients. The unitor is explicitly transported through ε, and the cast
comparison changes only the notation for the target degree.

The substantive issue found during this reading/compile cycle was that writing `X.Modules`
in category-bearing expressions selects Scheme.Modules' different category instance.
Changed all such occurrences to the shared `SheafOfModules` carrier (named A inside the
proposition), retaining exactly the binder of `schemeDerivedCategory`. This repaired the
interface without restricting universes or changing a mathematical object. Checked that
`IsModuleCupProduct` still elaborates on these identical coefficient objects. Also checked
Mathlib's `extMk_hom`: the normalization uses the inverse localized augmentation and hence
does not omit the canonical-resolution requirement. No unresolved statement mismatch or
STATEMENT-DISPUTED flag remains.


## New nodes

`def-sfb-signed-derived-tensor-shift` records the already published definition
`AlgebraicGeometry.schemeSignedDerivedTensorShift` in
`Sheaf.AlgebraicGeometry.LocalizationTensoratorSignedShifts` with `existing: true` and
no file field. There is no new definition module. The node gives a separate definition
attachment for the plain construction so the item need not add the compatibility theorem
to stmt_deps. It cites exactly `def-pc-scheme`, `def-pc-derived-category`,
`def-pc-scheme-derived-tensor-structure`, and `def-sc-scheme-canonical-tensor-shift`.
Those four dependencies supply X, its shared derived category, its K-flat tensor, and the
canonical coherent one-variable tensor shifts. The recorded definition's existing
signature is copied verbatim, including its module-level explicit variable X and the
independent derived-universe binder. Its three isomorphisms extract the second shift b,
shift the first-factor comparison for a by b, and combine [a][b] to [a+b]. It introduces
no arbitrary tensor, comparison or choice.

Source: Stacks more-algebra.tex Tag 0FNH, item-shift-tensor, in the prescribed
second-shift-first convention, and sites-cohomology.tex Tag 06YU for K-flat descent.
The source text and the existing canonical-shift implementation were read. Edge cases
include all integer a,b (negative, zero, a+b=0), arbitrary derived objects, independent
universes u,w, zero objects and empty schemes. No additional hypothesis is imposed.

Search results are preserved in mathlib_searches, with the corrected reuse verdict:
LeanSearch returned eight shift ingredients, including mapBifunctorShift₁Iso;
LeanFinder returned eight unrelated scheme tensorCongr results; Loogle for
CategoryTheory.shiftFunctorAdd' returned twelve hits giving the composition comparison
and its laws. Mathlib grep returned twenty-five general commShiftIso hits. Direct rg in
WeilConjectures found the canonical one-variable structure and no named signed comparison;
direct rg in Sheaf found schemeSignedDerivedTensorShift only in the existing localization
module. DAG grep found its helper record only on the theorem node. The blueprint search
found zero nodes matching signed derived tensor shift, and ancestor returned None, as
recorded. The new node therefore reuses the exact found declaration; it does not duplicate
it. The search queries, outputs and dates remain in the node.

## Return repair

Return on immutable head `5719214d83fe`: the collision gate reports the attempted new
module's schemeSignedDerivedTensorShift as already declared in the original localization
module and requests importing and reusing that declaration. This repair adopts reuse:
removed the sandbox SignedDerivedTensorShift module, removed the sandbox replacement of
LocalizationTensoratorSignedShifts and its dependency-node edit, and changed the new
definition node to `existing: true` on the original module/declaration. The item publicly
imports that original module. It retains only the definition node as its added stmt_dep;
the compatibility theorem remains in proof_deps. No declaration is renamed, added, moved
or re-proved. This is a substantive change from the returned relocation packet.

The current server source was read through scompile.py --source and agrees with the
read clone: the original module still defines the comparison, and the attempted new
module has not landed. Rebased the item's node copy on current main: only lean and the
one added definition stmt_dep change. The dependency module/node are absent from this
packet. The delivery wrapper constructs its commit against fresh origin/sheaf-dag.
All mathematical clauses already accepted by the first return remain unchanged.

Repair second reading: opened the original declaration and the item side by side.
The imported existing comparison has exactly the old name, type and second-shift-first
body used in the cup formula. Verified the new node's existing:true record names that
module, has no lean.file, and has a verbatim declaration signature; the four statement
citations match its four stmt_deps. Verified the only delivered Lean module declares
SchemeModuleCupShiftedHomComparison and scheme_module_cup_shifted_hom_comparison,
with no declaration of schemeSignedDerivedTensorShift. Thus the reported duplicate
cannot be introduced by this packet. The first return's definition-node requirement
and the latest return's reuse requirement are both met. This is the author's rereading;
the maintainer provides the independent review.

Repair verification: scompile.py compiled the item in sandbox mode (6.3 s) and named
library mode (6.5 s), without errors or non-sorry warnings. deliver2.py additionally
checks the existing comparison with a module-mode import/#check probe.
