## Worker report

The delivery states the finite-coefficient purity theorem and constructs its specified fundamental class and its two canonical isomorphisms in `Sheaf.Paper.RegularImmersionPurity`. All postponed assertions have sorry-only proofs with source and proof docstrings. Definition data are explicit composites, or choices from unique-existence theorems that determine the resulting object up to equality.

Hypotheses and conclusions were compared with the node and the current main-20261015 blueprint, sec-smooth-purity/sk-thm-regular/thm-pur-regular-immersion-purity:

- The standing finite-field, prime-to-characteristic coefficient and positive finite-level data are the existing `PurityFiniteSetting.{u}` argument `P`. Its coefficient is the universe lift of the actual quotient A_{E,n}, not an arbitrary finite ring. No divisibility of n by the ramification index is assumed.
- `i : Z ⟶ X` and `[IsClosedImmersion i]` give the named closed immersion. `c : ℕ` and `hi : PurityConventions.IsRegularOfPureCodimension i c` give exactly the published affine-neighbourhood regular-sequence convention, including c=0.
- `aX : X ⟶ Spec (.of P.field.k)`, `[Smooth aX]`, `[IsSeparated aX]`, and `[QuasiCompact aX]` give smooth X in the chapter's separated finite-type setting. Smooth gives locally finite type. Mathlib’s `LocallyOfFiniteType.isLocallyNoetherian` and `QuasiCompact.compactSpace_of_compactSpace` supply the Noetherian instance used by the exact closed-pushforward comparison; it is derived, not added as an assumption. The regularity of Z is `hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)`. No global relative dimension is fixed and no connectedness is assumed.
- `regularTate X c` is the existing finite Tate sheaf, inverse-image transported to the pro-etale site, embedded in degree zero and shifted by 2c. `P.regularExceptional i aX` specializes the published finite-coefficient `rightDerivedUpperShriek`; the actual quotient-finiteness theorem supplies its finite instance.
- `regularImmersionPurity` says every cohomology object at r≠0 is zero, its degree-zero cohomology is isomorphic to the constant free rank-one coefficient sheaf, and the specified class map is an isomorphism.
- `regularSupportedEquiv` is the displayed H^0/supported-cohomology identification, using the exceptional adjunction and the exact closed-coefficient comparison. The supported group is the existing `cupSupportedHom`; H^0 with coefficient unit is the Hom from its degree-zero constant sheaf. The equivalence fixes the actual counit normalization.
- `RegularFrameNormalization` quantifies over every existing `i.EtaleFrame c`. Its equality uses the already defined `frameBoundaryProduct`, the ordered cup of the individual Kummer boundaries. This is the underlying fold used by `frameClass`, without inheriting that wrapper's unrelated relative-dimension binder. `regularFundamentalClass_existsUnique` gives exactly existence and uniqueness, and `regularFundamentalClass` selects that unique element.
- `regularFundamentalClassMap` is the adjunction transpose of this class, so it sends 1 to precisely that class. `regularPurityIso` uses its asserted `IsIso`, not a separately selected isomorphism.
- `regularCancelledPurityIso` has source Ri! A_X and target A_Z(-c)[-2c]. Its expression is the inverse of cl_i tensor the negative shifted line, followed by the unit action and the uniquely counit-normalized cancellation comparison. `regularCancellation_existsUnique` fixes the comparison by the projection/counit/dual-evaluation equation, so its choice has no free orientation scalar.
- `regularFundamentalClass_etale` says for every etale Cartesian square that the pulled-back class is exactly the unique frame-normalized class. Its candidate-class formulation permits even non-quasi-compact etale neighbourhoods, without assuming that the exceptional functor is supplied on them.
- `regularFundamentalClass_product` says the product closed immersion is regular of codimension c+d, its source is regular, and its unique normalized class is `regularExteriorClass`. That exterior class is the actual supported cup of the two projection-pulled classes, transported along the unique support isomorphism and the ordered Tate tensor identification. The product of the purity morphisms is determined by these classes under the same adjunction, as is the inverse twisted form.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, `Ring`, `Coefficient`, `constant`, `constantEtale` (the lean binding of def-pur-conventions).
- `Sheaf.Paper.PurityConventions`: `WeilConjectures.PurityConventions.IsRegularOfPureCodimension` (the sk-def-purity-conv convention), and the existing finite Kummer setup.
- `Sheaf.Paper.PurityFrameClass`: `WeilConjectures.PurityFiniteSetting.frameBoundaryProduct`, `frameClass`, `frameCupSheaves`, `frameClosedCoefficientIso`, `frameCupTransport`, and `frameEtaleTensorNext` (def-pur-frame-class).
- `Sheaf.Paper.PurityFrameIndependence`: `WeilConjectures.PurityFiniteSetting.frameClass_independent` and `frameClassOnPullback` (lem-pur-frame-independence). The module is imported; its frame normalization supplies the proof plan for uniqueness and restriction.
- `Sheaf.Paper.SupportedCupFunctoriality` (definition owner `def-pur-supported-class-operations`): `functorialCupPullback`, `functorialCupTwistPullback`, `functorialCupTwistProduct`, and the section-normalized `functorialCupExchange`; the last is used inside the former.
- `Sheaf.Paper.PurityFrameKummer`: `frameTwist`, `frameTwistEtale`, `frameTwistPullback`, `frameConstantPullback`.
- `Sheaf.Paper.SupportedCup`: `AlgebraicGeometry.ProEtale.cupSupportedHom`, `cupSingle`, `cupSingleTensorMap`, `cupConstantIso`, `cupTensorShiftIso`, `CupDerivedCategory`, and their fixed shared derived tensor instances.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriek`: `rightDerivedUpperShriek`, `rightDerivedUpperShriekCounit`, `rightDerivedUpperShriekHomEquiv`; `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`. Compactness needed by the bounded-below interface is the actual `QuasiCompact.compactSpace_of_compactSpace aX`.
- Published pro-etale derived adjunction: `rightDerivedUpperShriekHomEquiv`, `derivedUpperStarLowerStarAdjunction`, and the exact derived/single comparisons. `Sheaf.AlgebraicGeometry.SupportedExteriorProduct` supplies the actual `AlgebraicGeometry.Etale.supportedProductImmersion` (only its scheme morphism is used; the sheaves in this delivery remain pro-etale).
- `Scheme.finiteEtaleTateSheaf` supplies signed twists; `Etale.p1DecompositionSheafPullback` supplies their root/dual-normalized pullback.

Canonical-map adapters are specializations of published constructions. The final module consistently imports the modern `FiniteCoefficient` family, avoiding the older `FiniteTypeExceptionalInverseImage` wrapper's incompatible legacy imports. `regularProperComparison` aliases `rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar`; `regularProjection` specializes `regularProjectionCanonical`, whose body is exactly the published `projectionMap` component. The helper `regularProjectionHom` names the native Hom type before coefficient specialization; `regularProjectionCanonical` and its specialization use that shared type, avoiding repeated kernel expansion of concrete coefficient dictionaries. Its body remains the same published projection-map component. The supported pullback and signed twist comparison are specializations of `Sheaf.Paper.SupportedCupFunctoriality`, with its unique section-normalized ordinary coefficient exchange. `regularSquare` retains the actual canonical pullback identification. These helpers do not assume an arbitrary base-change map, counit, or isomorphism. All declarations are recorded in lean.declarations.

Edge cases checked: c=0 uses the existing empty boundary product and the unitor tensor identifications; the negative zero twist is the actual degree-zero signed twist. The empty support and empty scheme have unique zero classes and the corresponding zero coefficient sheaves, with no nonempty hypotheses. Disconnected smooth schemes may have different component dimensions; only the immersion codimension is fixed. Positive levels with ramification index not dividing n remain included. The variable u is explicit, schemes have universe u, coefficient modules have universe u+1, and the published small pro-etale site is retained.

Searches made for an exact existing declaration:

- LeanFinder through msearch.py: “purity regular closed immersion fundamental class exceptional inverse image Tate twist”; eight unrelated Proj/immersion results, no normalized cohomological purity theorem.
- LeanSearch through msearch.py: “purity regular immersion exceptional inverse image fundamental class”; eight scheme immersion results, no match.
- Loogle through msearch.py: “IsRegularImmersion, fundamentalClass, IsIso”; unknown IsRegularImmersion, no result.
- Mathlib grep through msearch.py: `purity|Purity|fundamentalClass` under AlgebraicGeometry; zero matches.
- rg in WeilConjectures and lean/Sheaf for regular purity, fundamental classes, supported pullbacks and Tate comparisons: the older regular-immersion API gives nonempty isomorphisms in the etale setting, not the specified pro-etale frame-normalized class and both compatibilities. The existing frame fold, coefficient setting, supported cup, signed twist and exceptional functor were reused.
- `grep -rn thm-pur-regular-immersion-purity` in upstream WeilConjectures: no tagged declaration. `tools/lean_names_upstream.py show thm-pur-regular-immersion-purity` exposed no exact binding.

The item and all four new definitions cite `def-pur-supported-class-operations` for
`FunctorialCupH`, `functorialCupPullback`, `functorialCupTwist`, its multiplication
and its pullback comparison. They do not cite the functoriality theorem as a
statement dependency. The canonical adapters are owned by
`def-pur-regular-immersion-class-data`, in `Sheaf.Paper.RegularImmersionClassData`;
the other three definitions and the item cite this class-data node.

## New nodes

- `def-pur-regular-immersion-class-data` defines the actual finite-quotient pro-etale
  frame-normalized fundamental class and its exceptional-adjunction transpose, using
  the same all-frame normalization, supported pullback, exact coefficient comparison,
  and unique-existence theorem already in the saved packet. Codimension zero, empty
  schemes and disconnected schemes are included. Upstream Etale.fundamentalClass and
  `pur9-rg-def-fundamental` use ordinary etale coefficients with a different twist
  interface; neither supplies this actual finite-quotient pro-etale class. Existing
  pro-etale cups, finite twists and exceptional functors are reused.
- `def-pur-regular-immersion-exterior-class` constructs the supported exterior class
  by the two projection pullbacks, ordered supported cup, Tate multiplication and
  unique support comparison. It states no purity assertion. The existing
  `def-pur-supported-exterior-shift` concerns a different compact-support operation.
- `def-pur-regular-immersion-signed-evaluation` constructs the shifted dual evaluation
  and signed Tate pullback. Its data are the finite sheaf dual evaluation, actual
  monoidal comparison, degree-zero tensor localization and tensor-shift comparison.
  Its carrier equalities merely identify the same canonical localization and objects.
- `def-pur-regular-immersion-cancellation` defines the unique counit-normalized
  cancellation isomorphism and ordinary coefficient-unit action. Uniqueness fixes
  the comparison; no arbitrary map or scalar is selected. The final theorem module
  still defines the inverse-twisted purity isomorphism as exactly the inverse of the
  class isomorphism tensor the negative line, followed by these comparisons.

All four notions follow the current blueprint's fundamental-class paragraph and
its displayed cancelled isomorphism. The new modules preserve their previously
reviewed expressions and docstrings, with the owning blueprint tags updated.
Each node records fresh LeanSearch, LeanFinder, Loogle and Mathlib/source grep
results. The searches found no exact finite-quotient pro-etale canonical map;
blueprint_refs and DAG grep distinguished the related ordinary-etale class and
compact-support exterior construction. These are definitions used to type the
statement, not an alternative proof route or a correction of the theorem.

## Returned H2/H13 repair, 2026-10-19

The retained packet's required initial dry run passed mechanically (b8061ac9e3),
but still contained the independently returned ownership error. This repair
addresses that return substantively. The entire published
`Sheaf.Paper.SupportedCupFunctoriality` module and
`lem-pur-supported-cup-functoriality` node record are restored to live by removing
their replacement files from the delivery. No dependency module is delivered.

All 34 `regular*`/`Regular*` adapters formerly appended to that theorem module
now occur in `RegularImmersionClassData`, before the class constructions which
use them. Their signatures, attributes and bodies are unchanged; their source
and blueprint docstrings identify the class-data owner. The owner's
`lean.declarations` lists all 34 in addition to its original declarations.
Required projection/derived-single/site-comparison imports and the explicit
universe names moved with them. No copied supported-cup operation or law occurs
in the delivery. The item and all four new definition nodes drop the theorem
from `stmt_deps` and cite the already landed definition node
`def-pur-supported-class-operations`; the new-node prose references are updated
to that same owner. The item's mathematical statement, proofs and original
statement dependencies are unchanged.

The live source was read with `scompile.py --source
Sheaf.Paper.SupportedCupFunctoriality`. Its supported Hom, signed twist,
normalized cup, ordinary coefficient exchange and exact supported pullback
signatures/docstrings agree with the definitions used here. The original
1206-line source and its theorem record remain outside the packet. Only local
unique-existence helpers are chosen by the delivered class/support/cancellation
constructions; the functoriality theorem is not used to supply definition data.

All five delivered files passed `scompile.py` cleanly in private, sandbox and
library passes. Library measurements: class data 27.3 s, exterior class 19.4 s,
signed evaluation 6.4 s, cancellation 9.1 s, main purity 8.2 s. The moved
adapters retain actual canonical composites and the same named carrier-equality
theorems, rather than introducing any new map or assumption.

## Second reading by NU

This is an author self-check, not an independent worker review: the dispatcher
explicitly prohibits starting other agents. The maintainer supplies the independent
mathematical review. I reopened the current blueprint theorem, the five node
records, all five modules and the live supported-cup definition owner's record
and source. The returned review had accepted every mathematical clause; this
repair preserves their signatures and bodies.

In particular, `P` retains the finite quotient and every positive level; `i`, `c`
and `hi` retain a closed regular immersion of pure codimension including zero;
`aX` remains smooth, separated and quasi-compact, and `hZ` states stalk regularity.
The theorem still asserts all-frame normalization, concentration away from zero,
free rank-one degree-zero cohomology and invertibility of the exact adjoint
transpose. `regularSupportedEquiv` supplies the stated H^0/support identification.
The etale identity still covers arbitrary etale neighbourhoods; the product identity
still asserts regularity and the actual supported exterior class. The inverse-twist
form still uses the inverse of this same class isomorphism, its negative-line tensor,
the coefficient unit and the uniquely counit-normalized cancellation comparison.
Empty schemes/supports, disconnected schemes, codimension zero and the small-site
universe convention remain covered. No statement correction or disputed clause arises.

The self-check verifies the precise returned repair: no supported-cup theorem node
or module is delivered, no `stmt_deps` names that theorem, the already existing
plain-operation definition node is cited, and each moved adapter is declared once
and listed by its new owner. All five principal `lean.statement` strings remain
verbatim in their modules and all Lean lines fit 100 characters.

The repaired dry run passed compilation and maintainer preflight at 4c765d2a32.
Its staged inventory contains only the five regular-immersion modules, their five
nodes and this report; the supported-cup module and theorem node are absent.
