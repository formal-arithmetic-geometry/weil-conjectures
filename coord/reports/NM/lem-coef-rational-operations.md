## Worker report

Module: `Sheaf.SixFunctors.RationalOperations`; main theorem:
`WeilConjectures.coef_rational_operations`. Stage 2: its only theorem proof is `sorry`.
The auxiliary definitions are explicit functors or records packaging precisely this
node's identifications. The return repair uses the reviewer's explicit §1(B) alternative: the existing
definition node def-weil-exceptional-inverse-image now records the published
integral/rational System interface. No new definition or statement correction
is needed. The node's statement is unchanged. Its current
main-20261015 text drops “in the manuscript”; that editorial change has no mathematical effect.
The full current DAG proof, including all 20 numbered steps and their dependencies,
is in the theorem docstring. The resolved stage-1 repair note was read: the split
proof is retained verbatim in the node and in the proof docstring.

Hypotheses and clauses, with their Lean counterparts:

- The inherited global datum is `D : FiniteFieldDatum.{u}`; `l : ℕ`, `[Fact l.Prime]`
  and `hl : l ≠ D.p` give the coefficient prime and its characteristic restriction.
- The inherited separated finite-type k-schemes are `X Y : Scheme.{u}`,
  `[X.Over (Spec (.of D.k))]`, `[Y.Over ...]`, and the `LocallyOfFiniteType`,
  `QuasiCompact`, and `IsSeparated` instances on both structure morphisms.
- Every separated finite-type k-morphism is an arbitrary `f : X ⟶ Y` with
  `[f.IsOver (Spec (.of D.k))]`, `[IsSeparated f]`, `[LocallyOfFiniteType f]`,
  `[QuasiCompact f]`. `c : Compactification f` is arbitrary; it fixes the common
  finite-stage model, and imposes no condition since these morphisms are compactifiable.
- Every finite E/Q_l and every finite coefficient extension are quantified in
  `Conclusion` as `F G : ConstructibleExceptionalCoefficients.FieldStage.{u} l`
  and `ι : F.carrier →ₐ[Padic l] G.carrier`. FieldStage contains exactly a field,
  its Q_l-algebra structure and finite dimensionality. No embedding into Ω is assumed.
  Ω is an arbitrary algebraic closure used by the already recorded exceptional
  system, whose finite/rational stages are independent of Ω; this auxiliary
  presentation is always available and imposes no condition on X, Y, E, or L.
- The categories are exactly `sfIntegralConstructibleCategory` and their raw
  `sfRationalConstructibleCategory` scalar localizations, with the unchanged objects.
  `HomIdentification.permitted` asserts closure on ALL pairs; it is not an assumption.
  `homPair`, `homRight`, and `homDual` only restrict/lift the already recorded
  `rationalDerivedInternalHom`, retaining its object and pure-tensor map formulas.
- “Integral tensor is completed derived tensor”: `tensorLeft` uses precisely
  `rationalDerivedTensor`; its integral object is `constructibleIntegralTensor`,
  whose underlying functor is `integralCompletedTensor`. `integral_evaluation`
  uses the inverse of the specified `A.completion.map`, whose K-flat generator
  and mapping-fiber-coordinate normalization is retained in RationalVerdier.Datum.
- Internal Hom is the closed operation: `HomIdentification.adjunction K` is
  tensor(K,-) ⊣ RHom(K,-). Its `integral_evaluation` fixes the counit to the
  localization of completed integral evaluation. The unit is thereby fixed too;
  both triangle identities are included in Lean's `Adjunction`.
- `D_X,E K = RHom_E(K,omega_X,E)` is the natural identification
  `HomIdentification.duality`, with omega the raw localization of `w.omega`.
  The `evaluation` equation identifies the actual Verdier evaluation with the
  closed evaluation through this comparison, rather than asserting an arbitrary iso.
- `Rf_E!` is the actual `S.ring.operation c (.rational F).G`. Its finite origin,
  integral normalization and rationalization comparisons are retained by the
  published `System`, with finiteRight identifying the finite etale-origin formula.
  `ExceptionalIdentification.comparison` identifies it with `dualFormula`, namely
  `DY.dual.rightOp ⋙ (rationalDerivedPullback ... f).op ⋙ DX.dual`.
- Right adjunction to the actual `Rf_!,E` is
  `ExceptionalIdentification.adjunction`, whose left functor is exactly
  `sfCompactSupportFiniteFunctor`. The fields `unit` and `counit` give explicit
  equations transporting the existing system's unit/counit through its actual
  `rationalLeft` and the exceptional comparison.
- `omega_X,E = Ra_X,E! E` is `DualizingIdentification`, using the same exceptional
  system at a_X, its arbitrary finite coefficient field F, the recorded Nagata
  compactification, and the explicit completed regular module in degree zero
  localized by `coefficientUnit`. There is no unspecified point coefficient object.
  `structureSystem` is only a specialization of `System`; its globally available
  helper `structureIsOverSpec` supplies the canonical over-base proof from the
  existing `specOverSpec_over` and Spec identity laws. No extra hypothesis is imposed.
- Evaluation under finite scalar extension is the explicit
  `HomScalarCompatibility` equation, using `rationalHomScalarComparison` and
  `rationalTensorScalarComparison`; it is required for both X and Y.
- The duality comparisons under finite extension are `ScalarCompatibility.dualX`
  and `.dualY`; `.normalizedX` and `.normalizedY` are the full existing
  `RationalVerdier.ExtensionProperties`, retaining canonical integral u and beta,
  and the evaluation and actual biduality squares.
- `ScalarCompatibility.exceptional` is the commuting square between scalar
  extension of the exceptional identification, the canonical `dualScalar`
  comparison, and the system's actual exceptional mate `.b`. `dualScalar` uses
  the contravariant inverse of the pullback/target-duality comparison. Thus the
  unit/counit equations of the identification and of the system's scalar
  Comparison concern the same maps. Rationalization unit/counit compatibility
  is retained by `S.fields.rationalizationComparison`.
- `Conclusion` existentially asserts the exceptional systems and all the above
  data for every extension. There is no existence, closure, adjunction, or
  compatibility hypothesis substituting for a clause of the conclusion.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `def-weil-scheme-morphism-properties` is a convention node; its recorded
  Mathlib properties `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`,
  `Scheme.Over`, and `Scheme.Hom.IsOver` are used directly.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`, publicly imported; the underlying
  completion is `completedIntegralCommRingSheafUnrestricted`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory` (completeness, all reductions, uniform interval).
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization` and the recorded raw scalar extension.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedTensor`,
  `rationalDerivedPullback`, `rationalDerivedInternalHom`, their permitted-pair
  predicates, and all three canonical scalar comparisons.
- `Sheaf.Paper.QcqsCompactSupportRealization`: `sfQcqsCompactSupportRealization`,
  reexporting the actual `sfCompactSupportFiniteFunctor` used in the statement.
- `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`: `sfFiniteExceptionalAt`,
  reexporting `sfFiniteExceptional`; the System's finiteRight is the recorded
  intrinsic realization of that Rnu_* / etale-adjoint / nu* construction.
- `Sheaf.SixFunctors.RationalVerdier`: `coef_rational_verdier`, `Datum`, `Completion`,
  `Extension`, `ExtensionProperties`, `units`, `scalar`, and `tensor`.
- Repaired definition node `def-weil-exceptional-inverse-image`:
  `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`, `System`,
  `FieldStage`, `RingSystem`, `FieldSystem`, `Operation`, `Comparison` and the
  related records. These already-published definitions are now recorded by the
  definition node itself, whose previous finite-only record did not expose the
  integral/rational system. `exists_system` is not applied by the item and its
  theorem node is not a statement dependency. The definition's original finite
  `sfFiniteExceptionalAt` declaration remains reexported and recorded.
- Additional already-landed node `lem-weil-constant-coefficient-objects-constructible`:
  `Sheaf.Paper.ConstantCoefficientObjectsConstructible`,
  `integralConstantCoefficientObject`, `integralConstantCoefficient_constructible`.
  These give the actual point coefficient object and its membership proof.
- Every published recorded proof-dependency module is imported without `public`
  unless already a statement import. Unstated proof dependencies are not fabricated.
  Read-only traversal verified that the coefficient-unit dependency has no path
  back to this item through statement/proof dependencies. The exceptional
  definition was already a statement dependency of the item.

Edge cases checked before drafting and again against the final types: zero K or M;
empty X (including the unique morphism to Y); empty Y forces empty X; f = identity;
E = L with ι = identity; and ramified finite extensions. No nonempty scheme, positive
cohomological bound, or positive relative dimension is assumed. Coefficient levels
in the imported operations are n+1, so the zero quotient is never used. The scalar
square contains no inverse of a noninvertible map: the pullback and duality scalar
maps are recorded isomorphisms. Both contravariant reversals in D_X f* D_Y are retained.
Universes are explicitly declared; all variables are bound, and `autoImplicit` is false.

Searches (all through the authorized wrappers or read-only rg):

- LeanFinder: “rational constructible coefficient scalar localization internal Hom
  exceptional inverse image Verdier duality”: eight generic localization/derived
  category hits, no match for this identification theorem.
- Loogle: `CategoryTheory.Adjunction, CategoryTheory.ScalarLocalization`: no hits;
  ScalarLocalization is a project declaration rather than a Mathlib declaration.
- Mathlib grep: `rational.*(InternalHom|Exceptional)|coef_rational_operations`: no hits.
- LeanSearch: “rational internal Hom exceptional inverse image constructible sheaves”:
  eight ordinary sheaf Hom hits, none stating the derived coefficient identification.
- rg in the upstream WeilConjectures tree for the item id and rational exceptional/
  Hom names: no existing theorem. rg in lean/Sheaf found the dependency operations
  and the downstream SfBidualityClass reference, but no theorem for this item.
- rg for `RationalOperations|coef_rational_operations` in Mathlib/upstream/project
  names (including dag/lean_names_upstream.json): no duplicate declaration.

No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by NM

Author self-check only; this is not an independent review. The maintainer performs
the independent reading required by the dispatcher brief. The source checked is
`literature/blueprint/master/blueprint/sec-six-functors/`
`sk-prop-sf-biduality-general/lem-coef-rational-operations.md`,
node lem-coef-rational-operations, order 2152: statement displays and the proof
paragraphs beginning “The integral exceptional adjunction” and “For finite scalar
extension”. The node, that source text, dependency signatures and module were open. I checked every correspondence above again. Internal
Hom is on all pairs, not merely the allowed-pair subcategory: closure is an asserted
field. Its adjunction uses tensor(K,-), matching the ordinary presentation, and
integral_evaluation includes the completion inverse. The exceptional comparison
is natural; the left adjoint in its adjunction is the actual compact-support functor,
and both displayed transport equations use the same comparison. The scalar dual
formula was checked in order: TX DX f* DY, dual-X comparison, then DX_L applied to
the opposite of f*_L applied to the inverse dual-Y comparison followed by inverse
pullback comparison. This has the required endpoints; reversing only one of those
inverse maps would not type-check. The structure-map comparison uses the real
coefficient unit, and all data are conclusions quantified for every F,G,ι.
During compilation I corrected a product-functor spelling, made f explicit in
`dualFormula` applications, and supplied the canonical Spec identity proof
with `structureIsOverSpec`; none changes the mathematical hypotheses.
No source statement correction was introduced. The lean-only repair of the
existing exceptional-definition record is described below. No published Lean
declaration, definition body, or theorem type is changed.

Validation: `scompile.py NM lem-coef-rational-operations .../RationalOperations.lean`
completed cleanly for both the sandbox check and the final module path (10.7 s and
13.4 s respectively), with no errors or unexpected warnings. No global build or
live-source mutation was performed. Delivery preflight is run through deliver2.py.


## Return repair

The immutable-head return at `070596bbadf3` identified H2: the item cited the
`exists_system` theorem's node while using only the definitions in its module.
The saved-packet dry run passed (commit `d71bd67928`); the substantive repair here
is the explicit alternative in that return: §1(B) re-records
`def-weil-exceptional-inverse-image` with the existing integral/rational system.
The item removes `lem-sf-constructible-exceptional-adjunction-coefficients` from
its added statement dependencies and uses its already-present exceptional
**definition** dependency. `Conclusion` still existentially supplies its own
systems, and never applies `exists_system`. The accepted constant-coefficient
membership dependency remains: `coefficientUnit` uses
`integralConstantCoefficient_constructible`'s conclusion.

The minor source-place correction is in the author self-check above, citing the
node's master source place, order 2152. It is labeled as the author's self-check,
not an independent second reading. The maintainer supplies independent review.

## Dependency modules

`def-weil-exceptional-inverse-image` has a lean-only §1(B) repair using an existing
published declaration, with `existing: true` and `lean.note`; no new module is
needed. The previous record's `sfFiniteExceptionalAt` gives only the fixed finite
coefficient functor. It cannot type the integral/rational coefficient-system
notation in this item. The record now names the existing definition
`WeilConjectures.ConstructibleExceptionalCoefficients.System` from
`Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`, together with its
existing `FieldStage`, `RingSystem`, `FieldSystem`, `Operation`, `Comparison` and
related definitions. `exists_system` is deliberately excluded. The old finite
`sfFiniteExceptionalAt` is publicly reexported by that module and retained among
the recorded declarations, so the fixed finite interface is retained.

The repaired definition record follows the dependency node's own source,
main-20261015 exceptional-inverse-image definition, finite and higher coefficient
stages and adjunction paragraphs, and the node's expanded integral reduction/system
construction. `RingSystem.finiteRight` identifies the finite etale-origin formula;
`integralLeft`, `left`, `scalar`, `finiteScalar_eq`, `integralScalar_eq` and their
normalization fields retain the specified integral and reduction realizations;
`FieldSystem.rationalizationComparison` and `rationalComparison` retain raw
localization and finite scalar-extension mates. `Operation.adjunction` and
`Comparison.unit`/`.counit` retain the actual adjunction maps and their coefficient
compatibility. `CommonSystem` and `RefinementSystem` package the same operations
at common stages and across compactifications. Thus recording these definitions
gives the higher coefficient interface missing from the former finite-only record;
it does not add an existence hypothesis or choose a system from a theorem.

This uses the already-published package with exactly the same names, field types,
and bodies. No second definition, new node, new postponed theorem, or change to
any dependency's statement/proof/dependency lists is made. The item's node differs
from current main only in `lean` and the accepted coefficient-unit addition to
`stmt_deps`; the repaired exceptional node differs only in `lean`.

Final self-check: the original edge cases (zero objects, empty schemes, identity
morphisms, identity coefficient extensions, and ramified finite extensions) and
all universe parameters are unchanged. The retained module's signature and every
comparison field are the previously independently reviewed ones. The source's
exceptional adjunction, evaluation, dualizing-object, finite-scalar and unit/counit
clauses still have exactly the Lean counterparts listed above.
