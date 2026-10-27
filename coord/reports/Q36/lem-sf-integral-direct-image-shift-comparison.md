## Worker report

The item is stated by `WeilConjectures.sfIntegralDirectImageShiftComparison` in
`Sheaf.Paper.SfIntegralDirectImageShiftComparison`. Its only proof is `sorry`.
The supporting §1(A) definition node def-sf-ambient-integral-direct-image owns
Sheaf.Paper.SfAmbientIntegralDirectImage and all ten sfAmbient* declarations.
The item's stmt_deps gains this node. The item statement, proof plan and proof
dependencies are unchanged. The landed def-weil-derived-direct-image node and
its Q29 Lean record are not part of the delivery and remain byte-identical to live.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Prime ℓ | `(l : ℕ) [Fact l.Prime]` |
| Finite extension E/ℚ_ℓ | `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]` |
| Valuation ring, chosen uniformizer, positive finite quotients | Existing `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, and `coefficientExtensionRing l E (n+1)` used by the imported coefficient system; index n denotes positive exponent n+1. No different coefficients are introduced. |
| Morphism of schemes f:X→Y | `{X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y)` |
| ℓ invertible on X and Y | `_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x)` and the corresponding `_hY` |
| Small pro-etale sites | `X.ProEt`, `Y.ProEt` and `ProEt.topology`, inherited by the module categories |
| Completed coefficient sheaves, not discrete constant integral coefficients | `scalarReductionSource l E X` and `scalarReductionSource l E Y`, the recorded module categories over `completedIntegralCommRingSheafUnrestricted` |
| Ambient unbounded derived categories | `DerivedCategory (scalarReductionSource l E X)` and its Y counterpart; these are the standard unbounded localizations |
| Rf_* = Rlim Res_n Rf_{*,n}(K tensor^L A_{E,n}) | `sfAmbientIntegralDirectImage l E f`: actual derived strict-system reduction, exact scalar restriction, right derivation of sectionwise direct image on completed-module towers, then `coefficientConstantTowerLimit l E Y`; details below |
| Every r∈ℤ and every K | `∃ θ : ∀ r : ℤ, shiftFunctor ... r ⋙ F ≅ F ⋙ shiftFunctor ... r`; the natural isomorphism's components quantify over every ambient K |
| θ maps Rf_*(K[r]) to (Rf_*K)[r] and is an isomorphism | At K, `(θ r).app K` has precisely these source and target objects |
| Natural in all derived morphisms, including inverse quasi-isomorphisms | `≅` between functors is `NatIso`: its naturality applies to every morphism of `DerivedCategory`, including the inverse of every localized quasi-isomorphism |
| θ_{K,0}=id | `θ 0 = Functor.CommShift.isoZero F ℤ`, the canonical identity comparison after the two `shiftFunctorZero` identifications. This avoids incorrectly equating maps with different nondefinitionally equal zero-shift endpoints. |
| No constructibility, boundedness or derived completeness assumed | None appears as a binder, type restriction, or premise. No coherence under addition of shifts, beyond what the node states, is imposed. |

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`, reexporting `Sheaf.NumberTheory.Padics.CoefficientExtension` and its coefficient constructions.
- `def-weil-scheme-morphism-properties` is recorded as a convention with no declaration; the statement uses Mathlib `Scheme`, its morphisms, stalks and `IsUnit`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt` and `ProEt.topology`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`, `WeilConjectures.integralConstantToCompletionOfUniverses`, reexporting the completion and finite projections with independent universes.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, `CategoryTheory.Pretriangulated`; the actual shifts are those on Mathlib's derived categories, with the signed cochain convention.
- `Sheaf.Paper.SfDerivedDirectImage`, `WeilConjectures.SfIntegralDirectImage`, `sfDirectImageTerm`, `sfDirectImageTransition` and `sfDerivedRestrictionComparison`; retained by public reexport, with its landed node record untouched.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`, `WeilConjectures.scalarReductionDerivedExtension`, `scalarReductionDerivedRestriction` and `scalarReductionSource`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`, `CategoryTheory.IsDerivedLimit` and `IsDerivedLimitTriangle`; these specify the Roos-triangle property, not a functor. The new ambient realization uses the existing total right-derived limit on strict towers.
- The existing `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` theorem `coefficientDerivedSystemEvaluationCalculus` supplies its actual reduction, its fixed-limit adjunction and its strict K-flat representative model; `Sheaf.Paper.CoefficientRingedSequenceSite` supplies exact restriction and total derived limit. The calculus is an explicit statement dependency of the new definition node, because the definition uses its .choose.reduction.
- Proof imports preserve the plan: ringed sequence-site interpretation, independent-universe ringed derived pullback, constant-coefficient inverse image, semilinear derived sections, K-injectives, right-derived shifts, exact-functor derived shifts, and the strict-tower homotopy-limit theorem. All recorded modules were inspected; Mathlib-only proof dependency `lem-sf-exact-functor-derived-triangulated` is imported through `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.

Edge cases checked by reading the types and constructions:

- Zero and negative shifts are included because r is an unrestricted integer. At zero the canonical zero comparison explicitly fixes the normalization.
- Zero complexes and empty schemes remain allowed. There are no nonemptiness or geometric finiteness assumptions.
- Arbitrary unbounded, noncomplete and nonconstructible input complexes remain allowed; reduction and simultaneous K-injective resolutions are the unbounded constructions.
- The tower begins with exponent one (`n=0`), never the zero quotient exponent; all positive levels and quotient transitions are retained.
- Coefficient and scheme universes are independent u and t. The original small site remains object universe t+1, morphism universe t; module/ring size is max u (t+1). No equality of these universes is assumed.
- The invertibility assumptions are genuine geometric hypotheses: they fail in residue characteristic ℓ. They are not replaced by a unit condition on an identity morphism or another tautology.

Searches (2026-10-24):

- msearch LeanFinder: “The derived direct image on completed integral coefficient sheaves formed as the derived inverse limit of finite reductions commutes naturally with integer shifts”. Eight generic exact-functor/shift and unrelated category results; none gives this integral ambient realization.
- msearch Loogle: `CategoryTheory.Functor.CommShift, CategoryTheory.Functor.commShiftIso_zero`. No hits; the second qualified identifier was not recognized by the search server. The local Mathlib source `CategoryTheory/Shift/CommShift.lean` supplies the actual `CommShift.isoZero` definition.
- msearch grep: `integral.*DirectImage|sfDirectImage|rightDerivedFunctor.*CommShift`. No Mathlib hits.
- msearch LeanSearch: “The derived inverse limit of derived direct images of finite coefficient reductions commutes naturally with every integer shift”. Eight hits, including `Functor.instCommShiftDerivedCategoryMapDerivedCategoryInt` and generic exact-functor comparison instances, but no integral direct-image theorem.
- rg of both `lean/WeilConjectures` and `lean/Sheaf` for integral direct-image and shift names found the existing objectwise `SfDerivedDirectImage`, completed-ring direct image, and shift data for other interpretations. None states the present arbitrary-input reduction/limit realization theorem. The blueprint id has no upstream declaration hit.
- rg of Mathlib, both project roots, and `dag/lean_names_upstream.json` for all new declaration names found no collisions before writing the modules.

Validation: prescribed `scompile.py` compiled each of the two modules separately,
including their private dependency overlay and their final library names. Final
runs took roughly 2–3 seconds per file and returned no errors or unexpected warnings.
An initial universe metavariable failure came from the generic successor-universe
sheafification instance; disabling that instance uses the already recorded
`integralCoefficientAbSheafify` at max u (t+1), as the existing coefficient modules do.
No universe restriction or mathematical hypothesis was added to fix elaboration.

## New nodes

def-sf-ambient-integral-direct-image owns the canonical ambient realization and
its ten sfAmbient* declarations. Its source is latest blueprint
fix-cor-verdier-exchange.proof.md, Step 3, with the actual reduction/system-image/
limit construction spelled out in the item's accepted proof steps 1-4; Stacks
03CO, 03DA, 03D1, 0941 and 07A6 supply the named general constructions.
The existing SfIntegralDirectImage owns the individual-object Roos presentation
and remains imported from Sheaf.Paper.SfDerivedDirectImage, with all fifteen
landed declarations and its node record unchanged. The new node owns only the
additional functor on arbitrary ambient inputs. It explicitly cites
lem-coef-derived-system-evaluation-calculus in stmt_deps, as the definition
selects that theorem's .choose.reduction.

New-node searches on 2026-10-24: msearch LeanSearch query “Ambient integral derived
direct image constructed by derived reduction to coefficient systems, exact
restriction to completed-module towers, total right-derived tower direct image
and derived inverse limit” returned eight hits on module direct limits, adic
completion, scheme-module restriction, and condensed limits, none this functor.
msearch LeanFinder query “Canonical ambient integral direct image on unbounded
derived categories of completed coefficient sheaves through strict towers” returned
eight hits on local cohomology diagrams, derived-category fractions, and sheaf
cohomology, none this construction. msearch grep query
sfAmbientIntegralDirectImage|sfAmbientDerivedTowerPush|ambient.*[Ii]ntegral.*[Dd]irect
returned zero Mathlib hits. rg of the two names and the new node id in Mathlib,
lean/WeilConjectures, lean/Sheaf, and dag/nodes returned no hits.
tools/blueprint_refs.py search 'ambient integral direct image' returned zero
blueprint nodes. A broader prose search found RealizationLocalizedPush.lean:168,
a preservation predicate for a supplied realization, which does not define this
ambient functor. The new node records the search results and uses the ancestor
fix-cor-verdier-exchange and via chain returned by blueprint_refs.py ancestor.

The ring map is not arbitrary: `sfAmbientCoefficientMap_existsUnique` requires its
composite with every finite projection to be the sheafified constant-section map.
The definition selects that unique map. `sfAmbientModulePush` then uses the actual
sectionwise precomposition/restriction-of-scalars functor. `sfAmbientTowerPush`
applies it to an actual strict completed-module tower and its transition arrows;
`sfAmbientDerivedTowerPush` is its total right-derived functor on simultaneous
K-injective tower resolutions, using the existing tower-resolution instance.

Reduction is the reduction field of the existing coefficient calculus theorem.
This use of existence determines the needed functor up to natural isomorphism:
it is left adjoint to the fixed `coefficientSequenceLimit`, with the recorded
strict K-flat model and evaluated scalar-extension comparisons. It is not data
chosen from unconstrained existence. All other irrelevant fields of that calculus
are discarded. The resulting direct-image realization is used only up to natural
isomorphism, precisely the equality appropriate for a derived functor.

At finite evaluation, the reduction model is the derived tensor with the actual
finite quotient. After scalar restriction, the normalized completed ring square
identifies tower direct image with `Res_n Rf_{*,n}` of that tensor. Evaluation of
derived tower direct image agrees with derived evaluation/direct image because
constant-coefficient tower evaluation has an exact left extension. Compatibility
with quotient transitions comes from the single structural ring map and the actual
strict-system model, not from picking unrelated finite-level maps. Finally
`coefficientConstantTowerLimit` is the actual total derived inverse limit, whose
Roos triangle is the existing `IsDerivedLimitTriangle` presentation. Thus this
construction realizes exactly the stipulated ambient formula on arbitrary inputs.

The new node's clauses match its declarations: schemes, coefficient field and
independent universes are the explicit section variables; completed/finite sheaves
and projections are the existing imported constructions; sfAmbientRingPush
and sfAmbientFiniteRingMap give precomposition and the constant-section adjunct;
sfAmbientCoefficientMap_existsUnique gives exactly all finite projection
equations and uniqueness, and sfAmbientCoefficientMap selects that unique map;
sfAmbientModulePush gives canonical sectionwise scalar restriction and
sfAmbientModulePush_additive gives additivity; sfAmbientTowerPush and its
additive instance preserve actual tower transitions; sfAmbientDerivedTowerPush
is the total right derivation; sfAmbientIntegralDirectImage is exactly the
four-factor composite in the node. The positive exponent convention and arbitrary
unbounded ambient inputs are unchanged. At f = identity this realization includes
completion; it is not asserted to be the identity on noncomplete inputs.

The two helper theorems are the existence/uniqueness of the structural coefficient
map and additivity of its module direct image. They support this new definition node,
carry its blueprint id and full natural-language proof, and have `sorry` as their
whole proofs. All definition bodies contain actual constructions.

## Second reading by Q36

Author's separate rereading, not a claim of an independent agent review (the
assignment explicitly prohibits starting another agent and assigns independent
review to the maintainer). I reopened the node and the final two modules and
checked each row of the hypothesis/clause table. The comparison orientation is
shift-then-image to image-then-shift. `NatIso` supplies naturality on the derived
category itself. `isoZero` has the needed shift-zero endpoints and normalizes to
identity under their canonical identifications. Neither completeness nor boundedness
has entered the source type. The ambient construction retains actual tower maps,
uses completed rather than discrete integral coefficients, and preserves independent
universes. The old objectwise interface is still reexported. No statement dispute,
source correction or dropped clause was found. On the repair rereading I checked
the new definition node against all ten declaration signatures and their bodies;
the unique coefficient map, additive pushforward, actual tower transitions and
four-factor derived composite match clause by clause. Its stmt_deps explicitly
includes the chosen coefficient calculus, and the item cites the new node.

## Repair of returned head ea572efb6e3c

H13 is repaired by the maintainer's option (b). Removed the packet's copy of
def-weil-derived-direct-image.json, so delivery cannot overwrite the landed
Q29 record, primary declaration or fifteen names. The new §1(A) node
def-sf-ambient-integral-direct-image owns SfAmbientIntegralDirectImage.lean
and all ten sfAmbient* declarations, whose blueprint tags now name that node.
Its statement dependencies include lem-coef-derived-system-evaluation-calculus,
which supplies the selected reduction. The item gains only this new definition
node in stmt_deps; its theorem signature and its mathematical statement remain
exactly those independently accepted in the return. No dependency module is
replaced, and no landed API changes.
