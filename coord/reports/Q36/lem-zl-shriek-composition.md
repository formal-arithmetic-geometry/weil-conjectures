## Worker report

The delivery states `WeilConjectures.zlWeilShriekComposition` in
`Sheaf.Paper.WeilShriekComposition`. Its conclusion is a natural isomorphism on the
full underlying common-stage Qbar constructible categories, together with an equality
of natural transformations expressing compatibility with the canonical geometric
Frobenius exchanges. It therefore induces a natural isomorphism on the recorded
Weil fixed-pair categories, including the inverse Weil-morphism equation.
Every theorem in the delivery has proof `sorry`; definitions have actual data.
The original item's statement, proof, source, and all non-Lean fields are unchanged,
except that `stmt_deps` gains the new definition described below.

Clause-by-clause reading of the item:

- The global finite-field convention is `(D : FiniteFieldDatum.{u})`; this retains
  the prime p, positive exponent a, q, finite k0, and its chosen algebraic closure k.
  `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)` is the permitted coefficient prime.
  `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]` is Qbar.
  Universes u and v are independent.
- `X₀ Y₀ Z₀ : Over (Spec (.of D.k₀))` are the three schemes over k0.
  Each has `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact` on its structure
  map. These are exactly separated finite type; none of the three schemes is omitted.
- `(f₀ : X₀ ⟶ Y₀) (g₀ : Y₀ ⟶ Z₀)` are composable morphisms over that same field.
  For each, the three classes on `.left` express separatedness and finite type.
  The composite is `(f₀ ≫ g₀)`, in Lean's diagrammatic order.
- `cf`, `cg` and `cfg` are arbitrary compactifications of those three morphisms.
  They are construction choices, universally quantified, not additional geometric
  conditions: Nagata applies to separated finite-type maps of these Noetherian
  schemes. The conclusion includes every choice, also choices unrelated to one
  another. No compactification or coefficient action is assumed compatible with
  composition, and no Frobenius-equivariance hypothesis is supplied by the caller.
- `zlCommonStageShriek` is open extension followed by proper derived image on the
  actual category C_Y of common-stage coefficient pairs. Its underlying operation
  is naturally identified with the recorded compact-support action on all maps by
  `zlCommonStageShriek_recorded`. We do not identify the different pbc pair-category
  encoding with C_Y. This follows the explicit coefficient clarification in the
  item's proof and review record.
- `∃ β : ... ≅ ...` gives `R(gf)! ≅ Rf! ⋙ Rg!`, meaning `Rg! Rf!` in the paper.
  A natural isomorphism of functors includes naturality on every underlying complex
  and morphism, not only on objects already carrying a Weil structure.
- The remaining equality is
  `(β ▷ F_Z) ≫ e_iterated = e_composite ≫ (F_X ◁ β)`.
  At K this reads `F_Z(β_K) ≫ e_iterated,K = e_composite,K ≫ β_(F_X K)`.
  Compose with the image of theta_K and use naturality of β. The result is exactly
  `theta_composite ≫ β_K = F_Z(β_K) ≫ theta_iterated`, the node's Frobenius
  compatibility in diagrammatic order. Invertibility gives the inverse equation.
  `zlShriekCompositeFrobenius` explicitly composes the two exchanges, so it is the
  iterated Weil structure specified by the node, not another Frobenius action.

Recorded declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `geometricFiber`.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilComplex`,
  `sfCommonStageWeilFrobeniusPullback`, `sfCommonStageWeilForget` and the inherited
  invertibility construction. Fixed pairs here are not the upstream derived
  category of Weil sheaves.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory` and its actual stage system.
- `Sheaf.Paper.WeilIndSheafCategory`: `zlFiberMap`, `zlPull`,
  `zlFrobeniusSquare`, `zlPullComp`, `zlStagePullIso` and their normalized integral
  characterizations. Only their common-stage inverse images and squares are used;
  the ind-category and its heart adjoints are not substituted for derived complexes.
- `Sheaf.Paper.WeilCompactSupportCohomology`: `zlCompactificationOpen`,
  `zlCompactificationProper`, their middle-scheme finite-type instances,
  the geometric-fibre structure/base-change instances, and `zlClosurePrimeUnit`.
- `Sheaf.Paper.QcqsCompactSupportRealization` and its reexported
  `IntegralRationalQbarCompactSupport`: the recorded compact-support values and
  `sfQcqsCompactSupportRealization`. `CompactSupportCoefficientAction` supplies
  `SfCompactSupportCoefficientAction`, `system` and its descended `functor`.
  The comparison uses this complete normalized functor interface, not only values.
- `Sheaf.Paper.PbcQbarCategory`: `AlgebraicGeometry.Scheme.pbcQbarCategory` was
  read and its module is imported as an original statement dependency; it is the
  separate convention mentioned in the proof, not a second carrier for this theorem.
- `def-weil-pbc-scheme-conventions` explicitly introduces no declaration. Its
  Mathlib classes `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact` are used.
- `Mathlib.CategoryTheory.Adjunction.Basic`: `Functor.IsLeftAdjoint`,
  `Functor.IsRightAdjoint`, their selected adjoints and `Adjunction.ofIsLeftAdjoint`
  / `ofIsRightAdjoint`; uniqueness of adjoints supplies the permitted universal
  determination of their data.
- `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates` and Mathlib's mates:
  `mateEquiv` / its inverse, specifying the actual proper/open comparisons.
  `CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso` gives the optional fixed-pair
  functor using those specified exchanges.

Proof dependency imports: `prop-functor-package` has the upstream recorded module
`WeilConjectures.WeilSheaf.LowerShriekFunctoriality`, imported privately as required.
Its presently recorded base-change declaration is not a finished Qbar composition
statement and is not asserted to prove this theorem. `lem-fix-weil-operations` has
no published Lean declaration, so no module can yet be imported for it. The source
proof is retained verbatim in mathematical content in the docstring. All statements
remain postponed; this delivery does not claim a stage-3 proof from those records.
The Mathlib separated/finite-type base-change leaves are available through the
geometric-fibre dependency imports. No import cycle is introduced.

Edge cases checked before writing and again on rereading: either map an identity;
empty X0, Y0 or Z0 whenever such a morphism exists; zero complexes; both maps proper;
both maps open; an open followed by a proper map; target Spec k0; arbitrary finite
extension degree of the finite base field; independent coefficient universe; and
all compactification choices. The proper and open mates reduce to the usual unit
comparisons in the identity cases. No nonempty scheme, finite Frobenius orbit,
finite-Tor assumption, cohomological degree, weight or smoothness hypothesis occurs.
The coefficient prime condition excludes exactly the residue characteristic.

Searches for the item (msearch.py, Q36 / lem-zl-shriek-composition):

- LeanFinder: "For composable separated finite type morphisms over a finite field,
  derived exceptional direct images compose naturally compatibly with Frobenius".
  Eight results, including ideal-sheaf map_comp, affine-space map_comp and finite-map
  composition. No exceptional direct-image or Weil fixed-pair comparison.
- Loogle: `"shriek", "comp"`: zero results.
- Mathlib grep: `lowerShriek.*[Cc]omp|[Cc]omp.*[Ss]hriek` in AlgebraicGeometry:
  zero results.
- LeanSearch: "Derived exceptional direct image composition isomorphism compatible
  with Frobenius": eight results concerning field Frobenius, Witt-vector
  isocrystals, ordinary sheaf/module pushforward and derived-zero comparison.
  No matching statement.
- Source rg for shriek/composition, `lem-zl-shriek-composition`, and declaration
  names: the upstream `DeligneLaumon.Reduction.FormalSteps` mentions the item in
  the docstring of a Leray filtration theorem; it does not state composition.
  Upstream `WeilComplex.derivedLowerShriek` uses the excluded derived-of-Weil-sheaves
  construction. Side-library searches found finite-level etale-origin composition,
  integral/qbar coefficient action and higher Weil-heart images; none states this
  full common-stage comparison with its Frobenius natural-transformation equation.
  All existing components are reused.

No false or ambiguous source statement was found. No statement correction or
STATEMENT-DISPUTED flag is needed.

## New nodes

`def-zl-common-stage-weil-shriek` introduces the missing full common-stage
compact-support functor with its specified Frobenius exchange. Source: the first
paragraphs of `lem-fix-weil-operations.proof.md` in main-20261015, and the proper/open
construction SGA 4 XVII §5--6 used by `lem-zl-shriek-composition`. Its adjoints are
selected from their universal properties, which determine the operations up to
compatible isomorphism. Comparisons are actual mates of the existing normalized
square. No unconstrained map or choice from a mere Nonempty is used.

The definition's clauses match its module as follows. `zlPull_proper_isLeftAdjoint`
and `zlPull_open_isRightAdjoint` assert the two constructible adjoint existence
clauses. `zlCommonStageProperPush` / `ProperAdjunction` and
`zlCommonStageOpenShriek` / `OpenAdjunction` expose the chosen adjoints with their
units and counits. `zlProperFrobeniusMap` is the right mate of the inverse
pullback square. `zlOpenFrobeniusInverseMap` is its left-mate counterpart.
Their two named `_isIso` theorems are precisely the node's invertibility clauses;
`zlProperFrobenius` and `zlOpenFrobenius` wrap those actual maps, with the inverse
for the open one. `zlCommonStageShriek`, `zlShriekFrobenius` and `zlComplexShriek`
are the proper/open composite, its composite exchange, and its explicit lift to
the existing fixed pairs. `zlCommonStageShriek_recorded` is the all-objects,
all-morphisms comparison with the normalized existing coefficient action for
every geometric compactification. `zlShriekCompositeFrobenius` is the iterated
exchange, with its associators. Each postponed theorem has a separate proof
paragraph in its docstring, and every one is an explicit clause of this DAG node.

Additional searches for this definition: LeanSearch queried "Exceptional direct
image functor on Frobenius fixed pairs is open extension followed by the proper
pushforward adjoint to inverse image" (eight ordinary sheaf/module adjunction
results). LeanFinder queried "Right adjoint and open immersion left adjoint of
pullback on constructible Weil complexes fixed pairs" (eight ordinary module
adjunction results). Mathlib grep `Weil|IsoAlgebra|[Ss]hriek` in AlgebraicGeometry
had zero results. Exact declaration-name searches across Mathlib, upstream source,
the upstream name index and lean/Sheaf had no matches. Searches for common-stage
pullback adjoints in lean/Sheaf/Paper had no matches. DAG searches and full reading
found the two existing zl ind-heart / higher-image definitions and the normalized
coefficient-action definition; these are dependencies, not duplicated notions.
`blueprint_refs.py search 'Weil compact support'` gave zero blueprint matches;
its ancestor command specifies `lem-zl-shriek-composition` for this new node.
All search records are retained in the node, with tools, queries and outcomes.

The new node is directly cited by the item's added statement dependency. Existing
nodes, including the original five statement dependencies, are unchanged.

## Validation

Both modules compiled separately, in dependency order, through scompile.py with
only postponed theorem proofs. A first compiled draft stated only a natural
isomorphism of fixed-pair functors; rereading detected that this did not explicitly
retain the underlying natural comparison on every complex. The final statement
uses a natural isomorphism on the full coefficient categories and its exchange
square, with the proper/open mate construction fixing both Weil actions.
The first dry run found only the blueprint ancestry metadata convention: because the
item is itself the blueprint ancestor, the new node's `blueprint.from.via` must be
empty. This metadata was corrected. The final dry run checks the complete packet.

The repaired dry run returned `OK (dry run): commit 60c40b11cf passes the preflight
and compiles; nothing pushed`. Both delivered modules were checked separately
through scompile.py, with no errors or unexpected warnings.

## Second reading by Q36

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
