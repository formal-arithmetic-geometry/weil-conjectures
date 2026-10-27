## Worker report

Item: `lem-pod-equivariant-mates-coefficient-transport`.
Module: `Sheaf.Paper.EquivariantMatesCoefficientTransport`.
All theorems have `sorry` proofs. All helper definitions contain real data. The node
changes only in `lean`; there are no new nodes, dependency repairs, or statement changes.

Source read: the current blueprint under `literature/blueprint/latest/`,
`sec-poincare-duality/sk-thm-frobenius/prop-weil-operations.proof.md` (the current
location of the node's older `sk-lem-finite` source), sentence concerning the induced
Weil structures, and the whole
`sec-six-functors/sk-rem-sf-pf-done/lem-fix-weil-operations.proof.md`.
The node's ten expanded proof steps are included in the declaration docstrings, split
across their corresponding clauses. No source correction is needed.

The main declaration `CategoryTheory.EquivariantMates.fixedPair_mate` and the other
listed declarations jointly state the item. Auxiliary `Square` packages the two
adjunctions and the given square; `FixedLift` packages precisely the supplied six
lifts, units, counits and equivariant square. It does not postulate an upstairs
adjunction or its triangle identities. `CoefficientComparison` packages the supplied
unit, counit and square compatibility using the dependency's existing comparison
interfaces. These are owning-node data helpers, not competing constructions of mates,
fixed-pair categories, or coefficient categories.

Hypothesis and clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Four arbitrary categories and their endofunctors | Independent `uA` through `uD`, `vA` through `vD`, category instances, and `PA`, `PB`, `PC`, `PD` in `fixedPair_mate`. No relation between object and morphism universes is imposed. |
| Fixed-pair objects and arrows | The recorded `CategoryTheory.Endofunctor.IsoAlgebra`, with `.carrier`, `.hom.f` and the inherited algebra intertwining equation. No new fixed-pair category is defined. |
| Two carrier adjunctions, units and counits | `Square.left₁`, `.right₁`, `.adj₁`, `.left₂`, `.right₂`, `.adj₂`. Units/counits are the specified adjunction fields. |
| Functors U and V, and alpha | `Square.horizontal`, `.vertical`, `.square : TwoSquare horizontal left₁ left₂ vertical`. The orientation is `U ⋙ L₂ ⟶ L₁ ⋙ V`. |
| All six functors have specified lifts | The six functor fields of `FixedLift`, with six `_over` equalities of composites with the recorded forgetful functors. These are strict carrier equalities, not unspecified natural isomorphisms. |
| The specified units and counits lift | `FixedLift.unit₁`, `.counit₁`, `.unit₂`, `.counit₂` and their four `_over` component equations. HEq only accommodates endpoints that become equal via the strict carrier equalities. |
| Alpha induces fixed-pair morphisms | `FixedLift.square`, already a natural transformation in fixed pairs, and `.square_over` prescribing its carrier. |
| Mate is natural upstairs and its carrier is the specified three-factor composite | `fixedPair_mate` supplies the two upstairs adjunctions with the exact supplied unit/counit fields; `mateEquiv a₁ a₂ W.square` is the upstairs natural mate. Its last clause identifies every carrier with `eta₂ ≫ R₂(alpha) ≫ R₂(V(epsilon₁))`. HEq expresses the exact map after strict endpoint identification, not equality modulo an isomorphism. |
| Pasting on the non-adjoint sides | `fixedPair_mate_pasting`, using the exact `mateEquiv_vcomp` orientation on fixed-pair categories. |
| Composition of adjunctions | `fixedPair_mate_adjunctionComposition`, using `Adjunction.comp` and `mateEquiv_hcomp`. The composite unit/counit are the dependency's specified formulas. |
| Changing either adjunction by a transformation | `fixedPair_mate_changeSecond` and `fixedPair_mate_changeFirst`, with `conjugateEquiv` and the respective `whiskerBottom`/`whiskerTop` equations. |
| p, a, q, k₀, k and p different from ell; finite-type geometric fibres | In `ArbitraryWeilStructures`, `D₀ : FiniteFieldDatum`, prime `l`, `hl : l ≠ D₀.p`, four `Over (Spec (.of D₀.k₀))` objects with `LocallyOfFiniteType` and `QuasiCompact`, and their actual `D₀.geometricFiber`. No separatedness is added. |
| E is a finite ell-adic coefficient field, and a fixed algebraic closure for common stages | `E : Type u`, field/algebra/finite-dimensional instances; `Ω : Type v` with `IsAlgClosure (Padic l) Ω`; finite stages use the recorded `AlgebraicallyClosedCoefficients.Index l Ω` and its actual coefficient models inside this closure. The closure universe is independent of the scheme universe. |
| The stipulated constructible coefficient categories and geometric Frobenius | `rational_weil_mate` uses `sfRationalConstructibleCategory`, `sfWeilFrobeniusPullback`, `sfWeilComplex`; `commonStage_weil_mate` uses `generalAlgebraicallyClosedConstructibleCategory`, `sfCommonStageWeilFrobeniusPullback`, `sfCommonStageWeilComplex`. |
| Coefficient comparisons intertwine units, counits and alpha | `CoefficientComparison.adj₁`, `.adj₂` are `ExchangeProjectionAdjunctionComparison`; `.square` is `ExchangeProjectionComparisonPreserves` for the actual composite comparisons. |
| Comparisons are identities for identity extensions and satisfy the tower cocycle | `compositeComparison_cocycle` takes the recorded `ExchangeProjectionScalarCocycle` for the two factors and concludes the same property for their actual composite. Applied to the mate source R₁ then U, target V then R₂, and iterated for intermediate vertices, it gives exactly identity/tower normalization. Both structure fields, `identity` and `composition`, are retained. |
| Rational image of an integral mate equals mate of the rational images | `rational_mate_exact` is the literal three-factor identity for `sfRationalConstructibleLocalization`; `rational_mate_coefficientTransport` identifies it with the stipulated rational mate using the supplied operation comparisons. |
| Finite-field transport equals the new mate conjugated by supplied endpoint comparisons | `finiteExtension_mate_coefficientTransport` uses the actual `GeneralAlgebraicallyClosedCoefficients.stageTransition`. `CoefficientComparison.source` and `.target` are constructed from the supplied functor comparisons by `compositeComparison`; they are not free isomorphisms. The equation is `source.inv ≫ T.map oldMate ≫ target.hom = newMate`. |
| Same identities for pasted mates | The four fixed-pair pasting identities above, together with `pasted_coefficientTransport` (cancellation for three successive factors, iterable for every displayed pasted composite) and `mate_coefficientTransport` applied to each pasted square. These statements apply also when the category itself is a fixed-pair category. |
| Common-stage class of a finite-stage mate | `commonStage_mate_coefficientTransport` uses the actual recorded stage-inclusion functors and the same prescribed source and target comparisons. |
| Independence of field and morphism representative | `commonStage_mate_representatives` quantifies over two arbitrary common stages and representatives that become equal after further transport, and states the mate naturality equation across these representatives. `commonStage_mate_coefficientTransport` identifies the finite-stage mate with that fixed common-stage transformation, and the cocycle theorem identifies iterated transport with direct transport. The definition of `ofHom` and `transport` is imported unchanged. |
| Every localized/common-stage morphism and every Weil structure, without stable integral lattice | The two `*_weil_mate` statements quantify over all objects of the recorded Weil categories and every morphism between them. Their `W` is any supplied lift on those categories; no integral representative or integral inverse is required. `commonStage_mate_representatives` also quantifies over every carrier arrow, not only a stage inclusion. |
| Invertible carrier has its actual inverse as a fixed-pair arrow | `fixedPair_inverse` quantifies over every fixed-pair morphism with `[IsIso f.hom.f]` and produces `g` with `g.hom.f = inv f.hom.f` and both inverse identities. This includes every lifted mate and comparison. No unconditional invertibility claim occurs. |

The general comparison identities are formal data calculations on arbitrary categories;
the concrete coefficient declarations specialize them to the actual recorded coefficient
categories and canonical localization, scalar transition and inclusion functors. They
introduce no alternative operations. Operations and comparisons remain supplied on their
stipulated closed domains, as in `def-exchange-projection`. The result never asserts that
such data exist for arbitrary bounded constructible operations.

Dependency declarations read and used:

- `def-weil-endofunctor-fixed-pair-category`: module
  `WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra`,
  `CategoryTheory.Endofunctor.IsoAlgebra`, `.forget`, `.carrier`, `.str` and the inherited
  full-subcategory morphisms. The upstream adjunction lift was also inspected: it is
  specialized to commutation-isomorphism lifts and does not state this arbitrary-lift
  mate/coefficient theorem.
- `def-weil-pbc-adjunction-mate`: Mathlib's
  `Mathlib.CategoryTheory.Adjunction.Mates`, `CategoryTheory.mateEquiv`; its full
  three-factor construction, not an unnamed equivalent natural transformation.
- `lem-weil-pbc-mate-pasting`: the same Mathlib module's `mateEquiv_vcomp`,
  `mateEquiv_hcomp`, `mateEquiv_conjugateEquiv_vcomp`,
  `conjugateEquiv_mateEquiv_vcomp`, and `Adjunction.comp` from its imported Basic module.
- `def-exchange-projection`: module `Sheaf.Paper.ExchangeProjectionSuppliedDomains`,
  `ExchangeProjectionAdjunctionComparison`, `ExchangeProjectionComparisonPreserves`,
  `ExchangeProjectionScalarCocycle`. Its supplied-domain stage and actual exchange and
  projection composites were read; the theorem does not impose their invertibility.
- `def-weil-derived-pullback-tensor-hom`: module `Sheaf.Paper.DerivedPullbackTensorHom`,
  the recorded rational/common-stage derived pullbacks used by the Frobenius definitions,
  and the supplied coefficient comparisons; the recorded main internal-Hom declaration
  and its docstring were read. The formal theorem applies to these supplied operation
  functors, including tensor/Hom and their specified admissible domains.
- `def-weil-finite-field-fiber`: module `Sheaf.Paper.FiniteFieldFiber`,
  `WeilConjectures.FiniteFieldDatum` and `.geometricFiber`.
- `def-weil-weil-sheaf-complex`: module `Sheaf.Paper.SfWeilSheafComplex`, all six rational
  and common-stage fixed-pair/Frobenius/forgetful declarations; the specialized statements
  use the recorded rational and common-stage Weil categories directly.
- Proof-only coefficient dependencies: `Sheaf.CategoryTheory.ScalarLocalization`,
  `Sheaf.Paper.SfRationalizationKaroubi`, and
  `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`. The actual
  `sfRationalConstructibleLocalization`, `stageTransition`, `inclusion`, `StageHom`,
  `transport`, `ofHom`, and `representatives` were read. No scalar-localization or
  common-stage quotient construction is copied.

Edge cases checked before and during writing: identity adjunctions give alpha itself;
identity scalar extensions are retained by `le_rfl` and the cocycle identity field;
three successive extensions use the actual transition associators; empty and zero
categories impose no hidden nonemptiness/nonzero hypothesis; an empty scheme is allowed;
all morphisms in raw rationalization and in common-stage Hom quotients are quantified;
a Weil structure need not be invertible integrally. With identity endofunctors and
identity structures on a nonzero vector space, the zero map is equivariant but not an
isomorphism: the final theorem correctly requires an invertible carrier. All category
object/morphism universes in the abstract statements are independent.

Searches actually run (recorded by `msearch.py` in `searches.jsonl`):

- LeanFinder: “Adjunction mates in endofunctor fixed pair categories commute with
  rationalization and common finite coefficient extension” returned 8 generic mate and
  conjugacy lemmas, beginning with `mateEquiv_apply`, `mateEquiv_counit`, `mateEquiv`.
  None states the fixed-pair/coefficient result.
- Loogle: `CategoryTheory.mateEquiv, CategoryTheory.Endofunctor.IsoAlgebra` returned
  “unknown identifier 'CategoryTheory.Endofunctor.IsoAlgebra'”; the upstream fixed-pair
  name is not indexed by that Mathlib service. This is not reported as evidence of absence.
- Mathlib grep: `mateEquiv|IsoAlgebra|coefficientTransport` under
  `CategoryTheory/Adjunction` returned five generic mate hits in `Mates.lean`.
- LeanSearch: “Equivariant adjunction mates commute with scalar extension and
  rationalization in fixed pair categories” returned 8 generic mates and module
  change-of-rings lemmas, no exact match.
- `rg` of the named upstream and project directories for the item id, fixed-pair mates,
  and mate/transport expressions found general upstream IsoAlgebra adjunction lifting,
  specialized geometric transport calculations, and the existing coefficient interfaces.
  The complete module combining this item's clauses did not exist. The item-id search
  in upstream Lean found no declaration.

Compilation: all delivered declarations compile in module mode with `autoImplicit false`
through the required `scompile.py`; both its sandbox and public-module passes are clean.
No proofs were supplied, and no extra assumptions about stable lattices, perfectness,
separatedness, or invertibility of arbitrary comparisons were introduced.

## Second reading by O1

The dispatcher brief forbids additional agents and assigns the independent delivery review
to the maintainer. This section records this worker's second reading, not a claim that
another worker reviewed it.

Re-read the full node against the final module. Checked all six strict lift equations,
the unit/counit carrier equations, and alpha's orientation. The fixed-pair mate conclusion
uses the actual three factors in the specified order and retains both supplied unit and
counit fields. Checked the two Mathlib pasting orientations (`≫ₕ` and `≫ᵥ`) against
`Mates.lean`; these require opening `CategoryTheory.TwoSquare`, which was added after the
first parser check. The source/target coefficient comparisons expand as
`U'(c_R₁) ∘ c_U` and `R₂'(c_V) ∘ c_R₂` in conventional composition order; thus the
transport equation has source inverse on the left in Lean's diagrammatic notation.
The common-stage hypotheses and conclusion use the existing eventual-equality relation,
not equality of representatives at their original fields.

The second pass added the literal `rational_mate_exact` formula and the two concrete
`rational_weil_mate`/`commonStage_weil_mate` statements to make exact rationalization and
the unrestricted Weil structures explicit. Checked their finite-type and distinct-prime
parameters, geometric Frobenius definitions, and arbitrary object/morphism quantifiers.
Rechecked all docstrings, signature metadata, line widths and explicit universes. No node
fault, source discrepancy, or STATEMENT-DISPUTED issue remains.
