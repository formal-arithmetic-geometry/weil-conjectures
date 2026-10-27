## Worker report

The module `Sheaf.Paper.ConstantPurityFrobeniusSquare` states
`WeilConjectures.ConstantPurityFrobenius.constant_purity_frobenius_square`.
Its conclusion is the transparent predicate `Square`, containing the three asserted
morphism equalities. Every theorem proof is `sorry`; definitions contain real
constructions. Helpers belong to the canonical maps specified by this item and are
all listed in `lean.declarations`. No independent coefficient category, Tate line,
Weil-pair category, exceptional operation or purity map is introduced.

The current item has Q47's accepted stage-1 proof split but no stage-2 Lean binding.
This delivery preserves that statement and proof. The previous unchanged-node
preflight failure does not apply to the new Lean binding.

### Hypotheses and objects

- `P : PurityFiniteSetting.{u}` supplies the recorded finite-field datum, the prime
  `P.coefficients.l`, its primality instance, `P.coefficients.different : l ≠ p`,
  and the fixed algebraic closure `P.coefficients.Qbar` of `Padic l`. Its finite
  subextension and positive level are the existing purity presentation data.
- `X₀ : Over (Spec (.of P.field.k₀))` is the specified arithmetic scheme and
  structure map. `LocallyOfFiniteType X₀.hom`, `QuasiCompact X₀.hom` and
  `IsSeparated X₀.hom` express finite type and separatedness. `d : ℕ` includes
  dimension zero and `[SmoothOfRelativeDimension d X₀.hom]` is precisely the
  prescribed smoothness and relative dimension.
- `point` is the identity arithmetic model of Spec k₀, and `pointMap` is X₀'s
  actual structure morphism in Over. Its geometric fibre is the pullback of the
  identity. `pointIso` exhibits its canonical isomorphism with Spec k by the
  second projection. Thus the geometric point used in the formulas is the
  canonical pullback presentation of the named s, not a separately chosen scheme
  or an arbitrary isomorphic substitute. `FrobeniusExchange.fiberMap D f₀` is the
  existing actual geometric base-change map; no duplicate map is defined.
- `c₀ : Compactification X₀.hom` presents the compact-support operation. Its
  geometric compactification is the recorded `geometricCompactification` and
  retains its middle arithmetic Frobenius. `S : systems ... X₀` is the existing
  normalized `ConstructibleExceptionalCoefficients.System` for that geometric
  map, as used by the purity declaration. It is operation presentation data,
  not an arbitrary functor, exchange or purity isomorphism. Every finite-type,
  separatedness, over-base, smooth-base-change and coefficient-invertibility
  instance used in `systems` and `Square` is explicitly inherited from the
  hypotheses and existing base-change results; no additional geometric binder is
  imposed by the main theorem.
- `sourceFrobenius` and `targetFrobenius` are the recorded common-stage Frobenius
  pullbacks. `operation ... .closed` gives F, G and their actual adjunction.
  `source` is the recorded `RationalSmoothPurityCanonical.commonSource`: its
  shifted Tate line is on the left of the tensor product, the canonical
  symmetry/shift presentation of H(K) = La* K(d)[2d].

### Each asserted clause

1. Constants: `unit` is only the literal least-stage carrier of the recorded
   constant pair, using `constantWeilRationalObject`; the structures are the
   actual `.str` fields of `constantWeilAlgebraicallyClosedComplex` on X₀ and
   the arithmetic point. `chainUnit_existsUnique` fixes the unit at every
   finite quotient by its actual constant generator and fixes the zero second
   Roos coordinate. Thus `chainUnit` is selected from a unique specification,
   not a mere existence assertion. `integralUnit`, `rationalUnit` and
   `commonUnit` respectively use the prescribed good-representative comparison,
   actual scalar localization and finite-stage inclusion. The first conjunct
   of `Square` is `t.hom ≫ a*.map θ₀.hom ≫ u.hom = Q.map u.hom ≫ θX.hom`,
   exactly the constant-pullback intertwining identity.
2. The map b: `sourceSquare` composes the canonical pullback tensor comparison
   with `shiftedLineTheta` and `podCommonSquarePullbackComponent` for
   `zlFrobenius_naturality`. `shiftedLineTheta` is finite-stage identification,
   the prescribed pullback/shift comparison and the actual normalized
   `rationalDerivedLineMap`. It introduces no adjustable scalar.
   `sourceUnit` is the tensor of the identity on the shifted line with u.
   `canonicalSourceTheta` conjugates the tensor of the actual shifted line
   Frobenius and θX through `sourceUnit`. The second conjunct is literally
   `θH.hom = b.hom ≫ H.map θ₀.hom`, so it expresses the canonical twisted and
   shifted structure on the identified constant, not a structure defined as the
   desired right-hand side.
3. Compact-support exchange and mate: `rationalBeta` conjugates the actual
   `frobeniusRational` proper/open exchange by `S.ring.rationalLeft`.
   `rationalExchange_endpoints` records the equality of its two presentations
   (the compact recipe literally uses that fixed compact-support functor).
   `betaAtStage` further conjugates by the recorded common-stage coefficient
   comparisons and Frobenius stage identifications. `beta_existsUnique` fixes
   *every* finite-stage component, and `beta` is selected only from this unique
   normalization. Thus beta cannot be selected from purity or from a bare
   Nonempty type. `exceptionalMate` is Mathlib's `mateEquiv` applied to beta's
   inverse, under the actual F ⊣ G adjunction on both sides. Its invertibility
   is stated in `exceptionalMate_isIso`, and `exceptionalIso` is `asIso` of that
   very natural transformation. In `Square`, e is this isomorphism and γ is
   directly `RationalSmoothPurityCanonical.commonIso P a c S d K`, not a
   quantified or newly chosen purity map. The third conjunct reads
   `Q.map γ.hom ≫ e.hom.app K ≫ G.map θ₀.hom = θH.hom ≫ γ.hom`, with exactly
   the order and endpoints in the node.
4. Dualizing normalization: γ is the published canonical commonIso, whose
   implementation uses the integral trace transpose, the recorded small-model
   scalar equivalences and the actual exceptional coefficient comparison.
   This is the purity of `thm-pur-rational-and-qbar-purity`; its inverse at the
   coefficient unit, under the usual unit/Tate source identifications, is the
   dualizing identification of the recorded corollary. The statement never
   permits substitution of another purity isomorphism or of a scalar multiple.
   The last sentence of the node specifies which γ is used; it is rendered by
   this direct canonical declaration, rather than by a free γ binder.
5. The conclusion is in `generalAlgebraicallyClosedConstructibleCategory`,
   not cohomology groups. There is no stable-lattice hypothesis on an arbitrary
   rational Weil pair. Only the explicitly constructed coefficient-unit lattice
   is used to construct u and the recorded constant structures.

### Dependency declarations read and used

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilComplex`,
  `sfCommonStageWeilFrobeniusPullback`, `sfWeilFrobeniusPullback`,
  `sfWeilStagePullbackIdentification`, `sfWeilPrimeInvertible`.
- Mathlib Smooth/Etale: `AlgebraicGeometry.SmoothOfRelativeDimension`,
  `smoothOfRelativeDimension_isStableUnderBaseChange`; ordinary base change
  through `MorphismProperty.overPullbackMap` and `baseChange_obj`.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `CategoryTheory.mateEquiv`.
- `Sheaf.Paper.RationalSmoothPurityCanonical` and its recorded source transports:
  `RationalSmoothPurityCanonical.commonSource`, `commonShiftedLine`, `commonIso`.
- `Sheaf.Paper.ConstantWeilStructure`: `constantWeilAlgebraicallyClosedComplex`,
  `constantWeilIntegralComplex`, `constantWeilIntegralGood`,
  `constantWeilRationalObject`, and the strict pullback Roos/generator APIs.
- `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical`:
  `FrobeniusCoefficientTwists.rationalDerivedLineMap`.
- `Sheaf.Paper.DerivedPullbackTensorHom`, `DerivedPullbackTensorIso`,
  `FieldWeilShriekShiftData`, and `SemilinearFieldOperationLifts`:
  the actual integral/rational/common-stage pullbacks and their object
  normalizations, `canonicalCommonStagePullbackTensor`, the prescribed
  pullback/shift instances and `podCommonSquarePullbackComponent`.
- `Sheaf.Paper.FrobeniusGeometricExchange`: the exact signatures and docstrings
  of `geometricCompactification`, `frobeniusCompactModel`, `frobeniusRational`,
  `fiber_finiteType`, `fiberMap_properties`. Its public import
  `Sheaf.Paper.FrobeniusSquareExchange` supplies `FrobeniusExchange.fiberMap`,
  defined as `zlFiberMap D f₀` and owned by
  `def-weil-operation-exchange-coefficient-descent`.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData`:
  `ConstructibleExceptionalCoefficients.System`, `.ring.operation`,
  `.ring.rationalLeft`, `.common.commonComparison`, and `commonField`.
- `Sheaf.Paper.AdicSmoothDualizingComplexes`: `AdicSmoothDualizing`'s canonical
  integral/rational/common-stage identifications. The main declaration uses
  their same trace-normalized purity realization, as explained above.

The two already-landed definition nodes `def-weil-frobenius-square-exchange` and
`def-weil-operation-exchange-coefficient-descent`, owning the actual exchange and
geometric map, are added to `stmt_deps`. No new node or dependency replacement is
needed. The stated proof dependencies that have published modules are imported
for the later proof, including constant-ring composition and completed-tower
substitution. Unstated proof nodes are not imported as nonexistent modules.

### Edge cases

- d = 0: the shift is 0 and the Tate line has exponent 0; the canonical maps
  remain the same specified unit and identity constraints.
- Empty X₀: all constant sheaves on the empty site and their unit maps are the
  unique zero objects/maps; the statement does not require a point or nonempty
  source. The strict generator normalization still determines the unit map.
- X₀ = Spec k₀ and a₀ = identity: the canonical pullback and unit comparisons
  are retained, and there is no extra Frobenius scalar.
- A disconnected smooth source is allowed; only pure relative dimension d is
  required. There is no connectedness, properness or projectivity binder.
- The excluded characteristic case is exactly `l ≠ p`; all positive coefficient
  levels in the Roos tower have the actual quotient transition maps. Rational
  Weil structures are used after localization, never reduced modulo a uniformizer.
- No independent small site/coefficient universe equality is assumed. The main
  input uses the recorded `PurityFiniteSetting.{u}` size convention; increasing u
  accommodates every such finite-field and algebraic-closure presentation.

### Searches and verification

Read the item, all original statement dependencies and their full used declaration
signatures/docstrings, Q47's split report, and both indicated main-20261015 proof
sources. Also read both added exchange-node statements and their recorded APIs.

- `msearch.py ... leanfinder`: "Canonical constant Tate sheaf smooth purity
  isomorphism commutes with geometric Frobenius and exceptional adjunction mate".
  Returned generic sheaf-module unit/pullback/adjunction lemmas, no exact match.
- `msearch.py ... loogle`: `"tateTwist"`; zero hits.
- `msearch.py ... grep`: `constantPurity|constant_purity|purity.*[Ff]robenius|[Ff]robenius.*purity`;
  zero exact matches.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, including an exact item-id
  search: no declaration states this constant/Tate comparison and rational
  adjunction-mate purity square. Nearby finite-coefficient Frobenius purity/trace
  declarations do not identify all the canonical rational maps of this item.
- Searches of the recorded source names led to the existing compact-support
  exchange, its explicitly typed geometric map and the canonical purity/constant
  declarations; these are reused without private copies.

Every compiler invocation used the prescribed scompile wrapper. Separate module-mode
component probes diagnosed endpoint elaboration; the complete delivered module then
compiled in both sandbox and library mode with no warnings. No global build or
read-only source mutation was performed. No statement correction or unresolved
statement dispute is needed.

## Returned-delivery repair

Addressed the H2 return on immutable head `b155e388dad9`: every use of
`PodFrobeniusExchange.fiberMap D X₀ Y₀ f₀` now uses the definition-owned
`FrobeniusExchange.fiberMap D f₀`, with the corresponding specialization at the
arithmetic point. Removed the `FrobeniusCompactSupportExchange` import and the
`lem-pod-weil-frobenius-compact-support-exchange` statement dependency; its theorem
conclusion was never used. Added the owning definition node
`def-weil-operation-exchange-coefficient-descent`. Read the map's full declaration
and docstring in `FrobeniusSquareExchange`: it is `zlFiberMap D f₀`, the same
`Over.pullback` map as the removed alias. `FrobeniusGeometricExchange` publicly
imports that definition module. The main theorem signature, all three equality
clauses, canonical maps, hypotheses and accepted edge cases are unchanged.

The advisory about reusing `frobeniusCommonStage` is optional; the previously
reviewed unique finite-stage normalization of beta is retained.

## Repair self-check (2026-10-22)

Inspected the retained packet before running the prescribed dry run. That first
run failed elaboration after the alias replacement: the default transparency
setting prevented use of inherited instances through `zlFiberMap`. Set both
backward definitional-equality transparency options to false, as in the owning
map and purity modules. The remaining failure at `commonIso` was instance search
through the local abbreviation `D := P.field`; supplied its existing base-change,
prime-invertibility and map-property proof arguments explicitly. These are the
same inherited proofs already used in `Square`, with no new hypothesis, map,
coefficient object or conclusion.

Rechecked the current base and saved node: only `lean` and `stmt_deps` differ;
the latter adds the two landed definition nodes named above. The removed theorem
is absent from the delivered dependency list and Lean imports, and every
geometric-map occurrence in the module is `FrobeniusExchange.fiberMap D f₀`
(or its specialization at `pointMap`). The declaration signature is verbatim in
`lean.statement`; every source line is at most 100 characters. Read the three
conjuncts again against the node: constant pullback intertwines the two actual
constant structures; the twisted constant structure equals `b` followed by
`H(θ₀)`; and purity intertwines that structure with the inverse-exchange mate.
The explicit `commonIso` call retains the trace-normalized canonical purity.
The reviewed d = 0, empty-source and identity-model cases are still included.

## Second reading by Q22

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
