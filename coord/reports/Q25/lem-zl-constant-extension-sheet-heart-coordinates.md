## Worker report

The new module `Sheaf.Paper.ConstantExtensionSheetHeartCoordinates` states
`WeilConjectures.constantExtensionSheetHeartCoordinates`. Its only postponed proof is
that theorem; the auxiliary structures package its clauses, and every definition has
actual data. The theorem docstring follows all seven DAG proof steps.

Hypothesis and clause correspondence:

- The global finite-field datum is `D : FiniteFieldDatum.{u}`. The separated finite-type
  model is `X₀ : Over (Spec (.of D.k₀))` with `LocallyOfFiniteType`, `QuasiCompact`, and
  `IsSeparated X₀.hom`. The extension degree is `m` with `hm : 1 ≤ m`.
- The coefficient prime is `l` with `[Fact l.Prime]` and `hl : l ≠ D.p`; the closure is
  `Ω : Type v` with `[Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]`.
  Its universe is independent of the scheme universe. Every finite extension `E`
  in `Type u` is quantified with its field, algebra, and finite-dimensional instances;
  the common-stage category uses the existing transported coefficient models.
- `X`, `X_(0,m)`, and `Y` are literally `D.geometricFiber X₀`,
  `constantExtensionOriginalModel D m hm X₀`, and that model's `D.geometricFiber`.
  The existing `constantExtensionCyclicSheet` is exactly `j₀ ≫ H^i`, where the
  distinguished sheet has first been identified with X by `constantExtensionFiberIso`.
- `ZlSheetTensorSplitting` uses the actual specified embedding algebra on k_m and a
  ring equivalence with the product indexed by all k₀-embeddings into k. Its formula
  on `t ⊗ b` is `σ t * b`, and the embedding count is m.
- `ZlSheetGeometry.opens`, `closed`, `disjoint`, `cover`, `coordinate`, and `factor`
  say that all m sheets occur as pairwise disjoint clopen opens, each isomorphic to
  X by its actual semilinear coordinate. `successor` and `return_map` express the
  cyclic sheet identities, hence `H^m j₀ = j₀ g_X^m`. `new_frobenius` identifies
  `g_X^m` with geometric Frobenius of the k_m-model via the canonical fibre iso.
- `ZlSheetFiniteStage.pull_fac` fixes finite pullbacks to `finiteDerivedPullback`
  on the full `intrinsicFiniteTorsionConstructible` categories. The exponent is n+1,
  so n=0 is the required positive exponent one, not a zero coefficient quotient.
- `ZlSheetCoefficientStage` uses `constructibleIntegralPullback` on
  `sfIntegralConstructibleCategory`, and `rationalDerivedPullback` on the raw
  `sfRationalConstructibleCategory`. `ZlSheetCommonClauses.product` uses
  `commonStageDerivedPullback` on `generalAlgebraicallyClosedConstructibleCategory`.
  In each case `ZlSheetEquivalence.equivalence` asserts that the actual tuple
  functor `Functor.pi'` is an equivalence.
- `ZlSheetEquivalence.standard` detects both standard halves, in every degree,
  componentwise. Its `heart` and `heart_fac` restrict the same functor to the
  standard heart; `heart_equivalence`, `heart_limits`, and `heart_colimits`
  assert exact equivalence. Component exactness is explicitly retained.
- The finite and integral `cohomology` fields use the canonical derived t-structure,
  its truncation cohomology, and the actual pullback functors. Rational and common
  cohomology clauses use `zlSheetRationalStandard` and `zlSheetStandard`, which
  install only the geometric fibre's inherited finite-type base data and then use
  the recorded standard t-structures. The comparisons are natural isomorphisms.
- `reduction`, `quotient_reduction`, and `rationalization` state compatibility
  with the actual integral-to-finite, quotient-to-quotient, and rationalization
  functors. `ZlSheetScalarCompatibility` provides natural scalar squares whose
  integral components and rational transformations equal the published
  `integralPullbackScalarComparison` and `rationalPullbackScalarComparison`.
  `stage` and `stage_normalization` retain the identity object comparison at
  each literal common coefficient stage, so arrows are the same representative
  classes, rather than arrows in a replacement category.
- `frobenius_equivalence`, `frobenius_limits`, and `frobenius_colimits` refer to
  the existing `zlHeartFrobenius`, the heart restriction of the actual Frobenius
  pullback. `coordinate_factors` gives exact restriction along each open inclusion,
  an exact heart equivalence along its semilinear coordinate isomorphism, the same
  coefficient-stage equivalences for that coordinate, and the natural factorization
  of each component of the sheet product through these two functors. Residue-unit
  structures occur existentially in the conclusion, not as extra hypotheses.
- `zlSheetCycle` sends a tuple to its successor component, and at the final
  component to the m-fold iterate of Frobenius pullback of component zero.
  `zlSheetCycleHeartProperty` is the componentwise standard heart on the existing
  `IsoAlgebra` category. Thus its objects are precisely A_i with the displayed
  invertible a_i; its inherited algebra morphism condition is precisely
  `a_i ≫ u_i = u_(i+1) ≫ a_i'`, and at the return
  `a_last ≫ u_last = P^m(u_0) ≫ a_last'` in Lean composition order.
- `ZlSheetWeilCoordinates.equivalence` compares this full category with the actual
  `sfCommonStageWeilSheaf` of the original-base constant-extension model.
  `identification` pins it to `IsoAlgebra.mapOfNatIso comparison`, on objects and
  morphisms. `successor_normalization` and `return_normalization` pin every
  component to `zlSheetSuccessorComparison` and `zlSheetReturnComparison`.
  These are real composites of `zlPullComp`, scheme equality comparisons, and
  `zlSheetPositiveComparison`; they are not arbitrarily supplied isomorphisms.
  `zlPullComp` is the existing uniquely integral-normalized common-stage compositor.
  This gives the natural identification and preserves its integral normalization
  through rationalization and common-stage descent.

Dependency declarations used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `extensionSubfield`,
  `extensionEmbedding`, `geometricFiber`.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: `FiniteFieldDatum.geometricFrobenius`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`, `Stage`, `inclusion`.
- `Sheaf.Paper.SfConstructibleHeart`: the integral/rational/common standard classes,
  `sfRationalHeartProperty`, `sfCommonStageHeartProperty`, and both standard t-structures.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilFrobeniusPullback`,
  `sfCommonStageWeilSheaf`, `sfCommonStageWeilForget`, `sfWeilPrimeInvertible`.
- `Sheaf.Paper.WeilIndSheafCategory`: `zlPullComp`, `zlHeartFrobenius`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteDerivedPullback`,
  `constructibleIntegralPullback`, `rationalDerivedPullback`,
  `commonStageDerivedPullback`, and the prescribed scalar comparisons.
- `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence`: `constantExtensionDatum`,
  `constantExtensionModel`, `constantExtensionOriginalModel`, `constantExtensionSheet`,
  and `constantExtensionFiberIso` are owned by `def-dl-a1-constant-extension-data`.
  The cyclic map `constantExtensionCyclicSheet` is owned separately by the new
  existing-definition node `def-zl-constant-extension-cyclic-sheet`. Both owners
  are in `stmt_deps`; the downstream equivalence theorem is not a dependency.
- `Sheaf.Paper.LocalFrobeniusTrace`: `localPositivePower`, indexed by n with exponent
  n+1, is owned by `def-weil-local-frobenius-trace`, now explicitly in `stmt_deps`.
- Mathlib's `Functor.pi'`, `Pi.eval`, `Functor.iterate`, `ObjectProperty` full
  subcategories, and the existing upstream `Endofunctor.IsoAlgebra` construction.

All recorded proof-dependency modules are imported. The two Mathlib leaves are
available through their recorded finite-field and affine-pullback imports. The
existing constant-extension module contains older downstream statements, but no
result from them is taken as a hypothesis or chosen to define the new coordinate
construction: the only maps used are its canonical data definitions.

Edge cases checked before writing: m=1 has no successor branch and its only arrow
is P A₀ ≅ A₀; m=0 is excluded precisely by the node. Empty X has m empty opens
(pairwise disjoint and covering), and every relevant coefficient category and
product is the zero category. No nonemptiness, connectedness, k-linearity, finite
Tor amplitude, or chosen coefficient-stage hypothesis is added. The zero object,
identity coefficient embedding, quotient level one, and arbitrary closure universe
are retained. The isomorphism factors r_i, rather than projections h_i*, are asserted
individually to be equivalences.

Searches: `msearch.py leanfinder` with “cyclic geometric sheet coordinates
constructible coefficient heart Weil sheaf” and “Finite constant field extension
cyclic geometric sheets pullback exact equivalence Weil constructible sheaf heart”
returned generic Galois/Frobenius results, no exact result. `msearch.py loogle` with
“equivalence product category sheaf heart Frobenius” and
“CategoryTheory.Functor.pi, CategoryTheory.Endofunctor.IsoAlgebra” found generic
interfaces only. `msearch.py grep` for
`sheet.*(heart|coordinate)|constantExtension.*(Heart|Sheet)` in CategoryTheory
returned zero hits. `rg` on both project roots for sheet/constant-extension names
found `constantExtensionCyclicSheet` and its canonical construction, reused here;
the exact item id had no Lean declaration. `dag/lean_names_upstream.json` had no
matching coordinate statement. The upstream constant-extension representation
lemmas address representations, not these coefficient hearts. No exact existing
statement covers this node's clauses.

Source read: the current blueprint's `thm-zl-real-mixed-by-curves.proof.md`
paragraphs 1 and 5, and the supplied Deligne PDF's Frobenius/change-of-constants
passage (1.1.7)--(1.1.10). No statement correction or disputed statement.

## Second reading by Q25

Author's self-check for direct delivery; the maintainer supplies the independent
review. Compared the node and all clause definitions again. Corrected the return
comparison orientation to run from P^m A₀ to h_last* H*N, kept the compositor
rather than an unspecified natural iso, and retained the distinction between
coordinate equivalences and exact component projections. Checked the actual
IsoAlgebra morphism equation against the node's two equations. Replaced implicit
open-sheet residue-unit inference by explicit subsingleton structures in the
conclusion, so no extra invertibility assumption enters the signature. Removed an
unused binder warning and wrapped long lines. Each coefficient stage uses its
recorded intrinsic category and both standard halves, and there is one sorry,
exactly the named theorem. The return adds definition ownership metadata for an already existing canonical map;
no new Lean construction or dependency-module repair is needed.

## New nodes

`def-zl-constant-extension-cyclic-sheet` registers the existing definition
`WeilConjectures.constantExtensionCyclicSheet` in
`Sheaf.Paper.ConstantExtensionWeilHeartEquivalence`. For every i in `Fin m`, it is
literally the inverse canonical fibre isomorphism followed by the distinguished
sheet and the i-th power of original-model geometric Frobenius. Its hypotheses
are the original finite-field datum, m ≥ 1, and a separated finite-type model.
Its three statement dependencies own precisely that data, Frobenius, and the
finite-field/geometric-fibre framework. The source is Deligne (1.1.7) and the
paragraph after (1.1.10), pp. 150–152, serving the constant-extension passages in
the current blueprint proof. LeanSearch found only field-level Frobenius results;
Loogle and Mathlib grep found no match. Upstream grep found no declaration and
project grep found this exact existing definition. DAG grep and blueprint search
found no definition owner; the old owner was the downstream parent theorem, which
would create a cycle. The raw search results and queries are recorded in the new
node. `existing: true` records the actual declaration without copying it or
introducing a new Lean module. At m=1 its power is the identity; empty X is allowed.

## Repair of return L/H2

Compared the retained delivery at immutable head `1ba84047da72` with the current
live node: the existing changes are its Lean attachment and the added canonical
constant-extension-data dependency. The mathematical statement and Lean module
are retained, as the independent review found their mathematics correct.

1. Added `def-zl-constant-extension-cyclic-sheet` with `existing: true` and exactly
   the three requested statement dependencies, and cited it in the item's
   `stmt_deps`. Corrected the dependency-owner sentence above: the older data node
   does not own `constantExtensionCyclicSheet`.
2. Added the landed owner `def-weil-local-frobenius-trace` to the item's `stmt_deps`.
   Its `localPositivePower` definition is the exact positive-power operation used
   by the unchanged coordinate comparisons. No parent-theorem dependency or cycle
   is introduced. The new definition record's signature was extracted verbatim
   from the existing declaration; its data are the displayed real composition.
