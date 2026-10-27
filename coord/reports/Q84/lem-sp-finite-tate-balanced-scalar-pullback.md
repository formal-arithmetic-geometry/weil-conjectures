## Worker report

The module `Sheaf.Paper.FiniteTateBalancedScalarPullback` states
`AlgebraicGeometry.Etale.finiteTateBalancedScalarPullback`, with proof `sorry`.
All five auxiliary definitions have real data and only name existing objects,
generators, degree-zero embeddings, or composites of existing canonical comparisons.
There are no new independent mathematical notions and no statement correction.

Hypothesis and clause audit:

* `N : ℕ`, `hN : 0 < N` express N ≥ 1. Scheme objects range over all
  `Scheme.{u}`; `f : T' ⟶ T` is arbitrary.
* Coefficients are `A B : Type (u+1)` with `CommRing`, `Finite`, a unital
  `φ : A →+* B`, and `hA : (N : A) = 0`, `hB : (N : B) = 0`.
  No coefficient-flatness or nontriviality hypothesis is imposed.
* Invertibility on a scheme is `∀ t : T, IsUnit (N : T.presheaf.stalk t)`.
  The theorem supplies global-section invertibility witnesses used by the existing
  roots-pullback API. In the square it names the corresponding condition on T';
  this condition follows from that on T along f, and quantification over its proof
  is not a restriction. This avoids introducing an extra postponed helper lemma.
* `finiteTateBalancedSheaf ... false` is the constant coefficient sheaf and
  `... true` is `finiteEtaleTateLine`, via the existing signed Tate sheaf at 0 or 1.
  `finiteTateBalancedObject` embeds these using `DerivedCategory.singleFunctor _ 0`
  in the existing ordinary, unbounded `Etale.DerivedCategoryModule`.
* `s T i` is the ordinary balanced isomorphism, for either of these two sheaves.
  The first conjunct specifies its scalar-adjunction adjunct on every constant
  generator a, or every root generator z tensor a: a maps to φ(a), and
  z tensor a maps to z tensor φ(a). B-linearity supplies the outer factor b,
  so the full map is a tensor b ↦ φ(a)b or (z tensor a) tensor b ↦ z tensor φ(a)b.
* The second conjunct specifies its actual inverse: the generator with coefficient
  b goes to b times the scalar-adjunction unit applied to the generator with
  coefficient 1. The unit is insertion m ↦ m tensor 1, hence these are exactly
  b ↦ 1 tensor b and z tensor b ↦ (z tensor 1) tensor b. The explicit `@id`
  restores the target B-module type after passing through restriction of scalars;
  it changes no element or action.
* `θ T hT i` is an isomorphism from the actual derived scalar extension to the
  B-line. The third conjunct fixes its hom to `scalarSingleMap` followed by
  the degree-zero image of the specified ordinary map s. Thus it is the derived
  ordinary coefficient comparison, not an arbitrary isomorphism.
* `finiteTateBalancedPullback` uses the recorded
  `finiteEtaleTwistPullbackData.c`, at 0 or 1, preceded by
  `singleFunctorCompLeftDerivedUpperStarIso`. Its laws identify the zero case with
  `upperStarConstantSheafIso` and the one case on root generators.
* The fourth conjunct uses the actual published `scalarPullbackIso.hom.app` for λ.
  Its two composites are λ ≫ E(u_A) ≫ θ_T' and f_B*(θ_T) ≫ u_B,
  where i=false gives the unit equation and i=true gives the twist equation.
  These are equalities in the derived category, not only on cohomology. Applying
  `shiftFunctor _ n` to both composites states the equation after every common
  shift, including zero. Under the canonical exact-functor shift comparisons this
  is precisely the square on shifted inputs.
* `finiteTateBalancedShiftIso` is the canonical scalar shift comparison followed
  by the shift of θ. The last conjunct gives an isomorphism for every finite
  family of either type of line with independently chosen integer shifts.
  Its two equations specify the images of every summand inclusion and projection.
  Thus the isomorphism is exactly the additive-functor biproduct comparison
  followed by the biproduct of these shifted θ maps, including an empty family.

Statement dependency interfaces read and used:

* `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule` and the standard degree-zero functor.
* `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `nonempty_derivedChangeOfRingsCochainModel`; its existing constant-coefficient
  specialization is `AlgebraicGeometry.Etale.scalarExtension` and its actual
  cochain representative counit (`Sheaf.Paper.EtaleDerivedScalarTensor`).
* `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`:
  `Scheme.finite_etale_torsion_twist_line`, reexporting `finiteEtaleTateLine`,
  `finiteEtaleTateTwist`, and the roots-module construction.
* `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`:
  `Scheme.etaleFiniteTwistPullback`, `FiniteEtaleTwistPullbackData`,
  `finiteEtaleTwistPullbackData`, and `finiteEtaleTateOneGenerator`.
* `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`:
  `CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons`,
  reexporting the representative-normalized ringed comparison interface.
* Added already-landed statement dependencies:
  `def-pur-finite-smooth-coefficient-arrows` owns
  `FiniteSmoothPurity.scalarSingleMap` and `scalarShiftIso` in
  `Sheaf.Paper.FiniteSmoothCoefficientArrows`;
  `def-pur-etale-scalar-pullback-iso` owns `scalarPullbackIso` and
  `scalarPullbackIso_existsUnique` in `Sheaf.Paper.PurEtaleScalarMateProjection`
  (also imported directly as a statement dependency). The definition is the unique
  K-flat-normalized comparison chosen from that existence/uniqueness theorem.
  These are existing canonical constructions, not interface repairs.

All recorded, stated proof dependencies are imported. Those used only for the proof
have plain imports: K-flat closure, sheaf/cochain tensor, exact inverse image,
cochain pullback/tensor coherence and canonical ringed tensor pullback.

Source: read the current blueprint Charts paragraph in
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md`.
It identifies these summands as free rank-one summands whose derived extension is
ordinary; the reviewed DAG makes both balancing formulas and geometric compatibility
explicit. The module docstring gives all seven DAG proof steps and their inputs.

Edge cases checked before and during writing: N=1 (only zero coefficient rings),
A=0 (a unital map forces B=0), B=0, empty scheme, identity scheme map, identity
coefficient map, arbitrary nonflat Z/4→Z/2 coefficient change, negative/zero/positive
shifts, mixed shifted summands, repeated summands, and the empty finite index type.
No Nonempty, IsDomain, Field or Nontrivial binder excludes these cases. J has an
independent universe w; only finite biproducts are requested.

Searches (outputs are retained in searches.jsonl):

* msearch leanfinder: "Derived coefficient extension of finite Tate roots of unity
  lines commutes with scheme pullback" — eight unrelated scheme-tensor pullback hits.
* msearch loogle: `"extendScalars", "Sheaf"` — zero hits.
* msearch grep: `Tate.*[Ss]calar|[Bb]alanced.*[Pp]ullback` — two unrelated Mathlib hits.
* msearch leansearch: "Balanced coefficient extension of finite Tate sheaves commutes
  with inverse image in the derived category" — eight generic shift, sheafification
  and Ext comparison hits; none states this theorem.
* rg of project WeilConjectures and Sheaf for the item id, balanced scalar pullback,
  finiteTateBalanced, scalarExtension, scalarPullbackIso, CoefficientLineComparison:
  no existing theorem for the whole statement; found and reused the existing scalar,
  roots, and representative-normalized comparisons listed above.

No STATEMENT-DISPUTED flag and no dependency fault remain.

## Second reading by Q84

This is the dispatched worker's own second reading; no other agent was started.
The maintainer's independent review remains separate. Read the node and source file
side by side, checked every clause using the audit above. Confirmed Boolean indexing
includes exactly 0 and 1, the inverse formulas use insertion at coefficient 1,
normalization fixes actual derived maps, both geometric equations are stated for all
common integer shifts, and both finite-sum equations are present. No flatness of B/A
or nonzero-ring hypothesis is present. Compiler feedback prompted an explicit target
B-module type for inverse-generator multiplication and an explicit biproduct family;
these elaboration repairs do not change the mathematical statement.

Validation: scompile.py passed both sandbox (21.2 s) and library (16.0 s)
compilation, with no errors or warnings.

## Returned delivery repair (H2)

The return on immutable head `ff78ee3f6e72` identified the wrong DAG owner for
`scalarPullbackIso`. Replaced `lem-pur-etale-scalar-mate-projection` in the item's
`stmt_deps` with the live existing definition node
`def-pur-etale-scalar-pullback-iso`. Read that node's statement and Lean record,
and the full signatures and docstrings of `scalarPullbackIso_existsUnique` and
`scalarPullbackIso` in `Sheaf.Paper.PurEtaleScalarMateProjection` (lines 120–160).
The latter is the `.choose` of the former, and both are recorded in the definition
node's `lean.declarations`. The direction remains geometric pullback after scalar
extension to scalar extension after geometric pullback, exactly as used for λ.
Updated the dependency audit above and `lean.note`; retained the import and the
entire Lean file unchanged, as requested. No mathematical statement changed.

Compared the retained packet with current live main: apart from `lean`, the only
item delta is adding the two existing definition dependencies named above. All
other node fields match live main. The first saved-packet dry run passed as commit
`aaad97f7bd0`; the explicit H2 ownership repair was then made before delivery.

Self-check by Q84: re-read the node and the Lean statement side by side; the
hypothesis and clause audit in this report still applies verbatim. The five
auxiliary definitions, generator formulas and inverses, scalarSingleMap
normalization, both shifted derived equalities, and finite biproduct inclusion
and projection equations are unchanged. The repair changes only the dependency
owner metadata and its explanation. No other agent was started.

Repair validation: scompile.py passed sandbox compilation in 46.3 s and library
compilation in 29.3 s, with no errors or warnings. A metadata self-check confirmed
the verbatim Lean signature, the two existing definition dependencies, the retained
public import, explicit-binder mode and all Lean line widths.
