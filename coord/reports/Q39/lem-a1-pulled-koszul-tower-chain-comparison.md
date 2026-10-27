# Q39: pulled principal Koszul tower comparison

## Worker report

The delivery states `WeilConjectures.pulled_koszul_tower_chain_comparison` in
`Sheaf.Paper.PulledKoszulTowerChainComparison`. It contains one theorem with `sorry`
and no definitions. Its original mathematical statement and six proof steps are
unchanged. Its statement dependencies now also cite the independent normalization
definition node required by the return. Q146's reviewed stage-1 split is retained
as the proof plan. This repairs the returned immutable head 6250f131e426.
The saved packet was
inspected first and its required initial dry run passed at 8afbc2dda97; that
automated result did not resolve the independent reviewer's F1/F2 findings.

### Hypotheses and objects

* Prime ell: `(l : ℕ) [Fact l.Prime]`.
* Finite extension E/Q_ell: `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. The existing coefficient extension constructions
  supply its valuation ring, chosen uniformizer and quotients; none is an extra input.
* Schemes T'=X, T=Y and their arbitrary morphism: `{X Y : Scheme.{t}} (g : X ⟶ Y)`.
  The two binders `hX`, `hY` assert ell is a unit in every local ring of X and Y.
  There is no finiteness, separatedness, Noetherian, nonemptiness, or flatness
  restriction on the schemes or the coefficient structural map.
* The universes `t u` are independent. Modules live in `max u (t+1)`, on the actual
  small pro-etale site of object universe t+1 and morphism universe t. There is no
  extra universe equality or unbound implicit variable (`autoImplicit false`).
* `CompletedTowerIndependent.Modules l E W` is the sheaf module category over the
  actual completed integral coefficient sheaf. `G l E g` applies the ordinary
  completed module pullback to every term and differential. Its underlying
  `CompletedTowerIndependent.pull` is the left adjoint of sectionwise pushforward
  through `directRingMap`, whose components are the actual coefficient projections
  and constant-coefficient maps. This is the ordinary ringed-topos pullback of
  `def-weil-pbc-completed-pullback`, with independent universe bookkeeping already
  supplied by `IntegralCompletedTowerPullbackUniverses`.
* `H l E W P` is exactly `PrincipalKoszulStrictReplacement.sourceTower`: direct-sum
  total tensor with P first and the actual two-term Koszul complexes, with transition
  `(t,1)`. The definition's index n denotes positive exponent n+1. Thus `n=0` here
  represents the node's first positive level, not an exponent-zero augmentation.
* `diagramPull` retains all strict maps when applying G; `transpose` converts a
  strict tower of complexes into a complex of strict towers, retaining transitions.

### Every conclusion

1. Goodness of GP is the first conjunct
   `integralOperationsGoodComplex l E X ((G l E g).obj P)`. The predicate is exactly
   K-flatness and flatness of every integer degree, with no boundedness condition.
2. Goodness of G(P tensor Q_n) is the second conjunct, quantified over every `n : ℕ`,
   on `((diagramPull ...).obj (H ... P)).obj (op n)`.
3. The existential family `θ` assigns to every good P an isomorphism in
   `ℕᵒᵖ ⥤ CochainComplex (Modules l E X) ℤ`, from G(H(P)) to H(GP). This is a strict
   chain isomorphism, rather than an identification of cohomology groups. Its images
   under transpose and `DerivedCategory.Q.mapIso` give the corresponding isomorphism
   in the derived category without an additional existence axiom or chosen object.
4. `KoszulNormalization l E g P (θ P hP)` is the existing full equation on BOTH
   Koszul basis vectors (the Boolean parameter indexes degrees -1 and 0), every
   homogeneous degree of P and every target coefficient b. It sends the pulled
   generator `b • generator ((x tensor e_i))` to the total-tensor generator
   `(b • generator x) tensor e'_i`. This is the node's coefficient-last formula
   `((x tensor e_i) tensor b) ↦ (x tensor b) tensor e'_i`. The generator is fixed
   by the actual pullback adjunction unit. Consequently this equation specifies
   the ordinary tensor comparison followed by the action unitor, including all
   coefficient scalars; it is not a bare, arbitrarily chosen `Nonempty` isomorphism.
   Since θ is a chain map, the two generator equations include the multiplication
   by t^(n+1) chain equation with no scalar or sign correction. Since θ is a
   natural isomorphism of strict towers, its naturality at the adjacent arrow is
   exactly the `(t,1)` transition equation; all longer transition equations follow
   from its actual tower naturality. No premise about preservation of arbitrary
   quasi-isomorphisms by G occurs.
5. The first universally quantified f-square is naturality of θ for every chain
   map between good P and P'. `sourceTowerMap` is f tensor identity; whiskering it
   by G is the source arrow, and `sourceTowerMap ... (G.map f)` is the target arrow.
6. The augmentation is the existing strict natural transformation
   `PrincipalKoszulStrictReplacement.comparison l E X (G.obj P)`. Its component is
   precisely tensorWith GP applied to the target quotient augmentation epsilon,
   zero on degree -1 and the actual limit projection in degree zero. Its target
   uses `residueStep`, the actual quotient transition. Strictness is already part
   of the natural-transformation type and the concrete construction.
7. `∀ n, QuasiIso (comparison.app (op n))` gives every level, and
   `QuasiIso (transpose.map comparison)` gives the quasi-isomorphism of complexes
   in the strict tower category. Both are explicit conclusions, not extra premises.
8. The final f-square gives naturality of that specified target augmentation for
   all chain maps between good complexes, using sourceTowerMap and targetTowerMap.

### Dependency declarations used and source reading

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, reexporting the actual
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionIdeal`, and `coefficientExtensionRing` constructions.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `WeilConjectures.integralConstantToCompletionOfUniverses` and the specified
  quotient cone, with the completed coefficient sheaf and its actual projections.
* `def-weil-scheme-morphism-properties` is explicitly a convention node and has
  no declaration of its own. `Scheme`, scheme morphisms and the local-ring unit
  predicate give exactly the properties used here.
* `Sheaf.Paper.PbcQbarCompletedPullback` is imported as the recorded completed
  pullback dependency module, retaining its original integral interfaces. Its
  Qbar constructible functor is not used in place of ordinary module pullback.
  The existing independent-universe ordinary interface is
  `Sheaf.Paper.IntegralCompletedTowerPullbackUniverses`:
  `WeilConjectures.CompletedTowerIndependent.directRingMap`, `pull`, `adjunction`,
  `Modules`, `Towers`, `transpose`. No dependency record requires replacement.
* `Sheaf.Paper.IntegralOperationsWellDefined`:
  `WeilConjectures.integralOperationsGoodComplex` (definition read in full).
* `Sheaf.Paper.PrincipalKoszulStrictReplacement`:
  `WeilConjectures.PrincipalKoszulStrictReplacement.Modules`, `uniformizer`,
  `residue`, `projection`, `koszul`, `multiplication`, `augmentation`, `tensorWith`,
  `sourceTower`, `residueStep`, `targetTower`, `comparison`, `sourceTowerMap`,
  `targetTowerMap`. These are the recorded definition-node declarations; the
  proof dependency is `principal_koszul_strict_replacement` in the same module.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal` and its recorded independent-site tensor.
* `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`, the
  total cochain tensor used by the existing towers, with differential signs 1, (-1)^p.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; no alternate localization is defined.
* `Sheaf.Paper.AdicCoefficientDatum`: recorded strict tower convention; the
  independent-universe integral specialization uses `CompletedTowerIndependent.Towers`.
* `Sheaf.Paper.PulledKoszulTowerNormalization`:
  `WeilConjectures.PulledKoszulTowerModel.G`, `H`, `diagramPull`,
  `KoszulNormalization`, `generator`, `tensorGenerator`, `koszulBasis`,
  `koszulDegree`, `koszulZero`, `koszulMinusOne`. These concrete helpers now
  belong to the new independent definition node. Their bodies are the same
  constructions as the formerly theorem-owned helpers, with no parent import.
  Neither `Comparison` nor `finite_pullback_strict_tower_comparison` is assumed.
* Proof imports include `Sheaf.Paper.KFlatRingedToposPullback`
  (`SheafOfModules.isKFlat_ringedToposPullback`),
  `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`
  (`CategoryTheory.CochainPullback.cochainPullbackTensorCoherence`),
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
  (`AlgebraicGeometry.Scheme.proEtaleSheafInverseImage`), and
  `Mathlib.CategoryTheory.Abelian.FunctorCategory`
  (`CategoryTheory.Abelian.functorCategoryAbelian`, the recorded Mathlib match).
  Remaining proof dependencies share the modules already publicly imported.

Read Stacks `sites-cohomology.tex` at `lemma-pullback-K-flat` (0G7E) and
`lemma-pullback-tensor-product` (07A4), including the proof's ordinary total-complex
comparison. The theorem docstring contains all six live DAG proof steps, with
preservation of the uniformizer, both differential signs, strict transitions,
naturality and levelwise homology. No source-based correction is needed.

## Repair of the returned delivery

F1: `def-a1-pulled-koszul-tower-normalization`, in its own module
`Sheaf.Paper.PulledKoszulTowerNormalization`, owns `G`, `H`, `diagramPull`,
`generator`, `tensorGenerator`, `koszulZero`, `koszulMinusOne`, `koszulDegree`,
`koszulBasis` and `KoszulNormalization`, in namespace
`WeilConjectures.PulledKoszulTowerModel`. It publicly imports only
`IntegralCompletedTowerPullbackUniverses`, `CoefficientRingedTensorHomModel` and
`PrincipalKoszulStrictReplacement`, the modules of its three statement dependencies.
The item now imports this module and opens this namespace, with no import or use
of `FinitePullbackStrictTowerComparison`. The theorem signature otherwise retains
all accepted clauses. No new theorem, arbitrary map or choice was introduced.

F2: the new definition node explicitly cites
`def-a1-integral-completed-tower-pullback-universes`, which owns `Modules`, `pull`,
`adjunction`, `transpose` and the completed structural map. The item cites the new
node; this gives the explicit statement-dependency path to those constructions.

Maintainer note: re-point the downstream parent module's ten identically named
helpers in `WeilConjectures.FinitePullbackStrictTower` to the new owner's
`WeilConjectures.PulledKoszulTowerModel` declarations (aliases are sufficient;
the bodies are unchanged). Add the new definition id to the parent's stmt_deps,
then its stage-3 proof can import this item without a cycle. The parent and its
node are outside this delivery's allowed edits and have not been modified.

## New nodes

`def-a1-pulled-koszul-tower-normalization` defines ordinary cochain and diagram
pullback, the adjunction-unit generator, both actual cone bases, the P-first
principal tensor tower, and the full two-basis normalization equation. Source:
Stacks 03D2/03EK/03EL and 07A4, with the principal Koszul cone already supplied by
`def-a1-principal-completed-koszul-towers`. Its three statement dependencies are
exactly the definition owners named in the return. `G` is `pull.mapHomologicalComplex`,
`diagramPull` is `Functor.whiskeringRight`, `generator` is the actual adjunction
unit, `tensorGenerator` is `coefficientTensorGenerator`, `koszulZero` and
`koszulMinusOne` use the actual mapping-cone inclusions, and `H` is the recorded
`sourceTower`. `KoszulNormalization` quantifies over all n, both degrees, every
homogeneous x and every target coefficient b and gives precisely the displayed
pure-tensor equality. There are no goodness or invertibility hypotheses on these
definitions, and no sorry in this module. Scheme and coefficient universes remain
independent. This is the extraction expressly required by F1, not a new tensor,
pullback or Koszul construction.

New-node searches were run with the prescribed wrapper and their complete output
is preserved in `mathlib_searches`: LeanSearch and LeanFinder for "Canonical pulled
Koszul tower tensor generator basis normalization ordinary pullback cochain
complex" returned eight unrelated normalization/cotangent/base-change hits each;
grep for `KoszulNormalization|koszulBasis|diagramPull` returned six unrelated
`diagramPullback` hits in Mathlib Sites Plus. Direct rg over DAG, upstream and
Sheaf found only the theorem-owned definitions and their theorem consumers;
`blueprint_refs.py search 'pulled Koszul tower'` returned zero blueprint matches.
Thus no independent definition node owned this interface. The blueprint ancestor
command returned `lem-a1-finite-map-purity`, recorded in the new node.

### Edge cases

* n=0 is exponent 1; no zero-exponent level is introduced or omitted.
* Both Koszul degrees are present, including the minus-one generator and its sign.
* P=0 and zero chain maps remain in the good full subcategory; all squares specialize
  to the unique maps between zero complexes.
* P=R[0] recovers the actual normalized two-term pullback, so a scalar-twisted
  automorphism fails the generator equations.
* Unbounded P is permitted: all degrees are integers, and the original signed
  direct-sum total tensor is retained.
* g=id is allowed, with its canonical adjunction generator, rather than a separately
  chosen identity comparison.
* X empty and/or Y empty impose no nonemptiness. The invertibility hypotheses are
  the stated pointwise ones; in particular the empty-scheme characteristic-ell
  case is not excluded by an extra base-field hypothesis.
* Non-flat and noninvertible completed ring maps are permitted; only the target
  augmentation's quasi-isomorphism is asserted.
* Different scheme and coefficient universes compile without identifying them.

### Searches

Used the prescribed msearch.py wrapper for Q39 and this item:

* leanfinder: "Ordinary pullback identifies the strict tower of tensors with principal
  Koszul complexes and preserves flat term K flat complexes; target quotient
  augmentation is a quasi isomorphism". Eight hits: Kahler/cotangent tensor-base-change
  and module flatness short-complex exactness; no strict completed Koszul tower theorem.
* loogle: "SheafOfModules.pullback, CochainComplex.mapBifunctor". Zero hits.
* grep: "pullback.*[Kk]oszul|[Kk]oszul.*pullback|KoszulNormalization". Zero hits.
* Direct rg over Mathlib sheaf modules for pullbackObjFreeIso and Koszul/pullback:
  `PullbackFree.lean` supplies ordinary free-sheaf pullback and its generator equations,
  not the good-complex and strict target-augmentation theorem.
* Direct rg over `lean/WeilConjectures` and `lean/Sheaf` for Koszul/pullback:
  ordinary local Koszul Ext results and completed inverse-limit comparisons are
  different. `FinitePullbackStrictTowerComparison` supplies the exact normalization
  helpers and a downstream theorem with substantially more conclusions (derived
  reduction, balanced finite comparison and shift descent). Its structure projections
  require that stronger Comparison as an input and are not this statement.
* Direct rg for this item id under `lean/WeilConjectures`: no existing declaration.
* `scompile.py --source Sheaf.Paper.FinitePullbackStrictTowerComparison` confirms
  the current server helper source agrees with the read clone.

No STATEMENT-DISPUTED flag or statement correction. The new definition owner
and the repaired dependency path are described above.

## Second reading by Q39

Repair self-check with both node files and both modules open (no other agent was
started, as instructed). The original hypotheses remain prime ell, finite E,
arbitrary g, and pointwise invertibility of ell on X and Y. Every accepted
conclusion is retained: goodness of GP and every pulled Koszul level; strict theta;
the two-basis, all-coefficients normalization; theta's naturality; the specified
target augmentation's levelwise and transposed quasi-isomorphism; and its
naturality. The new definition node has the same no-goodness, no-invertibility
scope as its module. Each of its ten declarations is recorded and has its own
source/blueprint docstring. Its real data comes solely from the three recorded
definition dependencies. The only former mismatch was ownership/import direction,
which this repair fixes. The n=0 exponent-1 level, zero P, unbounded complexes,
identity g, empty schemes and independent t/u cases remain admitted. Both choices
of the Boolean basis parameter give the actual degrees -1 and 0. The new module
contains no postponed theorem or hollow data.

### Validation

The saved pre-repair packet passed the required initial dry run at 8afbc2dda97.
Both repaired modules compiled cleanly through scompile.py, individually in
dependency order. The repaired dry run printed:
`OK (dry run): commit 9b5a0e5ade8 passes the preflight and compiles; nothing pushed`.
The item differs from current main only in `stmt_deps` and `lean`; both recorded
signatures match their source verbatim, no Lean line exceeds 100 characters,
and the new module contains no sorry. A source-import closure check, including
private imports, confirmed that neither delivered module reaches the downstream
parent. The delivery wrapper repeats preflight and compilation before pushing.
