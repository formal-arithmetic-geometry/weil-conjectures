## Worker report

This repairs immutable head 0a281b73c706. The initial required dry run of the retained
packet passed mechanically (bc8ad40c4e), but direct reading confirmed the return's mathematical
faults. The repaired packet retains the main node's original statement verbatim, removes
the unsupported replacement statement and statement_change, and supplies the canonical
constructions that replacement omitted.

Hypotheses and clauses, matched to Lean:

- A small site and commutative coefficient sheaf: `C : Type uC`, `Category.{vC} C`,
  `J : GrothendieckTopology C`, `R : Sheaf J CommRingCat.{r}`, and
  `EssentiallySmall.{r} C`. This is smallness relative to module size, not equality of
  the site-object, site-morphism, and coefficient universes. The derived morphism universe
  `w` is separate. For the small pro-etale site take object size `t+1`, hom size `t`,
  coefficient size `max u (t+1)`. The module category is the recorded `ringedSiteModules`.
- Regular global section: `t : (SheafOfModules.unit 𝓞).sections` and
  `hreg : Mono (globalSectionMultiplication R t)`.
- `B_m` and `Q_m`: `principalQuotient` is the categorical cokernel of multiplication
  by the positive power, `principalReduction` its single degree-zero complex, and
  `principalKoszul` the mapping cone of that multiplication on `O[0]`. Lean index `m`
  means source index `m+1`, so the first term is reduction modulo `t`, never modulo `1`.
- Canonical strict transitions: `principalKoszulTransition` uses the mapping-cone square
  with `t` on the source and identity on the target; `principalReductionTransition` uses
  `cokernel.desc` of the quotient projection. `Functor.ofOpSequence` extends these specified
  successor maps, and `principalTowerComparison` has precisely the cone quotient components.
  There are no arbitrary transition parameters or assumed comparison naturality.
- K-flat representative: `P` has exactly the dependency predicate
  `CochainComplex.IsKFlatIndependentCoefficients P`. The tensor is explicitly the canonical
  `SheafOfModules.monoidalCategory R`, supported by the recorded independent-coefficient
  zero-morphism infrastructure. The strict tensor functor uses the K-flat factor second,
  `Q_m ⊗ P`. Canonical signed symmetry identifies this with the source's `P ⊗ Q_m`;
  it carries the strict transitions, augmentations and quotient maps too.
- The strict tensor towers and map `a` are `koszulTensorTower`, `reductionTensorTower`
  and `koszulTensorTowerComparison`. `koszulTowerComplex` and `koszulTowerComplexMap`
  rearrange them degreewise into complexes and maps in `Tow(A)` using actual data.
- Levelwise quasi-isomorphism, derived-tower isomorphism and derived-limit isomorphism
  are respectively `∀ m, QuasiIso (a.app (op m))`, `QuasiIso aC`,
  `IsIso (DerivedCategory.Q.map aC)` and `IsIso ((koszulRlim R).map ... )`.
- `C_t(K)` is `koszulCompletion R P t`: the actual total right derived limit of the
  constructed Koszul tower. `koszulRlim` selects the functor supplied by
  `ringedStrictTowerHomotopyLimitIndependentCoefficients`, whose right-derived universal
  property determines it up to unique natural isomorphism. It is not an arbitrary object
  equipped with a triangle. The definition chooses only this universal-property object,
  not an arbitrary comparison arrow.
- The strict augmentation has components `koszulRepresentativeAugmentation`, insertion
  of `1 ⊗ x` followed by tensoring the cone inclusion. The comparison's augmentation
  clause is the equality of the two actual composites after `Q` and `koszulRlim`.
  `koszulRepresentativeQuotient` inserts `1 ⊗ x` and applies the quotient projection.
- The product/Roos clause existentially supplies products and a Roos triangle on this
  actual `koszulCompletion`, with the canonical derived successor transitions. Its
  product comparison is `IsIso (Limits.Pi.map aD)`.
- The optional quotient Roos triangle binds `K`, the representing isomorphism `e`,
  `pU` and `δU`. Its component hypothesis is explicitly
  `pU ≫ Pi.π UD m = e.inv ≫ Q.map (koszulRepresentativeQuotient R P t m)`.
  This both uses `e` and identifies every component with the prescribed quotient map.
- The conclusion returns one `φ : K ≅ koszulCompletion R P t`. For this same `φ`,
  it states each quotient projection equation, the full product equation, and
  `Pi.map aD ≫ δU = δV ≫ φ.inv⟦1⟧'`. No equation is asserted for arbitrary isomorphisms.

The auxiliary postponed theorems in the new definition-node module state the first proof
step's transition square,
quotient annihilation, augmentation naturality and the explicit augmentation/quotient
identity, and the unit inclusion's chain
condition. Their docstrings give the complete elementary proofs; they are listed with
the owning definition node in `lean.declarations`. All construction data are explicit.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlatIndependentCoefficients`,
  `independentCoefficients_isMonoidal`, and both independent-coefficient tensor
  zero-morphism theorems. Their full signatures and canonical-instance lets were read.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor` and the
  functorial `map₂CochainComplex`; `SheafOfModules.monoidalCategory` is the recorded
  canonical tensor from the upstream sheaf monoidal module.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimitTriangle`, whose definition is the distinguished
  triangle with `towerTransitionEndomorphism`.
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`: `functorCategoryAbelian`;
  the evaluation exactness is the recorded Mathlib functor-category limits/colimits
  infrastructure and `HomologicalComplex.quasiIso_iff_evaluation`.
- The strict-tower dependency is used through its supplementary independent-coefficient
  theorem, described below; its complete original statement was read.

Sources read: `literature/stacks-project/algebraization.tex`,
`lemma-derived-completion-koszul` (0A0E, principal case); and
`literature/stacks-project/sites-cohomology.tex`, `lemma-derived-limit-is-ok` (0941,
K-injective tower resolutions and Roos triangle). The statement is an intermediate
DAG node; no blueprint unit statement is changed.

Edge cases: `m=0` is the positive exponent 1; a unit `t` makes both towers zero in the
derived category, and a quotient Roos hypothesis then forces `K=0`; `t=0` is permitted
only when multiplication by zero is monic (the zero coefficient sheaf); `P=0`, the zero
ring and an empty site give zero constructions. A degree-zero flat representative gives
the ordinary quotient comparison. The former arbitrary-φ clause fails under φ ↦ -φ
when the connecting morphism is not 2-torsion; the repaired clause binds the actual
returned φ. The pro-etale universe specialization above retains distinct site sizes.

Searches: the saved packet's LeanSearch/Loogle/LeanFinder/grep searches found no combined
reconstruction theorem. Repeated `msearch.py leanfinder` with “Koszul tower quotient regular
global section derived inverse limit reconstruction” returned eight cotangent/Kaehler
construction results, no match. `msearch.py loogle` on
`Functor.ofOpSequence, CochainComplex.mappingCone.map` returned no results (remote index
unknown identifier), so the exact pinned Mathlib source was read instead. `msearch.py grep`
on `derivedComplete|principalKoszul|koszul_reconstruction` in `Algebra/Homology` returned
zero results. `rg` over Mathlib, the source `WeilConjectures` and side `lean/Sheaf` found no
existing combined statement or conflicting helper. It found the existing canonical
`Functor.ofOpSequence`, `NatTrans.ofOpSequence`, `mappingCone.map` and cone quotient API,
which this delivery uses rather than duplicating. The recorded independent-coefficient
K-flat predicate was found and is used directly. The previously missing canonical paired tower construction is now recorded as
`def-pur-principal-koszul-quotient-towers`, separating its file check from the reconstruction
theorem after the combined library-form file exceeded the fixed 60-second limit.

## Dependency modules

`lem-weil-pbc-ringed-strict-tower-homotopy-limit`: the recorded
`ringedStrictTowerHomotopyLimitOfUniverses` types coefficients as `max uC vC r`.
An independently fixed coefficient universe with `EssentiallySmall.{r} C` cannot be
recovered by solving that non-injective maximum-universe constraint. The supplementary
module `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
states the same right-derived universal property, K-injective computation, evaluation,
natural Roos triangles, pro-zero vanishing and cone criterion after passing to the
coefficient-universe small model. The site object and hom universes stay independent.
The original module is imported and preserved. Only this dependency node's `lean` is
changed, with the required explanatory note.

## Second reading by Q51

I reread the main node and repaired file clause by clause after the returned review.
This is the dispatcher's requested self-check, not a claimed second-agent review.
The old code allowed arbitrary transitions, arbitrary `C_t`, an unconstrained `pU`, an
arbitrary monoidal instance and the wrong tensor side; it also universally quantified
its final connecting equation over φ. These mismatches are removed by the actual strict
towers, universal-property-derived `koszulRlim`, explicit quotient components through
`e.inv`, canonical tensor, recorded K-flat predicate, and one existential iso containing
all three equations. The original node statement is restored exactly. I also checked the
supplementary dependency against every clause of its node: none is removed. I reread
the new definition node against its 28 declarations: cone, cokernel, strict transitions,
comparison, total tensors, unit and quotient maps, their chain/naturality equations and
the degreewise rearrangement are all explicit; neither regularity nor K-flatness is
assumed in this construction node. The three reconstruction declarations remain in the
item module. Splitting off the genuinely missing construction keeps each check within
the same 60-second file limit.

The citer search `rg -l '"lem-pur-derived-complete-koszul-reconstruction"' dag/nodes`
returns the item itself and `lem-pur-integral-operations-scalar-extension`; testing actual
`stmt_deps`/`proof_deps` leaves exactly the latter. Its proof Steps 4 and 5 use the strict
Koszul/quotient tower identification and `K ≅ C_R K` with quotient projections; the repaired
statement provides both under precisely its stated regularity, K-flat representative and
derived-completeness Roos hypotheses. Thus this citer's use holds. Its current recorded
module is `Sheaf.Paper.IntegralOperationsScalarComparisons` (Q118), whose interface is not
edited. I read `scalarCompletion_existsUnique` and `scalarCompletionIso`: the former
normalizes the completion map on good representatives and asserts it is invertible on
`IsSfDerivedComplete` inputs; the latter is exactly `asIso` of that map. This agrees with
the projection-normalized reconstruction used in its DAG proof, rather than asking for
the false assertion that every isomorphism respects a connecting map. No citer needs modification.


## New nodes

`def-pur-principal-koszul-quotient-towers` records the canonical negative-degree principal
Koszul cone and quotient tower pair, their strict comparison, their tensors with an
arbitrary complex, and the actual unit/quotient augmentations and degreewise tower
rearrangement. Its source is the principal construction in Stacks 0A0E and the strict
complex-tower formulation in 0941. These were missing interfaces required by this item's
original statement and are defined by actual data. LeanSearch and LeanFinder each returned
eight unrelated module presentation/local-cohomology results; Mathlib grep returned zero.
The source and side searches found no declarations with these constructions. The DAG and
blueprint searches were also read: `def-weil-pbc-ringed-koszul-system` builds positive
factors and their Hom-dual tower with equal site/coefficient universes, without the
negative mapping-cone/quotient pair; `def-weil-pbc-intrinsic-koszul-completion` is only for
constant Noetherian coefficients on a scheme. Neither supplies the present arbitrary-site
paired construction. Generic tensor complexes, cokernels, cones and inverse sequences are
reused from their recorded dependencies. The node has no regularity or K-flatness hypothesis:
those belong only to the reconstruction theorem. The item's only extra field change is
adding this definition node to `stmt_deps`; its statement remains verbatim.


## Compile-time repair of returned head e2328281005d

The return identifies a 60-second timeout in the preliminary library-form check of
`PrincipalKoszulQuotientTowers`. The retained packet was tested first, as instructed.
I investigated a three-layer split, compiled that experiment, and withdrew it after
rereading the worker rule forbidding a file split as a timeout workaround. There are
no extra nodes or module layers in this repaired packet.

The actual repair is in the two `NatTrans.ofOpSequence` constructions:
`principalTowerComparison` now uses only the two tower definitions and the
explicit successor-map rewrite to apply `principalAugmentation_naturality R t`;
`koszulStrictAugmentation` now uses
`koszulRepresentativeAugmentation_naturality R P t` directly. The latter type is already
exactly the needed successor naturality witness. The former needs just the named
successor-map equality for `Functor.ofOpSequence`. The original broad `simpa` calls asked
elaboration and simplification to unfold the cone, inverse sequence, and total tensor
constructions unnecessarily. Every declaration signature and all construction data
are retained; the reconstruction statement and all mathematical hypotheses are unchanged.
I reread the two witness types against the explicit `t/id` and quotient transitions,
and checked all 28 construction declarations remain in their original owning node.
The definition node's module remains `Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers`.

The independent-coefficient dependency is unchanged mathematically. The elementary
edge cases and source matches recorded above continue to apply. This is a self-check;
the maintainer performs the independent review, as the dispatcher instructed.


The repair rechecked the saved search evidence with `msearch.py leanfinder` on
"Canonical principal Koszul quotient tower cone augmentation and strict successor
transitions": eight hits (`ChainComplex.augment_X_succ`,
`CochainComplex.augment_X_succ`, `ChainComplex.augment_d_succ_succ`,
`CochainComplex.augment_d_succ_succ`,
`AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_succ`, `ChainComplex.augment`,
`CochainComplex.mkAux`, `ChainComplex.mkAux`), none defining the paired tower.
`rg` for `principalKoszul|principalReduction|koszulTensorTower` in Mathlib's
Algebra/Homology, source WeilConjectures, and the shared side Sheaf source found no match.
The pinned `Functor.ofOpSequence_map_homOfLE_succ` signature was read directly to
limit the simplification precisely to the needed successor transition.


Verification of the actual single-module repair: `scompile.py` compiled
`PrincipalKoszulQuotientTowers.lean` cleanly in sandbox form (20.3 s) and library form
(21.6 s), with no error or warning. No timeout limit was changed.
