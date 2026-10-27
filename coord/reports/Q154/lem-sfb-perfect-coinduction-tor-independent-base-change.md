## Worker report

The module `Sheaf.Algebra.Homology.PerfectCoinductionTorIndependentBaseChange`
states `ModuleCat.perfectCoinductionTorIndependentBaseChange`, with one postponed
proof. All three helper definitions contain real data or explicit predicates.
The accepted Q114 statement and proof plan are preserved. There is no released
repair note for this item. The old stage-1 live-wins refusal is superseded by the
stage-2 handoff in the standing brief: the accepted split has no Lean attachment.

Hypotheses and clauses, checked against the node and Stacks more-algebra.tex
0661, 0A6A case (1), 07VI, and dualizing.tex 0A70/0A71:

- The rings are `A B T D : Type u` with their four `CommRing` instances.
  `f g b q` are the four ring homomorphisms. `T` means A-prime and `D` means
  B-prime. `IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g)
  (CommRingCat.ofHom b) (CommRingCat.ofHom q)` specifies the ordinary tensor
  algebra including its two structure maps, up to its unique structural
  isomorphism. No arbitrary ring square replaces the tensor algebra.
- Perfectness is exactly `DerivedCategory.IsPerfectRingComplex` on the
  degree-zero object of B restricted along f, using `singleFunctor ... 0`.
- Positive Tor vanishing is `∀ i : ℕ, 0 < i → IsZero ...`, with Mathlib's
  first-factor `Tor'` on the two restricted regular modules. Degree zero is
  deliberately unrestricted. This is the projectively resolved first-factor
  convention of `def-weil-pbc-tor-modules`.
- Derived categories are ordinary unbounded `DerivedCategory (ModuleCat ... )`.
  Scalar extension is the recorded `ordinaryDerivedExtendScalars`; the helper
  `ordinaryCoinductionScalarPair` merely repackages that existing universal pair
  and its actual counit for the published exchange interface. Coinduction is
  the recorded `derivedCoinduction`, with its actual algebra action.
- `CoinductionTensorNormalized` fixes theta on K-flat models by the ordinary
  balancing formula. Thus theta is the canonical comparison using the
  Tor-independent identification of the derived tensor algebra with D[0].
- For every unbounded `N`, `IsIso (coinductionScalarExchange ... θ N)` is the
  asserted isomorphism in D(D). That existing definition is the adjunct of
  theta followed by scalar extension of the evaluation counit; it does not
  choose an arbitrary map or merely assert that two objects are isomorphic.
- The following quantified equality is precisely restriction of the mate
  followed by the new counit equals theta followed by the old counit after
  scalar extension. The next equality gives naturality on every derived
  morphism `v : N ⟶ M`, without a bound or representative restriction.
- `CoinductionPerfectHomFormula` identifies the underlying T-map with the
  canonical Hom base-change map. It quantifies over every bounded finite
  projective augmented resolution `E → B[0]` and every arbitrary unbounded
  K-flat target Q. `sT` has the canonical tensor-augmentation formula and is a
  quasi-isomorphism. `CoinductionHomScalarFormula` fixes every Hom product
  coordinate by `(χ(a tensor z))(c tensor x) = ac tensor z(x)`.
  `CoinductionHomModel` fixes the two Hom identifications by K-injective
  comparison. The displayed localized equality identifies this exact Hom map
  with the underlying coinduction mate, through theta and the actual counit.
  This is the ordinary-module presentation of `ordinaryModuleDerivedInternalHom`:
  Hom complexes followed by their canonical K-injective localization comparison.
- `CoinductionExchangeTower` is the existing normalized successive-extension
  equation, with its canonical scalar associators and Tor-independent direct
  extension. It quantifies over further scalar pairs, not a chosen tower.
  The separate identity clause is under the same perfectness assumption.
  `CoinductionIdentityScalarNormalized` fixes its unit identifications on
  K-flat representatives by ordinary scalar multiplication. The last equation
  identifies the counit mate with the identity under those identifications.
- The last clause of `CoinductionPerfectHomFormula` explicitly preserves the
  ordered evaluation sign `(r * n).negOnePow` in every homogeneous coordinate.
  This applies to bounded finite-free polynomial Koszul models in particular;
  it is the signed evaluation specialization of the same Hom comparison,
  including characteristic two and zero degrees. No second Koszul object or
  alternate sign convention is introduced.
- No Noetherianity, scalar flatness, surjectivity, boundedness of N, or
  nonzero-ring hypothesis is added.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex` (bounded finite-projective definition).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `DerivedCategory.Q`, `DerivedCategory.singleFunctor`.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`:
  `ModuleCat.OrdinaryDerivedChangeOfRings`, `ordinaryDerivedChangeOfRings`,
  `ordinaryDerivedExtendScalars`, with fields `counit`, `universal`, `computes`.
- `Sheaf.Algebra.Homology.DerivedCoinductionAdjunction`:
  `ModuleCat.derivedCoinduction`, `derivedCoinductionAdjunction`; the shared
  model predicates also use `derivedCoinductionModel` and
  `coinductionComplexFunctor` to normalize the K-injective Hom comparison.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`:
  `CategoryTheory.ordinaryModuleDerivedInternalHom`, the existing ordinary
  closed derived-Hom presentation used by the normalized Hom models.
- `Sheaf.Algebra.Homology.PerfectCoinductionTorIndependentExchange`:
  `ModuleCat.CoinductionScalarPair`, `CoinductionTensorNormalized`,
  `coinductionScalarExchange`, `CoinductionHomScalarFormula`,
  `CoinductionHomModel`, `CoinductionExchangeTower`; their complete signatures
  and normalizations were read. Their new definition owner
  `def-sfb-perfect-coinduction-exchange-data` is added to stmt_deps; the exchange
  theorem remains in proof_deps. No definitions are copied.
- `Mathlib.CategoryTheory.Monoidal.Tor`: `CategoryTheory.Tor'`; its existing
  owning definition node was added to stmt_deps. This derives in the first
  argument, exactly as in the node's free-resolution argument.

The stated proof-dependency modules are imported, either directly or through
public imports of the exchange module. The ringed-site perfect RHom map and its
isomorphism theorem are proof imports; the ordinary normalized Hom comparison
is used for the actual statement, so there is no change of module categories.
The remaining scalar-calculus proof dependency has no Lean declaration and
therefore has no import.

Edge cases checked: zero ring and zero N (no `Nontrivial` assumption); identity
extension with actual unit identifications; degree-zero Tor may be nonzero;
arbitrary unbounded N via unbounded K-flat Q; nonflat Tor-independent extension
(for example Z to F_p with B=Z); ordered evaluation in degree zero and in
characteristic two; successive extensions require the indicated Tor independence.
Rings can be lifted to a common universe; no relation between site object and
morphism universes occurs in these ordinary module categories.

Searches before writing (saved output is `searches.jsonl`):

- msearch leanfinder: “Derived coinduction of a perfect algebra commutes with Tor
  independent base change preserving evaluation counits”. Eight hits concerned
  cotangent complexes and representation Tor; none stated the item.
- msearch loogle: `ModuleCat.coextendScalars, ModuleCat.extendScalars`: no hits.
- msearch grep: `coinduction.*[Bb]ase[Cc]hange|[Bb]ase[Cc]hange.*[Cc]oinduction`:
  no Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, and the required node-id
  search in `WeilConjectures`: no declaration of this node. The existing
  exchange theorem is a component with derived Tor independence and a
  degree-zero-target resolution formula, rather than this positive-Tor-vanishing
  statement with arbitrary unbounded-target Hom identification. It is reused.
- Final full-name searches in both project source trees found no collision for
  any of the four delivered declarations.

The existing exchange helpers now receive the definition owner described below. No statement correction
or `STATEMENT-DISPUTED` flag is needed. The module compiles through the prescribed
`scompile.py`, with no errors or warnings.

## Second reading by Q154

This is a second pass by the dispatched worker, not a claim of an independent
reviewer; the brief assigns the independent reading to the maintainer. I reopened
the node and final file and checked every clause against the correspondence above.
The interrupted draft's tautological and ill-typed coherence placeholders were
removed. The final file reuses the landed normalized exchange predicates, writes
an actual identity equation, and extends the underlying Hom-coordinate equation
to arbitrary unbounded K-flat targets. The identity clause retains perfectness,
so it does not silently strengthen the node. No source statement was changed.


## New nodes

`def-sfb-perfect-coinduction-exchange-data` owns the seven existing plain
structure/definition declarations in the unchanged published module
`Sheaf.Algebra.Homology.PerfectCoinductionTorIndependentExchange`: the scalar pair,
tensor normalization, actual counit mate, K-injective Hom model, homogeneous Hom
scalar formula, scalar-composition normalization, and tower predicate. Its
`lean.existing: true` record copies no Lean file. The self-contained statement
spells out each definition, rather than asserting the exchange theorem. Its
source is dualizing.tex equation-base-change, 0A70/0A71, and more-algebra.tex
0661, 0A6A and 06Y6, read in this repair. LeanSearch and LeanFinder each returned
eight ordinary adjunction/coherence hits, and Mathlib grep returned zero hits
for the six requested helper names. Project searches locate the exact helpers
only in the existing Sheaf exchange module; DAG hits are theorem records, not
definition owners. `blueprint_refs.py search coinduction` returned zero matches;
the ancestor command returned None, preserved with the full inherited via list.
The new node records the actual three search-log results and the project search.

## Return repair: immutable head 35da431ffd9c

H2: replaced `lem-sfb-perfect-coinduction-tor-independent-exchange` in the item's
stmt_deps by `def-sfb-perfect-coinduction-exchange-data`. The exchange theorem is
still in proof_deps, and the proof plan is unchanged. The new definition owner
lists all six requested declarations, plus `CoinductionScalarCompNormalized`,
which the tower predicate itself uses. I read their complete signatures and
bodies, including the K-flat equations, K-injective comparison, and tower
quantifiers. These are plain definitions, independent of the postponed theorem.

H3: added `def-sc-module-total-hom-complex` to the item's stmt_deps. Its recorded
upstream declaration is `CochainComplex.moduleHomComplex` in
`WeilConjectures.Algebra.Homology.ModuleHomComplex`, whose complete definition
and signed differential were read. This is exactly the Hom complex used directly
throughout `CoinductionPerfectHomFormula`.

The Lean file and theorem signature remain byte-identical to the returned
packet; the mathematical clause-by-clause review is retained. The public
OrdinaryModuleDerivedInternalHom import is retained with its original recorded
statement dependency; the unused-import comment was advisory. No statement,
proof step, or proof dependency changes. Compared with current main, the item
still differs only in lean and stmt_deps. The initial saved-packet dry run passed;
the repaired packet is checked again before delivery.

## Second reading by Q154: repair self-check

I read the new definition statement against each existing body: the scalar pair
retains the universal and K-flat counit fields; tensor normalization quantifies
over all balancing isomorphisms with the pure-tensor formula; the mate uses the
actual adjunction bijection; the Hom model quantifies over every K-injective I
and map l (no quasi-isomorphism premise is invented); the Hom scalar formula
quantifies over every homogeneous coordinate; scalar associators are pinned by
the counits; and the tower predicate retains every further pushout, scalar pair,
direct Tor identification and unbounded M. Zero rings, zero complexes, identity
maps and arbitrary unbounded targets remain allowed. The definition node adds
no existence theorem and no IsIso claim. Each used plain exchange helper is
listed in this owner, and each direct moduleHomComplex use has its existing
owner in stmt_deps. Both return points are repaired without changing the Lean.
This is the worker's self-check; the independent review remains the maintainer's.

The repaired-packet dry run requested the standard `import_flags` key on the new
definition node; it is now the empty list. Single-file server compilation passed
without errors or warnings. The full dry run is repeated after this metadata fix.
