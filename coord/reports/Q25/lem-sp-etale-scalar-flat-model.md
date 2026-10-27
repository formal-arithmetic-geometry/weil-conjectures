## Worker report

Repair of returned immutable head `26c82bd64254`, findings H13 and H2.
The delivery contains one new statement module,
`Sheaf.AlgebraicGeometry.EtaleScalarFlatModel`, and its owning node record.
Its sole theorem is `AlgebraicGeometry.Etale.exists_etaleScalarFlatModel`, with
whole proof `sorry`. The node's mathematical statement, statement dependencies,
proof plan and proof dependencies agree with the current live node. Only `lean`
changes. There is no statement correction, new node, or dependency-record repair.

### Returned findings repaired

H13: removed the sandbox replacement of `lem-pur-derived-change-of-rings`.
The delivery makes no change to that node, so its live NZ record remains
byte-identical: module `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`,
primary `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`, with the
structure and existence theorem retained in `lean.declarations`. Its recorded
module is imported publicly, and the existing general ringed-site interface is
preserved. In particular this delivery neither replaces the general theorem by a
constant-coefficient specialization nor drops any declaration used by its citers.

The theorem now names
`AlgebraicGeometry.ProEtale.pbcFixedScalarExtension T.smallEtaleTopology φ`
directly, imported from `Sheaf.Paper.WitnessCompatibility`, as the return permits.
Its source fixes the functor to the left adjoint of actual derived restriction;
`pbcRestriction_isRightAdjoint` is obtained from the ordinary sheafified scalar
adjunction and its derived adjunction, with no flatness assumption. The ordinary
complex uses `AlgebraicGeometry.ProEtale.etaleSheafExtendScalars φ T`, defined in
`WeilConjectures.SixFunctors.ProEtale.ScalarExtension` as sheafified
`ModuleCat.extendScalars`. `Sheaf.Paper.EtaleDerivedScalarTensor` is imported for
its existing `scalarSheafExtension_additive` instance, which lets this ordinary
functor act on cochain complexes. That module supplies no replacement DAG record
in this packet. No shared dependency module is edited, so no changed importer
interface needs a clash audit; the repaired consumer itself is compiled with all
these imports together.

H2: restored exactly the live `stmt_deps`, removing the added existing node
`def-weil-pbc-constructible-complexes`. The statement now inlines its two clauses
using notions already recorded by the original dependencies: `K` belongs to
`DerivedCategory.Bounded` and `_hK` asserts
`Scheme.IsConstructibleEtaleModuleSheaf` for every cohomology sheaf of `K.obj`.
The conclusion likewise states that the specified extension is isomorphic to an
object of `DerivedCategory.Bounded`, and separately asserts constructibility of
every cohomology sheaf. The direct import of `BoundedConstructibleComplexes` was
removed; that predicate does not occur in the theorem signature. It may still
be imported internally by the unchanged proof-dependency module.

### Hypothesis and clause correspondence

- Noetherian scheme: `(T : Scheme.{u}) [IsNoetherian T]`, including quasi-compactness
  and local Noetherianness.
- Finite commutative unital rings: `(A B : Type (u + 1)) [CommRing A] [CommRing B]
  [Finite A] [Finite B]`. The arbitrary unital map is `(φ : A →+* B)`.
- Ordered integer endpoints: `(a b : ℤ) (_hab : a ≤ b)`.
- `K ∈ D^b(T_et,A)`: `K : DerivedCategory.Bounded
  (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))`. Its ambient object is `K.obj`.
- Constructible cohomology: `_hK` quantifies all `i : ℤ` and applies the recorded
  finite-value `Scheme.IsConstructibleEtaleModuleSheaf` to
  `(DerivedCategory.homologyFunctor _ i).obj K.obj`.
- Tor interval: `_hTor : DerivedCategory.hasTorAmplitudeIn A T a b K.obj` tests
  every A-module sheaf in degree zero with derived tensor, vanishing below a or
  above b; no finite-generation restriction on these tests is added.
- Existence of a representative: the first conjunct quantifies an actual
  `CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat A)) ℤ`.
  `∀ q, exactFunctor _ _ (tensorRight (P.X q))` is flatness of every term;
  `∀ q, Scheme.IsConstructibleEtaleModuleSheaf (P.X q)` is its constructibility;
  `∀ q, q < a ∨ b < q → IsZero (P.X q)` is the exact term support; and
  `Nonempty (DerivedCategory.Q.obj P ≅ K.obj)` is representation of K.
- Every such representative: the next conjunct universally quantifies a fresh P
  and assumes exactly those same four properties. No particular model is chosen
  for this universal assertion.
- Both K-flatness clauses use the published `MorphismProperty.kFlat`, specialized
  to quasi-isomorphisms and `HomologicalComplex.monoidalCategory` on cochain
  complexes. These are the full unbounded coproduct total tensors. Preservation
  of quasi-isomorphisms under tensor is equivalent to acyclic-tensor K-flatness
  in this additive symmetric monoidal category.
- Ordinary extension: `((ProEtale.etaleSheafExtendScalars φ T).
  mapHomologicalComplex (.up ℤ)).obj P` extends each differential. It is a genuine
  B-module complex on the ordinary small-etale site. Its presentation
  B tensor_A P has B acting on B and is canonically symmetric to P tensor_A B
  with the requested action on its second factor.
- Separate conjuncts assert flatness and constructibility of every extended
  term, and zero terms outside the same [a,b].
- The displayed representation is `Nonempty (K_B ≅ DerivedCategory.Q.obj Q)`
  in the B-module derived category, where K_B is explicitly
  `(ProEtale.pbcFixedScalarExtension T.smallEtaleTopology φ).obj K.obj` and Q is
  exactly that ordinary extended complex. Neither an arbitrary comparison
  functor nor an isomorphism after forgetting B is substituted.
- Boundedness of K_B: `∃ L : DerivedCategory.Bounded (Sheaf ... (ModuleCat B)),
  Nonempty (L.obj ≅ K_B)`. The full subcategory is closed under isomorphism,
  so this says precisely that K_B belongs to D^b.
- Constructible cohomology of K_B: the following conjunct quantifies every i
  and applies `IsConstructibleEtaleModuleSheaf` to its actual homology sheaf.
- Tor amplitude of K_B: `DerivedCategory.hasTorAmplitudeIn B T a b K_B` tests
  all B-module sheaves, including those not induced from A.
- No flatness, surjectivity, nonzero-ring, or finite-projective-dimension
  hypothesis is imposed on φ or B/A.

### Dependency declarations and sources read

- `def-weil-pbc-derived-categories`: module
  `WeilConjectures.AlgebraicGeometry.DerivedCategories`, exposing
  `AlgebraicGeometry.Etale.DerivedCategoryModule` (defined in
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`),
  `DerivedCategory.Bounded` and `DerivedCategory.homologyFunctor`.
  Read the Mathlib `DerivedCategory.TStructure` full-subcategory definition and
  inclusion of `Bounded`.
- `def-weil-pbc-etale-constructible-sheaf`: module
  `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`, declaration
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`. Its finite
  stratification, immersions, etale covering and finite module values are used.
- `def-kun-tor-amplitude`: module
  `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`, exposing the existing
  `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn`; its full signature
  and definition in `Etale.Derived.Coefficients` were read.
- `def-pc-cochain-complex-modules`: module
  `Mathlib.Algebra.Homology.HomologicalComplex`, declaration `CochainComplex`.
- `def-pc-flat-sheaf-modules`: module
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`, recorded
  `CategoryTheory.exactFunctor`; its node expressly permits exact tensorRight
  in the ordinary ModuleCat-valued encoding.
- `def-pc-kflat-complex`: module
  `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`, recorded companion
  `CategoryTheory.MorphismProperty.kFlat`; the node expressly exposes this
  predicate for the ordinary ModuleCat-valued encoding. Read its left and
  right tensor localizer conditions in `FromJoel.CategoryTheory.Monoidal.KFlat`.
- `lem-pur-derived-change-of-rings`: unchanged recorded module
  `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`, structure
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and theorem
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`. Read the structure's
  ordinary object/map formulas, K-flat invariance, separate localization
  universes, pointwise existence, universal counit, triangulatedness and
  computation clauses, and the existence theorem's full docstring/signature.

Stated proof dependencies remain imported as required: `EtaleFlatConstructibleModel`,
`BoundedAboveFlatSheafKFlat`, `ChangeOfRingsKFlat`, the above general
`DerivedChangeOfRingsCochainModel`, and upstream `DerivedCategory.FlatModel`.
Their full statement signatures and proof docstrings were read.
`lem-sp-constructible-coefficient-site-square` has no recorded Lean module;
its ordinary-etale input remains cited in step 4 of the proof docstring and
provides no missing notion needed to type this theorem.

Sources reread: Stacks `etale-cohomology.tex`, `lemma-when-ctf` (03TT), including
its final specified-interval assertion, and `lemma-tensor-constructible` (0GKB),
including its same-stratification hint. All six DAG proof steps remain in the
theorem docstring. No new theorem beyond the assigned node is postponed.

### Edge cases

- Empty scheme and K=0: boundedness, support and all universal test clauses
  still make sense; no positive number of strata is assumed.
- Zero rings: no Nontrivial instance is required. Maps into the zero ring and
  the necessarily zero target of a unital map out of the zero ring remain allowed.
- a=b: the model can consist of one flat constructible sheaf in that degree;
  no strict endpoint inequality is imposed.
- Identity coefficient map: the same ordinary extension represents K.
- Nonflat finite map Z/4 to Z/2 with model A[0]: the extended B[0] is B-flat and
  B-K-flat despite B not being A-flat and having infinite A-projective dimension.
- Non-surjective finite ring maps are allowed. The scheme and coefficients use
  the existing u and u+1 convention, with no additional universe equality.

Searches performed:

- `msearch.py ... leanfinder` with query "Bounded constructible etale flat complexes
  remain flat constructible K-flat after arbitrary extension of finite coefficient
  rings": eight hits, including scheme/ring flatness and
  `ModuleCat.preservesFiniteLimits_extendScalars_of_flat`; none states this result.
- `msearch.py ... loogle 'CategoryTheory.Sheaf, "flat"'`: one hit, a representably
  flat site-functor sheaf-pullback instance; no coefficient-model theorem.
- `msearch.py ... grep 'changeOfRing|scalarExtension|extendScalars'`: 25 reported
  ordinary ring/module scalar-extension hits; no constructible etale model theorem.
- `rg` in `lean/WeilConjectures` for this node id returned no match. The upstream
  name index also has no attachment for this new item.
- `rg` for scalar-extension, flat/constructible and Tor/constructible patterns
  in Mathlib, `lean/WeilConjectures` and `lean/Sheaf` located the reused APIs,
  `EtaleFlatConstructibleModel`, and `FiniteCoefficientInputModels`. The latter
  has extra prime-power hypotheses and etale/pro-etale conclusions and only
  chooses one model; it does not state this arbitrary finite-ring result and
  its universal representative clause. The scalar/tensor companion gives a
  canonical derived comparison, not model existence or constructibility.


### Validation

The saved packet first passed the prescribed `deliver2.py --no-push` dry run
(commit `710cca04267`), confirming the static checks did not themselves catch
these independent-review findings. Both findings were then repaired as above;
that original passing packet is not the final delivery. The repaired module passed `scompile.py` cleanly: sandbox 14.0 s and
library module 19.6 s, with no compiler messages. The final packet is checked
by `deliver2.py --no-push` and delivered with `deliver2.py`. No repository edits, direct Git
commands, global builds, new definitions or dependency-record changes are made.

## Second reading by Q25

Self-check against the node and repaired Lean signature: matched Noetherianness,
the arbitrary map of finite unital commutative rings, a ≤ b, boundedness,
constructible cohomology, universal Tor tests, model existence, every-model
quantifier, both K-flatness clauses, all three term properties after ordinary
extension, the B-linear derived representation, and bounded constructibility
and Tor amplitude of the specified K_B. H13 is repaired by preserving the entire
live dependency attachment and using the permitted existing fixed functor.
H2 is repaired by using bounded-category membership plus individual constructible
cohomology clauses without changing stmt_deps. No independent worker review is
claimed; the maintainer performs the independent reading.
