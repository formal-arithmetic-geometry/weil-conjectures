## Worker report

Repair validation (2026-10-21): the initial dry run of the retained packet passed
as commit 923cca002e1. This repair implements both dependency-record changes requested
by the maintainer on returned head 7f39e44a5d47. The accepted Lean module and its
verbatim theorem statement are retained. Repaired-packet validation is recorded below.

The proposed module is `Sheaf.CategoryTheory.KoszulFibreLinearDescent`, with main theorem
`CategoryTheory.koszulFibreLinearDescent`. It has one postponed proof, that theorem.
`KoszulFibreLinearDescentData` is a transparent proposition packaging the clauses of this
one node, not an extra hypothesis of the theorem. Its data witnesses are specified by
complete coordinate identities. The four abbreviations expose existing constructions;
none chooses data from an existence theorem. No mathematical statement correction was made.

Hypothesis and clause correspondence:

- A small site is `{S : Type u} [SmallCategory S] {J : GrothendieckTopology S}`. The
  module-sheaf coefficient universe is `u`, and `HasDerivedCategory.{w}` explicitly fixes
  the derived morphism universe; the coefficient ring `A : Type v` has an independent
  universe. These bind the size convention, not a geometric restriction.
- The commutative ring sheaf is `O : Sheaf J CommRingCat.{u}`. The action of the
  commutative ring `A` is the actual ring homomorphism `α` to `RingCat.sectionsSubring`.
  The proposition installs the existing `scalarLocalizationCoefficientLinear A O α`;
  derived Hom modules use Mathlib's induced `DerivedCategory.instLinear`. These are the
  prescribed actions, not arbitrary linear-category structures supplied by a hypothesis.
- Exact countable products are precisely the theorem binder `CountableAB4Star` on
  `SheafOfModules` over the underlying sheaf of rings. Existence of products and the
  abelian structure are the existing module-sheaf structures.
- The finite list is `r : ℕ`, `b : Fin r → ...sections`. No positivity assumption on r
  occurs. `ringedKoszulDualTower` is the published strict negative Koszul tower: it is
  the dual of the ordered positive tensor. Under its canonical finite-free duality
  identification, it has degrees [-r,0], differential b_j^(m+1) and transitions (b_j,1).
  This is the Koszul model explicitly used in Stacks 0A0E's proof. Index m here is the
  paper's positive index m+1.
- `koszulFibreProduct` is the Mathlib product of the actual `ringedKoszulTensorTower`
  values M tensor Q_m. `koszulFibreEndomorphism` is the published
  `towerTransitionEndomorphism` of its actual maps, hence exactly 1-s. `koszulFibreProductMap` is the product
  of the actual tensor maps a tensor 1, using the published tower functor on chain maps.
- The witnesses F and χ in `KoszulFibreLinearDescentData` have objects in degree i
  isomorphic to B(M)^i biproduct B(M)^(i-1). The first conjunct specifies the complete
  differential `(dx,(1-s)x-dy)`, including the degree transport. The second specifies
  F(a) as the product map on both coordinates. Thus neither an unrelated derived
  functor nor an arbitrary cone with merely the right isomorphism classes can satisfy
  the specification. These coordinate conditions determine the functor up to the
  unique isomorphism preserving its coordinates.
- `η` is a natural transformation id to F, and the third conjunct specifies its
  coordinates as `(koszulFibreProductUnit,0)`. That product unit is a real `Pi.lift`
  of the previously constructed degree-zero inclusions. The witness π is fixed by
  the fourth conjunct to be the actual first projection in these coordinates.
- The homotopy conjunct sends every nonempty `Homotopy a a'` to a nonempty homotopy
  between F(a) and F(a'). The following conjunct preserves every `QuasiIso a`.
  `F.Additive` and `F.Linear A` give the two scalar-linear identities on complexes.
- The zero comparison is an isomorphism `z : F.obj 0 ≅ 0` identifying the unit with
  the unique zero map. `IsIso (biprodComparison F M N)` makes the binary comparison
  the canonical map given by F of the projections. The same conjunct gives its unit
  identity, and the following conjunct states its naturality for every pair of maps.
- The witnesses D, κ and e give a derived endofunctor, a natural coaugmentation and
  the localization isomorphism `F ⋙ Q ≅ Q ⋙ D`. `D.Additive`, `D.Linear A`, and the
  explicit equality `D.map (t • a) = t • D.map a` include arbitrary derived morphisms.
  `Q.map (η.app M) ≫ (e.app M).hom = κ.app (Q.obj M)` specifies the descended unit.
- For every M the natural isomorphism of tower functors compares the localized strict
  tensor tower with the published derived tensor applied to Q_m. It includes all
  transitions, not just individual level objects. The subsequent existential product,
  p and δ satisfy the recorded `IsDerivedLimitTriangle` for the actual localized
  tower maps. The equation involving e, p, the product projections and Q(π) fixes the
  first projection to be the strict model's first projection. This supplies the
  required derived-limit representation and its specified strict coaugmentation.
- The final full subcategory is exactly the object property `IsIso (κ.app M)`.
  `HasZeroObject` and `HasBinaryBiproducts`, with the inherited preadditive structure,
  say that it is additive. The inclusion's `Functor.Linear A` uses the full
  subcategory's inherited Hom modules, rather than a separate arbitrary action.

Dependency declarations read and reused:

- `def-weil-size-convention`: metatheoretic record; explicit universes implement it.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`;
  the underlying category is exactly Mathlib's `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` and its localization instance.
- `Mathlib.Algebra.Homology.BifunctorShift`, `CochainComplex.mapBifunctor`;
  the existing `ringedKoszulTensor` uses this signed total tensor construction.
- `Mathlib.CategoryTheory.Linear.LinearFunctor`, `CategoryTheory.Functor.Linear`;
  additivity is stated separately, as required by this declaration's signature.
- `Mathlib.CategoryTheory.Functor.OfSequence`, `Functor.ofOpSequence` and
  `NatTrans.ofOpSequence`: tower indexing and transition-natural morphisms.
- `Mathlib.CategoryTheory.Limits.Shapes.Products`, `piObj`, `Pi.π`, `Pi.lift`,
  `Pi.map`; countable products from `Shapes.Countable`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`, `IsDerivedLimitTriangle`;
  its middle arrow is the recorded `towerTransitionEndomorphism`.
- Added already-landed statement dependency `def-weil-pbc-ringed-koszul-system`:
  `Sheaf.CategoryTheory.RingedKoszulSystem`, `ringedKoszulDualTower`,
  `ringedKoszulTensorTower`, `ringedKoszulTensorTowerComplex`, its map and
  `ringedKoszulTensorUnitComponent`. These avoid a duplicate Koszul construction.
- Read `Sheaf.CategoryTheory.StrictRoosModel` and its `roosP`, `roosU`, `roosPmap`.
  The helpers here specialize Mathlib products directly to the actual tensor tower,
  avoiding the tower-to-complex conversion's reconstructed differentials. Its
  shifted-cone signs are not silently substituted for this node's coordinates.
- Added already-landed statement dependency
  `def-weil-pbc-scalar-localization-coefficient-actions`:
  `Sheaf.CategoryTheory.ScalarLocalizationDerivedHom`,
  `CategoryTheory.scalarLocalizationCoefficientLinear`. This is the plain definition
  restricting the existing global-section Hom action along α, not a choice from the
  Hom-comparison theorem. Its signature and docstring at lines 77-92 were reopened.
  The definition node's lean-only repair explicitly records this underlying action.
- Added already-landed statement dependency `lem-weil-pbc-site-derived-tensor-descent`:
  `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`,
  `SheafOfModules.site_derived_tensor_descent_independentCoefficients` and
  `SheafOfModules.siteDerivedTensorIndependentCoefficients`. The latter exposes the
  tensor selected by the theorem's localization/representative universal property.
  The theorem is needed in the statement, not merely its proof: the tower comparison
  uses `SheafOfModules.KFlatFixedTensor.derivedTensor`, whose definition at
  `KFlatFixedTensorTriangulated.lean:69` is precisely the curry of this tensor.
  Its public import already exposes the site-descent module; no Lean import or
  mathematical clause needs changing.
  Other stated proof dependencies are imported without `public`: RoosCoordinatesQuasiIso,
  BoundedAboveFlatSheafKFlat, DerivedCountableProductsCore and Mathlib localization.
  `lem-weil-linear-abelian-derived-category` and `lem-sfb-linear-localization-descent`
  match the imported Mathlib DerivedCategory.Linear and Localization.Linear declarations.
  `lem-pur-additive-localization-descent` has no recorded Lean or Mathlib match on this
  checkout, and so has no proof-only module to import; its use remains in the proof docstring.

Source read: `literature/stacks-project/algebraization.tex`, lines 1090-1141,
`lemma-derived-completion-koszul`, including its identification of the negative Koszul
complex as the dual of the positive finite-free complex. The node's complete ten-step
refinement is included in the theorem docstring, including all relevant signs and
localization arguments.

Edge cases checked mathematically before drafting: r=0 gives the constant O[0] tower
and derived completion is the identity; M=0 gives the zero fibre and its unique unit;
b_j=0 does not require regularity and the tower construction is still defined; a unit
generator makes its Koszul factor contractible and completion zero; the zero coefficient
ring and empty site give zero module categories and do not invalidate any binder.
Unbounded M is retained. No nonzero ring, Noetherian, boundedness, regular-sequence or
positivity assumption was introduced. There is no STATEMENT-DISPUTED finding.

Searches actually run:

1. `msearch.py ... leanfinder "The explicit product mapping fibre of tensor with finite
   Koszul complexes induces an additive scalar linear derived completion functor"`:
   eight results, including HomologicalComplex.HasTensor/tensorObj/ιTensorObj and
   CategoryTheory.Tor. None supplies this coordinate model, its unit and its linear descent.
2. `msearch.py ... loogle "CochainComplex.mapBifunctor, Functor.Linear"`:
   zero results; the service reported `unknown identifier 'Functor.Linear'`. This is a
   query-resolution failure, not evidence of absence of the fully qualified declaration;
   its Mathlib source was located and read directly.
3. `msearch.py ... grep "koszul|Koszul" Algebra/Homology`: one hit,
   Mathlib/Algebra/Homology/LocalCohomology.lean:45, a roadmap comment about Koszul homology.
4. `rg` over `lean/Sheaf` for Koszul fibre/completion/tower names located the actual
   ringed-site system and several specialized pro-etale completion modules. None states
   this general exact-product scalar-linear descent with all its clauses.
5. `rg` over `lean/WeilConjectures` for Koszul and `grep -rn` for this node id:
   no exact statement match; the Koszul hits include monoidal sign and trace material.
6. Direct source searches located the canonical coefficient-linear structure and the
   generic strict Roos product; the coefficient action and underlying Mathlib product
  operations are reused. No new definition node is necessary.

## Second reading by Q36

This is the resumed worker's self-check; no independent agent was started, as the
current dispatcher brief expressly forbids that. The maintainer's independent
review remains the separate mathematical review of this packet.

I reopened the current DAG statement, all ten proof steps, the saved module, and
the published Koszul tower, its unit and tensor interfaces. The small-site and
commutative coefficient/action binders, CountableAB4Star, arbitrary finite r including
zero, unbounded complexes, the product of the negative Koszul tensor tower, both
fibre coordinates and the signed differential all match the node. The explicit
coordinate equations give the prescribed map on chain maps, unit and first
projection. The homotopy and quasi-isomorphism clauses, additive and A-linear
complex and derived functors, localization comparison and unit identity, full tower
comparison with derived tensor, distinguished Roos triangle and projection identity,
zero and canonical binary biproduct unit identities and naturality, and the additive
full subcategory with inherited A-linear Hom modules account for the remaining
clauses. The positive indexing m+1 covers exactly the node's m >= 1. The
r=0, M=0, zero generators, unit generators and zero coefficient cases remain included.

The first dry run now reached this module, exposing only elaboration/interface
errors. Repairs specify the tower family K in towerTransitionEndomorphism, use
Limits.Pi.map with explicit source and target families, open Mathlib's ZeroObject
scope, qualify Functor.biprodComparison, and invoke ObjectProperty.FullSubcategory
and ObjectProperty.ι explicitly. No mathematical clause, assumption or theorem
signature changed; no additional theorem or definition was introduced. The subsequent returned-delivery repair below supersedes the dependency records
from that validation; the accepted mathematical statement remains unchanged. The source has no line over 100 columns,
uses autoImplicit false with explicit universes, and leaves exactly its named main
theorem as sorry. A fresh collision search in Sheaf and WeilConjectures found no
existing declaration with either main name. The successful scompile.py call returned
exit 0 with no errors or warnings in either file-level compile.

## Dependency modules

`def-weil-pbc-scalar-localization-coefficient-actions` receives a §1(B) lean-only
repair, with `existing: true` on the same module
`Sheaf.CategoryTheory.ScalarLocalizationDerivedHom`. Its recorded declarations
previously omitted the plain module-sheaf coefficient action used by this item.
The repair adds `CategoryTheory.scalarLocalizationCoefficientLinear` and explains
that omission in `lean.note`, preserving the primary derived-action declaration
and the localized coefficient map. No dependency source module is added or changed;
every field outside `lean` is identical to the current main node.

## Returned-delivery repair and second reading, 2026-10-21

1. H2/H4, coefficient action: replaced the item's statement dependency
   `lem-weil-pbc-scalar-localization-derived-hom` by the existing definition node
   `def-weil-pbc-scalar-localization-coefficient-actions`. Added its plain definition
   `CategoryTheory.scalarLocalizationCoefficientLinear` to that node's
   `lean.declarations`, with the required explanatory `lean.note`. No theorem choice
   is used by the coefficient action; it explicitly installs `SheafOfModules.homLinear`
   and restricts the scalar action along the given ring homomorphism α.
2. Derived tensor: added `lem-weil-pbc-site-derived-tensor-descent` to the item's
   `stmt_deps`. Reopened `KFlatFixedTensor.derivedTensor` and
   `siteDerivedTensorIndependentCoefficients`, confirming the chain from curry to the
   tensor selected by the site's derived-tensor descent theorem. The statement's
   full tower comparison thus cites the theorem determining the tensor it uses.

Compared the retained packet with current main by parsing the node JSON and reading
both source paths, without Git commands. Current main has no item Lean module;
the saved module retains the source accepted by the immutable-head review. Only the
item's `lean`/`stmt_deps` and the coefficient dependency's `lean` differ from main.
No item statement, proof, proof dependency, hypothesis, conclusion, sign, unit,
projection, universe, or edge case was altered. The clause correspondence and
r=0, M=0, b=0 checks in the Worker report and Second reading remain applicable.
No new node, new definition, statement correction, or disputed statement is introduced.

Repaired-packet self-check: the item's verbatim Lean signature, one named postponed
theorem, explicit binders and 100-column limit pass. The dependency node changes only
`lean`; the item changes only `lean` and `stmt_deps`. The resulting dependency reach is
acyclic (303 nodes). The prescribed `scompile.py` passed with exit 0 and no diagnostics:
sandbox 31.2 seconds, library module 22.5 seconds. Both phases retain the 60-second limit.
