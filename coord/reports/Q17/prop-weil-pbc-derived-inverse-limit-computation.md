## Worker report

The item reuses the published theorem
`CategoryTheory.derivedCategory_towerLimit_core` in
`Sheaf.CategoryTheory.Triangulated.DerivedLimitTower`, with `existing: true`.
No new Lean module, definition, theorem or proof is delivered. The node copy
changes only `lean`; the recorded signature is verbatim the existing source.

This is the general-tower computation already used by clause (3) of
`lem-weil-derived-limit-existence`, not a bounded-below truncation theorem.
It states that the limit of a K-injective complex of towers represents the
triangulated derived limit of the system it represents. The item's exact
specialization is the following. Here B denotes modules over the completed
ring sheaf A_T, not the constant coefficient sheaf associated to A.

| Node hypothesis or clause | Lean rendering / specialization |
| --- | --- |
| T and the adic coefficient datum | Read `def-weil-pbc-adic-coefficient-datum` in full. Set the theorem's category parameter `A` to `B = Mod(A_T)`, using its actual inverse-limit coefficient sheaf. |
| The category Tow_A(T) | `ℕᵒᵖ ⥤ B`; Lean n corresponds to positive level n+1. |
| M is an arbitrary object of its unbounded derived category | `M : DerivedCategory (ℕᵒᵖ ⥤ B)`. Choose a complex representative only to express the given resolution; this is not a restriction on M. |
| M → I is a resolution in the abelian category of towers | A quasi-isomorphism `q : C ⟶ I`, where C represents M and `I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ`. This is a chain map of towers, so it commutes with all tower transitions. |
| The resolution is K-injective | The argument `[I.IsKInjective]` is Mathlib's generic K-injectivity in the tower category, not K-injectivity of each level asserted as an extra assumption. |
| The evaluated system of M | `K n = (((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory).obj M`. Exact evaluation descends termwise to the derived category. |
| Its successive transitions | `f n : K (n+1) ⟶ K n` is the descended evaluation transformation induced by `(homOfLE (Nat.le_succ n)).op`. The maps are those of M. |
| I represents that entire inverse system | `_e : I.asFunctor ⋙ DerivedCategory.Q ≅ Functor.ofOpSequence f`. This is supplied by the resolution and its representative isomorphism. It is a natural isomorphism, so it preserves transitions; it is not a family of unrelated object isomorphisms or an added hypothesis. |
| The termwise inverse-limit complex lim I_n | The conclusion supplies `c : Cone I.asFunctor` and `Nonempty (IsLimit c)`. The complex `c.pt` is an actual inverse limit in cochain complexes. Limits of complexes are degreewise. |
| That complex represents the sequential derived inverse limit | Exactly `IsDerivedLimit f (DerivedCategory.Q.obj c.pt)`. This is the Roos-triangle definition already recorded by `def-weil-derived-limit` and reused by `def-weil-pbc-derived-inverse-limit`. |

The limit witness is not a substitute for the specified inverse limit. It is
an actual limiting cone, unique up to the unique cone isomorphism. The published
companion `CategoryTheory.derivedCategory_towerLimit_property` in
`Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerProperty` states the same
property for **every** supplied limiting cone, so the usual chosen inverse
limit has the property as well. The main theorem also supplies existence;
there is no additional limit-existence assumption on the item's input.

The generic theorem displays the ambient hypotheses `Abelian B`,
`HasDerivedCategory B`, `HasCountableProducts B`, `CountableAB4Star B`,
`EnoughInjectives B`, and a product structure on `DerivedCategory B`. These
are properties of the coefficient category guaranteed by the item's existing
DAG, not additional hypotheses on T, A, M, I or q:

- Module sheaves form the abelian category of the adic datum. The derived
  category is the recorded unbounded localization.
- `lem-weil-pbc-ring-sheaves-grothendieck` gives the Grothendieck property of
  Mod(A_T). `lem-sp-grothendieck-enough-injectives` then supplies enough
  injectives. These are already proof dependencies of this item.
- `def-weil-pbc-derived-inverse-limit` explicitly supplies exact countable
  products through `lem-weil-proetale-countable-products-exact`. Its first
  clause is `HasCountableProducts`; products preserve kernels, and its
  epimorphism clause gives right exactness, hence `CountableAB4Star`.
- `CategoryTheory.derivedCategory_countableProducts_core` (also the first
  part of `derivedCategory_countableProducts_and_towerLimit`) supplies hP.
  No choice of hP changes the represented derived-limit property.

Thus this is precisely the existing computation after specializing its
ambient category and represented system. It does not assert a different
coefficient category, impose degreewise injectivity, require epimorphic
transitions, or assert functorial choice of a triangulated derived limit.
The property means an object admits the specified Roos triangle; any other
object denoted Rlim M is isomorphic to it by clause (1) of the existing
existence theorem. No canonical isomorphism between arbitrarily chosen
triangles is claimed.

### Dependencies and sources read

All five statement-dependency node statements and records were opened.

- `def-weil-pbc-adic-coefficient-datum` currently has no recorded declaration
  in the shared DAG. Its full statement fixes B and the strict tower category.
  I checked the server source with `scompile.py --source
  Sheaf.Paper.AdicCoefficientDatum`: unavailable. I also inspected Q02's
  coefficient-datum sandbox and the delivery-ref inventory. Its in-progress
  module is not imported or copied. This existing-theorem attachment needs
  no new coefficient construction: the theorem applies to B exactly as the
  already recorded clause (3) does. Defining a private B or replacing A_T
  by a constant ring sheaf would be wrong.
- `def-weil-pbc-kinjective-resolutions` records
  `CochainComplex.IsKInjectiveResolution` in
  `Sheaf.AlgebraicGeometry.KInjectiveResolutions`. I read the declaration
  and docstring: it is `QuasiIso f ∧ I.IsKInjective`, specialized to constant
  etale coefficients. As the item's proof explicitly explains, only this
  convention is being recalled here; its etale-specific abbreviation is
  not applied to towers. The generic definition below supplies the actual
  predicate in the correct category.
- `def-pur-kinjective-complex` is a Mathlib leaf, whose `mathlib_match` is
  `CochainComplex.IsKInjective` in
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`. I read its docstring
  and full class signature: every map from an acyclic complex is homotopic
  to zero. Together with `QuasiIso q` it gives exactly the tower resolution
  above. No new resolution predicate is needed.
- `def-weil-pbc-derived-inverse-limit` has no record in the shared snapshot;
  I inspected the already delivered Q02 record and report. It reuses
  `CategoryTheory.IsDerivedLimitTriangle` and `CategoryTheory.IsDerivedLimit`
  from `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`, specialized
  to the evaluated completed-coefficient tower. No new construction occurs
  in this definition, and no functor or object is chosen. The existing
  computation's conclusion uses that exact predicate directly.
- `def-weil-derived-limit` records
  `CategoryTheory.IsDerivedLimit` and `CategoryTheory.IsDerivedLimitTriangle`
  in the preceding published module. I read both signatures and bodies,
  including `towerTransitionEndomorphism`: it is identity minus the shift
  induced by the actual successive tower maps.

I also read the complete published sources of `DerivedLimitTower`,
`DerivedLimitTowerProperty`, `DerivedLimitExistence`, and `DerivedLimitProducts`;
the theorem signature and docstring were checked through `scompile.py --source`
as well as in the side checkout. The primary computation is already reached
by `lem-weil-derived-limit-existence`, which is a proof dependency of the
item. Its existing owner is `lem-weil-derived-limit-tower-core`. Reusing its
exact declaration avoids restating that computation.

For the ambient-category facts I opened
`Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`,
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`
(`SheafOfModules.isGrothendieckAbelian`), and Mathlib's
`CategoryTheory.IsGrothendieckAbelian.enoughInjectives` in
`CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`.
`ringedSiteModules` is transparently `SheafOfModules`. I read Mathlib's
`Functor.mapDerivedCategory` and its factorization isomorphism, and
`HomologicalComplex.quasiIso_iff_evaluation`.

The blueprint source was read in the launcher's read-only literature mirror,
`blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/
prop-weil-pbc-derived-inverse-limit-computation.md`, including its proof and
its source note distinguishing the general-tower statement from Stacks 070M's
truncation-tower example. I also read Stacks `derived.tex`, Section Derived
limits: Definition 08TC and the surrounding existence/uniqueness paragraph,
Lemma 07KC, and the bounded-below lemma 0BK7. This attachment uses the
blueprint's general-tower theorem, not an unsupported identification of that
theorem with the narrower Stacks truncation example.

### Edge cases

- Lean n=0 is positive level 1, and no quotient A/I^0 is introduced.
- Zero towers, the zero ring, and the empty scheme are allowed. No nonzero
  or nonempty hypothesis is present.
- There is no empty index set input: the fixed index is the positive integers.
- Identity and zero transitions are included; the middle Roos map always
  uses identity minus the actual successor shift.
- Complexes are unbounded and neither I's terms nor its evaluated terms
  are assumed injective. No bounded-below assumption is imported from 0BK7.
- No adic normalization, constructibility, completeness of M, flatness,
  epimorphic-transition, or Mittag-Leffler condition is added.
- The generic theorem has independent object, morphism and localization
  universes. It does not identify the small pro-etale site's object universe
  t+1 and morphism universe t. Its category parameter B accommodates the
  actual module category at its own sizes.

### Searches

All semantic calls used `msearch.py Q17
prop-weil-pbc-derived-inverse-limit-computation`.

- LeanFinder: `K-injective resolution of a tower termwise inverse limit
  computes derived inverse limit` returned eight injective-resolution and
  derived-functor hits, with no exact computation theorem in Mathlib.
- Loogle: `CochainComplex.IsKInjective, CategoryTheory.IsDerivedLimit`
  returned no hits (unknown identifier `CategoryTheory.IsDerivedLimit` in
  that service's index).
- Grep: `IsKInjective|derived.?[Ll]imit` in `Algebra/Homology` found
  Mathlib's K-injective and derived-category infrastructure, not the
  specialized inverse-limit theorem.
- LeanSearch: `The inverse limit of a K-injective complex of towers is a
  derived limit of its evaluated tower` was unavailable (Internal Server
  Error); no mathematical absence claim is based on that failure.
- Direct `rg` of the slopmaster2 `WeilConjectures` tree for the node id and
  tower/K-injective terms found no matching specialized declaration.
- Direct `rg` of side `lean/Sheaf` found the published generic computation
  above, and `rg` of the DAG found its recorded owner nodes. Full source
  inspection confirmed that it is the required general-tower computation.
- Server-source checks confirmed both the core and the arbitrary-limit-cone
  property theorem. The Q02 delivered Roos-definition reuse was read;
  unfinished coefficient definitions were not assumed published.

### Validation

The scratch-only `scratchpad/ExistingComputationCheck.lean` checks application
of the existing core and property theorems with independent universes.
It also checks localization of a genuine quasi-isomorphism of tower complexes
and its image under every derived evaluation. Its `resolutionLevelMap` is
the natural transformation obtained by termwise evaluation and localization;
the checked component isomorphism follows from
`HomologicalComplex.quasiIso_iff_evaluation`. Hence the resolution supplies
an isomorphism of the entire evaluated systems, retaining their transitions.
The scratch file is not a delivery module or a new library declaration.

There is no statement correction, new node, dependency-record repair, or
outstanding statement dispute. The prescribed dry run separately probes the
existing declaration and checks the node record against current server source.

The specialization scratch file compiled cleanly through `scompile.py` in both
its sandbox and library checks (6.9 s and 8.2 s), without warnings. The
`deliver2.py Q17 prop-weil-pbc-derived-inverse-limit-computation --no-push`
dry run printed OK: the existing declaration probe and server preflight pass,
with only the independent second-reading section reserved for the second reader.
Nothing was pushed.


## Second reading by Q17

I independently read the item node and the blueprint source at
`sec-proper-base-change/sk-thm-properbasechange/prop-weil-pbc-derived-inverse-limit-computation.md`,
then the existing theorem's complete source, also obtained through
`scompile.py --source Sheaf.CategoryTheory.Triangulated.DerivedLimitTower`.
The blueprint expressly distinguishes the arbitrary tower computation from
Stacks 070M's special truncation tower. I checked `derived.tex` Definition
08TC, Lemma 07KC, Lemma 0BK7 and Lemma 070M, and `injectives.tex` Theorem
079P. None justifies inserting boundedness, levelwise injectivity or
surjective transitions into this item's statement. The existing general
computation does not insert them.

My object/hypothesis/conclusion checklist, made before judging the attachment:

| Node item | Existing Lean and specialization | Verdict |
| --- | --- | --- |
| Scheme T and the coefficient datum of the cited definition | Specialize the theorem's category parameter to `B = Mod(A_T)`, with `A_T` the actual inverse-limit ring sheaf of `def-weil-pbc-adic-coefficient-datum`. The ring A, ideal, positive quotients, torsion, finiteness and perfectness conditions belong to that datum; the theorem works for its category B without further restrictions. | Same coefficient category; no constant-sheaf substitution. |
| Strict inverse systems of A_T-modules | `ℕᵒᵖ ⥤ B`, with index n standing for the positive level n+1. | Same tower category and levelwise compatible morphisms. |
| Arbitrary unbounded `M` in the derived category of towers | Choose a complex C representing M. Exact derived evaluation gives `K n = (ev_n.mapDerivedCategory).obj M` and its inherited successive maps `f n`. | Every M is covered; no special reduction tower or completeness condition is required. |
| A resolution `M → I` in that tower category | A chain map `q : C ⟶ I` with `QuasiIso q`, together with `[I.IsKInjective]`. The generic theorem needs only I and its represented system, not a redundant explicit q. | Same resolution convention; q is used to obtain e. |
| K-injectivity of the complex of towers | `[I.IsKInjective]` for `I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ`, using Mathlib's definition by null homotopies from all acyclic complexes. | K-injectivity is in the abelian category of towers, not an extra assumption about each level. |
| The system represented is the evaluated system of M, including transitions | `_e : I.asFunctor ⋙ DerivedCategory.Q ≅ Functor.ofOpSequence f`. Evaluation of q gives a natural transformation whose components are quasi-isomorphisms; localization inverts them. Its inverse, followed by the derived-evaluation comparison and the representative identification for C, gives e in the displayed direction. | This is a natural isomorphism of whole systems, supplied by the given resolution, not independently chosen object isomorphisms or an extra hypothesis on M. |
| Termwise inverse-limit complex `lim I_n` | `∃ c : Cone I.asFunctor, Nonempty (IsLimit c) ∧ …`; `c.pt` is the categorical limit complex, and limits of complexes are degreewise. | Actual inverse limit, with projections and universal property. |
| That complex represents the sequential derived inverse limit | `IsDerivedLimit f (DerivedCategory.Q.obj c.pt)`. Opening the definition gives the existential distinguished triangle with middle arrow `towerTransitionEndomorphism f = 𝟙 _ - towerProductShift f`. | Precisely the Roos property in the node and Stacks 08TC, for the prescribed evaluated transitions. |

The existential limiting cone does not weaken the conclusion about the
inverse-limit complex: any specified limit cone is uniquely isomorphic to
it. I also opened the complete companion
`derivedCategory_towerLimit_property`; it asserts the same derived-limit
property for every supplied limiting cone, so it applies directly to the
usual chosen inverse limit. Conversely, a categorical limit of complexes
supplies the cone in the core theorem. No canonical identification between
arbitrary derived-limit triangles is being asserted.

I opened all five statement-dependency nodes. The generic K-injective
Mathlib leaf `def-pur-kinjective-complex` gives exactly the predicate above.
`CochainComplex.IsKInjectiveResolution` in
`Sheaf.AlgebraicGeometry.KInjectiveResolutions` is indeed specialized to
constant étale coefficients, so it cannot be applied to this tower category;
the item explicitly cites it only for the resolution convention, while its
generic leaf supplies `QuasiIso q` and `I.IsKInjective` in the correct
category. No unusable specialized abbreviation is used here.

I read the full current statements of the adic datum and the sequential
inverse-limit definition, including their distinction between completed and
constant coefficients. They have no recorded declaration in the shared
snapshot. This attachment does not construct either notion or introduce a
new specialization needing their missing APIs: it attaches their already
expressed general computation to an existing declaration. There is no
private coefficient datum or private derived-limit definition to repair.
The actual conclusion uses the recorded `IsDerivedLimit` directly. I opened
its source and `IsDerivedLimitTriangle`, and checked the definitions of
`towerProductShift` and `towerTransitionEndomorphism`, including the order
`Pi.π K (n+1) ≫ f n`.

The generic theorem's category hypotheses do not strengthen the datum. I
checked the existing `countableProducts_exact` signature in
`Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`: it applies to an
arbitrary commutative ring sheaf on the small pro-étale site and provides
countable products and the product-of-epis property. Products preserve
kernels, so this is exactness, expressed by `CountableAB4Star`. I opened
`ringedSiteModules`, which is transparently `SheafOfModules`, and the
recorded `SheafOfModules.isGrothendieckAbelian` theorem for a ring sheaf on
a small site; Mathlib's `IsGrothendieckAbelian.enoughInjectives` supplies the
remaining hypothesis. I also opened `derivedCategory_countableProducts_core`
and clause (3) of `derivedCategory_countableProducts_and_towerLimit`:
the former supplies hP and the latter invokes this exact core theorem.
Thus the generic category and localization structures, hP and enough
injectives are available ambient data, not extra geometric assumptions.

Edge cases checked: the fixed index has no empty-index case; Lean level 0
is positive level 1, so no `A/I^0` is introduced. The zero tower, zero ring,
empty scheme, arbitrary characteristic, identity transitions and zero
transitions are allowed. The complex is unbounded in both directions. No
Mittag-Leffler, epimorphic-transition, constructibility or adic-normalization
hypothesis is present. Independent category-object, morphism and derived
localization universes are retained; the specialization does not identify
the small site's object and morphism universes.

Independent searches used words beyond the worker's original query:

- `msearch.py … leanfinder "inverse system K injective complex limit homotopy limit Roos triangle"`
  returned eight injective-resolution/complex-factorization hits; none states
  this inverse-limit computation.
- `msearch.py … loogle '"IsKInjective"'` returned twelve K-injectivity,
  homotopy and shift results, including the actual class signature; none is
  the tower computation.
- Direct `rg` for tower/K-injective combinations, `homotopy.limit`, and
  `Roos` in the upstream project, Mathlib homological algebra and side
  triangulated modules located this published core theorem and its property
  companion. Upstream `CategoryTheory.Triangulated.HomotopyLimit` defines
  `IsHomotopyLimit` and proves invariance/uniqueness, not this computation;
  it is not a reason to duplicate or replace the recorded Roos predicate.
- I checked the DAG owner `lem-weil-derived-limit-tower-core`, whose recorded
  signature is the same declaration. Reusing it avoids a second theorem.

No mathematical mismatch was found. I changed no statement, dependency,
module or Lean signature; I added this independent review only. There are
no new nodes or dependency modules, and no statement correction or citer
audit is needed. Because this is an existing-declaration attachment, its
source keeps its owner's blueprint docstring; no duplicate module with a
new docstring or new proof is delivered. The existing theorem's proof
comment gives evaluation, product, Roos comparison and transport steps;
the item's own proof records their coefficient-category specialization.

Validation in this reading: the stored `lean.statement` was checked
verbatim against the published source signature, and every non-`lean`
field was checked equal to the shared node. I reran the worker's scratch
specialization through the prescribed `scompile.py`; sandbox and library
checks passed cleanly (3.6 s and 3.2 s), with independent universes. That
scratch is not delivered. The delivery wrapper additionally compiles its
existing-declaration probe and runs the current server preflight.
