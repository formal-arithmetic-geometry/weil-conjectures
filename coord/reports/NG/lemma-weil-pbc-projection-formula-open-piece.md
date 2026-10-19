## Worker report

The module `Sheaf.Paper.OpenImmersionTensorPiece` states
`SheafOfModules.openImmersionTensor_iso`, with proof `sorry`. It expresses the open
formula as a natural isomorphism of bifunctors, characterized uniquely by the
adjunct of its inverse. Definitions contain actual data; no theorem is proved.
There is no statement correction and no disputed mathematical assertion.

Clause-by-clause reading:

- The schemes, map, and chosen compactification are `{X Y : Scheme.{u}}`,
  `{f : X ⟶ Y}`, and `c : Compactification f`. Its fields `i`, `g`, and `comm`
  supply j, p, and f=pj. The structure supplies open immersion and properness;
  `[QuasiCompact c.i]` supplies exactly the quasi-compactness required by the node
  (the upstream Compactification structure alone does not include it).
- The ambient site is `c.Z.ProEt` with `ProEt.topology c.Z`, with object universe
  u+1 and morphism universe u. `ProEt.mk c.i` is the open object. Modules on its
  slice present the open site's modules, using the underlying-site clause of
  `ProEt.weaklyEtale_localization`; no constant-coefficient clause is used.
- `R : Sheaf (ProEt.topology c.Z) CommRingCat.{u+1}` is arbitrary. The source ring
  is exactly `R.over (ProEt.mk c.i)`. No second ring or coefficient identification
  is introduced. Its underlying RingCat sheaf is Mathlib's `sheafCompose`.
- The first variable ranges over the entire unbounded derived category
  `Der (R.over (ProEt.mk c.i))`. No boundedness, flatness, constructibility, or
  representative condition is imposed on E.
- `openTensorCoefficients R` is the full subcategory of derived coefficients
  admitting a complex F with `∃ a b : ℤ, ∀ n, n<a ∨ b<n → IsZero (F.X n)` and
  `Nonempty (StrictPerfectCoefficientPackageOnSite _ F)`. The latter supplies
  ranks N(n), maps i(n), p(n), and `i(n) ≫ p(n) = 𝟙 _`, exactly the finite-free
  retract condition. The finite product of copies of `SheafOfModules.unit` is
  the finite tuple/free module sheaf. Splittings are degreewise, with no chain
  map condition. `Nonempty (Q ≅ DerivedCategory.Q.obj F)` allows all derived
  representatives, rather than selecting one model as extra data.
- `localizedModuleExtension` is the recorded extension presheaf followed by
  the recorded module sheafification. `localizedModuleRestriction` is precisely
  `SheafOfModules.overFunctor`. Their six exactness/additivity instances permit
  `mapDerivedCategory`; this is the termwise functor on unbounded complexes, so
  Lj*=j*. `localizedModuleDerivedAdjunction` is constructed by localizing the
  ordinary termwise adjunction, without making an arbitrary derived choice.
- `a`, `b` are the existing `ProjectionRestriction.TensorModel` interfaces for
  the ambient and slice rings. Their `representative` fields identify derived
  tensor with the signed total tensor on all flat K-flat pairs; `descent` fixes
  transformations by these representatives. `r : Restriction` and
  `t : openTensorRestrictionComparison R U a b r` (an abbreviation for
  `TensorComparison ... r.model a b r.ordinaryTensor`) specify canonical
  restriction, its pure-tensor normalization, and its representative-normalized
  derived tensor comparison. These are models of the operations named in the
  node, not replacement assumptions asserting the projection formula. The
  already-landed `lem-weil-pbc-ringed-projection-restriction` is added to
  stmt_deps to cite this existing interface; no notion is copied.
- `openTensorSource` is `(j_!E) tensor F`; `openTensorTarget` is
  `j_!(E tensor j*F)`. The conclusion `openTensorFormula ...` unfolds to the full displayed
  `∃! beta : source ≅ target` and its unit equation. The helper keeps exactness
  instances at fixed generic site universes before specialization; it adds no
  mathematical assumption.
  As an isomorphism of bifunctors, this is natural for every derived morphism
  in E and F, including maps transported through quasi-isomorphisms.
- The `homEquiv` equation in `openTensorFormula` says that `beta.inv` is the transpose of
  `unit(E) tensor 1`, followed by `t.comparison.inv`. Thus `beta.hom` has exactly
  the displayed direction in the node, and its inverse is exactly the
  adjunction projection map. The equation also determines the isomorphism
  uniquely. This is a normalization, not a choice of an unspecified isomorphism.
- Specializing R to the coefficient ring sheaf uses the same theorem without
  any further identification of ring sheaves.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `Etale.rightDerivedLowerShriekOfCompactification` and its underlying
  `Compactification` datum (X, Z, Y, i, g, comm and the two properties).
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`:
  `AlgebraicGeometry.Scheme.ProEt.weaklyEtale_localization`, specifically its
  underlying-site equivalence and covering compatibility.
- Mathlib `CategoryTheory.Sites.Over`,
  `Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `GrothendieckTopology.over`, `Sheaf.over`, `SheafOfModules.overFunctor`,
  `SheafOfModules.over`, `SheafOfModules.Hom.over`, `overMap`, `overFunctorMap`.
  These are the mathlib_match of `def-pur-localized-ringed-site` (a Mathlib leaf
  needing no lean record).
- `Sheaf.Paper.StrictPerfectCoefficientPackage`:
  `StrictPerfectCoefficientPackage`, generalized by the dependency module below.
- `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`:
  `localizedModule_adjunction_exact`, generalized and normalized below.
- `Sheaf.Paper.ProEtaleCanonicalTensorPullback`:
  the recorded tensor-pullback interface and its representative normalization.
  The equivalent already-landed generic/slice interface is
  `Sheaf.Paper.RingedProjectionRestriction`:
  `ProjectionRestriction.Mod`, `Der`, `TensorModel`, `Restriction`,
  `Restriction.model`, `TensorComparison` and its `representative` field.
- Proof imports retain Mathlib exact derived functors and total tensor,
  `ModulePullbackTensorIso`, `BoundedAboveFlatSheafKFlat`,
  `SiteDerivedTensorDescent`, `KFlatResolutionIndependentCoefficients`, and
  `KFlatIndependentCoefficients`, matching the node's five-step proof plan.

Edge cases checked: E=0; the zero coefficient complex; finite rank zero; all
ranks zero outside any finite interval; empty X; identity open immersion;
nonconstant and zero coefficient rings; arbitrary unbounded E; negative degrees
and arbitrary shifts; nonfunctorial choices of finite-free splittings; and
arbitrary derived morphisms between two represented coefficients. The full
subcategory is closed under isomorphism by its existential representation, so
naturality does not discard the different-representative cases. Site object and
morphism universes remain distinct throughout.

Searches:

- msearch.py leanfinder: “Extension by zero on a ringed site commutes with derived
  tensor with a bounded complex of finite projective sheaves”: eight hits on Tor
  and condensed internal projectivity; no exact statement.
- msearch.py loogle: `Adjunction.leftAdjointProjectionMap,
  SheafOfModules.overFunctor`: unknown first name, zero hits. Direct source
  inspection found upstream `Adjunction.projectionMap`, whose transpose has the
  same unit normalization; it does not state the ringed-site derived theorem.
- msearch.py loogle: `"extension", "tensor"`: twelve ring-extension and cotangent
  tensor hits; no extension-by-zero formula.
- msearch.py leansearch: “Extension by zero module sheaf derived tensor finite
  projective complex”: service unavailable (Internal Server Error).
- msearch.py grep: `extensionByZero|projectionMap` in
  Mathlib/CategoryTheory/Monoidal: zero hits.
- rg in Mathlib ModuleCat/Sheaf, the upstream WeilConjectures source, and
  side lean/Sheaf: found the ordinary pro-etale sheaf
  `openImmersionLowerShriekTensorIso` and its projection-map instance. They use
  sheaves valued in one coefficient category, not arbitrary ring-sheaf modules
  and their unbounded derived tensor; hence no exact existing match.
- rg for the item id in upstream WeilConjectures: no declaration for this node.
- rg for the proposed package/adjunction helper names in Mathlib, upstream and
  side sources: no collisions. The existing universe-specialized package and
  localized adjunction were read in full, and scompile.py --source confirmed
  the current recorded package source.

Source inspection: the blueprint lemma 1269 was read from the server literature
checkout (the read-only local literature omits the actual imported papers). Its
statement is exactly the displayed open formula and two-variable naturality.
The DAG's expanded five-step proof replaces its geometric-point shortcut with
finite-free, retract and signed-total calculations; all five steps appear in
the theorem docstring.

## Dependency modules

`def-weil-pbc-strict-perfect-coefficient-package`: the recorded structure equates
site objects, site morphisms, and coefficients. It cannot instantiate the actual
small pro-etale site. `Sheaf.Paper.StrictPerfectPackageOnSite` reexports that
module and supplies the identical finite-free splitting structure with independent
universes, with real data in all fields. Only the node's lean record changes.

`lem-pur-site-restriction-module-adjunction-exact`: the recorded SmallCategory
interface likewise cannot instantiate the site, and its bare adjunction existence
does not expose the unit needed to fix normalization. The module
`Sheaf.CategoryTheory.LocalizedModuleExactIndependent` keeps the actual direct-sum
extension/sheafification and sectionwise overFunctor, states their exactness, and
states a uniquely characterized adjunction with the direct-sum/sheafification unit.
The definition chooses from this uniqueness theorem, not from unconstrained
existence. Its derived adjunction is constructed through Mathlib localization.
Only the node's lean record changes. Both postponed theorems carry this node's
blueprint id and complete proof docstrings.

Validation: all three delivered modules passed scompile.py, each compiled separately
in dependency order against the current server sources. The last pass took 2.4 seconds
for the generalized package, 3.7 seconds for the exact adjunction, and 3.2 seconds for
the main statement, with no errors or warnings from the delivered files. The wrapper
correctly fell back from stale local ProjectionMateExact interfaces to server
confirmation. Definition-local exactness instances and explicit coefficient arguments
resolve elaboration without imposing a universe equality or an extra hypothesis.


## Second reading by NG

I independently read the base node, all three delivered Lean modules and their
node records, the six original statement dependencies and the added restriction
interface. I also read the imported blueprint lemma 1269 and definitions 1263
and 1268 in the server literature checkout. In Stacks sites-modules.tex I read
Section 03DH, the full extension construction and Hom adjunction in 03DI,
extension exactness in 03DJ, and tensor pullback in 03EL. Section 03DH assumes
only a ringed site and an object; no Noetherian, characteristic or finiteness
condition is implicit there. The source blueprint assumes exactly the chosen
compactification, arbitrary E and bounded finite-projective F used by the node.
There is no statement_change and no unit statement is changed.

Object, hypothesis and conclusion checklist (the node's order):

1. Schemes X,Y, f and a chosen factorization X --j--> Z --p--> Y, with j a
   quasi-compact open immersion and p proper: `c : Compactification f` and
   `[QuasiCompact c.i]`. I opened upstream Compactification/Defs.lean:
   `c.Z`, `c.i`, `c.g`, `c.comm`, `c.isOpenImmersion`, `c.isProper` give precisely
   these data. The extra instance supplies the quasi-compactness that upstream
   deliberately omits. Verdict: exact; no extra geometric hypothesis.
2. The small pro-etale site of Z and its localization at X:
   `ProEt.topology c.Z`, `ProEt.mk c.i`, `Over (ProEt.mk c.i)` and the over
   topology. I opened `ProEt.weaklyEtale_localization`: its underlying category
   and covering equivalences apply to this open immersion independently of its
   later constant-ring clauses. The slice is the explicitly authorized
   presentation of X_proet. Verdict: exact.
3. A sheaf of commutative rings R and its actual restriction R_X:
   `R : Sheaf (ProEt.topology c.Z) CommRingCat.{u+1}` and
   `R.over (ProEt.mk c.i)`. `ProjectionRestriction.Mod` uses the forgetful
   CommRingCat-to-RingCat sheaf and Mathlib SheafOfModules. I opened Mathlib
   Sites/Over.lean and ModuleCat/Sheaf/PushforwardContinuous.lean: over topology,
   ring and module restriction have the stipulated sectionwise formulas.
   Verdict: exact; no independent source ring or coefficient identification.
4. Arbitrary E in the unbounded derived category of R_X-modules:
   `Der (R.over U)` is the entire first factor of `openTensorSource` and
   `openTensorTarget`; `openTensorFormula` quantifies over every such E.
   I read `Mod`, the standard HasDerivedCategory instances and `Der`.
   Verdict: exact, without boundedness, constructibility or flatness on E.
5. Bounded finite-projective F and its degreewise finite-free retractions:
   `openTensorCoefficients R` requires a complex F, integers a,b and
   `n < a ∨ b < n → IsZero (F.X n)`, plus
   `Nonempty (StrictPerfectCoefficientPackageOnSite _ F)`.
   The package fields are N, i, p, and `i n ≫ p n = 𝟙 _` into the finite
   product of copies of the module unit. A finite product is the finite tuple
   free sheaf here. No chain-map relation on i,p is imposed. Its final
   `Nonempty (Q ≅ DerivedCategory.Q.obj F)` permits any represented derived
   object, with every derived morphism between these objects in the full
   subcategory. Verdict: exactly the bounded global condition in the node,
   not the different locally-perfect condition in the dependency's wider API.
6. Exact extension by zero and restriction, derived termwise, with Lj*=j*:
   `localizedModuleExtension` is the existing direct-sum extension presheaf
   followed by module sheafification, and `localizedModuleRestriction` is
   `overFunctor`. The six instances extracted from
   `localizedModuleExactIndependent` give exact additive functors, and
   `.mapDerivedCategory` is the standard exact localization. The derived
   adjunction is obtained from the ordinary normalized adjunction by
   `.mapHomologicalComplex` and `.localization`. Verdict: exact constructions.
7. The specified derived tensor and canonical restriction comparison:
   `a`, `b : ProjectionRestriction.TensorModel ...`,
   `r : ProjectionRestriction.Restriction ...`, and
   `t : openTensorRestrictionComparison ...`. I read their full structures:
   tensor has a natural signed-total comparison on all flat K-flat pairs and
   descent bijectivity; restriction is the actual overFunctor, its ordinary
   tensor comparison has the pure-section equation, and `r.model` is its
   actual `.mapDerivedCategory` with `mapDerivedCategoryFactors`.
   `TensorComparison.representative` fixes t on those signed totals. These
   binders name normalized models of the operations, without assuming any
   extension/tensor isomorphism. The generic/slice interface is already
   recorded by lem-weil-pbc-ringed-projection-restriction. Verdict: the same
   operations as the node, no private or arbitrary comparison.
8. Domain and codomain of the displayed map: `openTensorSource` is
   `(j_!E) tensor F`, while `openTensorTarget` is
   `j_!(E tensor j*F)`, using exactly those derived functors and rings.
   Verdict: correct order and direction.
9. Isomorphism and two-variable naturality: `openTensorFormula` asserts
   `∃! beta : openTensorSource ... ≅ openTensorTarget ...`.
   A natural isomorphism of these product-category functors includes all
   derived morphisms in E and F, not just maps of chosen split complexes.
   Verdict: all clauses present. The explicit uniqueness is forced by the
   next normalization, rather than an additional mathematical restriction.
10. Canonical normalization: the homEquiv equation applies to `beta.inv`,
    a map from j_!(E tensor j*F) to j_!E tensor F. Its adjunct is b.map of
    `(unit_E, identity)` followed by `t.comparison.inv`. This is exactly
    unit tensor 1 followed by the restriction-tensor identification.
    Verdict: beta.hom has the node's direction, and beta.inv is the specified
    adjunction projection map. All homEquiv arguments have the correct types.
11. Specialization to the coefficient ring sheaf: R is arbitrary, so this
    specialization is included without an additional comparison hypothesis.
    Verdict: present.

Edge cases: ranks N(n)=0 use the empty finite tuple sheaf (the zero module),
including the zero coefficient complex; the interval may be empty and degrees
range over all integers. E=0, zero rings, empty X or Z, and the identity open
are permitted by the binders and constructions. No positive-characteristic,
invertibility or nonzero assumption appears. E may be unbounded in both
directions. Splittings may vary independently by degree. All derived
isomorphism transports of a bounded representative remain admitted. The site
has object universe u+1, Hom universe u and coefficient/module universe u+1;
no equality of site universes is imposed. The auxiliary package independently
binds object, morphism and coefficient universes. Every variable/universe used
in the delivered declarations is explicitly introduced, with autoImplicit false.

Dependency-module reading: there are two repairs and no new nodes. For
`def-weil-pbc-strict-perfect-coefficient-package` I compared N,i,p,splitting
with the full node and the original StrictPerfectCoefficientPackage. The
repair changes only universes of the identical splitting data, and publicly
reexports the original module's other notions. Its data are actual structure
fields, with no sorry. For `lem-pur-site-restriction-module-adjunction-exact`,
I compared both functors, both exactness conclusions and the natural Hom
adjunction with the node and Stacks 03DI/03DJ. The old SmallCategory interface
cannot express the actual pro-etale site. The new module exposes both the
exactness theorem and the uniquely normalized adjunction theorem in
lean.declarations. The latter fixes the unit by insertion into the direct sum
at the structure arrow followed by the sheafification unit. Choosing that
adjunction is justified by uniqueness, not arbitrary Nonempty choice; the
derived adjunction is constructed by localization. All theorem proofs are
sorry and refer to the matching node. No hidden proof or hollow data found.

Independent H4 searches used different wording from the author's:

- msearch leanfinder: "For modules on a localized site tensoring an extension
  by zero by a perfect complex is the extension by zero of the restricted
  tensor product": eight Tor and condensed-module results, no exact match.
- msearch loogle: `"shriek", "tensor"`: zero hits.
- msearch grep: `projection.{0,8}formula|extensionByZero.{0,15}[Tt]ensor|[Tt]ensor.{0,15}extensionByZero`
  under Algebra/Category/ModuleCat/Sheaf: zero hits.
- msearch leansearch: "Derived tensor product and extension by zero along a
  localized ringed site commute with perfect coefficients": service returned
  Internal Server Error; the failed search is recorded, without a verdict.
- rg on upstream WeilConjectures, Mathlib and side lean/Sheaf, using
  projection-formula, tensor and shriek combinations: I opened upstream
  ProEtale/LowerShriek/OpenImmersion/Projection.lean. Its
  openImmersionLowerShriekTensorIso and projection-map isomorphism concern
  A-valued sheaves, not unbounded derived modules over arbitrary ring sheaves.
  I also opened side OpenExtensionProjectionFormula.lean: that theorem uses
  Zariski O_X-modules on schemes, not the pro-etale site or arbitrary R.
  The ringed-slice tensor DAG node is sheaf-level, not this derived statement.
  There is no exact existing declaration. Searches of all three source roots
  for the three proposed primary names found no collisions.

Mismatches found and repaired: the main theorem's proof docstring listed the
retract maps in the wrong order. I changed it to tensor i, finite-free inverse,
extension of tensor p, matching B(i), alpha_free inverse, A(p). The repaired
exactness theorem's docstring was too compressed and suggested presheaf direct
sums alone established exactness on sheaves. I replaced that paragraph by the
node's four steps: actual functors, linear Hom adjunction, abelian restriction
comparison, abelian extension comparison and reflection. It now cites each
non-elementary input and retains the universe explanation. No signature,
mathematical node statement, hypothesis, conclusion, or definition changed.

Second-reader validation: scompile.py compiled each of the three delivered
modules separately and cleanly, with server confirmation after a stale local
ProjectionMateExact overlay error. The package took 2.6 s, the independent
exactness/adjunction module 3.2 s, and the main theorem 2.8 s; server compilation
also refreshed their recorded prerequisites. All invocations kept the 60-second
limit, two threads and nice 19. The final docstring repairs do not alter any
elaborated declaration. Node records were refreshed from the file signatures;
comparison with the shared node copies confirms only lean records and the
item's added landed stmt_dep changed.
