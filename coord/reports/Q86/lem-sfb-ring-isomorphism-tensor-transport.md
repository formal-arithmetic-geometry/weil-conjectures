## Worker report

This packet retains and repairs the saved draft rather than replacing the item. It
states `SheafOfModules.ringIso_tensor_transport`; its sole theorem proof is `sorry`.
`RingIsoTensorTransport` packages every clause. Three definitions package its
derived clause and specialize Mathlib's canonical localization construction;
two transparent instance helpers cache the existing monoidal structure on
complexes. None contains postponed data or chooses an arbitrary morphism.

Hypotheses and objects, checked against the node:

- A site is `C : Type u`, `[Category.{v} C]`, and
  `J : GrothendieckTopology C`. The topology is the sheaf-relevant presentation
  of the covering-site convention; no extra covering condition is required.
- Smallness in the coefficient universe is `[EssentiallySmall.{r} C]`.
  The coefficient universe `r` is independent of both `u` and `v`.
  `HasSheafify J AddCommGrpCat.{r}`, `J.WEqualsLocallyBijective ...`, and
  `J.HasSheafCompose ...` expose the canonical sheafification and abelian
  interfaces on such a site. They impose no geometric or boundedness condition.
- The commutative ring sheaves are `R S : Sheaf J CommRingCat.{r}`, and
  `c : R ≅ S` is their actual ring-sheaf isomorphism.
- `scalarModules J R` unfolds to the recorded `ringedSiteModules`, hence the
  Mathlib `SheafOfModules` category with commutativity forgotten, not another
  category of module sheaves. `scalarRestriction c.hom` is precisely the
  recorded Mathlib `SheafOfModules.restrictScalars`.
- The two `HasDerivedCategory` binders choose the unbounded localizations.
  Their morphism universes `wR` and `wS` remain independent. The helpers
  `ringIsoDerivedRestriction c h` and `ringIsoRestrictionComparison c h`
  use Mathlib `Functor.mapDerivedCategory` and `mapDerivedCategoryFactors`,
  with the exactness proof supplied by the transport structure itself.
  Thus exactness is a conclusion, never an added hypothesis of the theorem.

Clause correspondence:

1. `equivalence`, `functor_eq`, and `inverse_eq` give the equivalence with
   precisely `Res_c` and `Res_(c.inv)` as its two functors. `additive` and
   `exact` assert its additivity and preservation of finite limits and colimits.
2. `monoidal : (scalarRestriction c.hom).Braided` is a strong braided monoidal
   functor between the actual symmetric sheaf tensor categories. Its oplax
   maps `δ` and `η` are the displayed tensor and unit isomorphisms; its lax
   maps are their inverses. Mathlib's class includes naturality, associator,
   left/right unitor, and braiding coherence.
3. `pure_hom` and `pure_inv` say both tensor maps send the image of
   `x ⊗ y` in the sheafification to the image of the same tensor. They use
   the existing `ScalarHomOrdinary.pure`, not tensors in an unrelated model.
   `unit_hom` says sectionwise that `η(s) = c.inv.hom.app U s`.
4. `totalIso` uses the actual monoidal total tensor of cochain complexes.
   Its degree-n object is the direct sum over `p + q = n`; the existing
   differential has the second sign `(-1)^p`. `total_naturality` is naturality
   in both chain-map variables. `total_summand` identifies its degree-n map
   on each coprojection with the ordinary tensor comparison. This pins the
   total-complex map to the specified local pure-tensor map.
5. `acyclic_iff`, `flat_iff`, and `kflat_iff` assert preservation and reflection
   of acyclicity, the recorded sheaf flatness, and the recorded acyclic-tensor
   K-flatness. Each quantifies over all objects/complexes, with no boundedness
   or flat-term restriction. Applying the theorem to `c.symm` gives the same
   assertions for the inverse restriction.
6. `kflat_test_R` and `kflat_test_S` identify the acyclic-tensor definition
   with `IsKFlatForTotalTensor` on each module category. The latter definition
   requires preservation of every quasi-isomorphism in both tensor orders.
7. `derived` supplies `RingIsoDerivedTensorCompatible c exact totalIso`.
   Its existential monoidal and symmetric structures, together with the lax
   braided localization functors, present the derived symmetric tensors:
   their unit maps and their tensor maps on every K-flat pair are invertible.
   These are conclusions supplied by the packet, not assumptions on a
   preselected presentation. In particular this clause is not a conditional
   assertion that could be vacuous for lack of a derived tensor structure.
8. The existential `d : (ringIsoDerivedRestriction c h).Braided` gives the
   coherent natural derived tensor comparison for all derived objects.
   The final equation says its representative, after the canonical
   localization factors and model isomorphisms, is exactly
   `DerivedCategory.Q.map (t P Q).hom`. It holds for every K-flat pair,
   hence in particular on corresponding K-flat resolutions. The orientation
   is `δ_D ; (comparison ⊗ comparison) ; μ_R = D(μ_S) ; comparison ; Q(t)`.
   The derived associator, unitor, and symmetry compatibility are part of `d`.

Dependency declarations used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings` (site convention).
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`; Mathlib
  `Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`: `SheafOfModules.restrictScalars`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `cochainModulesMonoidal`, `cochainModulesSymmetric`, `cochainModulesPreadditive`,
  and both colimit-preservation instances. These use the already recorded
  sheafified balanced tensor, with independent site universes.
- Mathlib `Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`;
  `HomologicalComplex.ιTensorObj` is its monoidal total-tensor coprojection.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `IsFlatOnSite`;
  `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso`:
  `CochainComplex.IsKFlatForTotalTensor` (both tensor orders).
- Mathlib `Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`; Mathlib
  `Algebra.Homology.DerivedCategory.ExactFunctor`: `mapDerivedCategory`
  and `mapDerivedCategoryFactors`.
- The two added definition dependencies are
  `def-sfb-scalar-hom-comparison-data` (module
  `Sheaf.Algebra.Homology.ScalarInternalHomData`, `scalarModules` and
  `scalarRestriction`) and `def-sfb-sheaf-tensor-pure-section`
  (module `Sheaf.Algebra.Homology.ScalarHomOrdinaryTensorComparison`,
  `ScalarHomOrdinary.pure`). The scalar-data node is already landed; the pure-section node binds an
  existing declaration in this delivery. Both declarations were read in the
  current live sources; neither has a dependency path back to this item.
- The non-public imports retain the recorded proof dependencies: sheaf tensor
  closedness, exact-functor cohomology, the cone criterion and tensor/cone
  comparison, localization, K-flat resolutions and tensor models, tensor
  descent, and derived symmetric monoidal coherence.

Edge cases: the zero ring sheaf and zero modules are allowed; the unit formula
still applies. Identity isomorphisms and arbitrary ring automorphisms are
included, not only identity coefficient changes. There is no inhabitance
assumption on the site, no connectivity, no nonzero hypothesis, no boundedness,
and no finite-support assumption on complexes. The direct sums range over all
integer degree decompositions. The tests quantify over every acyclic complex
and every quasi-isomorphism, including zero-to-acyclic maps. The independent
universe binders cover unequal site object/Hom sizes and unequal localization
morphism universes.

Searches retained from the earlier packet (`searches.jsonl` records the actual
queries and responses): LeanFinder, restriction along a sheaf-ring isomorphism
preserves tensors and K-flatness, returned flatness/ring-map invariance results;
Loogle `SheafOfModules.restrictScalars` returned the functor, its additive
instance and section formulas; Mathlib grep
`restrictScalars.*(tensor|[Ee]quivalence)|ring.*[Ii]so.*tensor` under
`Algebra/Category/ModuleCat` returned ordinary module scalar equivalences;
LeanSearch for a symmetric monoidal ring-sheaf restriction equivalence returned
restriction functors and ordinary module results. None states this item.
Current `rg` searches in `lean/WeilConjectures` and `lean/Sheaf` for this node
id and `ringIso_tensor_transport`/`RingIsoTensorTransport` found no existing
statement. The partial match
`Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso` was read: it
identifies scalar extension with inverse restriction, but supplies none of
this item's K-flat/total-complex/derived comparison package.

Sources read: Stacks `sites-cohomology.tex`, `definition-K-flat` (06YN),
`lemma-K-flat-quasi-isomorphism` (06YP), the K-flat derived tensor construction
and `definition-derived-tor` (06YT), and the scalar-coordinate proof in this
node. The theorem docstring records that proof, including inverse restriction,
sheafification, signed totalization, exact cohomology, flatness, both K-flat
conventions, localization and representative coherence.

There is no statement correction or disputed mathematical clause. The item's
`lean` and its two definition-dependency additions change. The new definition
node below replaces the saved packet's incorrect citation of a theorem node
for a plain definition. No existing base statement dependency is removed.

## Second reading by Q86

This is the dispatcher's required self-check; the maintainer performs the
independent review. Reopened the item and each field of the module. The saved
draft had not been attached to the node and its derived comparison used a
same-universe helper. The repair keeps `wR` and `wS` independent, takes exactness
from the theorem's conclusion, and uses Mathlib's two-universe localization
functor and factor. The representative square was also reversed incorrectly:
`μ_S` now occurs on its right-hand path, before the localization comparison.
The derived presentation is existential, including invertible K-flat models,
so the final clause asserts actual existence instead of a possibly vacuous
conditional on a model. Ordinary coherence, both local pure-tensor formulas,
unit `c.inv`, total summands, both preservation/reflection directions, both
K-flat tests, and the representative derived square are all present. The
helper definitions contain real Mathlib constructions and no `sorry`.

## New nodes

`def-sfb-sheaf-tensor-pure-section` records the canonical local pure-tensor
section as the exact existing definition
`SheafOfModules.ScalarHomOrdinary.pure`, in
`Sheaf.Algebra.Homology.ScalarHomOrdinaryTensorComparison`, line 36.
Stacks 03EK (`sites-modules.tex`, `section-tensor-product`, lines 3550–3576)
defines the presheaf tensor sectionwise and the sheaf tensor by sheafification.
The definition's body applies that sheafification unit and then
`tensorObjIsoSheafification.inv`; it has actual data and uses no choice from
the theorem in that module. The node's parameters match the definition:
`A`, `M N`, `V`, and `x y` render the coefficient sheaf, two modules, opposite
site object, and the two input sections; its target is exactly the monoidal
tensor section. The implicit site, independent universes and sheafification
interfaces are inherited from the recorded tensor construction. Empty sites,
zero rings and zero modules remain allowed. This records a helper in its own
definition node, without writing any new Lean declaration.

Searches for this node: LeanSearch `canonical pure section in the sheaf tensor
product of sheaves of modules` returned sheaf Cartesian tensors, free sections
and presheaf tensor morphisms; LeanFinder `image of a local pure tensor under
the sheafification unit into tensor product of sheaves of modules` returned
`PresheafOfModules.toSheafify` and component lemmas; Mathlib grep
`tensorObjIsoSheafification|sheafificationAdjunction|def pure` under
`Algebra/Category/ModuleCat/Sheaf` found sheafification adjunction uses.
DAG grep `ScalarHomOrdinary.pure` found only the ordinary-comparison theorem
node's helper list, and `blueprint_refs.py search 'sheaf tensor pure section'`
found no definition node. Upstream grep found formulas in
`TensorBilinearUniversal` and `TensorHomAdjunction`; project grep found the
exact existing `pure` and `siteSheafTensorTmul` with its alternate site-tensor
target. Exact queries and results are retained in the new node's
`mathlib_searches`.

## Returned-head repair and second reading by Q86

The immutable-head return for `34ed7f399cbb` accepted the full Lean statement
and requested one dependency correction. Reopened the saved node, report,
Lean file, and the existing `pure` definition. The saved packet differs from
the current main node only in `lean` and added `stmt_deps`. It cited the
ordinary-comparison theorem but never used its chosen comparison: it used
only `pure`. Replaced that added theorem citation with the new definition
node above. The Lean source and every mathematical clause remain unchanged;
all original base dependencies and proof dependencies remain unchanged.
The existing module import supplies exactly the new definition node's
recorded declaration. The new node's signature is verbatim from its defining
module. The theorem helper is not used to supply plain definition data.

The initial required saved-packet dry run timed out at 60 seconds locally
and on the server, with no elaboration error, as in the returned review.
The unchanged delivery module then passed the server compiler in 58.4 seconds,
under the unchanged 60-second limit, with no errors or non-sorry warnings.
Diagnostic copies stayed under `scratch/` and are not delivered; no profiler,
transparency adjustment, extra instance, or explicit-argument variant was
applied to the delivery module. Thus the returned review's instruction to
leave the Lean unchanged is satisfied.

## Previous attempt status

The dependency repair is complete and the delivery Lean is unchanged.
The unchanged module passed `scompile.py` server confirmation in 58.4 seconds.
Subsequent `deliver2.py --no-push` runs repeatedly returned
`Sheaf/Algebra/Homology/RingIsomorphismTensorTransport.lean: timeout after 60 s`
before building a commit or running preflight. Retries included a quiet
interval and a server load decrease from about 202 to about 173. No wrapper,
limit, live file, or launcher script was modified. No delivery was pushed.
The next attempt should retain this repaired packet and rerun the dry run.

## Compile-cost repair and second reading by Q86

The required first dry run of the saved packet again timed out in both the
preliminary and server-confirmation compiles. A scratch file containing only
the imports compiled in 5.2 and 5.1 seconds, so import loading was not the cause.
A scratch profiler showed repeated synthesis of
`MonoidalCategoryStruct (CochainComplex (scalarModules J A) ℤ)` costing about
2–3 seconds per tensor occurrence; the derived compatibility definition alone
spent about 42 seconds elaborating. Merely applying `no_expose` to its three
helper definitions did not resolve that repeated instance search.

The delivered repair adds `SheafOfModules.ringIsoCochainMonoidal`, whose real
body is `inferInstance` for the existing Mathlib cochain monoidal structure,
and `SheafOfModules.ringIsoCochainMonoidalStruct`, whose real body is precisely
its `toMonoidalCategoryStruct` projection. Their higher instance priority lets
all existing tensor expressions reuse that specialization. These are public,
transparent helpers of this owning node, listed in `lean.declarations`, with
source and blueprint docstrings. They add no tensor construction, hypothesis,
postponed proof, or localization-universe equality. No existing declaration
body or mathematical clause changes. All users in this module elaborate
against these definitionally identical existing structures. The diagnostic
version compiled without errors or non-sorry warnings in 34.1 and 29.8 seconds.

For the second reading, reopened the two helper bodies, the item's statement,
the new pure-section definition node, and the final theorem and structure.
Every clause enumerated in the Worker report remains textually unchanged:
equivalence and inverse, additive and exact, ordinary braided coherence, both
pure formulas, inverse ring unit, total naturality and each summand, the three
preservation/reflection iff clauses, both K-flat tests, and the derived
representative square. Every universe and binder also remains unchanged.
The theorem-node dependency fault remains repaired by the definition node.
No file-local instance or notation and no transparency/profile option is added.

Final per-file compile and delivery preflight results are recorded below.

The delivered module passed `scompile.py` under its actual module name in
39.1 seconds (sandbox check: 34.1 seconds), with no errors or non-sorry warnings
and the unchanged 60-second limit. A fresh `rg` search for both helper names
in Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` found no existing declaration
with either name. The node differs from current main only in `lean` and the two
added definition dependencies; its theorem signature is verbatim from the file,
all Lean lines are at most 100 characters, and its sole `sorry` remains the
item's named theorem.

The full-packet dry run compiled all files and reached preflight. Its two
failures were the two ids in the new node's combined citation bracket.
Replaced that bracket by separate `[id]` citations; the mathematical statement
and dependencies are unchanged. Also aligned the existing pure definition's
recorded signature with the extractor by starting at the `def` keyword,
retaining the source's exact text through the result type.

Final dry run: `deliver2.py Q86 lem-sfb-ring-isomorphism-tensor-transport
--no-push` printed `OK (dry run)` for commit `255174a5398`: the full packet
passes the current server preflight and compiles. The delivered Lean and node
records are unchanged after that successful check; only this result was
appended to the report before the final delivery command.
