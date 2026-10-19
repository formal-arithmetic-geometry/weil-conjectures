## Worker report

Repaired the returned stage-1-only packet by supplying the actual stage-2 module
`Sheaf.AlgebraicGeometry.UnboundedDirectImageSectionPresheaf`. Its only postponed theorem is
`AlgebraicGeometry.RingedSpace.unboundedDirectImage_sectionPresheaf`; every helper has real data.
The item was copied from current main with its original `split_report` intact. The returned
credit-only sentence is absent. No citations.json is claimed or needed by this statement packet.
The theorem proves nothing in this stage: its proof is exactly `by sorry`.

Clause-by-clause rendering:

- A morphism of ringed spaces is `{X Y : RingedSpace.{u}}`, `f : X ⟶ Y`. These are
  `SheafedSpace CommRingCat` morphisms, with the continuous map `f.hom.base` and structure
  morphism `f.hom.c`. There is no local-stalk hypothesis. The dependency record is repaired
  under section 1(B) to name this general part of its existing Mathlib interface.
- Module sheaves are literally `ringedSiteModules.{u} (moduleRings X)` and the analogous
  category on Y. `ringedSiteModules` is the landed transparent abbreviation for Mathlib
  `SheafOfModules`. `moduleRings` is the published structure sheaf with commutativity forgotten.
- The sites are `Opens X` and `Opens Y`, with `Opens.grothendieckTopology`. The presheaf of
  sections is `localAbelianSections`, exactly `SheafOfModules.toSheaf` followed by
  `sheafToPresheaf`; hence all actual restriction maps are retained.
- The common size universe is `u`; `wX` and `wY` are independent derived morphism universes.
  The two `HasDerivedCategory` binders implement the size convention rather than a geometric
  assumption. Abelian presheaves have their standard localization in the required larger
  universe, using `HasDerivedCategory.standard`. No universe is auto-bound.
- E ranges over the whole `DerivedCategory (ringedSiteModules.{u} (moduleRings X))`.
  The displayed comparisons are natural isomorphisms of functors out of this category;
  in particular their components include every E. The normalization also quantifies E explicitly.
- Ordinary f_* is the published `RingedSpace.moduleDirectImage f`. It is Mathlib's
  `SheafOfModules.pushforward` along `Opens.map f.hom.base`, with ring action induced by
  whiskering `f.hom.c`. Its sections are literally F(f^-1 V), not an abstract replacement.
- `sectionDerivedDirectImage` is exactly this functor's
  `rightDerivedFunctorOfQuasiIsoResolutions (localSectionsEnoughKInjectives X)`.
  The resolution witness uses the published `kInjectiveResolutionFunctor` and
  `toKInjectiveResolution`; it imposes no resolution-existence assumption on the caller.
- `derivedLocalAbelianSections` right derives the abelian presheaf of sections by the same
  construction. Evaluation at each open is exact, so its degree-q homology is
  H^q(RGamma(V,E)), computed on the same K-injective representative. Homology in an abelian
  presheaf category is sectionwise. This simultaneous form supplies all restriction maps.
- The unrestricted degree is `q : ℤ`. `localHypercohomologyPresheaf Y q` is the right-hand
  presheaf. `inverseOpenHypercohomologyPresheaf f q` right derives the actual functor
  `moduleDirectImage f ⋙ localAbelianSections Y`, so its value at V is H^q(f^-1 V,E).
- Clause (a) is `e : inverseOpenHypercohomologyPresheaf f q ≅ sectionDerivedDirectImage f ⋙
  localHypercohomologyPresheaf Y q`. The additional equality `e.hom =
  localHypercohomologyComparison f q` fixes its canonical map. This map is obtained from the
  universal bijection of the recorded total right-derived functor applied to the pasted units.
  The use of `Classical.choose` is solely to select the unique preimage under that bijection;
  it is not choice of an arbitrary isomorphism or of undetermined mathematical data.
- Clause (b), for the right presheaf, is the natural isomorphism `s` after
  `presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}` to
  `sectionDerivedDirectImage f ⋙ (DerivedCategory.homologyFunctor ... q ⋙
  SheafOfModules.toSheaf (moduleRings Y))`. Its component at E is required to be
  `localHypercohomologySheafificationAt q ((sectionDerivedDirectImage f).obj E)`.
  That model uses the canonical right-derived unit on a K-injective representative, exact
  sheafification commuting with homology, the sheafification counit, and the localization
  homology comparison. It therefore fixes the actual canonical sheafification map.
- Clause (b), for the left presheaf, is the isomorphism `t`. Its equality to
  `Functor.isoWhiskerRight e (presheafToSheaf ...) ≪≫ s` fixes its canonical map too.
- Naturality in E is built into all three natural isomorphisms e, s, t, including all
  derived morphisms, not only chain maps. Restriction compatibility is built into the
  presheaf-valued functors and their natural transformations. There is no `Nonempty` iso,
  arbitrary comparison, scheme assumption, boundedness or quasi-compactness binder.

Sources read: `literature/stacks-project/cohomology.tex`, local Leray lemma 0D5W,
lines 7918-7939; higher direct images lemma 0D5X, lines 7942-7956. The source identifies
H^q(f^-1 V,E) with H^q(V,Rf_*E) and applies the sheafification-cohomology lemma 0BKJ.
The theorem docstring expands the node's five proof steps and explicitly distinguishes
acyclicity for subsequent direct image from preservation of K-injectivity.

Dependency declarations used/read:

- `Mathlib.Geometry.RingedSpace.Basic`: `AlgebraicGeometry.RingedSpace`, with inherited
  morphisms from `Mathlib.Geometry.RingedSpace.PresheafedSpace`.
- `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`: `AlgebraicGeometry.LocallyRingedSpace.Hom`
  was read and rejected as the sole interface: it adds the local-stalk condition.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`; the small
  open-cover topology itself is Mathlib's `Opens.grothendieckTopology`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`, Q;
  `...HomologySequence`: `homologyFunctor`, `homologyFunctorFactors`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the recorded construction,
  unit, universal bijection and `rightDerivedFunctorOfQuasiIsoResolutionsObjIso`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`: `CochainComplex.IsKInjective`.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`, `sheafificationAdjunction`.
- `WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage`: `moduleRings` (transitively),
  `moduleGrothendieckAbelian`, `moduleDirectImage`, and its additive instance. Its full
  current source was read using `scompile.py --source` because the old checkout lacks it.
- Proof imports: `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`,
  `Sheaf.Algebra.Homology.KInjectiveRestrictOpen`,
  `WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact`,
  `Sheaf.AlgebraicGeometry.RingedSpaceDirectImageKInjectiveAcyclic`, and
  `Sheaf.AlgebraicGeometry.RingedSpaceSheafificationCohomology`. Their signatures/docstrings
  were read, including the current server sources of the last four through `--source`.
  The K-injective Hom comparison is provided transitively by the published resolution imports.

Edge cases checked before finalizing the statement: empty spaces and empty opens have the
usual zero abelian sections and impose no nonemptiness binder; E=0 is allowed; negative q,
q=0 and positive q all use the same ℤ-indexed homology; the identity map is allowed and the
comparison is normalized by its units; arbitrary f-sharp is allowed, without flatness or
local-stalk conditions. There is no assertion that f_* preserves K-injectivity (false for
arbitrary ringed morphisms); the proof uses the recorded acyclicity theorem instead.

Searches made (2026-10-19):

- msearch.py LeanFinder: "For a morphism of ringed spaces local hypercohomology of derived
  direct image equals hypercohomology on inverse image opens, naturally as abelian presheaves".
  Eight results, notably `Sheaf.cohomologyPresheafFunctor` and `Sheaf.cohomologyPresheaf`;
  these use ℕ and single sheaves, not unbounded module complexes or this canonical comparison.
- msearch.py Loogle: `"rightDerived", "cohomology"`: no results.
- msearch.py LeanSearch: "Sheafification of the presheaf of unbounded hypercohomology is the
  cohomology sheaf of derived direct image": eight sheafification constructions, no theorem
  giving the required ringed-space comparison.
- msearch.py grep: `cohomologyPresheaf|rightDerived|sheafification` in
  `CategoryTheory/Sites/SheafCohomology`: ten hits, all Basic/MayerVietoris for single sheaves.
  Read Basic's signatures: the degree is ℕ and the input an abelian sheaf.
- rg in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id,
  `ringedSpace.*[Cc]ohomology|sheafification.*[Cc]ohomology`: no exact result.
- rg in `lean/Sheaf` for hypercohomology, ringed sections and sheafification found
  `RingedSpaceSheafificationCohomology` (only sheafification, noncanonical existential P),
  `BoundedComplexDirectImagePresheaf` (bounded-below pro-etale complexes), and
  `UnboundedDirectImageComparison` (pro-etale/etale comparison). Full relevant signatures
  were read. None states this unbounded ringed-space natural presheaf comparison.
- rg checked the new declaration names against `lean/Sheaf` and the upstream source;
  none was already declared. Helpers are components of this node's canonical construction,
  not new independent mathematical notions. No new DAG node is needed.

Validation: scompile.py compiled both `Sheaf.Stage2.Sandbox0` and the actual module path
without errors or warnings (compile-4.log, 20.1 s and 19.9 s). Every universe and variable is
explicit; only the named final theorem is `sorry`. Dry-run/preflight result recorded below.

## Dependency modules

`def-weil-locally-ringed-space-morphism`: section 1(B), existing Mathlib declarations only.
Its old match named only the locally ringed morphism, unusable for the generality of this
consumer. The new lean-only record names RingedSpace and the inherited PresheafedSpace.Hom
as well as the locally ringed specialization; it changes no statement or mathlib_match.
No dependency module is created because Mathlib already gives the exact general notion.

## Second reading by Q06

Reopened the current item JSON and final Lean module for a separate clause-by-clause pass.
This is a self-review in this dispatched worker: the brief explicitly forbids starting
another agent, so no independent-agent review is claimed. The maintainer's fresh review
remains the independent stage-2 review.

1. Generality: X and Y are RingedSpace, f an ordinary ringed-space morphism. Compared the
   local Hom signature: it imposes IsLocalHom and was not used. Repaired its dependency
   lean record to include the ringed-space interface. No scheme/locality condition remains.
2. Categories and size: checked every object is DerivedCategory of the dependency's
   ringedSiteModules, every degree is ℤ, and all presheaf values are AddCommGrpCat in u.
   Derived morphism universes wX and wY remain independent. Every binder is explicit.
3. Rf_*: checked the transparent abbreviation actually calls the required
   rightDerivedFunctorOfQuasiIsoResolutions on the published ordinary module direct image;
   its witness is a real K-injective replacement, not an existential choice of data.
4. Local groups: checked derivedLocalAbelianSections and inverseOpenHypercohomologyPresheaf
   derive actual section functors and use presheaf homology. Exact evaluation computes the
   local RGamma groups and keeps their restrictions. No higher cohomology of a single
   sheaf or bounded-below substitute is used.
5. Canonical (a): e is a natural isomorphism whose hom is the fixed comparison, selected
   through a bijective universal factorization of pasted units. No free iso is accepted.
6. Canonical (b): initial draft exposed a generic sheafification comparison on D(Y).
   Tightened the final theorem to state exactly both sheafification isomorphisms for Rf_*E:
   s is normalized at every E by its K-injective model, and t is explicitly the sheafified
   e followed by s. Read each component of the model: right-derived unit, exact homology
   comparison, sheafification counit, localization homology comparison, representative
   transport. None is `sorry` data and no Nonempty choice occurs.
7. Naturality: e, s and t are isomorphisms of functors, so their naturality equations
   quantify all derived morphisms; their components are presheaf/sheaf morphisms, so
   restriction compatibility is built in. No separate unbound morphism is assumed.
8. Edge cases: negative degrees, zero object, identity f and empty opens remain in the
   types. No finiteness, boundedness or flatness assumption was introduced.
9. Returned packet faults: there is now a real Lean file, a verbatim lean.statement,
   Worker report and this second reading. The stage-1 split_report edit is reverted by
   copying current main without changing that field; no credit-only delta is submitted.
10. Proof plan: compared all five node steps with the theorem docstring. The dangerous
    preservation-of-K-injectivity claim is absent; the relevant direct-image result is
    acyclicity. Imports retain all stated proof dependencies; clean compile verified them.

No statement correction, new nodes, or STATEMENT-DISPUTED issue remains.

## Repair validation after resumption

The first retained-packet dry run identified an incorrect defining-module record for
`RingedSpace`. Pointing to Basic alone then exposed the unavailable locally ringed
specialization in the preliminary declaration check. Repaired the dependency metadata
with primary declaration `AlgebraicGeometry.LocallyRingedSpace.Hom`, declared in
`Mathlib.Geometry.RingedSpace.LocallyRingedSpace`, and retained all four declarations.
That module imports the general RingedSpace and PresheafedSpace.Hom interfaces.
The theorem still uses arbitrary RingedSpace morphisms; the local-stalk condition
occurs only in the dependency's separate locally ringed specialization.

Repeated the clause-by-clause self-check against Stacks 0D5W, 0D5X and 0BKJ:
the canonical Leray transformation is fixed by the universal derived units; e.hom
is exactly this map, s is fixed on every Rf_*E by its K-injective model, and t is
the sheafified e followed by s. All three are natural isomorphisms. The integer
degree, unrestricted ringed morphism, derived input, and all restriction maps
remain in the types. The item differs from current main only in lean; split_report
is identical. The recorded theorem signature matches the file verbatim, every
helper is listed, there is one sorry (the final theorem), and no line exceeds 100
characters. Retained searches.jsonl confirms the report's previous three search kinds.
