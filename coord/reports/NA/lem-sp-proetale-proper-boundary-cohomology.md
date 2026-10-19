## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleProperBoundaryCohomology` states
`AlgebraicGeometry.Scheme.proEtale_proper_boundary_cohomology`, with `sorry` as its
only postponed proof. It follows the already corrected DAG statement, including its
etale-origin hypothesis. It changes only this node's `lean` record. No new node,
dependency module, or statement correction is needed.

`properBoundary_hasInjectiveResolutions` is a supporting global instance with real
construction data: take the first component of the recorded Grothendieck theorem,
then Mathlib's enough-injectives and injective-resolutions instances. It introduces
no axiom or additional hypothesis. Its universe arguments are explicitly
`{u + 1, u, 0}`: the site has object universe `u+1` and morphism universe `u`.
There is no equality imposed on those universes.

Clause-by-clause correspondence:

- The affine base is literally `Spec (CommRingCat.of R)`, for `R : Type u`
  and `[CommRing R]`. All schemes are `Scheme.{u}` and all module sections
  live in `u+1`, as in the recorded original small pro-etale site.
- The explicit w-contractibility condition is `hR`: for every `S : Type u`,
  commutative-ring instance and ring map `φ : R →+* S`, faithful flatness
  `φ.FaithfullyFlat` and weak etaleness `φ.WeaklyEtale` imply existence of
  `r : S →+* R` with `r.comp φ = RingHom.id R`. This is precisely an
  R-algebra retraction, including preservation of the given structural map.
  Its quantifier has the ring's universe, as does the recorded affine evaluation lemma.
- The closed immersion is `z` with `[IsClosedImmersion z]`; the complementary
  open immersion is `e` with `[IsOpenImmersion e] [QuasiCompact e]` and
  `hcomplement : Set.range e = (Set.range z)ᶜ`.
- Every point specializes into Z is
  `hspecializes : ∀ x, ∃ t : Z, Specializes x (z t)`. By the definition of
  `Specializes`, this says `z t ∈ closure {x}`, exactly the node's closure condition.
- Properness is `[IsProper p]` for `p : P ⟶ Spec (CommRingCat.of R)`.
  The fibre product P_E is Mathlib's `pullback p e` with projection
  `pullback.fst p e` to P.
- The clopen inclusion is `h : U ⟶ pullback p e` with `[IsOpenImmersion h]`
  and `hclosed : IsClosed (Set.range h)`. Its composite j is written
  `h ≫ pullback.fst p e`; `[QuasiCompact (h ≫ pullback.fst p e)]`
  is the node's quasi-compactness assumption. Its open-immersion instance is
  inherited from base change of e followed by composition, not assumed separately.
- The finite commutative coefficient ring is `A : Type u` with `[CommRing A]`
  and `[Finite A]`. The canonical `ULift.{u+1,u} A` is exactly the recorded
  coefficient-size convention, with its induced ring and scalar action.
- `J : proEtaleRingModules U (proEtaleConstantRing U A)` is a module sheaf
  over the constant ring sheaf, and `[Injective J]` retains precisely injectivity
  in that category. In particular the theorem does not assume j_!J injective.
- `hetale` quantifies over an actual module sheaf `J₀` on `U.smallEtaleTopology`,
  encoded by `Sheaf ... (ModuleCat.{u+1} (ULift A))` as authorized by the etale
  dependency's encoding note. Its `Nonempty (... ≅ J)` is the required
  isomorphism: apply `ProEtale.comparisonUpperStar` and then the canonical
  realization `(sfIntrinsicModuleEquivalence U A).functor`. This is the recorded
  comparison morphism on fixed coefficients expressed in the recorded intrinsic
  category; it is not an arbitrary map or an assumption of comparison isomorphism.
- Extension by zero is exactly
  `(sfIntrinsicExtensionByZero (h ≫ pullback.fst p e) A).obj J`.
- The conclusion takes any `q : ℕ` and `hq : 0 < q` and asserts `IsZero` of
  the qth right-derived global-sections functor at that extension. The composite
  inside `rightDerived q` first applies `SheafOfModules.toSheaf` to forget the
  scalar action, then `sheafToPresheaf`, then evaluation at `ProEt.mk (𝟙 P)`.
  Its source remains the intrinsic constant-A module category, so its resolution
  is a MODULE injective resolution. This is not abelian-site cohomology obtained
  by resolving the underlying abelian sheaf. The output is an abelian group;
  `IsZero` states precisely the asserted zero group. The rightDerived API computes
  it by an N-indexed injective resolution, equivalent to the node's resolution
  extended by zero in negative degrees. No degree-zero vanishing is added.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Spec`;
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`, `ProEt.mk`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Morphisms.ClosedImmersion`: `IsClosedImmersion`; `Morphisms.FiniteType`
  and `Morphisms.QuasiCompact`: `QuasiCompact`; `Morphisms.Proper`: `IsProper`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: `Module.FaithfullyFlat`;
  `Mathlib.RingTheory.RingHom.FaithfullyFlat`: `RingHom.FaithfullyFlat`.
- `Sheaf.RingTheory.IndEtaleUniverseTransport` reexports
  `Sheaf.RingTheory.IndPrincipalZariski` and the existing ring-map predicate
  `RingHom.WeaklyEtale` from `WeilConjectures.RingTheory.ProEtale.WeaklyEtale`.
  The item's hypothesis concerns this predicate, not ind-etaleness.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`;
  `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`;
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleConstantRing`;
  `Sheaf.AlgebraicGeometry.ProEtaleOperations`: `proEtaleRingModules`.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `Injective` and the
  resolution interface from `Preadditive.Injective.Resolution`;
  `Mathlib.CategoryTheory.Abelian.RightDerived`: `Functor.rightDerived`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `sfIntrinsicModuleEquivalence`, `sfIntrinsicExtensionByZero`. The equivalence is
  the canonical associated-module-sheaf realization, fully faithful and essentially
  surjective; its functor extends fixed scalars to locally constant sections.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `proEtaleSiteComparisonModules`,
  using `ProEtale.comparisonUpperStar` from its public upstream import.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: its recorded category conventions
  `Sheaf`, `SheafOfModules` and fixed-coefficient alternative in the node's note;
  no unrelated constructibility hypothesis is introduced.
- `Sheaf.CategoryTheory.SiteCoveringAxioms` retains the cohomology API of
  `def-weil-pbc-sites-and-cohomology`; `rightDerived` gives its stated
  injective-resolution meaning here with source the module category.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`:
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`;
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`:
  `IsGrothendieckAbelian.enoughInjectives` supplies the supporting instance.

The file also imports every recorded proof-dependency module (including the
Mathlib matches without `lean` records): finite-level pro-etale proper base change,
fixed etale-origin witnesses, extension comparison/exactness/adjunction, ringed
open-closed localization, immersion exactness, specialization zero, affine
weak contractibility, exact evaluation, K-injective comparison, module
sheafification and base-change stability. These imports are private unless a
statement or the explicit resolution instance uses them. The seven proof steps
are transcribed into the theorem docstring, including each step's cited nodes.
No step is presented as proved by this delivery.

Edge cases checked:

- The zero ring R and empty base are allowed; no nontriviality or nonempty
  scheme hypothesis is added. The retraction condition is still quantified as written.
- If Z is empty, the specialization condition forces Q empty. If E is empty,
  its fibre product and U are empty. Both are included by the statement.
- Empty U, empty P, and the zero module J are permitted. No positive rank,
  nonzero section, connectedness, or constructibility assumption is present.
- Noetherian or finite-type hypotheses on the base are not added. Only p is proper.
- Degree zero is excluded by `hq`; every positive degree is included.
- The zero coefficient ring is permitted. Finite rings require only `Finite A`,
  without choosing a finite enumeration; the size lift is canonical.
- The source's additional etale-origin condition is retained even though the
  seven-step argument does not otherwise use injectivity or the clopen condition.

Searches made:

- `msearch.py ... leanfinder "Positive cohomology of extension by zero on a proper
  scheme over a weakly contractible affine vanishes"`: 8 hits, including
  structure-sheaf limit vanishing, Ext vanishing and generic injective-resolution
  facts; no theorem about the specified open-extended sheaf.
- `msearch.py ... loogle '"Injective", "rightDerived"'`: generic
  injective/rightDerived hits, no boundary-cohomology theorem. These generic
  vanishings require injectivity of the input on P and do not apply directly here.
- `msearch.py ... grep 'proper.*cohomology|boundaryCohomology|boundary_cohomology'`:
  0 hits.
- `rg` of the source `WeilConjectures` and published `lean/Sheaf` for boundary
  cohomology, the item id and proposed declaration names: no matching statement.
  Hits in the proper-open acyclicity module cite this item as an unproved dependency.
- `rg` of evaluation/rightDerived in published modules and Mathlib found the
  existing `SheafOfModules.toSheaf`, evaluation, and `Functor.rightDerived` APIs.
  Reading `ModuleAbelianEvaluationComparison` confirmed the distinction between
  module and abelian resolutions; the statement derives the composite in modules.
- `rg` for `HasInjectiveResolutions`/`EnoughInjectives` in published pro-etale
  modules found `ProEt.BasisDerivedDetection.smallModulesEnoughInjectives`, which
  applies to a transported AsSmall site, not this intrinsic original-site category.
  Hence the instance here reuses the independent-universe Grothendieck theorem.

Sources inspected: the node's complete statement, all statement-dependency
statements and Lean/mathlib records, and their signatures/docstrings; the blueprint
unit `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-existence/_section.md`;
Stacks `more-etale.tex` at `lemma-shriek-proper-and-open` and `proetale.tex` at
`lemma-jshriek-zero`. The latter is only section vanishing, as the node already
explicitly says; the theorem's higher-degree argument goes through proper base change
and exact evaluation, not a false direct use of Tag 09AG in positive degree.
Missing/stale local module source was read through `scompile.py --source`, notably
`WeilConjectures.AlgebraicGeometry.EtaleSheaves`,
`Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`, and
`Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationExact`.

No new STATEMENT-DISPUTED issue was found. The earlier correction is preserved
verbatim, including its history and citer audit. No target or unit statement is changed.

## Second reading by NA

This is a final in-thread consistency check, not an independent-agent review;
the dispatch brief forbids starting other agents and assigns independent review
to the maintainer. Reopened the node and completed file. All geometric, coefficient,
injectivity and etale-origin hypotheses match the correspondences above. The
conclusion derives global sections on the module category, at the identity site
object, with precisely positive degree. The coefficient realization is the recorded
canonical equivalence and the existing site comparison. No new definition of
extension by zero, site, or cohomology was introduced. Compiler-guided fixes made
the category-evaluation identifier explicit and supplied the resolution instance
at universes `(u+1,u,0)`; they do not modify the mathematical statement.
