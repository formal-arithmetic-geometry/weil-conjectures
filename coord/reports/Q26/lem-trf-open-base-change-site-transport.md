## Worker report

The module `lean/Sheaf/AlgebraicGeometry/OpenBaseChangeSiteTransport.lean` defines the two
canonical derived comparison isomorphisms used to render the statement, and states
`AlgebraicGeometry.ProEtale.StrictTower.openBaseChangeSiteTransport` with proof `sorry`.
The source is the Stacks pro-etale text, Tag 09AF (`lemma-jshriek-comparison`, adjoint
normalization), together with the blueprint item `lem-trf-open-base-change-site-transport`.
No theorem is proved and no definition contains postponed data.

The finite commutative coefficient ring is rendered by
`Λ : Type (u + 1)`, `[CommRing Λ]`, `[Finite Λ]`, with
`[TopologicalSpace Λ] [DiscreteTopology Λ]`; the latter are the explicit discrete
constant-coefficient structures required by the recorded pro-etale module construction.
The four schemes and four arrows are
`{U' U Z' Z : Scheme.{u}}`, `r : U' ⟶ U`, `j' : U' ⟶ Z'`,
`j : U ⟶ Z`, and `q : Z' ⟶ Z`.  The two open-immersion hypotheses are
`[IsOpenImmersion j] [IsOpenImmersion j']`.  The eight qcqs hypotheses are the
individual binders `[QuasiCompact r] [QuasiSeparated r]`, and the corresponding
pairs for `j'`, `j`, and `q`.  The four Noetherian hypotheses are
`[IsNoetherian U'] [IsNoetherian U] [IsNoetherian Z'] [IsNoetherian Z]`;
Mathlib's `AlgebraicGeometry.IsNoetherian` is the scheme class extending local
Noetherianity and compactness, which is the finite affine Noetherian-cover meaning
used by the node.

The Cartesian square clause is `sq : IsPullback r j' j q`; its chosen commutative
square `sq.toCommSq.w` is passed to the canonical pro-etale map.  The object clause is
`M : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))`, and
`DerivedCategory.Plus.ι.obj M` is the underlying ordinary derived object at which all
natural transformations are evaluated.

`H Λ X Λ (RingHom.id Λ)` is the recorded constant-coefficient site comparison and
renders `C_X`.  `derivedPullbackComparison Λ f` is the derived inverse-mate pullback
comparison and renders `a_f`; it is built from `hPullbackInv` and its isomorphism proof.
`derivedOpenComparison Λ i` is the unit-normalized derived open-extension comparison
and renders `e_i`; it is built from `hOpen` and `hOpen_isIso`.  The left side is the
threefold composite
`a_q`, then the image under `q_p^*` of `e_j`, then
`singleBeta Λ r j' j q sq.toCommSq.w sq`, whose component is the canonical pro-etale
`β^p` at `C_U M`.  The right side first applies `H` to the inverse component of
`Etale.mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso`; because the recorded
étale isomorphism has direction `j'_! r^* ≅ q^* j_!`, its inverse component is exactly
`β^e : q_e^*j_{e,!}M → j'_{e,!}r_e^*M`.  It then applies `e_{j'}` and the derived
pullback comparison `a_r` under `j'_{p,!}`.  Thus the displayed Lean equality is
exactly `β^p_{C_UM} ∘ S_M = T_M ∘ C_{Z'}(β^e_M)` as an equality of actual derived
morphisms.

The helper definitions and theorem use these dependency declarations:

* `WeilConjectures.AlgebraicGeometry.DerivedCategories`,
  `AlgebraicGeometry.Etale.DerivedCategoryModule` and
  `DerivedCategory.Plus` (the node's recorded derived-category declarations).
* `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`,
  `AlgebraicGeometry.ProEtale.FiniteCoefficientModules` and its recorded finite
  coefficient derived-category declarations.
* `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`,
  `AlgebraicGeometry.Scheme.proEtaleSiteComparison`.
* `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`,
  `AlgebraicGeometry.ProEtale.supportSiteComparison_pullback_coherent` and its
  coefficient pullback/comparison declarations.
* `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`,
  `AlgebraicGeometry.ProEtale.fixedComparisonDirectImageMatePlus` (the canonical
  counit-mate interface retained by the dependency record).
* `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`,
  `AlgebraicGeometry.ProEtale.openImmersionLowerShriekComparison_coherence`.
* `Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport`,
  `AlgebraicGeometry.ProEtale.StrictTower.H`, `hOpen`, `hOpen_isIso`,
  `hPullbackInv`, and `hPullbackInv_isIso`.
* `Sheaf.AlgebraicGeometry.OpenImmersionSquare`,
  `AlgebraicGeometry.OpenImmersionSquare` (the square notion is represented in the
  theorem by the more general Mathlib `IsPullback` datum recorded by the dependency).
* `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
* `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherian`/`IsNoetherianRing`.
* `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`,
  `AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekBaseChangeMap`, together
  with the derived declaration
  `AlgebraicGeometry.Etale.mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso`.
* `Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized`,
  `AlgebraicGeometry.ProEtale.StrictTower.singleBeta` and its inverse/naturality
  declarations.

The standard old pro-etale open-base-change module was not imported because its
legacy `UpperLowerStar.Iso` declarations duplicate the current finite-coefficient
framework.  The recorded finite-coefficient transport and `singleBeta` are the
canonical normalized interfaces for the same maps; no arbitrary map or mere
`Nonempty` choice is introduced.

Edge cases were checked before writing.  Empty open subschemes are allowed by
`IsOpenImmersion` and are handled by the unit-normalized comparison and `singleBeta`;
there is no inhabitedness assumption.  Identity arrows and the identity Cartesian
square are allowed, and the recorded identity normalizations apply.  The zero finite
commutative ring and an empty scheme are covered by the same module and site
constructions.  The scheme universe is shared explicitly as `Scheme.{u}` and the
coefficient universe is `Type (u + 1)`, so no covered size case is discarded.  The
statement is for an arbitrary object of the bounded-below derived category, including
zero objects; no conservativity or nonzero hypothesis is added.

Searches made on 2026-10-17:

* `python3 /home/ubuntu/weil-launcher-nt/msearch.py Q26 lem-trf-open-base-change-site-transport leanfinder "site comparison preserves canonical open immersion base change for finite coefficient derived sheaves"` returned eight generic Mathlib pullback/sheaf hits and no exact statement.
* `python3 /home/ubuntu/weil-launcher-nt/msearch.py Q26 lem-trf-open-base-change-site-transport loogle "mapDerivedCategoryNatIso, openImmersionLowerShriek, singleBeta"` returned zero hits (`mapDerivedCategoryNatIso` was unknown to the search service).
* `python3 /home/ubuntu/weil-launcher-nt/msearch.py Q26 lem-trf-open-base-change-site-transport grep "openBaseChangeSiteTransport|singleBeta|derivedOpenComparison" WeilConjectures/SixFunctors` returned zero hits.
* `rg -n "openBaseChangeSiteTransport|open base change|singleBeta" /home/ubuntu/weil-src-slopmaster2/WeilConjectures` found only generic lower-shriek/open-comparison declarations; no declaration for this item.
* `grep -rl "lem-trf-open-base-change-site-transport" /home/ubuntu/weil-src-slopmaster2/WeilConjectures` returned no files.
* `rg -n "openBaseChangeSiteTransport|site comparison.*base change" /home/ubuntu/weil-newtargets-shared/lean/Sheaf` found no existing project statement.

`STATEMENT-DISPUTED:` none.  No statement correction, new definition node, or
additional dependency module was needed.

## Second reading by Q26

I reopened the target node, every recorded statement dependency, the final Lean file,
and the declaration signatures used in the helpers.  The second pass matches the finite
ring, all four schemes, all four named arrows, both open-immersion instances, all eight
qcqs assumptions, all four Noetherian assumptions, the chosen Cartesian square, and the
single arbitrary bounded-below object `M`.  It confirms that `H` supplies the same
constant-coefficient comparison at each scheme, that `derivedPullbackComparison` is the
named `a` map, and that `derivedOpenComparison` is the named `e` map.  It checks the
composition order: the left side is `a_q`, `q_p^*(e_j)`, then `β^p`; the right side is
`C_{Z'}` applied to the inverse étale base-change component `β^e`, then `e_{j'}`, then
`j'_{p,!}(a_r)`.  The inverse orientation was checked directly against the recorded
signature of `mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso`.

No hypothesis is silently added beyond the explicit discrete topology structures needed
by the recorded constant-coefficient definitions, and no conclusion is weakened or
strengthened.  Empty and identity cases remain admitted by the same typeclasses and
natural transformations.  The module compiles cleanly with the required `scompile.py`
wrapper; its only postponed proof is the theorem's `sorry`.
