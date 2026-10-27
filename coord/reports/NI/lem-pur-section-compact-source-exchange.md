## Worker report

The module `Sheaf.Paper.SectionCompactSourceExchange` states
`AlgebraicGeometry.SectionCompactSource.section_compact_source_exchange` and the
composition normalization clause `composition_normalization`. Both proofs are `sorry`.
Every other declaration is a real degree-zero construction, a canonical comparison,
or an instance transported from an existing finite quotient. There is no statement
correction, disputed statement, or dependency-module repair. The returned H2
repair adds two existing:true definition nodes owning already landed constructions;
no Lean source is added or changed for those nodes.

Hypotheses and objects, clause by clause:

- The prime is `(l : ℕ) [Fact l.Prime]`; the finite extension is
  `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. The positive level is `(n : ℕ) [Fact (1 ≤ n)]`.
  `Coefficient l E n` is exactly `ULift (Padic.coefficientExtensionRing l E n)`.
  This is the standard size lift of O_E/(varpi_E^n), with the same ring structure.
  `coefficientFinite` uses the dependency's positive-level finiteness theorem.
- `(K₀ : Type u) [Field K₀] (_hl : IsUnit (l : K₀))` renders the field and
  invertibility hypothesis. It is retained even though the normalization is more
  general and does not use invertibility in its construction.
- B and X are schemes over `Spec (.of K₀)`, each with `LocallyOfFiniteType`,
  `QuasiCompact`, and `IsSeparated` on its structure map. The specified h has
  `h.IsOver`, `IsSeparated h`, `LocallyOfFiniteType h`, and `QuasiCompact h`.
  The compactification is the existing `Compactification h` with open leg c.i,
  proper leg c.g, and factorization c.comm. No density hypothesis is added.
- The section is `(s : B ⟶ X) [IsClosedImmersion s]`, with
  `hs : s ≫ h = 𝟙 B`. There is no arbitrary supported complex in its place.
- `etaleConstant` and `proConstant` put the existing constant sheaf of the
  coefficient module in degree zero. `etaleSupported` and `proSupported` put
  the existing ordinary direct image of that constant in degree zero. Their
  explicit endpoint types preserve the site's object universe u+1 and morphism
  universe u. These are derived objects, not just lists of cohomology groups.
- F_h is `rightDerivedLowerShriekOfCompactificationPlus (ModuleCat A) c` on
  each site, the bounded-below restriction of the recorded Rp_* Dj_! formula.
  All input objects here are degree zero, so D+ covers precisely these inputs
  and its fully faithful inclusion gives the same maps in the ambient D.

Conclusions and prescribed normalizations:

- `etaleSource` is an isomorphism with the exact requested endpoints. Its inverse
  is F_h of `closedSingle` inverse, followed by Rp_* of normalized proper/open
  interchange for `(id,j,s,sj)`, then `compositor` inverse and `directIdentity`.
  The identity extension in that interchange is removed using its adjunction
  normalization. Properness of sj is obtained from `(sj)p=id` and separatedness
  of p, using Mathlib `IsProper.of_comp`, inside the data construction.
- `interchange` selects the family supplied by
  `Etale.properOpenInterchangeCoherence`; its ordinary section and derived-unit
  normalizations determine the map. It is not a choice of an unconstrained
  isomorphism. `compositor` is the actual right-derived composition comparison;
  `directIdentity` is `Etale.lowerStarIdDerivedPlus`.
- `compareConstant` is the exact functor/single comparison followed by the
  existing scalar-unit isomorphism `SupportedConstantNormalization.compareUnit`.
  `compareSupported` is the degree-zero image of the specified counit mate gamma.
  `sourceComparison` is the actual `compactSupportSiteComparisonPlus` followed
  by F_h(gamma), retaining its direction and endpoints.
- `proSource` is literally `compareConstant.inv`, comparison pullback of
  `etaleSource.hom`, then `sourceComparison`. Thus the site-comparison square
  identifies these actual source maps and its base endpoint is precisely the
  scalar-unit comparison, with no scalar automorphism or arbitrary endpoint map.
  The first two IsIso conclusions assert invertibility on B and arbitrary B'.
- `proClosedSingle` computes the closed-section compactification `(id,s)` using
  the existing pro-etale exact closed-direct-image theorem on its quasi-compact
  complementary open. `proCompositionInverse` then uses the computed proper/open
  composition `finiteCompactSiteCompositionAtWitness` for `(s,h)`, with the
  retained constant witness, the supplied tower, the proper compactification of
  s and the identity compactification copied along hs. The last factor is the
  actual identity normalization `finiteCompactSiteIdentityProPlus`.
- `composition_normalization` asserts that proSource followed by this specified
  composition inverse is identity, for every compatible tower. Its Noetherian
  hypotheses apply to all finite-type schemes over K₀ in the main statement;
  the same clause covers finite-type B' whether or not separated. On arbitrary
  B' the definition of proSource is instead the stipulated transport of the
  etale formula, so it requires no Noetherian hypothesis.
- The arbitrary base change is `(g : B' ⟶ B) [g.IsOver ...]`, with no finiteness,
  flatness, quasi-compactness, Noetherian, or separation condition on B'.
  `(v,h',sq : IsPullback v h' h g)` is an arbitrary presentation of X×_B B'.
  The section s', its closed-immersion instance and hs' give the induced
  section; `sqS : ChosenCartesianSquare g s' s v` retains its Cartesian
  identification, not an extra restriction on which base changes are allowed.
- `etaleBeta` and `proBeta` are the single-functor images of the existing actual
  supported-constant exchanges, with the exact-pullback/single comparison.
  Their IsIso conclusions give precisely the beta isomorphisms in the node.
- The first displayed equality in the theorem is
  g_et^*(a_h) ≫ C_et(s_*A) ≫ F_h'(beta_et) = constantPull.hom ≫ a_h'.
  C_et is the recorded compactification-relative exchange, and its target
  compactification is exactly `c.ofIsPullback sq`.
- The second equality is the identical expression on the pro-etale site.
  `proExchange` descends the existing ambient compactification exchange through
  the fully faithful D+ inclusion, inserting only the recorded exact-pullback
  and D+/D compatibility isomorphisms. It is the proper derived mate followed
  by the open-extension base-change comparison, not an arbitrarily transported
  arrow. The finite-level comparison identifies this actual arrow with the
  transported one at the supported-constant etale-origin witness.
- `constantPull` and `proConstantPull` explicitly insert the scalar-preserving
  identifications g^*A_B ≅ A_B'. Thus both equalities express identity on A_B'
  under the stated source normalizations.

Dependency declarations read and used (the module imports retain these interfaces):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; the reexported coefficient ring and uniformizer.
- Mathlib morphism modules `FiniteType`, `Proper`, `ClosedImmersion`:
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`, `IsProper`,
  `IsClosedImmersion`, and `IsProper.of_comp`.
- `WeilConjectures.Compactification.RefinementCategory`:
  `Compactification`, `Compactification.Refinement`, its category;
  the actual base-change construction `Compactification.ofIsPullback`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `Etale.DerivedCategoryModule`, the ordinary sheaf-of-ModuleCat encoding,
  `DerivedCategory.Plus`, `singleFunctor`, and its fully faithful inclusion.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  the finite coefficient realizations of the ordinary module sheaf category.
  `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport` reexports the corresponding
  intrinsic presentation; this item explicitly requests ordinary fixed-scalar modules.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`:
  `Etale.rightDerivedLowerShriekOfCompactificationPlus` and
  `Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`.
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`:
  `Etale.ProperOpenDerivedFamily`, `Etale.properOpenInterchangeCoherence`.
- `Sheaf.Paper.EtaleDerivedDirectImageCoherence`:
  `Etale.exists_normalizedDerivedDirectImageCoherence`, whose normalized
  derived comparators are `Functor.rightDerivedFunctorPlusCompIso'` and
  `Etale.lowerStarIdDerivedPlus` used here.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`:
  `ProEtale.originComposition` and its canonical etale-origin normalization.
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`:
  `ProEtale.compactSupportSiteComparisonPlus` and its ambient version.
- `Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange`:
  `ProEtale.isIso_csAuxiliaryExchange`, identifying the actual proper/open exchange
  at the finite coefficient witness.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange`:
  `ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap` and its
  exact-pullback and bounded-below compatibility comparisons.
- Definition ownership after the H2 repair: the already landed
  `def-pur-supported-constant-exchange-maps` owns `constant`, `supported`,
  `unitIso`, `compareUnit`, `gamma` and their ordinary components in
  `Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization`.
  The new `def-pur-supported-constant-base-change-maps` owns `square` and
  `exchange` in that same module. The new
  `def-pur-finite-compact-site-constructions` owns the eight plain constructions
  in `Sheaf.Paper.FiniteCompactSiteCoherence`, including the composition at a
  retained witness and identity normalization. The already landed
  `def-sf-compact-support-site-comparison-construction` owns
  `ProEtale.compactSupportSiteComparisonPlus` used by `sourceComparison`.
  Both `lem-pur-supported-constant-exchange-normalization` and
  `lem-sp-finite-compact-site-coherence` stay in `proof_deps` for the eventual
  proofs; their conclusions do not supply the data of these plain definitions.
- The exact closed computation also uses the recorded proof dependency
  `ProEtale.preservesFiniteColimits_lowerStar_of_isCompl`, imported from its
  finite-coefficient module, and the etale exact finite-direct-image interface.

Edge cases checked before completing the statement: empty B (and hence empty X
when h has empty target), s=id and h=id, nonreduced bases, zero module objects,
arbitrary non-Noetherian/non-quasi-compact B', nonflat g, nonseparated finite-type
B', and the first positive coefficient level n=1. No nonemptiness, smoothness,
reducedness, irreducibility, or flatness is assumed. n=0 is outside the node's
positive-level range. The construction is independent of the chosen Cartesian
presentation and the theorem retains that presentation explicitly.

Searches for an existing exact statement:

- msearch.py LeanFinder: “Compact support of a constant sheaf supported on a
  closed section identifies with the constant sheaf on the base and arbitrary
  base change exchange is identity”. Eight results, headed by
  `CompHausLike.LocallyConstant.counit_app_val` and constant-sheaf results;
  none is this normalization/exchange theorem.
- msearch.py Loogle: `"lowerShriek", "comp"`; no results.
- msearch.py grep, AlgebraicGeometry:
  `(shriek|compactSupport|lowerShriek).*(section|comp)|(section).*(shriek|compactSupport)`;
  no matches in Mathlib.
- msearch.py LeanSearch: “Compact support of the constant sheaf supported on a
  closed section is the constant sheaf on the base, compatibly with arbitrary
  base change”. Eight constant-sheaf/essential-image results, no matching theorem.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for the item id: no declaration.
  Concept searches found existing composition, support, coefficient-comparison,
  and base-change interfaces, reused above. Searches for SectionCompactSource
  and section compact-source exchange found no existing combined assertion.

Validation: scompile.py compiled the complete module in sandbox and library module
mode with no errors or warnings (38.0 s and 40.7 s in the saved theorem check).
The earlier timeout was diagnosed: using a Bool-selected site in the inferred
object types forced deep derived-localization equality checking. Explicit etale
and pro-etale endpoint types resolved it without changing the objects or universes.
The final file has no diagnostic commands, no local notation or local instances,
and no auto-bound variables or universes.


## Returned-delivery repair

Return L, immutable head fb50ca0e70ff, H2, repaired point by point:

1. Removed the two theorem nodes added to `stmt_deps` by the returned packet.
   Used the landed `def-pur-supported-constant-exchange-maps` for the ordinary
   components and gamma. Added the existing:true definition node
   `def-pur-supported-constant-base-change-maps` for the closed adjunction-mate
   exchange and its square. Its formula is the literal transpose of square,
   inverse-image of the counit, then the scalar-preserving unit identification;
   this is the construction of Stacks 07A7, with the localized adjunction
   normalization cited in 03S6. It asserts no invertibility theorem.
2. Added `def-pur-finite-compact-site-constructions`, existing:true on
   `Sheaf.Paper.FiniteCompactSiteCoherence`, owning all eight requested defs:
   `finiteCompactSiteChangePlus`, `finiteCompactSiteChangeAtWitness`,
   `finiteCompactSiteOpenCongr`, `finiteCompactSiteTowerOpen`,
   `finiteCompactSiteTowerPlus`, `finiteCompactSiteCompositionPlus`,
   `finiteCompactSiteCompositionAtWitness`, `finiteCompactSiteIdentityProPlus`.
   Both theorem nodes remain in `proof_deps` unchanged. No `.choose` or theorem
   result is used by these eight plain definition bodies.
3. Followed the advisory in the item's `lean.note`: the compositor is the
   computed alpha^pro of `lem-sp-finite-compact-site-coherence`, which is
   identified with `thm-sf-comp-composition`'s canonical composition, and
   `compactSupportSiteComparisonPlus` is cited through its definition owner
   `def-sf-compact-support-site-comparison-construction`.

The live item still has no Lean record. Comparing the saved packet with that
item shows that its original statement, proof, proof_deps, source and all other
fields are unchanged; only `lean` and authorized added statement dependencies
are delivered. The prescribed delivery wrapper rebases on the current live tip.
The Lean module is unchanged from the returned, mathematically accepted module.

## New nodes

`def-pur-supported-constant-base-change-maps` records the existing square and
supported-constant exchange in `SupportedConstantExchangeNormalization`.
The statement names arbitrary schemes and vertical morphisms, a chosen Cartesian
square, the actual inverse-image square identification on each site, and the
counit-mate composite with the constant unit. It therefore includes the closed
case without asserting that exchange is invertible for arbitrary morphisms.
Source: Stacks 07A7, the base-change adjunction construction, with 03S6's
localized adjunction normalization. LeanSearch and LeanFinder returned eight
hits each about general adjunctions or constant sheaves, with no exact map.
Mathlib grep found zero hits. DAG ownership search found only the theorem's
helper list; `def-pur-supported-constant-exchange-maps` does not own these two
helpers. Blueprint search “supported constant” returned zero nodes. The exact
Sheaf definitions are reused with no new module.

`def-pur-finite-compact-site-constructions` records the existing common-refinement
change and its witness transport, equality transport of open extension, tower
open composition, computed proper/open tower arrow, supplied-compactification
composition and its witness transport, and identity normalization. Its sources
are Stacks 0F7I, 0F7J, 0F7K. The item uses the composition at the retained
constant witness and the identity normalization exactly as before. LeanSearch
and LeanFinder returned eight algebraic or geometric finiteness hits each and
no exact construction; Mathlib grep found zero hits. Blueprint search “compact
site” returned zero nodes. DAG ownership search found only the theorem's helper
list, while the existing chosen-compositor definition owns a different
construction using chosen compactifications. The exact eight Sheaf definitions
are reused with no new module. Each new node's mathlib_searches contains the
actual returned search output and the repository ownership-search findings.

## Second reading by NI

Repair self-check by the same worker, without starting another agent as the
brief requires. The maintainer's independent mathematical reading of the returned
head is retained as the independent review; this section does not claim another
worker performed a new reading.

I reopened the item node, the complete unchanged Lean module, both new node
records, and the bodies of all ten newly owned existing definitions. The coefficient,
field, separated finite-type hypotheses and closed-section equation match the
binders of `section_compact_source_exchange`. The arbitrary base-change binders
impose no finiteness, flatness, Noetherian or separation condition on B'. The
four IsIso clauses and the two actual exchange equations have exactly the
recorded supported-constant and compactification endpoints. The normalization
clause still compares `proSource` to the actual computed composition inverse,
and the etale definition still uses normalized interchange, inverse compositor,
and identity direct image. No mathematical statement or Lean binder changed.

For the first new node, `square` uses the etale square identification or the
specified pro-etale coherent square; `exchange` is exactly the counit mate
followed by `unitIso`. Both are defined without choosing data from the
normalization theorem. For the second new node, I checked the direction of
common-refinement changes: `properTransportRefinementPlus r` maps from the fine
to the coarse compactification, so its inverse followed by the other leg is
exactly Delta. The witness inverse precedes the computed map and the forward
witness follows it. The tower body uses the inverse open comparison, the actual
proper/open interchange, then the forward open comparison, proper compositor,
equality transport and open compositor in that order. The composition body
inserts exactly C at the intermediate etale witness. The identity body uses
the actual direct-image and open-adjunction identities. The new nodes assert
only these constructions, leaving all coherence and invertibility to the two
proof dependencies. The mismatch found was precisely H2 ownership; it is
repaired by the two new definition records and the two landed definition citations.

Repair validation (2026-10-23 UTC): prescribed scompile.py passes the unchanged
item module in sandbox mode (38.0 s) and library module mode (40.7 s), with no
errors or warnings. The updated packet passes deliver2.py --no-push, commit
c1386612bf5, including preflight and its declaration checks. The two new nodes
have all dependencies present; a complete statement-dependency traversal found
no cycle. A structured comparison against the current read-only live item
confirms that only lean and stmt_deps changed and that both normalization
theorems remain in proof_deps. No library file or launcher tool was edited.
