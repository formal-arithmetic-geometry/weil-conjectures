## Worker report

Repaired the returned immutable head `2a3f4394d0fc` in the retained packet. The prescribed
initial dry run passed (`eb9089328d`), but reading the saved Lean against the return confirmed
both semantic defects. This repair changes the actual interface; it is not an unchanged repush.
The current shared node still has the original mathematical statement and no Lean binding.
The delivery wrapper rebases the repaired packet onto the current `newtargets-dag`.

H3 is repaired as follows.

* Exchange is now the existing `supportedConstantExchange A i i' h hD sqD.toCommSq` from
  `Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary`, not a free field. That definition
  is the published `baseChangeMap` mate followed by `lowerStar i'` of
  `Scheme.upperStarConstantSheafIso`. Its inverse satisfies both inverse equations.
* `SupportedHomConeModel.q_spec` specifies restriction in every degree by
  `globalSectionsUpperStarMap`. `modelIso_spec` fixes the resolution comparison to
  `supportedHomModelMap`: the derived image of `toKInjectiveResolution`, followed by
  `rightDerivedFunctorObjQIso`. This does not choose an unspecified isomorphism.
* `toSections_spec` is evaluation at 1 of precomposition by the existing
  `supportedConstantUnit`. `inclusion_fst` and `inclusion_snd` uniquely specify the kernel
  inclusion into the shifted cone: its sections component is `toSections`, and its other
  component is zero. `comparison_spec` fixes the cone isomorphism to the localized inclusion
  composed with the fixed Hom-model comparison. Rescaling the comparison is no longer allowed. `comparison_naturality` also records
  the dependency's naturality equation for every map of coefficient complexes, using the actual
  resolution-functor and diagonal-cone maps.
* `resolutionComparison_spec` requires the actual comparison of resolutions to extend the
  pulled-back resolution unit. Such comparisons are unique up to homotopy, which is the
  equality relevant after localization. They cannot be arbitrary coefficient maps.
  `sectionsMap_spec` and `openSectionsMap_spec` fix their components to section pullback
  followed by that comparison; the latter includes the specified square composition iso.
  `restriction_square` makes their square commute strictly. `supportedRelativePullback` is
  a real definition: `Q.map` of the shifted `mappingCone.map` of those two chain maps.
* `homMap_spec` fixes each component on EVERY sheaf morphism `c` to
  `exchangeInverse ≫ (upperStar _ h).map c ≫ resolutionComparison.f n`.
  `supportedHomPullback` localizes this map and transports it through the fixed model isos.
  The final pullback equation uses these actual definitions, not independently chosen maps
  of cohomology groups.
* Forgetting has the fixed target `H^n(Q(Γ(T,I)))`. `projection_spec` uniquely fixes the
  cone-to-sections projection. The two final conjuncts, on both T and T', compare its image
  under homology with the image of `toSections`, hence with precomposition by the constant
  unit. The arbitrary `forgetTarget`, `forget`, and `forgetHom` fields have been removed.

H8 is repaired: the final theorem's docstring now contains eight numbered proof steps covering
all ten steps in the node: closed exchange on stalks; normalization on constant units;
resolution comparison by fibrant lifting; the open-closed short exact sequence; computing
Hom and sections on K-injectives; the signed kernel/cone quasi-isomorphism; the strict maps
of complexes and their homotopy independence; the induced derived-morphism formula; and
forgetting support. The docstring names the proof dependencies at the steps using them.
The final theorem is the only `sorry`; all helper definitions have real data.

Hypothesis/clause correspondence, with the node and final file read together:

* The commutative ring is `(A : Type (u + 1)) [CommRing A]`. Ordinary constant A-module
  sheaves are `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)`, with exactly the existing
  six-functor encoding and its universe convention. No ring finiteness, nontriviality,
  invertibility, or Cartier-divisor assumption is imported into a signature.
* The six schemes are `{T' T D' D V' V : Scheme.{u}}`; `h`, `i`, `i'`, `hD`, `v`, `v'`,
  `hV` are the maps. Closed immersions and open immersions are explicit typeclass binders.
  `sqD : IsPullback hD i' i h` and `sqV : IsPullback hV v' v h` give exactly the two
  scheme-theoretic pullback squares. `hcomp`, `hcomp'` equate the ranges of the open
  immersions with the complements of the respective closed ranges.
* The canonical closed exchange is `supportedConstantExchange`; `exchange_isIso` states
  invertibility. Its two inverse laws fix `exchangeInverse` uniquely.
* The relative-section object is `supportedRelativeObject`: the localization of the shifted
  cone of restriction on the functorial K-injective resolution. This is canonically the
  node's shift of the localized cone because `DerivedCategory.Q` commutes with shifts.
  The source and target models have separate, fully specified restriction and comparison
  maps; neither is obtained by pulling an injective resolution back and assuming it injective.
* `supportedHomObject` is literally the recorded `closedSupportHom` left-hand side,
  `R(linearCoyoneda A (i_* A_D))(Q K)`. The normalized kernel inclusion realizes that
  dependency's comparison. Its degree-n homology is ordinary derived Hom in degree n,
  equivalently `Hom_D(i_* A_D, K[n])` by the K-injective cocycle/derived-morphism
  interpretation used in the node proof. `supportedHomIdentification` applies homology to
  the inverse normalized comparison.
* `K` is a cochain complex of these sheaves, `_hK : ∃ b, ∀ n < b, IsZero (K.X n)` is
  bounded-below, and `(n : ℤ)` allows every degree. The first conjunct is the node's
  pullback equation as an equality of A-module morphisms, hence for every element x.
  Its Hom-side action is fixed by `homMap_spec`, so it is exactly inverse image followed
  by precomposition with inverse exchange.
* The last two conjuncts give the node's forgetting-support identification for each pair,
  with actual projections and fixed global-section targets. Their maps are fixed before
  the compatibility equations are asserted.

Dependency declarations read and used:

* `Sheaf.AlgebraicGeometry.ClosedSupportHom.closedSupportHom` (declaration namespace
  `AlgebraicGeometry.Etale`): the recorded ordinary RHom and restriction cone, with
  functorial K-injective models and naturality. Its signature and full proof docstring were
  read locally and checked with `scompile.py --source` against the current published source.
* `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `upperStar`, `lowerStar`,
  `upperStarLowerStarAdjunction`, and `upperStarComp`; all signatures and their descriptions
  of the canonical site functors and composition comparisons were read.
* `WeilConjectures.AlgebraicGeometry.DerivedCategories` / `...Etale.Derived.Coefficients`:
  the recorded `DerivedCategoryModule` encoding (current source read with `--source`).
  Mathlib's `DerivedCategory`, `Q`, shift, and `homologyFunctor` give the actual categories
  and operations. `...Etale.Derived.LowerShriek.rightDerivedGlobalSections` and `cohomology`
  explain the dependency's computation of RΓ and cohomology on these models.
* Mathlib: `Scheme`, `IsClosedImmersion`, `IsPullback`, `constantSheaf`,
  `constantSheafAdj`, and `Sheaf.ΓNatIsoSheafSections`. Read the signatures of the
  recorded dependencies, including the limit condition in `IsPullback` and the
  sheafification/terminal-evaluation adjunction for the constant sheaf.
* `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer.ordinaryFiniteConstant` and
  `Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary.supportedConstantUnit`,
  `supportedConstantExchange` (all in namespace `AlgebraicGeometry.Etale`). Their helper
  signatures apply to EVERY commutative ring and arbitrary scheme maps, despite their
  owning nodes' broader Kummer subject. The two already-landed owning nodes are added to
  `stmt_deps`; their node files are not changed. They have no dependency on this item.
* `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`:
  `Functor.rightDerivedFunctorObjQIso`, whose construction is the inverse derived-functor
  unit on a K-injective complex; `...GrothendieckAbelian.KInjectiveResolution` supplies the
  actual functorial replacement and its resolution unit.

No new definition node or dependency repair is needed: the new helper declarations are the
representative operations and characterizations of this item's own support-Hom comparison.
They are all listed in `lean.declarations`. The proof-dependency imports are retained for
stage 3; no other file is changed.

Edge cases were checked on the formulas: identity h; empty D (V=T); D=T (empty V); empty
schemes; zero coefficient ring; zero K; negative, zero, and positive degrees; and a complex
whose lower bound is attained. No case requires flatness or nonzero coefficients. For
h=id the resolution comparison extends the identity coefficient pullback; on D=T it gives
the ordinary section/Hom map. In a nonzero constant degree-zero example a zero comparison
cannot extend the resolution unit, and a zero forgetting map cannot satisfy projection_spec.
The all-zero solution from the return is therefore excluded precisely when the canonical
map is nonzero; genuinely zero cohomology groups remain permitted.

Searches retained from the previous packet: LeanFinder, "naturality of the supported Hom
identification under base change" (only generic naturality); LeanSearch, "cohomology with
support derived Hom pullback" (generic derived and short-complex results); Loogle,
"support, Hom" (`HomologicalComplex.IsSupported`, unrelated); rg in Mathlib, WeilConjectures
and lean/Sheaf for supported Hom and support pullback (no complete existing theorem).
The exact item-id search in the upstream source found no declaration for this item.

Repair searches actually run:

* `msearch.py ... grep 'upperStar.*[Cc]onstant|[Cc]onstant.*upperStar'`: zero Mathlib hits.
  Source rg located the canonical `Scheme.upperStarConstantSheafIso` and the existing
  constant exchange helpers; the delivered file reuses them.
* `msearch.py ... leanfinder 'canonical relative cohomology pullback via a diagonal map of
  restriction mapping cones and closed support Hom'`: eight hits, including
  `mappingCone.lift`, `liftCocycle`, `fst`, and unrelated group-cohomology maps; none is
  the etale supported-Hom theorem. The appropriate existing `mappingCone.map` is used.
* `msearch.py ... loogle 'CochainComplex.mappingCone.map,
  CategoryTheory.Functor.rightDerivedFunctorObjQIso'`: zero hits; the latter name is
  unknown to Mathlib's index because it is a project declaration. Its actual upstream
  source was read and is used, not copied.
* `msearch.py ... leansearch 'relative cohomology supported Hom pullback kernel inclusion
  mapping cone canonical'`: eight generic mapping-cone or kernel hits, no exact theorem.
* `tools/blueprint_refs.py search 'supported Hom'`: zero blueprint matches. rg of the
  actual DAG and project Lean found the already-recorded closed-support theorem and the
  unrestricted unit/exchange helper nodes, which are reused.
* rg for evaluation-at-one/`ΓNatIsoSheafSections` in the ordinary support modules and the
  upstream etale directory found the generic global-section comparison, no duplicate of
  this helper's combined constant-adjunction evaluation.

## Second reading by Q58

The dispatcher explicitly forbids additional agents, so this is a second self-reading with
the node and final Lean file open. The returned packet's uncharacterized exchange, two
arbitrary cohomology pullbacks, scalar-ambiguous cone isomorphisms, and arbitrary forgetting
target were the mismatches. All are replaced or characterized as detailed above. In
particular the compatibility equation cannot itself define pullback, since the relative
pullback is already the actual diagonal cone map; the Hom side is independently fixed on
every representative morphism. The separate comparison_spec fixes the normalization of Φ.

I checked the ring and all seven scheme maps; both cartesian-square hypotheses; both open
complement equations; exchange and its inverse; the lower bound and arbitrary integer
degree; the relative pullback equation; and forgetting support on both schemes. There are
no additional geometric or coefficient restrictions. All variables are bound explicitly
and the file disables autoImplicit. Only the final theorem has a postponed proof, and its
full natural-language proof is now in its docstring. The two additional dependency nodes
supply existing constructions and introduce no circular dependency.

## Statement corrected

The correction retained from the saved packet expands the original statement recorded
verbatim in `statement_change.old_statement`. It introduces the open-complement schemes,
immersion maps and cartesian-square maps that were implicit in the original prose. The
repair additionally spells out the canonical representative constructions that the old
Lean packet failed to fix: unit-compatible resolution comparison, section pullbacks,
diagonal cone map, inverse-exchange Hom map, kernel-inclusion cone comparison and
projection to global sections. These are the operations in the node's original proof,
Stacks Tags 095L and 0A45, and the current blueprint's penultimate supported-Hom paragraph
of `lem-amb-cartier-kummer-map.proof.md`. No source hypothesis or conclusion is changed.

The complete current-main citer audit (`rg -l` followed by checking both dependency lists)
finds only `lem-asd-ordinary-supported-kummer`: holds true. It uses canonical exchange,
support-Hom pullback and the identification after forgetting support. The repaired formulas
supply exactly those operations; the existing published unit/exchange helpers are the
ones that citer already uses. That citer's node and module are not edited.

Validation: final `scompile.py` passed without errors or warnings, for both its sandbox and
library-path checks (44.2 s and 47.1 s, each below the unchanged 60-second limit). The exact
recorded theorem signature, declaration inventory, 100-character lines and single named
`sorry` were checked. A targeted dependency traversal from each newly cited helper node
found no path back to this item. The prescribed delivery dry run and push perform the
maintainer preflight and per-file compilation again.
