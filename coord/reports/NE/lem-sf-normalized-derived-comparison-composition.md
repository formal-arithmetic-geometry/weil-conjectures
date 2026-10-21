## Worker report

The module `Sheaf.CategoryTheory.NormalizedDerivedComparisonComposition` states
`CategoryTheory.Functor.normalizedDerivedComparison_composition`. Its proof is `sorry`.
The two accompanying helpers are fully defined: the canonical localization isomorphism
for a specified equality with a composite, and the predicate expressing exactly the
normalization supplied in this node. They belong to this node's displayed formula, rather
than introducing an independent mathematical notion. No definition has postponed data or
an internal sorry. No other theorem is introduced.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The six abelian categories are `A0`, `A1`, `A2`, `B0`, `B1`, `B2`, with explicit
  `Category` and `Abelian` instances. Each has its own object, morphism and localization
  universe. `HasDerivedCategory` specifies the chosen localization universe, as required
  by the recorded `def-weil-abstract-derived-category` interface; there are no equalities
  between these universes.
- The existence of arbitrary K-injective resolutions in each source category is exactly
  `enough0`, `enough1`, `enough2`: every integer-indexed cochain complex has a morphism to
  an `IsKInjective` complex which is a `QuasiIso`. No monomorphism requirement is added.
  No resolution-existence hypothesis is imposed on any target category `Bi`.
- `F0`, `F1`, `F2` and their `Additive` instances render the three additive functors.
  No left exactness is required of them. Their total right derived pairs are exactly the
  recorded `rightDerivedFunctorOfQuasiIsoResolutions` and
  `rightDerivedFunctorOfQuasiIsoResolutionsUnit`, with the relevant `enough` argument.
  This uses the canonical representative of the universal pair fixed by the dependency;
  another universal pair is uniquely isomorphic to it compatibly with its unit, by
  `rightDerivedFunctorOfQuasiIsoResolutions_unique`, so no choice of pair is excluded.
- The localizations `Qi` and `Pi` are `DerivedCategory.Qh` on homotopy categories or
  `DerivedCategory.Q` on complexes, related by `quotientCompQhIso` inside the recorded
  resolution comparison. Cochain complexes have shape `.up ℤ`, without boundedness.
- Each `c_a` is the recorded
  `rightDerivedFunctorOfQuasiIsoResolutionsObjIso enough a`. Its definition is RF(Qa)
  followed by the inverse unit and the canonical Q/Qh transports. This is exactly the
  resolution comparison from `lem-sf-kinjective-derived-map-computation`.
- All three `rij` and all three `sij` are explicitly bound. Each has `Additive`,
  `PreservesFiniteLimits` and `PreservesFiniteColimits` instances, exactly the node's
  exact-additive requirement. Their termwise and derived actions are
  `mapHomologicalComplex` and `mapDerivedCategory`.
- `er : r02 = r12 ⋙ r01` and `es : s02 = s12 ⋙ s01` are the two stated composition
  equalities. Lean functor composition is written in application order. `e01`, `e12`
  and `e02` are exactly `Fi rij = sij Fj`, as equalities of functors, hence on objects
  and morphisms. All three equalities are retained explicitly.
- `β01`, `β12`, `β02` are supplied natural isomorphisms, with precisely the source and
  target functors RF_i r_ij and s_ij RF_j. They are not arbitrary componentwise maps.
- `h01`, `h12`, `h02` each assert `IsKInjectiveNormalizedDerivedComparison`. Expanding
  that predicate quantifies over every K-injective `H` in the appropriate source, every
  K-injective `I` in the receiving category, and every quasi-isomorphism
  `a : r(H) ⟶ I`. The existential proof `hFa : IsIso (Q.map (F.map a))` is precisely
  the node's invertibility clause. It is proof data, not a chosen morphism.
- The normalization equality in that predicate is `c_a.inv`, followed by the supplied
  comparison transported by `normalizedDerivedComparisonComplexIso`, followed by
  `s.mapDerivedCategory.map (G.ObjIso enough (𝟙 H)).hom`, and the inverse
  `normalizedDerivedComparisonTargetIso`. The identity-resolution comparison equals
  eta_H inverse, with the recorded Q/Qh transports. The target helper uses the supplied
  strict equality `r ⋙ F = G ⋙ s` and the exact localization factorization for s.
  Thus this is exactly `(s eta_H)^(-1) beta_H c_a^(-1) = P(Fa)^(-1)` with its
  canonical endpoint identifications. `@CategoryTheory.inv ... hFa` refers to the
  inverse of that actual localized image map.
- `L : DerivedCategory A2` is arbitrary. The conclusion is equality of the actual
  morphisms `β02.hom.app L` and the composite of `β01` at `r12(L)` with
  `s01.mapDerivedCategory.map (β12.hom.app L)`. The first and last factors insert
  exactly the canonical source/target identifications stipulated by the node.
  The helper `normalizedDerivedComparisonCompositionLocalizationIso` is defined by
  `mapDerivedCategoryNatIso (eqToIso e)` followed by `mapDerivedCategoryCompIso`.
  Its inverse is used at the target. It supplies composite exactness instances inside
  its definition; it adds no hypothesis and introduces no file-local instance.
- There is no assumption anywhere that an `rij` preserves K-injective complexes.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic` (full class and docstring inspected).
- `def-sp-left-exact-additive`: the match's additivity clause is
  `CategoryTheory.Functor.Additive`,
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`. The node here only asks for
  additivity of Fi, so its left-exact and R^n clauses are not imposed.
- `def-sfb-right-derived-functor`:
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`, the recorded
  functor, unit, universal/uniqueness statements, unit invertibility and `ObjIso`.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q` and `DerivedCategory.Qh`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `lem-sf-kinjective-derived-map-computation`:
  `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`; read the full recorded
  helper and theorem signatures/docstrings, including functoriality, transition
  computation, transition laws and naturality. Its resolution maps use exactly the
  above `ObjIso`, which this statement also uses.
- `lem-weil-pbc-exact-functor-derived-factorization`: its `mathlib_match` is usable:
  `CategoryTheory.Functor.mapDerivedCategoryFactors` and `mapDerivedCategory` in
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`. Their full signatures and
  documentation were read. No repair of this leaf is needed.
- `def-sf-normalized-derived-comparison-identifications`: the new definition node
  owns the existing `normalizedDerivedComparisonComplexIso` and
  `normalizedDerivedComparisonTargetIso` in
  `Sheaf.CategoryTheory.NormalizedDerivedComparisonCommonResolution`. This definition
  node is the statement dependency for those two real-data endpoint identifications.
  Its module is public because these helpers appear in the normalization predicate.
- `lem-sf-normalized-derived-comparison-common-resolution`: retained solely in
  `proof_deps`; its theorem `normalizedDerivedComparison_commonResolution` supplies
  step (2) of the composition proof. Read its entire module, including both endpoint
  definitions, the resolution-map helper, and both theorem signatures/docstrings.
  The endpoint definitions are not choices from either theorem, so the theorem node
  cannot own their use as notions in this item's statement.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `mapDerivedCategoryNatIso` and `mapDerivedCategoryCompIso`, with their explicit
  localization constructions and factorization characterizations. These are reused,
  not reconstructed or assumed. The generic helper compiled with all category and
  localization universes independent.

Edge cases checked before writing: identity restrictions and identity resolutions give
inverse-unit normalization and the usual two-factor comparison; a zero category or zero
complex is included, with all normalization maps of the same types; acyclic complexes
remain permitted and no representative is required to have nonzero cohomology; arbitrary
unbounded complexes are included; `r12(H)` and `r01(J)` need not be K-injective, because
resolutions are chosen in their receiving categories. The orientation of the source
transport is from r02 to r12 followed by r01; the target transport is its inverse for s02.
This checks the two sides have identical endpoints even when derived composition is not
strict. No statement fault or disputed mathematical assertion was found.

Source read: `literature/stacks-project/derived.tex`,
`lemma-K-injective-defined` (Tag 070Y), and the following enough-K-injectives lemma;
the actual six-step composition proof is the node's explicit agent-written argument.
The theorem docstring carries those six steps and their dependencies.

Searches performed (raw responses are in the sandbox's `searches.jsonl`):

- `msearch.py ... leanfinder` with query
  `K-injective normalized comparisons of total right derived functors commute with composition of exact functors`:
  returned `NatTrans.rightDerived_comp[_assoc]`, the single-localizer
  `rightDerivedFunctorComparison_fac` family, and ordinary derived natural-transformation
  results. These concern vertical composition or one comparison, not this horizontal
  three-comparison normalization theorem. The relevant signatures and docstrings in
  `Functor/Derived/RightDerived.lean` and
  `Localization/DerivabilityStructure/PointwiseRightDerived.lean` were inspected.
- `msearch.py ... loogle '"mapDerivedCategoryCompIso"'`: found the canonical
  composition isomorphism and its characterizations. Reused the published upstream
  declaration after reading its full implementation; it does not state the requested
  normalization-composition theorem.
- `msearch.py ... grep 'rightDerived.*(comp|[Cc]omparison)|KInjective.*[Cc]omparison' CategoryTheory`:
  eleven results in ordinary right-derived functors and the single-localizer
  comparison file. No exact match.
- `msearch.py ... leansearch` with query
  `Successive K-injective resolutions give composition compatibility for normalized comparisons of total right derived functors`:
  eight ordinary injective-resolution/right-derived natural-transformation results;
  no statement of the requested theorem.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `normalizedDerivedComparison` found the shared common-resolution helpers/theorem
  and a different private reconstruction comparison, not this composition theorem.
  A broader search for comparison/composition found the canonical exact-derived
  composition API above and unrelated tensor, Ext or adjunction comparisons.
- `rg` of the proposed declaration names in `dag/lean_names_upstream.json`,
  `lean/WeilConjectures` and `lean/Sheaf` found no existing declaration.
- `rg` for this item's blueprint id in `lean/WeilConjectures` found no module.
  Broader DAG/Lean searches for normalized comparison composition found this node,
  the existing common-resolution node and different adjunction/operation statements.
- `scompile.py --source Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` confirmed
  the live Mathlib factorization interface; composition functoriality is supplied by
  the separate upstream WeilConjectures module already imported here.

Validation: the prescribed `scompile.py NE lem-sf-normalized-derived-comparison-composition`
compiled the complete file twice (sandbox and actual library module name) against the
live server, with no errors or warnings (2.2 s and 2.0 s). All variables and universes
are explicitly bound, and every Lean source line is at most 100 characters.

No independent second reader was started: the dispatch brief explicitly forbids starting
agents and assigns independent review to the maintainer after self-delivery.

## New nodes

`def-sf-normalized-derived-comparison-identifications` owns exactly the existing
`CategoryTheory.Functor.normalizedDerivedComparisonComplexIso` and
`CategoryTheory.Functor.normalizedDerivedComparisonTargetIso`, with `existing: true`
on `Sheaf.CategoryTheory.NormalizedDerivedComparisonCommonResolution`. No new module
or duplicate definition is introduced. The source is the normalization convention in
this item and its common-resolution sibling, using the K-injective evaluation setting
of Stacks Tag 070Y. The new node's first formula is beta at Q(N) after RF of the
inverse factorization for r; its second is Q of the degreewise equality isomorphism
Fr = sG, then the inverse factorization for s. These are exactly the bodies of the
two declarations at lines 52–70 of the published module. All four categories are
abelian, all object/morphism/localization universes remain independent, F and G are
additive, both source categories have arbitrary K-injective resolutions, r and s are
exact additive, e is a strict functor equality, and beta is a supplied natural
isomorphism. N and J are arbitrary complexes, with no K-injective assumption.
The target helper uses only its relevant section parameters (F,G,r,s,e), so its data
does not depend on the resolution-existence assumptions or beta.

Searches: `msearch.py leansearch` for canonical localization identifications of a
supplied derived comparison returned eight generic total-derived/localizer comparison
results; `leanfinder` for the same comparison and Fr=sG returned eight generic
localization lifting/uniqueness results. Neither is this pair of endpoint definitions.
`msearch.py grep` for the two helper names and mapDerivedCategoryFactors in
Algebra/Homology/DerivedCategory returned ten hits, including the factorization reused
by both definitions. The raw structured search responses are copied verbatim from
searches.jsonl into the new node's mathlib_searches results. The DAG/source `rg`
search found the two definitions only in the published common-resolution module and
only the common-resolution theorem node recording their names; no definition node
owns them. `blueprint_refs.py search 'normalized derived comparison'` returned zero
blueprint matches. `blueprint_refs.py ancestor` gives
`def-weil-integral-rational-qbar-compact-support`; the new node retains that ancestor
and prefixes this item to its via path. Identity functors/equality and zero complexes
reduce both identifications to their canonical identity transports; no nonzero,
boundedness or K-injective preservation assumption is introduced.

## Repair of the returned delivery

The maintainer's H2/H12 finding at immutable head 8711b9b5240a is repaired by the
new definition node above. The saved packet was first inspected and dry-run; that
unmodified packet passed mechanically at e34f93b9e1d, but still had the ownership
fault. Compared with the current base, only lean and stmt_deps change on the item:
stmt_deps gains the new definition owner and does not gain the common-resolution
theorem. The latter remains in proof_deps, without any proof/proof_deps changes.
The saved Lean file and its theorem signature are retained exactly; all reviewed
hypotheses, normalization, canonical composition transports, and independent universes
are retained. This is a metadata ownership repair, with no mathematical statement
correction and no dependency module repair.

Self-check: read both existing definition signatures, their section parameters,
docstrings and real bodies, then matched each displayed source/target and factor in
the new node with those bodies. The first helper includes no equality e; the second
includes e and no beta or enough parameters. The source factorization is inverted
before applying RF, and the target factorization is inverted after Q(eqToIso e).
The normalization still quantifies over every K-injective H and every resolution
of rH and includes the actual localized F-image invertibility; the common-resolution
hnormalized convention is unchanged. No additional theorem or postponed data is
introduced. The only sorry in the delivered Lean file remains the requested theorem.
No agent was started; independent review remains with the maintainer as instructed.

Validation after repair (2026-10-21 UTC): scompile.py compiled the retained module
under its sandbox name (2.2 s) and library name (2.0 s), with no errors or warnings.
The repaired packet passed deliver2.py --no-push at a93f2df626b, including the
existing-definition declaration checks and per-file server compilation. The final
packet also normalizes TeX display newlines in the new node; the final dry run and
push revalidate the complete packet. The item signature is byte-for-byte the saved
signature, both new-node declarations refer to their existing source, and the
common-resolution theorem is excluded from stmt_deps and retained in proof_deps.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
