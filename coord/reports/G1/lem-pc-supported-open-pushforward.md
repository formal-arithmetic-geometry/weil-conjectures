## Worker report

The module `lean/Sheaf/AlgebraicGeometry/SupportedOpenPushforward.lean` states
`AlgebraicGeometry.RingedSpace.supported_open_pushforward`, with proof `sorry`.
The original node's statement and proof are unchanged. Two missing definition nodes supply
perfectness on arbitrary ringed spaces and concrete canonical derived open-inclusion maps.
No theorem is proved. The only other sorry is the named well-definedness theorem
`derivedOpenExtensionByZero_unit_isIso` in the canonical-maps definition module; its docstring
contains its source and complete stalkwise/termwise proof. All definition data is written in full.

Hypothesis and conclusion correspondence:

- A ringed space `(X,O_X)` is `X : RingedSpace.{uSO}`; the shared structure sheaf carrier is
  `moduleRings X`, with `SheafOfModules.{uSO}`. Commutativity agrees with the project's
  definition of ringed space. No scheme, local-ring, Noetherian or quasi-compact hypothesis occurs.
- The open immersion of ringed spaces is represented by `U : Opens X` with its induced ring
  sheaf `(moduleRings X).over U`. This is the localized open site, equivalent to the opens of
  the open subspace with its restricted sheaf. Every ringed open immersion identifies its domain
  with this induced ringed open subspace; this chooses that presentation, not a special case.
- `T : Set X`, `hT : IsClosed T`, and `hTU : T ⊆ (U : Set X)` are exactly the closedness
  and containment hypotheses. `⟨Tᶜ, hT.isOpen_compl⟩` is the complementary open V.
- The first and third clauses quantify over `F : DerivedCategory (SheafOfModules
  ((moduleRings X).over U))`, hence over D(O_U). The second quantifies over the corresponding
  category on X. The `HasDerivedCategory` binders choose localizations and their Hom universe;
  they are size infrastructure, not a boundedness or geometric assumption. Every open has its
  localization in the same chosen universe. All universes and variables are explicitly bound.
- Every cohomology sheaf is supported on T: `∀ n : ℤ, IsZero (...)`, using
  `DerivedCategory.homologyFunctor ... n`. For E the ordinary `overFunctor` restricts the
  cohomology sheaf to V. For F the ordinary `overMap` along `U ⊓ V ≤ U` restricts its cohomology
  sheaf to U minus T. These are sheaves of modules, so `IsZero` is the intended vanishing,
  not `IsZero` of a bare type, nor vanishing only of sections or of selected degrees.
- F perfect is `RingedSpace.IsPerfectOnOpen X U F`: each point of U has a smaller open V,
  a bounded complex of finite-free summands on V, and a derived isomorphism with F|V.
  There is no uniform global bound or uniform rank.
- First conclusion: `RingedSpace.IsPerfect X ((derivedOpenDirectImage X U).obj F)` says
  exactly that Rj_*F is perfect on X. `derivedOpenDirectImage` is the right derived functor
  of Mathlib's open-site pushforward, whose sections on V are F(V intersection U).
- Second conclusion: `IsIso ((derivedOpenDirectImageAdjunction X U).unit.app E)` is
  invertibility of the actual canonical map E to Rj_*(E|U). The adjunction is constructed
  by the upstream `mapDerivedCategoryRightDerivedAdjunction`, not supplied as an unconstrained
  hypothesis or replaced by existence of an arbitrary isomorphism.
- Third conclusion: `IsIso (derivedOpenExtensionByZeroToDirectImage X U F)` states
  invertibility of the specified canonical comparison j_!F to Rj_*F. Its definition takes
  the inverse of the extension/restriction unit and applies the restriction/direct-image
  adjunction's Hom equivalence. It uses the shared `Classical.choice
  (derived_open_shriek_adjunction X U)` for the extension-by-zero adjunction, as prescribed by
  the project. The theorem retains the perfectness hypothesis on this clause to render
  the node's literal “every such F”. Stacks 08DF(2), and the node's proof, give the stronger
  fact for arbitrary supported F, but no extra conclusion is added here.

Dependencies read and used:

- `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage`:
  `RingedSpace.derivedModuleDirectImage`, `moduleDirectImage`, `moduleGrothendieckAbelian`.
  The recorded direct-image construction is module pushforward followed by
  `Functor.rightDerivedFunctor`. The new open-site specialization uses exactly these
  existing constructions, with `SheafOfModules.pushforwardOver` and
  `SheafOfModules.overPushforwardOverAdj`; it does not redefine K-injective resolutions.
- `Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact`:
  `AlgebraicGeometry.open_restriction_adjunction_exact`, supplying exactness/additivity
  of extension by zero and its adjunction with restriction.
- `Sheaf.Algebra.Homology.DerivedOpenShriekAdjunction`:
  `AlgebraicGeometry.derived_open_shriek_adjunction`, chosen for the shared derived adjunction.
- `Sheaf.Paper.DerivedHomMayerVietoris`: `moduleRings`,
  `moduleOverFunctor_additive`, `moduleOverFunctor_limits`, `moduleOverFunctor_colimits`,
  and the analogous `moduleOverMap` instances. These shared instances are reused, not restated.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`:
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions`, applied to
  the small localized site and `X.sheaf.over U`. The new instance projects its Grothendieck
  structure, enabling the existing K-injective-resolution instance.
- Upstream `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`:
  `CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction`; its full signature
  and docstring were read. Mathlib's `overPushforwardOverAdj`, `pushforwardOver`,
  `overFunctor`, `overMap`, `DerivedCategory`, `HasDerivedCategory`, `homologyFunctor`,
  `SheafOfModules.free`, and `RingedSpace` are used directly.
- The original dependencies `def-pc-derived-category`, `def-pc-perfect-complex`, and
  `def-pc-derived-direct-image` record `schemeDerivedCategory`, `Scheme.IsPerfect`, and
  `schemeDerivedDirectImage`. Their full source declarations/docstrings were read.
  They take schemes, so cannot be instantiated with arbitrary ringed spaces. Their nodes
  are kept unchanged: the statement here does not specialize X to a scheme or change the
  meanings of those scheme nodes. The general category is already Mathlib `DerivedCategory`;
  only the missing general perfect predicate and the localized canonical maps are added.

Edge cases checked before writing:

- T empty forces every cohomology sheaf to vanish everywhere; all asserted maps are between
  zero derived objects. Perfectness includes the zero complex, with zero free rank in each degree.
- U empty forces T empty. Perfectness on U is vacuous pointwise, correctly for the empty
  module site; its derived direct image is zero and the E clause applies precisely to zero E.
- X empty is covered by the same definitions. Neither `Nonempty X` nor a nonempty cover is imposed.
- U = top: restriction is the localized-site equivalence, all maps are the identity under the
  induced adjunction identifications, and perfection is unchanged.
- T = X is allowed only when U = top. This correctly allows all complexes in the second clause.
- Unbounded E is allowed in the second clause; F has only local finite bounds, which may
  vary across a non-quasi-compact space. No quasi-coherence or scheme hypotheses are introduced.
- The hypothesis T closed in X is necessary: a closed-in-U support accumulating at the boundary
  need not satisfy the assertions. The theorem uses ambient closedness, not closedness only in U.

Searches (run using the mandatory msearch wrapper; exact queries and digests in searches.jsonl):

- LeanFinder: “perfect complex supported on closed subset open immersion derived pushforward”:
  8 hits about cohomological t-structure bounds, no supported open perfect-pushforward theorem.
- Loogle: `DerivedCategory, SheafOfModules`: generic derived/sheaf signatures, no exact statement.
- LeanSearch: “perfect complexes of sheaves of modules on a ringed space” and
  “canonical map extension by zero to derived pushforward open immersion”: both unavailable,
  returning Internal Server Error; no successful result is claimed.
- LeanFinder: “perfect derived object ringed space locally bounded finite free direct summand
  complex”: 8 hits about representatives of t-structure-bounded objects, no ringed perfect predicate.
- Grep: `IsPerfect|StrictlyPerfect` in Mathlib/Algebra: zero hits. The whole-Mathlib search with
  `IsPerfect|StrictlyPerfect|overPushforwardOverAdj|mapDerivedCategoryRightDerivedAdjunction`
  returned mostly unrelated perfect-field and perfect-pairing material. Mathlib's open adjunction
  was then found and read directly. Loogle `SheafOfModules.overPushforwardOverAdj`: one exact hit.
- LeanFinder: “extension by zero restriction adjunction unit is isomorphism”: 8 hits, all module
  change-of-ring adjunctions, none defining the desired open-inclusion canonical comparison.
- Grep: `extensionByZero.*(unit|comparison|adjunction)|overPushforwardOverAdj.*counit`:
  zero Mathlib hits.
- `rg` of WeilConjectures for this item's id and `supported.*Perfect|Perfect.*Pushforward`
  found no matching O-module theorem (only unrelated etale material).
- `rg` of both upstream and lean/Sheaf for `IsPerfectOnOpen|RingedSpace.IsPerfect|
  derivedOpenDirectImage|derivedOpenExtensionByZeroToDirectImage`, including the upstream name
  index, found no existing declarations. The existing `Scheme.IsPerfect` is scheme-only;
  upstream `DerivedCategory.IsPerfect` concerns modules over a single ring.
- DAG grep and `tools/blueprint_refs.py search 'perfect ringed space'` (0 blueprint nodes),
  and `search 'extension zero derived direct image'` (0 blueprint nodes), found no node carrying
  either missing definition. Broad DAG matches were existing scheme statements and this item.

Sources were opened directly at https://stacks.math.columbia.edu/tag/08DP,
https://stacks.math.columbia.edu/tag/08DF and https://stacks.math.columbia.edu/tag/08CM,
since the local literature/stacks-project/cohomology.tex is absent on this machine.
08DP has arbitrary ringed spaces and ambient-closed supported perfect objects; 08DF has
ambient-closed T contained in U and the two displayed canonical-map conclusions.
There is no statement correction and no disputed statement.

Server validation: all three modules compiled together cleanly in 10.2 seconds (exit code 0),
under the default server limit. Initial elaboration errors were repaired by explicit reuse of
restriction's additivity/exactness proofs, projecting the small localized site's Grothendieck
structure, and using the correct direction of `Adjunction.homEquiv`. No #check lines remain.

## New nodes

`def-pc-ringed-space-perfect-complex` supplies `RingedSpace.IsStrictlyPerfectOnOpen`,
`IsPerfectOnOpen`, and `IsPerfect`. Its statement gives precisely the local finite-free-summand
models for a general ringed space and its open subspaces (Stacks 08C4/08CM).
Searches above found no general existing declaration or node; `def-pc-perfect-complex` explicitly
supplies only the scheme specialization. The general predicate therefore does not overwrite or
silently widen that dependency. It uses the shared module carrier, localizations, restriction,
free modules, and all exactness instances.

`def-pc-derived-open-inclusion-maps` supplies the concrete open-site derived direct image,
its canonical restriction adjunction, the existing exact extension-by-zero functor and shared
adjunction, and the specified comparison j_!F to Rj_*F (Stacks 079V/08DF/08BT).
The only newly stated proof needed to define the comparison is
`derivedOpenExtensionByZero_unit_isIso`; its source and full proof are in its docstring.
The node includes this invertibility as the well-definedness fact used by the definition.
No arbitrary morphism or arbitrary right adjoint is a hypothesis of the item. Searches above
found Mathlib's underived adjunction and the existing upstream derived-adjunction construction,
which are reused, but no declaration packaging these canonical open-site operations for this
module carrier. The two infrastructure instances simply project/reuse existing proofs.

The dry-run preflight resolves the full ancestry path rather than the short stored via. Both
new nodes record its resolved path through perfect-generation-open-induction-step,
derived-qcoh-perfect-generation, smooth-proper-diagonal-tensor-formula,
smooth-proper-relative-dualizing-general, smooth-proper-curve-dualizing, and finite-duality-trace.

## Second reading by G1

I reread the node statement, its Stacks source places 08DP and 08DF, and all three
modules in this delivery. The introduced objects and hypotheses match as follows:

- `X : RingedSpace.{uSO}` and `U : Opens X` render the ringed space and its open
  immersion, with the localized ring sheaf `(moduleRings X).over U`; no scheme,
  separatedness, Noetherian, quasi-compact, or local-ring hypothesis is added.
- `T : Set X`, `hT : IsClosed T`, and `hTU : T ⊆ (U : Set X)` render the closed
  support and containment. The complement is exactly
  `⟨Tᶜ, hT.isOpen_compl⟩`, and the intersection restriction is through
  `overMap` along `U ⊓ ⟨Tᶜ, hT.isOpen_compl⟩ ≤ U`.
- The two explicit `HasDerivedCategory` binders provide the derived categories
  on `X` and every localized open. They are universe infrastructure and do not
  restrict the geometric objects.
- The first and third clauses quantify over
  `DerivedCategory (SheafOfModules ((moduleRings X).over U))`; the middle clause
  quantifies over `DerivedCategory (SheafOfModules (moduleRings X))`.
  `DerivedCategory.homologyFunctor` followed by `overMap` (first/third) or
  `overFunctor` (middle) states vanishing of every cohomology sheaf on
  `U ∩ (X \ T)` or `X \ T`, exactly the node's support condition.
- `IsPerfectOnOpen X U F` is the local bounded finite-free-summand predicate
  from `RingedSpacePerfectComplex`; `IsPerfect X (...)` is the corresponding
  local predicate on `X`.
- `derivedOpenDirectImage X U` is the right derived open-site pushforward, and
  `derivedOpenDirectImageAdjunction X U` supplies the canonical restriction/
  pushforward unit. Thus the first conclusion is perfectness of `Rj_* F`, and
  the second is `IsIso` of the canonical `E → Rj_*(E|U)`.
- `derivedOpenExtensionByZeroToDirectImage X U F` is the specified canonical
  `j_!F → Rj_*F`; the final clause asserts its invertibility for every F with
  exactly the node's perfectness and support hypotheses.

No mismatch was found and no source or statement correction was needed. In
particular, no stronger global boundedness or uniform rank is hidden in
`IsPerfectOnOpen`, and the final perfectness hypothesis is retained verbatim.
The empty set T, empty U (forcing T empty), empty X, U = top, T = X when
allowed, zero complexes, unbounded E, and varying local bounds on noncompact
spaces are all covered by the definitions and binders. Characteristic is
unrestricted and all universes are explicit.

The worker's searches were independently checked in `searches.jsonl`: the
LeanFinder/Loogle/LeanSearch queries found no existing supported-perfect
pushforward statement; grep over Mathlib, `WeilConjectures`, and `lean/Sheaf`
found no `IsPerfectOnOpen`, general `RingedSpace.IsPerfect`, or canonical
open derived maps. The existing scheme-only `Scheme.IsPerfect` is a different
notion. The new definition nodes therefore are justified and their modules
use the recorded source notions rather than private replacements.

I recompiled all three delivery modules together with `scompile.py`; compilation
completed cleanly with no errors or warnings. No repairs were necessary in this
second reading.
