## Worker report

Item: lem-sfb-ringed-site-global-rhom-derived-limits. Group Q32, stage 2,
2026-10-24. The module is
`Sheaf.Algebra.Homology.RingedSiteGlobalRHomDerivedLimits`; its main statement is
`CategoryTheory.RingedSiteGlobalRHom.preserves_derived_limits`. The one theorem
has proof `sorry`. All eleven declarations, including the transparent construction
helpers, are listed in `lean.declarations`. There is no new definition node and
no dependency-record repair.

Sources read: sites-cohomology.tex, section-global-RHom (Tag 0B6E), starting
at line 9235, and spaces-perfect.tex, lemma-pullback-and-limits (Tag 0D3F),
statement and proof at lines 6270–6330. The former defines RΓ of internal RHom
in the derived category of the global ring and gives the cohomology identities;
the latter explicitly invokes preservation of products and derived limits.
The item's six-step expanded proof is included in the declaration docstring,
with its K-flat, K-injective tower, strict Roos, naturality, and cohomology steps.
No correction to the statement was needed.

The theorem uses the resolution model specified in the node, rather than choosing
an arbitrary vertex of a triangulated Roos triangle. In detail:

- The small ringed site is `{C : Type c} [Category.{v} C]` with
  `J : GrothendieckTopology C`. Coefficient sections and module values have
  universe `max c v r`; `c`, `v`, and `r` remain separate. The two standard
  sheafification binders are the existing abelian-module infrastructure on
  a site small in that module universe. They hold for this small-site situation.
  The independent derived morphism sizes are `w` and `z`, with the usual
  `HasDerivedCategory` binders. They do not equate object and morphism sizes.
- The commutative ring sheaf is `R : Sheaf J CommRingCat.{max c v r}`.
  `Modules` is a transparent specialization of the recorded `ringedSiteModules`,
  hence of Mathlib `SheafOfModules`; there is no newly constructed category.
- The specified commutative ring and homomorphism are `(A : Type a) [CommRing A]`
  and `(φ : A →+* Scalars R)`. `Scalars` is exactly `RingCat.sectionsSubring`
  of the underlying ring presheaf: compatible families over all site objects,
  so no final object is assumed. The coefficient ring universe `a` is independent.
- `sections` is the existing linear covariant Hom functor at `SheafOfModules.unit`,
  followed by `ModuleCat.restrictScalars φ`. `modulesLinear` merely exposes the
  existing `SheafOfModules.homLinear` instance at the bundled-ring-sheaf interface;
  its data are that existing instance, with every universe supplied explicitly.
  Thus the A-action is postmultiplication by the specified global section φ(a).
- The displayed definition of global RHom is `globalHom R A φ E`: curry the
  recorded `derivedInternalHomOfUniverses J R`, fix `op E`, and compose with
  `(sections R A φ).rightDerivedFunctor`. This is full unbounded RΓ with its
  A-module values, not H⁰ and not a complex with forgotten coefficients.
  Its Grothendieck structure is the existing named resolutions theorem; no
  instance is chosen from a bare `Nonempty` or unspecified existence assertion.
- `E : DerivedCategory (Modules R)` is arbitrary. `L` and
  `eL : DerivedCategory.Q.obj L ≅ E` specify a representative for the explicit
  chain model. Every E has such a representative; there is no boundedness or
  flatness hypothesis on L. The theorem quantifies over every such choice.
- A strict tower is a complex in `ℕᵒᵖ ⥤ Modules R`. Index `n : ℕ` means the
  source's positive index n+1; transitions use `(homOfLE (Nat.le_succ n)).op`.
  `resolvedProperty` is the subcategory of K-injective complexes of towers with
  injective tower terms. The first conjunct supplies a quasi-isomorphism from
  EVERY strict tower X to such an I. It does not assume the original tower is
  injective, split, surjective, or quasi-coherent.
- The natural representative comparison `β` identifies `Q(Γ Hom(L,I))` with
  global RHom on every K-injective complex I. Its first equation is naturality
  for every chain map between such representatives. Consequently the tower
  `representativeTowers` represents the stated RHom tower, transitions included.
- The source of the natural isomorphism `α` is `limitGlobalHom`: the actual
  ordinary limit of a resolved tower, localized and then sent through global
  RHom. The target `globalHomLimit` is the localization of the actual ordinary
  limit of the strict tower `representativeTowers`. These are the respective
  resolution models of the two derived inverse limits in the displayed formula.
- The normalization conjunct asserts that `limit I.obj.asFunctor` is K-injective
  and pins `α.hom.app I` to `β(lim I).inv ≫ Q.map (limit.post ...)`.
  `limit.post` is Mathlib's canonical compatible-family map, fixed by its
  projection equations. Thus α is tied to the limit comparison, rather than
  merely asserting the objects are isomorphic.
- The next conjunct supplies the SOURCE Roos triangle using the recorded
  `IsDerivedLimitTriangle`; its p has n-th projection exactly
  `Q.map (limit.π I.obj.asFunctor (op n))`.
- The projection compatibility conjunct states that α followed by the n-th
  target limit projection and β is exactly RHom applied to the source's
  n-th limit projection. This is the requested compatibility with the
  resolution-derived limiting cone.
- The TARGET Roos-triangle conjunct uses `IsDerivedLimitTriangle` on the actual
  transition maps of `representativeTowers`, with p's components exactly the
  localized ordinary limit projections. It identifies the target ordinary
  limiting complex as a derived limit. Countable products are taken in D(A),
  with the usual `1-s` sign fixed by the recorded derived-limit definition.
  No exactness of products of arbitrary module SHEAVES is assumed.
- α is a `NatIso` between the two displayed functors on resolved strict towers,
  so its naturality quantifies over all strictly commuting tower maps. Maps of
  original strict towers are resolved in the homotopy category of K-injectives;
  the functors here kill homotopies after Q, and quasi-isomorphisms between these
  representatives are homotopy equivalences. This is precisely the chosen
  resolution presentation of naturality for original strict towers. In
  particular changing a tower resolution transports the same comparison.
- The final existential gives additive equivalences e for EVERY
  `N : DerivedCategory (Modules R)` and EVERY `q : ℤ`, between
  `H^q ((globalHom E).obj N)` and `(E ⟶ N⟦q⟧)`.
  The subsequent equation is naturality in N for every derived map f. The
  last equation explicitly respects scalars, `e (b • x) = φ(b) • e(x)`,
  using the induced global-section action on derived morphisms.
- There is no quasi-coherence predicate, no boundedness predicate and no
  finite-generation assumption anywhere in the statement or its models.

Dependency declarations read and used:

- def-weil-size-convention is metatheoretic; it supplies no declaration. The
  explicit universes and derived-size binders implement it.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`,
  and Mathlib `SheafOfModules`, its linear morphisms and its abelian instance.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom` publicly retains
  the general-site declarations of `DerivedInternalHomOfUniverses`. The one
  used here is `CategoryTheory.derivedInternalHomOfUniverses`, whose full
  generic signature and localization/comparison docstrings were read. The
  primary ordinary-module abbreviation is not applied to sheaves.
- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`,
  `CategoryTheory.ringedSiteZerothHypercohomologyOfUniverses`. Its full
  definition is H⁰ of the unbounded right derived Hom-from-unit functor.
  The present `sections` uses that same Hom-from-unit construction with
  the already available global-ring action and explicit scalar restriction.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`,
  `CategoryTheory.IsDerivedLimitTriangle` and `IsDerivedLimit`: the latter
  chooses no functor, so actual limit functors on resolved towers provide
  the canonical choice here; the former states both normalized Roos triangles.
- Added landed statement dependencies: `def-pur-hom-complex`, through
  `WeilConjectures.Algebra.Homology.HomComplex`, `homComplexFunctor`, whose
  signature, product terms and differential were read; and
  `def-pur-sheaf-modules-hom-module`, through
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule`,
  `SheafOfModules.homModule` and `homLinear`, whose complete signatures and
  pointwise scalar-action docstrings were read. Neither record is changed.
- The proof imports the recorded sections-model, native tensor–Hom adjunction,
  native tensor, K-flat resolutions, Hom-into-K-injectives, injective-tower Roos,
  strict derived-tower limit, right-adjoint preservation of K-injectives,
  kernel-to-shifted-cone, strict Roos comparison, and Mathlib K-injective and
  bounded-below Hom-computation modules. The Mathlib functor-category import
  supplies the proof dependency on levelwise abelian towers.

Edge cases checked: empty site (compatible families and Hom-from-unit still
make sense); zero ring A and zero ring sheaf (the specified unital map is
retained); E=0; zero tower; constant tower and zero transition maps; arbitrary
unbounded L and I; q=0 and negative q; site objects and arrows in different
universes; coefficient ring A in another universe; arbitrary nonsurjective
original tower (only its resolution has split transitions). The tower index is
nonempty by definition and never replaced by a finite or empty set. The Hom
complex uses products over all integers, not finite sums.

Searches actually run with msearch.py, as Q32 and this item:

- LeanFinder: "Global derived Hom on a ringed site preserves derived inverse
  limits of strict towers with coefficients in a ring acting on global sections".
  Eight hits, including `SheafOfModules.createsLimit`, `SheafOfModules.hasLimit`,
  and module-presheaf limits; no global-RHom derived-limit comparison.
- LeanSearch: "Global derived Hom preserves countable derived inverse limits
  on ringed sites". Eight hits on ordinary sheaf-module limits and
  `HasDerivedCategory.standard`; no exact statement.
- Loogle: "CategoryTheory.linearCoyoneda, SheafOfModules.sections,
  CategoryTheory.Functor.rightDerivedFunctor". Zero hits, with the explicit
  unknown-identifier diagnostic for the last identifier; this query is not
  recorded as evidence that right derived functors are absent.
- Follow-up Loogle: "CategoryTheory.linearCoyoneda". Eleven hits; read
  Linear/Yoneda.lean and reused linearCoyoneda and its additive instance.
- msearch grep: `global.*[Hh]om.*[Ll]imit|linearCoyoneda|sectionsSubring`
  in Mathlib CategoryTheory. Five hits in Linear/Yoneda.lean, reused.
- rg in the specified source repository `lean/WeilConjectures`: searched
  global sections, Hom modules, RHom and limits; found the exact existing
  `SheafOfModules.homLinear` action and right-derived functor infrastructure;
  no global ringed-site RHom/tower comparison. Searching the item id found
  no upstream declaration. The upstream name index and source directories
  contain no declaration in the new `RingedSiteGlobalRHom` namespace.
- rg in `lean/Sheaf`: found `DerivedInternalHomSectionsModel` and specialized
  global sections in `RingedSiteGlobalDerivedAdjunction` on bundled tensor
  corners, and specialized adic/closed-support global Homs. None states
  this theorem. The generic sections helper is only the composite of existing
  linearCoyoneda and scalar restriction; no second internal Hom, scalar
  action, K-injective replacement or limit construction is introduced.

All compilation, including helper probes, used the prescribed scompile.py
wrapper. The final module compiles with no errors and no non-sorry warnings.

## Second reading by Q32

A second pass by the same dispatcher-started worker reread the node statement,
both source passages, and the final file; no other agent was started. The
maintainer's independent review follows delivery.

The initial elaboration failed to infer universe parameters hidden in
`max c v r`, and a generic helper initially tried to put Hom sets in universe r
rather than `max c r`. The helper now has a plain coefficient-universe parameter,
explicit site and module universes, the appropriate sheaf-compose interface,
and the correct Hom-set universe. At the theorem the helper is specialized to
`max c v r`. No equality between site universes was imposed.

The second content pass checked that `sections` retains the specified map φ,
that `globalHom` ends in D(A), and that the cohomology identities include both
negative degrees and the scalar equation. It found that the first draft's
projection equations alone did not explicitly expose the chain-level
normalization. The final statement adds the equation using the actual
`limit.post` comparison and the source Roos triangle with its projections.
Both source and target limits are consequently tied to actual limiting cones.
The comparison is a natural isomorphism of resolved STRICT tower functors,
not a choice of unrelated isomorphisms on the tower's levels. Arbitrary original
towers are covered by the initial resolution-existence conjunct, and no
quasi-coherence or exact-sheaf-products assumption slipped into the theorem.
The representative L has no K-flatness assumption; K-flat replacement belongs
only to the proof, as required by the node.
