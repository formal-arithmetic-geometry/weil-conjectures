## Worker report

The module `Sheaf.AlgebraicGeometry.DerivedBasisIncreasingUnion` states
`AlgebraicGeometry.derived_basis_increasing_union`, with proof `sorry`, exactly for
the continuous ordinal gluing assertion in Stacks, Cohomology, Tag 0D6B,
`lemma-glueing-increasing-union` (cohomology.tex, lines 11343–11360).
The node statement and other DAG fields are unchanged except for its Lean record.
No new nodes or dependency repairs are needed.

The hypotheses and conclusions match as follows:

- The scheme is `(X : Scheme.{u})`, using the recorded Mathlib scheme notion.
- A set-sized ordinal is `(lambda : Ordinal.{v})`; `lambda.ToType : Type v`
  is its canonical small well-ordered representative (Ordinal.Basic, lines
  110–127). The index universe v is independent of the scheme universe u and
  of the localization morphism universe w. No nonemptiness is assumed.
- The open family is `W : lambda.ToType → X.Opens`. `hincreasing : Monotone W`
  gives exactly every inclusion W_beta ⊆ W_alpha for beta < alpha.
- The covering equation is `hcover : iSup W = ⊤`.
- Continuity is `hcontinuous`: for every `alpha`, `Order.IsSuccPrelimit alpha`
  implies `W alpha = ⨆ beta : {beta // beta < alpha}, W beta.val`.
  The predicate means that no element is immediately below alpha, so includes
  the minimum as well as nonzero limit indices. In particular its empty union
  forces W_0 to be empty whenever the index type is nonempty. This is the
  source's non-successor condition, with no continuity imposed at lambda itself.
- The local objects are `K alpha : DerivedCategory (SheafOfModules
  ((moduleRings X.toRingedSpace).over (W alpha)))`.
  This is the established localized-open-site encoding of D(O_(W_alpha)),
  also used by `derived_basis_local_hom_glue`. Mathlib's
  `Scheme.Modules.overEquiv` (Modules/Sheaf.lean:558) identifies module sheaves
  on this site with modules on `(W alpha).toScheme`. Its exact equivalence
  induces the same derived category. `overMapCompOverEquiv` (lines 566–600)
  and `overFunctorEquiv` (line 605 onward) identify both restriction functors
  with the actual open-subscheme restrictions. Thus the encoding changes
  neither objects, shifts, morphisms, nor the compatibility requirement.
- `hnegative` is `∀ alpha i, i < 0 → Subsingleton (K alpha ⟶ (K alpha)⟦i⟧)`.
  The Hom group has its zero morphism, so singleton means exactly vanishing.
  There is no boundedness, quasi-coherence, or uniform amplitude condition.
- `r beta alpha h` is an isomorphism from the exact derived restriction of
  K_alpha along W_beta ⊆ W_alpha to K_beta. Only strict pairs are supplied;
  no identity transition is added as data.
- `hcocycle` is equality of the homs for every gamma < beta < alpha.
  The inverse of `derivedModuleOpenMapCompIso` first identifies direct
  restriction to gamma with restriction to beta and then gamma; the next
  factors are restriction of r_beta^alpha and r_gamma^beta. Its right side
  is exactly r_gamma^alpha. Equality of homs is equality of isomorphisms.
- The result existentially supplies `L : schemeDerivedCategory X` and `rho`
  identifying its restriction on every W_alpha with K_alpha.
- The final equation uses the inverse of the existing
  `SheafOfModules.openRestrictionComparison`, followed by restricted rho_alpha
  and r_beta^alpha, and equates the composite to rho_beta. This is precisely
  the node's required r_beta^alpha ∘ (r_alpha restricted) = r_beta.

The `HasDerivedCategory.{w}` binders are the shared localization structures of
`def-pc-derived-category`, for the global and localized module categories.
They encode the categories being mentioned; they impose no extra geometric or
cohomological condition. All variables and universes are explicitly bound, and
`autoImplicit` is disabled.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  read with their docstrings and full structure signatures at lines 36–82.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory`, read through `scompile.py --source`
  because the older local source checkout lacks that file. The full source
  also documents the shared module carrier and the auxiliary QCoh property.
- Existing restrictions and exactness instances come through
  `WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris`;
  `SheafOfModules.overFunctor`, `overMap`, and `overFunctorMap` are from
  Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous (lines 58–87).
- `SheafOfModules.openRestrictionComparison`, read in the current source of
  `WeilConjectures.Algebra.Homology.OpenCoverAdjunctionTriangle`, is used in the
  conclusion. Its construction is the derived-composition comparison followed
  by the derived image of `overFunctorMap`.

The two helper definitions belong to the item's canonical restriction notation,
not independent notions. `moduleOpenMapCompIso` is constructed by the identity
map on every module of sections, lifted through the fully faithful forgetful
functor. `derivedModuleOpenMapCompIso` applies the existing exact-functor
localization comparisons to that explicit isomorphism. Both have real data;
neither uses a postponed theorem or a choice of an arbitrary comparison. Both
are recorded in `lean.declarations`. The theorem docstring gives all ten proof
steps of the node, including the corrected direction at the limit comparison
and the use of Hom uniqueness instead of circular object descent. The modules
of the stated proof dependencies are imported privately.

Edge cases checked before finalizing the statement:

- lambda = 0: no local data or equations are required; the cover forces X empty,
  and the zero global object supplies the assertion.
- lambda = 1: continuity at its unique minimum forces the only open, hence X,
  empty. There is no accidental assumption excluding this degenerate case.
- A nonzero limit: all earlier indices appear in the continuity supremum;
  the node's transfinite proof uses precisely that cover.
- A successor final lambda: no condition is imposed at the excluded endpoint;
  the final tail may have a last element, as allowed by the proof.
- Repeated opens, empty opens, zero objects, and the empty scheme: inclusions,
  comparison isomorphisms, and all equations remain defined without strict
  growth, nonzero objects, or nonempty intersections.

Searches actually run for this item:

- `msearch.py leanfinder`, query “Glue compatible derived category objects along
  a continuous increasing ordinal open cover with vanishing negative self
  extensions”: eight hits, headed by
  `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE` and boundedness/representative
  results; no gluing statement.
- `msearch.py leansearch`, query “Compatible objects of derived categories over
  increasing open subsets glue by transfinite recursion”: eight hits on ordinary
  ringed-space, topological, or sheaf gluing; no derived ordinal descent result.
- `msearch.py loogle`, query `"DerivedCategory", "glue"`: zero hits.
- `msearch.py grep`, regex
  `BBD|[Dd]erived.*[Gg]lu|[Gg]lu.*[Dd]erived|transfinite` in
  Mathlib/Algebra/Homology: zero hits.
- `rg` searched the upstream WeilConjectures tree and project `lean/Sheaf` for
  the exact node id and derived/increasing keyword combinations: no existing
  statement. A wider restriction/gluing search found the shared restriction
  interfaces and the distinct local-Hom theorem, which were read and reused.
- `rg` checked the proposed full declaration names in Mathlib/upstream/project
  sources and `dag/lean_names_upstream.json`: no collisions. Searching for
  overMap composition comparisons found `overFunctorMap` and the existing
  global comparison but no three-open local-object comparison.

Validation: the prescribed `scompile.py` compiled both the sandbox source and
its library-path form successfully, each within 60 seconds, with no errors or
warnings. An initial missing exactness-instance error in the helper construction
was repaired by explicit composition instances; the initial unqualified order
predicate was repaired to `Order.IsSuccPrelimit`. No statement correction or
STATEMENT-DISPUTED finding is needed.

## Second reading by NC

No second worker reading was performed: the dispatcher brief requires direct
worker delivery and the maintainer's independent review. After the clean compile,
I reread the complete node and signature, checking each hypothesis and clause as
listed above, especially continuity at zero and the directions of both inverse
restriction comparisons. This is a self-check, not an independent review.
