## Worker report

The module `lean/Sheaf/AlgebraicGeometry/CoherentPseudoCoherent.lean` states
`AlgebraicGeometry.Scheme.isPseudoCoherent_singleFunctor_obj_of_isCoherent`.
Its proof is `sorry`, as required in stage 2. No definitions, dependency modules,
new nodes, or statement corrections are needed. Only the item's `lean` field changes.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- “Let Y be a Noetherian scheme”: `(Y : Scheme.{u}) [IsNoetherian Y]`.
  Mathlib's `AlgebraicGeometry.IsNoetherian` means locally Noetherian and
  quasi-compact; neither separatedness nor a base field is imposed.
- “F a coherent O_Y-module”: `(F : SheafOfModules.{u} (moduleRings Y.toRingedSpace))`
  and `(hF : RingedSpace.IsCoherent Y.toRingedSpace F)`. The recorded coherent
  predicate is finite type plus finite-type kernels of all finite-free maps on opens,
  rather than the source project's different quasi-coherent-plus-finite-presentation predicate.
- “Viewed as a complex concentrated in degree zero”:
  `(DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj F`.
  Mathlib defines this as the image of the single cochain complex in the derived category;
  `DerivedCategory.Q_obj_single_obj` explicitly identifies these objects.
- “Is pseudo-coherent over O_Y in the sense of def-pur-pseudo-coherent-complex”:
  `Y.IsPseudoCoherent` applied to that degree-zero object, using the dependency's exact
  recorded predicate. It quantifies over every point, an open neighbourhood, and a
  bounded-above complex of finite free modules isomorphic to the restricted object in D.
- The `HasDerivedCategory.{w}` binders on Y and every open U are the localization
  infrastructure already required by `Scheme.IsPseudoCoherent`; they do not impose a
  geometric assumption. They use the same `SheafOfModules` abelian category and universe
  throughout, without choosing a competing abelian instance. All universes are explicit.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`. Read their full definitions
  and docstrings in the pinned Mathlib. The scheme module is imported transitively.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.Coherent`, declaration
  `AlgebraicGeometry.RingedSpace.IsCoherent`; directly imported.
- `def-pur-pseudo-coherent-complex`: `Sheaf.AlgebraicGeometry.PseudoCoherentComplex`,
  declaration `AlgebraicGeometry.Scheme.IsPseudoCoherent`; directly imported.
- Mathlib `AlgebraicGeometry.IsNoetherian` from `Mathlib.AlgebraicGeometry.Noetherian`,
  directly imported; Mathlib `DerivedCategory.singleFunctor` from
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, imported transitively.

Source check: the local Stacks checkout is absent on this machine, so I opened
https://stacks.math.columbia.edu/tag/08E8 . Its characterization on a Noetherian scheme
identifies pseudo-coherent objects with bounded-above objects having coherent cohomology.
The degree-zero coherent module is the stated special case. The node's proof is rendered
in the theorem docstring: use `lem-sc-coherent-affine-free-resolution` at each point,
then the defining local condition of `def-pur-pseudo-coherent-complex`.

Edge cases checked before writing: the empty scheme gives a vacuous local condition and
is not excluded; the zero coherent module has the zero finite-free resolution; finite
ranks may be zero and may vary with degree and neighbourhood; the bounded-above resolution
need not be bounded below, so no regularity or perfection assumption is smuggled in.
Non-affine and non-separated Noetherian schemes are included. No characteristic restriction,
nonempty-point hypothesis, positive-rank hypothesis, or additional quasi-coherence binder
is imposed. Arbitrary object universe u and derived hom universe w are explicit.

Searches for an existing theorem (2026-10-11):

- `msearch.py H1 lem-sc-coherent-pseudo-coherent leanfinder`
  query `coherent module on Noetherian scheme is pseudo-coherent complex`: eight hits,
  including `SheafOfModules.IsFiniteType`, `IsFinitePresentation`,
  `QuasicoherentData.IsFinitePresentation`, and the scheme module category's abelian
  instance; no coherent-to-pseudo-coherent theorem.
- `msearch.py ... loogle` query `SheafOfModules.IsFiniteType, PseudoCoherent`:
  zero hits; unknown identifier `PseudoCoherent`.
- `msearch.py ... grep` query `pseudo.?coherent|PseudoCoherent`, subdirectory
  `AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... leansearch` query
  `coherent module on Noetherian scheme is pseudo-coherent complex`:
  unavailable, Internal Server Error; no negative verdict inferred from unavailability.
- `rg -n 'pseudo.?coherent|PseudoCoherent|lem-sc-coherent-pseudo-coherent'`
  in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`: only an unrelated prose
  mention in `AlgebraicGeometry/Cohomology/DirectImage.lean`, not a declaration.
- `rg` in the project's `lean/Sheaf` for coherent/pseudo-coherent combinations:
  the existing scheme pseudo-coherent definition and separate ring pseudo-coherent
  modules, but no theorem for a coherent scheme module in degree zero.
- Exact candidate-name `rg` in Mathlib, WeilConjectures, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no existing
  `isPseudoCoherent_singleFunctor_obj_of_isCoherent` declaration.

No STATEMENT-DISPUTED or node fault found.

## Second reading by H1

I independently read the item's node, its source place, its three statement
 dependency nodes and their actual Lean declarations, and the delivered module.
The local Stacks checkout is absent. I read the TeX source at
https://raw.githubusercontent.com/stacks/stacks-project/master/perfect.tex,
including its Conventions section and `lemma-identify-pseudo-coherent-noetherian`,
and checked the tag page https://stacks.math.columbia.edu/tag/08E8.
The conventions identify a module with its degree-zero complex. Tag 08E8 concerns
Noetherian schemes and objects with quasi-coherent cohomology; in this special
case coherence implies quasi-coherence (01XZ), and the single complex has only
one possibly nonzero cohomology sheaf. Thus no separate quasi-coherence
hypothesis must be added to this node. There is no standing separatedness,
regularity, field, or characteristic assumption in the source section.

Object, hypothesis and conclusion checklist, recorded before the comparison:

- Object: a scheme Y. Lean: `(Y : Scheme.{u})`. Verdict: exact. I read
  `Scheme` and `Scheme.Hom` in Mathlib/AlgebraicGeometry/Scheme.lean: the scheme
  is locally ringed and locally affine, without extra geometric structure.
- Hypothesis: Y is Noetherian. Lean: `[IsNoetherian Y]`. Verdict: exact.
  Mathlib/AlgebraicGeometry/Noetherian.lean defines this as locally Noetherian
  and compact, which is precisely the scheme hypothesis; no base is introduced.
- Object: an O_Y-module F. Lean:
  `(F : SheafOfModules.{u} (moduleRings Y.toRingedSpace))`. Verdict: exact.
  The same carrier is used in both recorded dependency declarations. I also
  read `moduleRings` in DerivedHomMayerVietoris and `schemeDerivedCategory`
  in DerivedCategory: these use the structure sheaf's ring sheaf and Mathlib's
  sheaf-of-modules abelian category, not a new module category.
- Hypothesis: F is coherent in pqf-def-coherent's sense. Lean:
  `(hF : RingedSpace.IsCoherent Y.toRingedSpace F)`. Verdict: exact. I unfolded
  the recorded Coherent.lean definition: finite type, and finite-type kernels
  for every finite-free map on every open. `SheafOfModules.IsFiniteType` was
  checked in Mathlib's Generators.lean. The source project's `Modules.isCoherent`
  instead says quasi-coherent plus finite presentation; it is not substituted.
- Construction: regard F as a complex concentrated in degree zero. Lean:
  `(DerivedCategory.singleFunctor (SheafOfModules.{u}
  (moduleRings Y.toRingedSpace)) 0).obj F`. Verdict: exact. I read
  `singleFunctors`, `singleFunctor`, and `Q_obj_single_obj` in Mathlib's
  DerivedCategory/Basic.lean, which identify this with localization of the
  single cochain complex at integer degree zero.
- Conclusion: that object is pseudo-coherent, with def-pur-pseudo-coherent-complex's
  definition. Lean: `Y.IsPseudoCoherent` of the preceding object. Verdict:
  exact. I read PseudoCoherentComplex.lean: for each point, some open containing
  it and some integer-indexed complex, bounded above with finite-free terms,
  whose localization is isomorphic to the derived restriction. Neighbourhood,
  upper bound and degreewise rank have precisely the local quantifier order.
- Infrastructure binders: `HasDerivedCategory.{w}` for Y and for all its opens
  are exactly those of the recorded pseudo-coherent predicate. Verdict:
  these supply localization models with the shared Mathlib abelian instance;
  they introduce no geometric or finiteness assumption, and do not select a
  competing abelian structure. Both u and w are explicitly bound.

Edge cases: the empty scheme has no points and the defining local condition
is vacuous. F = 0 is included, using rank-zero terms of the zero complex.
There is no nonempty index type or positive rank requirement: `Fin 0` is
allowed in the dependency definition. Degree zero is the integer 0, not a
positive-degree condition; the resolution can extend indefinitely to negative
degrees. Non-affine and non-separated schemes, all characteristics and
arbitrary scheme universe u are covered. No finite projective dimension,
regularity or bounded-below hypothesis appears. The module universe is the
same as in both dependency definitions, so no case of those nodes is lost.

Independent searches (different queries from the first worker):

- `msearch.py H1 lem-sc-coherent-pseudo-coherent leanfinder`
  with `finite locally free resolution coherent sheaf degree zero derived category`:
  eight results, including abstract projective resolutions, finite type and
  finite-presentation sheaf predicates; no matching coherent-to-pseudo-coherent
  theorem for schemes.
- `msearch.py ... loogle` with `DerivedCategory.singleFunctor, SheafOfModules`:
  zero results.
- `msearch.py ... leansearch` with
  `coherent sheaf has locally bounded above finite free resolution`:
  unavailable (Internal Server Error); no absence conclusion inferred.
- `rg` for `PseudoCoherent|pseudo.coherent|finite.free.resolution` across
  the pinned Mathlib/AlgebraicGeometry, WeilConjectures, and project lean/Sheaf:
  only the scheme predicate, ring-level pseudo-coherence and module resolutions,
  and an upstream prose mention in Cohomology/DirectImage.lean. No duplicate
  theorem. I opened upstream AlgebraicGeometry/Modules/Coherent.lean as well.
- Exact declaration-name search across Mathlib, WeilConjectures, lean/Sheaf,
  and dag/lean_names_upstream.json: no existing declaration with this name.

No new definition nodes, dependency modules or statement corrections were
supplied or needed. All three recorded statement dependencies are usable.
The proof docstring reproduces the node's local affine-resolution step and
its conclusion via the pseudo-coherent definition. The only theorem has a
`by sorry` proof; no definition or extra proof is introduced. Source tags,
blueprint tags, namespace, topic, imports and line widths satisfy H5-H9.
I checked that the node's `lean.statement` equals the file's signature verbatim.

Mismatches found: none. Changes: appended this independent second reading;
left the correct Lean module and node record unchanged. The required server
single-file compile completed successfully in 2.2 seconds with no warnings.
