## Worker report

The new module `Sheaf.Algebra.Homology.RingedSiteTorFlatModel` states
`SheafOfModules.torAmplitude_iff_exists_bounded_flat_model`, with `sorry` as its entire proof.
It formalizes Stacks Project, Cohomology on Sites, Tag 08G1, equivalence (1)-(2).
I read the source's statement and proof at `lemma-tor-amplitude` and the preceding
`lemma-last-one-flat`. The six-step DAG proof is included in the theorem docstring.
No definition or auxiliary theorem is introduced.

Hypotheses and clauses, in order:

- An arbitrary small site is `{C : Type u} [Category.{v} C] (J : GrothendieckTopology C)`.
  The object and morphism universes are independent. The chosen universe for coefficients
  and module carriers is `max u v`, so the site is small relative to it.
- A sheaf of commutative rings is `(R : Sheaf J CommRingCat.{max u v})`. Its underlying
  ring sheaf is `(sheafCompose J (forget₂ CommRingCat RingCat)).obj R`, with both coefficient
  universes explicitly specified in the file. This is arbitrary R, without constancy.
- The module category is Mathlib's `SheafOfModules` of this ring sheaf, exactly the
  transparent abbreviation `CategoryTheory.ringedSiteModules` in the dependency module.
  `HasSheafify` and `WEqualsLocallyBijective` provide its standard abelian structure;
  these are the sheafification infrastructure available on any site small in the chosen
  universe, not a geometric restriction or an enough-points hypothesis.
- `[HasDerivedCategory.{w} ...]` chooses the morphism universe of the unbounded derived
  category. `K : DerivedCategory ...` is an arbitrary object, without boundedness assumed.
- `(a b : ℤ) (_hab : a ≤ b)` gives the exact interval and its ordering hypothesis.
- Condition (1) is the left side of `↔`: `∀ (M : SheafOfModules ...) (i : ℤ)` quantifies
  over every module sheaf and degree. `DerivedCategory.singleFunctor _ 0` places M in
  degree zero. `(wfSiteDerivedTensor J R).obj (K, ...)` is the established K-flat
  derived tensor; `DerivedCategory.homologyFunctor _ i` is the recorded cohomology-sheaf
  functor. `i < a ∨ b < i → IsZero ...` says exactly that cohomology vanishes outside
  the closed interval. It imposes no condition on the cohomology inside the interval.
- Condition (2) is the right side: `∃ P : CochainComplex (SheafOfModules ...) ℤ`.
  `∀ i : ℤ, IsFlatOnSite (R := R) (P.X i)` imposes exactness of tensor by every term,
  using the recorded definition. Its site arguments `(C := C) (J := J)` are explicit
  to avoid early universe inference at this dependent sheaf-coefficient expression. `∀ i : ℤ, i < a ∨ b < i → IsZero (P.X i)` is the
  categorical assertion that every term outside the interval is zero. Finally,
  `Nonempty (K ≅ DerivedCategory.Q.obj P)` asserts existence of the specified
  derived isomorphism. No chosen chain map or stronger representative data is required.
- The final sentence of the node is honored: there are no constructibility, enough-points,
  constant-coefficient, scheme, or finiteness hypotheses.

Dependency declarations read and used:

- `def-weil-size-convention`: metatheoretic convention, no Lean declaration; rendered by
  explicit universes u, v, w as described above.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  transparent abbreviation of the Mathlib module category used throughout the signature.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, and `DerivedCategory.singleFunctor`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`,
  `DerivedCategory.homologyFunctor`: cohomology sheaves, as in the dependency's Mathlib match.
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`,
  `SheafOfModules.wf_site_derived_tensor_descent`: K-flat localization and tensor descent.
- `Mathlib.Algebra.Homology.HomologicalComplex`, `CochainComplex`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`, `SheafOfModules.IsFlatOnSite`:
  exactness of the sheafified sectionwise tensor functor, not sectionwise flatness.
- `Sheaf.Paper.WeilTensorProduct`, `SheafOfModules.wfSiteDerivedTensor`: the already
  defined choice of the bifunctor supplied by the descent theorem. Its full signature,
  defining expression, and docstring were also read from the current source through
  `scompile.py --source`. This uses the existing generic helper rather than defining
  another tensor. Added its already landed owning node `def-wf-tensor-product` to
  `stmt_deps` under the standing permission to add landed nodes. A traversal of the
  dependency closure found no path back to this item.

All recorded proof-dependency modules are imported without `public` unless already
needed in the public statement. The standard t-structure dependency is the Mathlib
match `DerivedCategory.TStructure`, represented by its `TStructure` module. The
bound-preserving replacement and flat-opcycles criterion are proof imports; no
extra hypotheses from their existing signatures are imposed on this statement.

Edge cases checked against the source and the signature:

- `a = b` allows a single nonzero flat term and all integer singleton intervals.
- The zero object and zero ring are included; tensor and all asserted vanishing remain valid.
- The empty site is permitted, with its zero module category; no object or point is chosen.
- A one-object ringed site recovers the usual ring-theoretic finite-Tor/flat-model criterion.
- Over the integers, the module Z/2 in degree zero does not satisfy the condition in [0,0];
  a two-term flat resolution fits [-1,0]. Thus flatness is not confused with the mere
  cohomological support of K or of its individual cohomology sheaves.
- Unequal site object and morphism universes remain unequal; the maximum only fixes the
  chosen universe in which this small site, coefficients and module sheaves are considered.

Searches before writing:

- `msearch.py leanfinder`, query “Finite Tor amplitude for a complex of sheaves on a ringed
  site is equivalent to a flat complex supported in the same interval”: eight hits on
  `DerivedCategory.isGE_Q_obj_iff`, `isLE_Q_obj_iff`,
  `exists_iso_Q_obj_of_isGE_of_isLE` and related cohomological bounds; none asserts flatness.
- `msearch.py loogle`, query `IsFlatOnSite, DerivedCategory.homologyFunctor`: zero hits,
  unknown project identifier `IsFlatOnSite`; not an exact match.
- `msearch.py leansearch`, query “A complex of module sheaves on an arbitrary ringed site
  has Tor amplitude in a fixed interval if and only if it has a flat representative
  supported in that interval”: eight hits, including `SheafOfModules`, its limit APIs,
  and ordinary `Module.Flat` tensor criteria; no ringed-site derived statement.
- `msearch.py grep`, query `torAmplitudeIn_iff_exists|flat_model|flat.*representative`
  in `Algebra/Homology`: zero hits.
- `rg` in Mathlib, project source and `lean/Sheaf` for Tor/flat models and names: found
  the general categorical theorem `DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat`
  in `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`, and its étale and pro-étale
  specializations. I read the general theorem and its surrounding hypotheses: it requires
  supplied closed monoidal and functorial flat resolution structures and uses that derived
  monoidal tensor. It does not itself provide the arbitrary-ringed-site specialization using
  the existing K-flat descent tensor and `IsFlatOnSite`. The étale/pro-étale specializations
  also fix a geometric site and constant coefficients. None is an exact statement match.
- `rg` for this blueprint id in the source tree: no hits. `rg` for the new declaration name
  across Mathlib, the source and `lean/Sheaf`: no hits. The existing
  `SitePerfectTorWindow` theorem concerns locally perfect inputs and local finite-projective
  models, a different statement, but confirms the established generic tensor API to use.

No statement correction, disputed statement, new definition node, or dependency repair.

## Second reading by Q03

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
