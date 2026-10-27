## Worker report

Item: lem-trf-algebra-module-simultaneous-generic-flatness.
Module: `Sheaf.RingTheory.AlgebraModuleSimultaneousGenericFlatness`.
Declaration: `Module.exists_nonzero_flat_localizationAway_algebra_module`.

The module states the node with a single `sorry`, and defines no new notions. The node is
unchanged except for its `lean` record. No new nodes or dependency repairs are necessary.

Source read: `literature/stacks-project/algebra.tex`, lines 28564–28634, Tag 051T,
`lemma-generic-flatness`, including its hypotheses and proof; and
`literature/stacks-project/more-morphisms.tex`, lines 6562–6625, Tag 0573,
`lemma-scheme-theoretically-dense-generic-fibre`, especially the third paragraph's simultaneous
flatness application. Tag 051T actually gives freeness over the localized base, hence the
node's two flatness assertions over the original base; no correction is needed.

Hypothesis and clause correspondence:

- The commutative integral domain A is `(A : Type u) [CommRing A] [IsDomain A]`.
- The commutative A-algebra B is `(B : Type v) [CommRing B] [Algebra A B]`; its structure
  map φ is precisely `algebraMap A B`. Finite type is `(hB : (algebraMap A B).FiniteType)`.
  Mathlib's `RingHom.FiniteType` is `Algebra.FiniteType` for that map's algebra structure.
- The finitely generated B-module M is `(M : Type w) [AddCommGroup M] [Module B M]
  [Module.Finite B M]`. There is no independent A-action to introduce or constrain.
- The common nonzero base element is `∃ a : A, a ≠ 0 ∧ ...`.
- The ring B_a is `Localization.Away (algebraMap A B a)`; the first conjunct is flatness
  of the exact composite `((algebraMap B (Localization.Away (algebraMap A B a))).comp
  (algebraMap A B)).Flat`. By the definition of `RingHom.Flat`, this is flatness of B_a
  as an A-module under the specified composite action.
- The module M_a is `LocalizedModule.Away (algebraMap A B a) M`; the second conjunct is
  `@Module.Flat A (LocalizedModule.Away (algebraMap A B a) M) _ _
  (Module.compHom _ (algebraMap A B))`. The B-action on this module multiplies fraction
  numerators; `Module.compHom` restricts it along A → B. This is the canonical restriction
  of the B_a-action along A → B → B_a: a scalar x sends m/s^e to φ(x)m/s^e.
- Both `Away` constructions use exactly `Submonoid.powers (algebraMap A B a)`; they do
  not invert an unrelated element of B.
- There is no Noetherianity, finite-presentation, injectivity or faithfulness assumption.
  Universes u, v, w are explicitly bound and independent. `autoImplicit` is disabled.

Dependency declarations read and used:

- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` and `Algebra.FiniteType`, supplying
  def-weil-pbc-finite-type-algebra. Read their full signatures and defining conditions.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, supplying
  def-weil-finitely-generated-module; its `fg_top` is finite generation, not `Finite M`.
  It is publicly available through `Mathlib.RingTheory.FiniteType`.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`; and
  `Mathlib.RingTheory.Flat.Basic`: `Module.Flat`, supplying def-weil-pbc-flat-ring-map.
  Read the full definitions, tensor injectivity characterization and `flat_algebraMap_iff`.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`, supplying
  def-weil-ring-localization-away; ring structure and canonical algebra map are provided
  by the public import `Mathlib.RingTheory.Localization.Away.Basic`.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule.Away`, supplying
  def-weil-pbc-module-localization-away. Read its abbreviation, fraction relation,
  `smul'_mk`, localized scalar action and scalar-tower compatibility.

The proof dependencies also have their stated imports: private imports of
`Mathlib.Algebra.TrivSqZeroExt.Basic` (`TrivSqZeroExt`, def-sc-trivial-square-zero-extension)
and `WeilConjectures.RingTheory.GenericFlatness`
(`RingHom.exists_nonzero_flat_localizationAway`, lem-sbc-finite-type-algebra-generic-flatness).
The remaining proof dependency is `Module.Flat.of_retract` in
`Mathlib.RingTheory.Flat.Basic`, already exposed through the public flatness import.
Its full signature was read. The theorem docstring includes all four recorded proof steps,
including the fraction-relation check that makes the retractions well-defined.

Edge cases checked mathematically before writing:

- `M = 0` is allowed; its localization is zero and flat, so the algebra-only conclusion remains.
- `B = 0` is allowed. Every unital B-module is zero, and both localizations are zero and flat;
  choose the nonzero element 1 of A. No `Nontrivial B` binder excludes this case.
- A noninjective structure map is allowed: if a nonzero base element lies in its kernel,
  inverting its image gives zero localizations, which are flat.
- `A` may be a field or a non-Noetherian domain; neither is excluded. Empty generating
  families are allowed by the finiteness predicates. The zero base ring is excluded exactly
  because the node asks for an integral domain and a nonzero element.
- No finiteness of the underlying set of M and no finite presentation of B or M is imposed.

Searches actually run (2026-10-24):

- `msearch.py ... leanfinder "A finite type algebra over an integral domain and a finitely
  generated module become simultaneously flat after inverting one nonzero base element."`:
  eight hits, including `RingHom.Flat.holdsForLocalizationAway`, `IsLocalization.flat`,
  `Module.flat_of_localized_span`, and `Algebra.Smooth.flat`. These assert flatness for
  localizations, local criteria, or smoothness; none chooses the common base element.
- `msearch.py ... loogle "Module.Flat, LocalizedModule.Away"`: two hits,
  `Module.flat_of_localized_span` and
  `Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant`; neither states the item.
- `msearch.py ... leansearch "Simultaneous generic flatness for an algebra and a finite
  module over a domain"`: eight hits (flatness criteria, descent and `RingHom.Flat`),
  with no generic simultaneous existence result.
- `msearch.py ... grep "generic.{0,40}(flat|free)|(flat|free).{0,40}generic" RingTheory`:
  one unrelated `genericPolyMap` hit in `MvPolynomial/FreeCommRing.lean`.
- `rg` over `lean/WeilConjectures` for generic flatness/freeness found the algebra-only
  `RingHom.exists_nonzero_flat_localizationAway` and Noetherian generic flatness
  `Module.exists_flat_localizedModule_powers` in
  `WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.FreeLocus`. The latter explicitly
  assumes `IsNoetherianRing R`; it does not cover this node. The node-id search in
  `lean/WeilConjectures` had no hits.
- `rg` over `lean/Sheaf` for generic flatness/freeness found the Noetherian and finitely
  presented algebra/module generic-freeness modules and generic finite-presentation data.
  Their signatures were read: the former require Noetherianity or finite presentation;
  the latter assert presentation data, not the item's flatness. None is an exact match.
- The proposed declaration name was searched in Mathlib, `lean/WeilConjectures`,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`; no existing declaration was found.

Validation: prescribed `scompile.py Q32 lem-trf-algebra-module-simultaneous-generic-flatness`
compiled this file in sandbox and library modes successfully (1.3 s and 1.4 s).
No errors or unexpected warnings. Every line is at most 100 characters.
No node faults or statement disputes were found.

## Second reading by Q32

This is the same worker's second pass, not a claim of an independent agent review; the brief
forbids starting other agents and assigns the independent delivery review to the maintainer.
Reopened the node and finished Lean file and checked every binder and conjunct. The two
commutative rings, domain, structure map, finite algebra, finite B-module, single nonzero a,
the two powers localizations and the stipulated A-actions all match the correspondences above.
The first conjunct is flatness of the composite map, hence exactly flatness over A; the
second uses the canonical B-action restricted to A, rather than an arbitrary A-module
structure. Neither conjunct silently asserts flatness only over B or only over A_a. Separate
universes permit all object sizes. The Noetherian and finite-presentation restrictions of
nearby existing results have not entered this statement. No mismatch or correction was found.
