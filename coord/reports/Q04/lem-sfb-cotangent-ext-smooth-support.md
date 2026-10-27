## Worker report

The module `Sheaf.RingTheory.CotangentExtSmoothSupport` states
`Algebra.CotangentResolution.cotangentExt_finite_localization_smooth_support`.
The node statement and dependency lists are unchanged; only its `lean` field is set.
The one postponed theorem has the node's complete six-step proof plan in its docstring.
All helper definitions have actual data and source/blueprint docstrings. They belong to
this node's Ext/localization interface and are listed in `lean.declarations`.

Hypotheses and objects, clause by clause:

- `f : Arrow CommRingCat.{u}` encodes the given commutative algebra map `k → P`;
  `f.left` is k and `f.right` is P. `_hk : IsField f.left` asserts that the
  existing commutative ring structure is a field. This is equivalent to equipping
  that same ring structure with `Field`; it avoids installing an unrelated second
  ring structure on the bundled source ring.
- `_hfinite : RingHom.FiniteType f.hom.hom` is exactly finite type of that algebra
  map. There is no finite-extension assumption on the field.
- `N : ModuleCat.{u} f.right` and `[Module.Finite f.right N]` give an ordinary
  finite P-module. Both zero modules and the zero target algebra are allowed.
- `C : Algebra.CotangentResolution.Coherence.{u}` is the recorded model package
  for the standard polynomial cotangent complex. The section explicitly binds
  the family's `HasDerivedCategory.{u+1} (ModuleCat.{u} B)` instances required by
  this dependency. These are derived-category infrastructure, not additional
  algebraic hypotheses. All universes and variables are explicitly bound.
- `cotangentExt C f N j` is exactly the Hom type from `cotangentComplex C f` to
  `((DerivedCategory.singleFunctor (ModuleCat f.right) 0).obj N)⟦j⟧`.
  Its canonical P-module structure is the Mathlib linear derived-category structure.
  The full alternating polynomial complex from the dependency is retained; no
  naive cotangent complex, truncation, or homology replacement is used.
- `(j : ℤ) (_hj : 1 ≤ j)` binds every positive integer degree. The first conjunct
  `Module.Finite f.right (cotangentExt C f N j)` states finiteness.
- The second conjunct quantifies over every `S : Submonoid f.right`, with no
  nonzero-elements assumption. `localizedArrow f S` is the actual composite
  `k → P → Localization S`. `localizedCoefficient S N` is the actual
  `LocalizedModule S N`, bundled over `Localization S`.
- The arrow `ι` in that conjunct is required pointwise to equal
  `LocalizedModule.mk n 1`, so it is the canonical coefficient localization map.
  The isomorphism `e` is an isomorphism in `ModuleCat (Localization S)` from
  `LocalizedModule S (cotangentExt C f N j)` to the cotangent Ext group of the
  localized arrow and coefficients. It therefore states an S⁻¹P-linear isomorphism.
- This is the canonical isomorphism, rather than an unspecified isomorphism:
  for every ξ the conclusion requires `IsCotangentExtLocalization ... ι ξ
  (e.hom (LocalizedModule.mk ξ 1))`. This predicate is the commuting derived Hom
  square: coefficient localization after ξ equals the canonical `cotangentMap`
  followed by restriction of the localized morphism, using the exact
  restriction-of-scalars functor's canonical shift and single-object comparisons.
  The usual localization adjunction (the target is already S-local) determines
  this morphism uniquely, and S⁻¹P-linearity determines e from values ξ/1.
- In the third conjunct `q : PrimeSpectrum f.right` ranges over every prime.
  `∃ U : (Spec f.right).Opens, q ∈ U ∧ Smooth (U.ι ≫ Spec.map f.hom)` means that
  Spec P → Spec k is smooth on an open neighborhood of q. This uses exactly the
  recorded scheme smoothness notion; it does not use formal smoothness of the
  local ring. `Subsingleton (LocalizedModule q.asIdeal.primeCompl ...)` is precisely
  zero of the localized additive module.
- The last conjunct writes the support exactly as the node defines it, the set
  of primes with nonsubsingleton localization, and asserts its inclusion in the
  complement of those smooth primes. The separately stated vanishing and support
  clauses are both retained because the node explicitly states both.

Dependency declarations read and used:

- `def-weil-field`: `Field` in `Mathlib.Algebra.Field.Defs`; the compatible predicate
  `IsField` and its `IsField.toField` construction are in `Mathlib.Algebra.Field.IsField`.
- `def-weil-pbc-finite-type-algebra`: `RingHom.FiniteType`,
  `Mathlib.RingTheory.FiniteType`.
- `def-weil-finitely-generated-module`: `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs`.
- `def-trf-cotangent-resolution-data`: `Algebra.CotangentResolution.Coherence`,
  `cotangentComplex`, and `cotangentMap`, in
  `Sheaf.RingTheory.CotangentResolutionCoherence`. The whole module, including the
  standard alternating complex and the canonical derived comparison, was read.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  and `DerivedCategory.singleFunctor`, `Mathlib.Algebra.Homology.DerivedCategory.Basic`;
  canonical scalar actions come from `Mathlib.Algebra.Homology.DerivedCategory.Linear`.
- `def-weil-pbc-module-localization`: `LocalizedModule` and `LocalizedModule.mk`,
  `Mathlib.Algebra.Module.LocalizedModule.Basic`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.

All currently recorded proof-dependency modules are imported, including the finite
polynomial resolution, coherence, polynomial differential basis, K-projective and
derived-Hom results, Noetherian results, lci cotangent presentation, normalized vs
alternating homotopy equivalence, smooth differentials, exact module stalks, tilde
stalks, and finite locally free sheaves. The proof-only dependency
`lem-trf-cotangent-augmentation-localization` currently has no Lean record or Mathlib
match, hence no module to import; it is retained in the proof plan and the unchanged
DAG proof dependencies. It is not needed to type the statement.

Sources checked: Stacks `cotangent.tex`, Tags 08PX (`proposition-polynomial`),
08QI (`remark-resolution`), 08SF (`lemma-localize`), and 08R5
(`lemma-when-projective`); `more-algebra.tex`, Tag 0A6A(3). These agree with the
node's finite-free Hom calculation, localization comparison, and smooth vanishing.
No statement correction or disputed statement is needed.

Edge cases checked mathematically before finalizing:

- `j = 1` is included; zero and negative degrees are excluded exactly as written.
- `N = 0` gives zero Hom modules and zero localizations.
- `P = 0` is allowed: Spec P is empty, all module Hom groups are zero, and support
  and smooth-prime assertions are vacuous. No target nontriviality was added.
- `0 ∈ S` is allowed: the localization is the zero ring and both modules in the
  comparison vanish. The canonical coefficient square remains meaningful.
- `S = {1}` gives the identity localization comparison; all-element sets and prime
  complements are also covered without a finiteness restriction on S.
- Smooth polynomial algebras give positive-degree vanishing everywhere. Singular
  and non-lci algebras are permitted: the full complex need not be two-term or
  bounded below; no perfectness or lci assumption has been imposed.
- Characteristic is unrestricted and every prime, not only closed primes, is used.

Searches for existing statements and declarations (the msearch results are recorded
in the sandbox's `searches.jsonl`):

- `msearch.py leanfinder`, query `finite cotangent Ext modules localize vanish smooth locus`:
  eight hits, headed by `Algebra.smoothLocus_eq_compl_support_inter` and smooth-locus
  lemmas. These concern the naive cotangent homology/smooth locus, not positive
  full cotangent Ext with finite coefficients; no exact match.
- `msearch.py loogle`, query `DerivedCategory Hom Ext cotangentComplex Module.Finite`:
  zero hits, diagnostic unknown identifier `Hom`. Replaced with the valid query
  `Module.Finite, LocalizedModule`: six hits including
  `Module.Finite.instLocalizationLocalizedModule` and
  `LocalizedModule.exists_subsingleton_away`; none states the theorem.
- `msearch.py grep`, query `cotangentExt|cotangent.*Ext|Hom.*cotangent|Smooth.*localiz`,
  Mathlib: zero hits.
- `rg` on the Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` sources for cotangent
  Ext, the theorem name, helper names, and the node id: no existing full theorem
  or conflicting fully qualified declaration. The affine deformation lift mentions
  this node in its proof plan but does not state it. Other `localizationSquare`
  declarations lie in different namespaces and describe different squares.
- `rg` on `dag/lean_names_upstream.json` and Mathlib for the new names: no exact
  declaration. Related Mathlib `cotangentExtendScalarsEquiv` concerns cotangent
  spaces, not the present derived Ext module.

Validation: `scompile.py` compiled the module both as a sandbox file and as its
library module on the live server, cleanly with no errors or warnings. The delivered
file contains only the theorem's expected `sorry`, and no hollow definitions.

## Second reading by Q04

No second reading by a worker: the dispatcher authorizes direct worker delivery;
the maintainer's independent review is the review of this packet.
