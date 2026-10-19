## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian` states
`AlgebraicGeometry.ProEtale.finiteTorComparisonNoetherian` with its entire proof `sorry`.
It defines nothing. The natural-language statement, statement dependencies and proof plan
of the item are unchanged. One dependency receives an existing-declaration interface repair.
There are no new nodes and no statement correction or statement dispute.

### Hypotheses and clauses

- A scheme is `(X : Scheme.{u})`. Quasi-compactness is `[CompactSpace X]`; quasi-separatedness
  is `[QuasiSeparatedSpace X]`. Mathlib's `quasiSeparated_iff_quasiSeparatedSpace` identifies
  this with quasi-separatedness of the structure morphism to Spec Z. No separatedness,
  finite type, Noetherian scheme, or nonemptiness hypothesis is added.
- Discrete Noetherian commutative coefficients are
  `(A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A]`. The coefficient ring is used
  as a constant ring sheaf; it is not given an adic completion or non-discrete topology.
  The independent universes permit arbitrarily large coefficients relative to the scheme.
- Both ambient derived categories are `ConstantCompletion.D (ConstantCompletion.constant T A)`
  for the recorded `Scheme.smallModelComparisonEtaleTopology.{u,v} X` and
  `Scheme.coefficientProEtaleModelTopology.{u,v} X`. Despite the namespace, `constant` is just
  the ordinary constant ring sheaf and `D` is `HasDerivedCategory.standard` localization;
  neither an ideal nor a completeness condition occurs. These are the same presentations
  as the dependency `constructibleComparison`.
- The derived comparison inverse image is the existential functor `D` together with
  `Nonempty (ConstantCompletion.Q _ ⋙ D ≅ constructibleComparisonComplexPullback X A ⋙
  ConstantCompletion.Q _)`. This fixes the functor up to the natural isomorphism inherent
  in localization, by its action on *all* cochain complexes. The module-level functor in
  that equation is the existing canonical ringed-site pullback: module Kan extension and
  sheafification along the constant-section ring map. Thus no arbitrary comparison functor
  is a hypothesis or substituted for nu*.
- `K ∈ D^b_c(X_et,A)` is the bound variable of the middle clause, with premise
  `Scheme.IsCoefficientBoundedConstructibleEtale X A K`. Its definition is constructibility
  of every cohomology sheaf and a single finite vanishing interval. Constructibility is the
  recorded affine-local finite constructible stratification with finite-type constant
  local models; it imposes no global constant model.
- `a ≤ b` is `∀ a b : ℤ, a ≤ b →`. The same `a` and `b` occur on both sides of `↔`.
  Etale Tor amplitude is the existing `HasCoefficientModelTorAmplitude _ K a b`.
  Pro-etale Tor amplitude is the existing
  `Scheme.HasCoefficientProEtaleTorAmplitude X A (D.obj K) a b`.
  The latter abbreviation unfolds to precisely the former generic predicate on the
  pro-etale constant ring. This predicate quantifies over every K-flat representative
  P of K, every module sheaf M in degree zero, and every integer q outside [a,b], requiring
  `IsZero` of the ordinary total-tensor homology. K-flat resolutions exist by
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`; hence this expresses
  the stated derived tensor test and is not vacuous. In particular the pro-etale tests
  are NOT restricted to classical, constructible, finitely presented, or flat M.
- The final `∃ e : ... ≌ ...` is exactly the consequential equivalence of full finite-Tor
  bounded constructible subcategories. The source object predicate is
  `Scheme.IsCoefficientBoundedConstructibleEtale X A K ∧
  ∃ a b : ℤ, HasCoefficientModelTorAmplitude _ K a b`.
  The target is `coefficientBoundedConstructibleProEtale X A K ∧
  Scheme.HasFiniteCoefficientProEtaleTorAmplitude X A K`.
  An ordered common interval is part of the Tor predicate; the bounds do not depend on M.
  The discrete constant-ring realization of Dctf is the intersection of bounded
  constructibility and finite Tor amplitude, as in
  `det-def-sfb-constructible-tor-amplitude` and the discrete presentation already used in
  `constructibleComparison`. No second constructibility or tensor construction is made.
- Both categories are `ObjectProperty.FullSubcategory`, retaining every ambient morphism.
  The final `Nonempty (e.functor ⋙ ObjectProperty.ι ... ≅ ObjectProperty.ι ... ⋙ D)` identifies
  the forward equivalence with restriction of this same nu*, so the result does not merely
  assert an unrelated abstract equivalence of the two categories.

### Dependencies used

Read each statement dependency's natural statement and full declaration/docstring before
writing the file. Public statement imports are:

- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (def-weil-pbc-quasi-compact-scheme).
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `AlgebraicGeometry.QuasiSeparated`,
  and `quasiSeparated_iff_quasiSeparatedSpace` for its scheme formulation
  (def-weil-quasi-separated-morphism).
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, `isNoetherianRing_iff_ideal_fg`
  (def-weil-pbc-noetherian-ring).
- `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules`:
  `AlgebraicGeometry.ProEtale.proEtaleClassicalSheavesModules`
  (det-pe-classical-sheaves-modules): exact and fully faithful module inverse image.
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`:
  `AlgebraicGeometry.ProEtale.constructibleComparisonRingMap`,
  `constructibleComparisonPullback`, `constructibleComparisonComplexPullback`,
  `constructibleComparison` (sk-thm-pe-constructible-comparison). Its public dependencies
  supply `Scheme.IsCoefficientBoundedConstructibleEtale`,
  `coefficientBoundedConstructibleProEtale`, the equivalent small site models and ordinary
  standard-localization abbreviations used here. All displayed categories match that
  dependency rather than using fresh versions.
- `Sheaf.Paper.ConstantModelTorAmplitude`:
  `AlgebraicGeometry.ProEtale.constantModelConstructibleFiniteTor_wellDefined`, publicly
  importing the recorded `ConstantModelBoundedConstructible` /
  `ConstantModelConstructibleFiniteTor` and generic `DerivedCategory.torAmplitudeIn`
  (det-def-sfb-constructible-tor-amplitude). This supplies the general internal-module
  convention; the statement uses its discrete constant-ring presentation, as above.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`:
  `AlgebraicGeometry.Etale.derivedTensor` (def-kun-derived-tensor), the K-flat total tensor.
  On intrinsic constant-ring modules the Tor test uses the same ordinary module tensor
  and K-flat resolutions, not a copy of a fixed-ModuleCat tensor definition.
- `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude`:
  `CategoryTheory.HasCoefficientModelTorAmplitude`,
  `AlgebraicGeometry.Scheme.HasCoefficientProEtaleTorAmplitude`, and
  `AlgebraicGeometry.Scheme.HasFiniteCoefficientProEtaleTorAmplitude`
  (def-weil-proetale-tor-amplitude, repaired record; see below).

The other already-stated proof dependency modules are imported non-publicly, including
`ProEtaleSiteComparison`, `RingedToposFlatPullback`,
`RingedTopoiCanonicalTensorPullbackOfUniverses`, standard derived category/t-structure,
`BoundedFlatReplacement`, `BoundedAboveFlatSheafKFlat`, `SiteFlatOpcyclesTorCriterion`,
`TruncationsAndHomotopyColimits`, pro-etale `FiniteCoefficient.Derived.Tensor`, and
`Mathlib.Algebra.Homology.BifunctorShift`. The module docstring and theorem docstring name
sources; the theorem docstring carries all seven proof steps of the node.
`def-weil-size-convention` has no recorded module, so no import is invented for it.

### Edge cases

Checked mathematically before writing: the empty scheme and zero coefficient ring are
allowed; all module sheaves there vanish, so every ordered interval is valid and both
full subcategories have the stated comparison. The zero complex passes every ordered
interval. Singleton intervals a=b, negative bounds, and intervals not containing zero
are all permitted; no Nat degree convention is used. For a nonzero free sheaf in degree
zero, a test by the coefficient ring rules out intervals omitting degree zero. Infinite
Noetherian rings (e.g. Z) and coefficient characteristics not invertible on X are included:
there is no Finite, field, exponent, or characteristic hypothesis. Arbitrary pro-etale
module tests remain quantified, rather than being inferred from tests on the essential
image of comparison. K-flat-resolution existence on both small site models makes the
representative quantification nonvacuous. No extra site-universe equality is imposed.

### Searches and validation

- `msearch.py leanfinder`, query: "Etale to proetale comparison preserves and reflects Tor
  amplitude for discrete Noetherian coefficients and restricts to constructible finite Tor
  equivalence". Eight results concern ring-theoretic etaleness; no matching theorem.
- `msearch.py leansearch`, query: "Tor amplitude is preserved and reflected by etale to
  proetale inverse image for discrete Noetherian ring coefficients". Eight results concern
  formal etaleness, base change, and finite presentation; no matching statement.
- `msearch.py loogle`, query: `"torAmplitudeIn"`. Zero Mathlib hits.
- `msearch.py grep`, query: `torAmplitude|TorAmplitude|finiteTor`. Zero Mathlib hits.
- `rg` across the source `WeilConjectures` tree and project `lean/Sheaf`, queries
  `finite.tor.comparison|torAmplitudeIn|HasProEtaleTorAmplitude|coefficient.*Tor` and
  `ringedSiteDerivedTensorOfUniverses|ringedSite.*Tor|ConstantCompletion.*tensor|def .*TorAmplitude|def .*torAmplitude`.
  Found and read the existing coefficient-model Tor interface and the constructible
  comparison interfaces reused here. No exact Noetherian Tor comparison statement exists.
- Upstream `SixFunctors/ProEtale/Derived/HomComparison.lean` has
  `torAmplitudeIn_mapDerivedCategory` and `torAmplitudeIn_of_mapDerivedCategory` for finite
  coefficient rings (the latter also assumes invertible exponent). These do not state
  this arbitrary Noetherian coefficient result or its restricted equivalence.
- `grep -rn det-pe-finite-tor-comparison-noetherian` in the upstream source finds no item.
- Read the item's blueprint statement and its four-paragraph proof at the recorded
  main-20261015 source path, as well as the node's expanded seven-step proof.
- Used `scompile.py --source` for the current
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor` source (absent
  from the older read-only checkout); its signature and docstring confirm the proof import.
- The prescribed `scompile.py NK det-pe-finite-tor-comparison-noetherian <module>` passed
  both sandbox and library-path compilation in 4.0 seconds each, with no errors or warnings.
  Every universe and variable is explicitly bound; no local notation or local instance is
  introduced, and every source line has at most 100 characters.

## Dependency modules

`def-weil-proetale-tor-amplitude`: lean-only repair under §1(B), binding to the already
published `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude` interface. No module is
added for the dependency. This coefficient module publicly imports the old
`Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude` module, so its record now names all five
declarations: the retained `Scheme.HasProEtaleTorAmplitude` and
`Scheme.HasFiniteProEtaleTorAmplitude`, together with
`CategoryTheory.HasCoefficientModelTorAmplitude`,
`Scheme.HasCoefficientProEtaleTorAmplitude`, and
`Scheme.HasFiniteCoefficientProEtaleTorAmplitude`. The former predicate accepts a ring in
`Type t` on `Scheme.{t}` and the ULift constant ring on the original site. It cannot accept
the coefficient-sized intrinsic derived objects used by the recorded constructible
comparison. The coefficient-sized predicates say the same universal Tor condition on the
equivalent small site with independent coefficient size, and the finite variant requires one
ordered interval. No notion or tensor product is redefined. Only this node's `lean` field
changes, with `existing: true` and a note naming both modules.

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
