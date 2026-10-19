## Worker report

The module `Sheaf.AlgebraicGeometry.FlatValuationLifting` states
`AlgebraicGeometry.exists_flat_valuation_lift`, the scheme specialization of
Stacks Project Tag 089F (`spaces-morphisms.tex`,
`lemma-lift-valuation-ring-through-flat-morphism`). The proof is `sorry`;
its docstring carries all six steps of the node's proof. No definitions,
helper theorems, dependency repairs, new nodes or statement corrections are needed.

Hypothesis and conclusion correspondence:

- Schemes and the morphism `f : Y → T`: `{Y T : Scheme.{u}} (f : Y ⟶ T)`.
- Flatness: `[Flat f]`, the recorded Mathlib definition. Its stalkwise
  characterization is `Flat.iff_flat_stalkMap`.
- The valuation ring `R`: `(R : Type u) [CommRing R] [IsDomain R]
  [ValuationRing R]`. The explicit domain instance is required by the Mathlib
  valuation-ring class, not an extra mathematical hypothesis. `ValuationRing.TFAE`
  identifies this with the node's fraction-field condition.
- The morphism `b : Spec R → T`: `(b : Spec (CommRingCat.of R) ⟶ T)`.
- Its closed-point image belongs to `f(Y)`:
  `(h : b (IsLocalRing.closedPoint R) ∈ Set.range f)`.
  The closed point is the maximal ideal; localness of a valuation ring is an
  existing instance, not an added hypothesis.
- Existence of a valuation ring `R'`: the dependent existential
  `∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : ValuationRing R')`.
- The injective local map: `(ι : R →+* R'), Function.Injective ι ∧ IsLocalHom ι`.
  `IsLocalRing.isLocalHom_iff_comap_closedPoint` identifies the latter with
  equality of the inverse-image maximal ideal and the original maximal ideal,
  exactly the parenthetical clause of the node. No residue-field isomorphism
  or restriction on the extension of fraction fields is asserted.
- The morphism into `Y` and the commutative square:
  `∃ c : Spec (CommRingCat.of R') ⟶ Y,
  c ≫ f = Spec.map (CommRingCat.ofHom ι) ≫ b`.
  Composition order agrees with `f ∘ c = b ∘ Spec(ι)`.
- No finite-presentation, Noetherian, rank or discreteness hypotheses occur.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat`, with `Flat.iff_flat_stalkMap` confirming the interface.
- `def-trf-valuation-ring`: its Mathlib match in
  `Mathlib.RingTheory.Valuation.ValuationRing`, `ValuationRing` and
  `ValuationRing.TFAE`; no lean record is needed for this Mathlib leaf.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`.

Public imports supply those four notions. Non-public imports retain the node's
proof plan: `Mathlib.AlgebraicGeometry.PullbackCarrier` (also supplies pullbacks),
`Mathlib.AlgebraicGeometry.Stalk`, `Mathlib.RingTheory.TensorProduct.Nontrivial`,
`Mathlib.RingTheory.Spectrum.Maximal.Basic`,
`Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`,
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`, and
`Mathlib.RingTheory.Valuation.LocalSubring`. The base-change dependency is in the
already publicly imported flat-morphism module.

Source reading: the full statement and proof of Tag 089F, and More on Algebra,
`definition-extension-valuation-rings`, were read. The latter explicitly says
injective and local. The scheme specialization requires no algebraic-space
structure or specified base scheme.

Edge cases checked before writing: if `R` is a field its closed point is zero,
so the hypothesis still has its intended meaning; all valuation ranks including
rank zero are admitted. An empty `Y` makes the image hypothesis false, rather
than requiring an unwanted nonemptiness assumption. Empty `T` admits no `b` from
the nonempty spectrum of a domain. Nonreduced `Y` or a nontrivial residue-field
extension is permitted: the proof uses a prime quotient of the local ring and
never assumes a rational point in the fibre. Neither surjectivity of `f` nor
faithful flatness of `f` is assumed. All schemes and rings use the common universe
`u` required by Mathlib's scheme category; the proof constructs `R'` from a local
ring of a pullback, its prime quotient and its fraction field, all of size `u`.
This excludes no mathematical case and introduces no vacuous small test universe.

Searches for an existing exact statement (all through the prescribed `msearch.py`
wrapper unless described as source ripgrep):

- LeanFinder: "A map from the spectrum of a valuation ring lifts through a flat
  scheme morphism after an injective local extension if the closed point is in
  the image". Eight results: valuative criteria and `Flat.generalizingMap`.
  Those concern generic-point squares/specializing maps or topological
  generalization lifting, not the injective local valuation extension here.
- Loogle: `AlgebraicGeometry.Flat, ValuationRing`. Zero results.
- Mathlib grep, directory `AlgebraicGeometry`:
  `lift.*valuation|valuation.*lift|valuation.*flat|flat.*valuation`. Zero results.
- LeanSearch: "Flat morphisms of schemes lift maps from valuation ring spectra
  after an injective local extension of valuation rings". Eight results,
  comprising `ValuativeCriterion`, its existence and uniqueness properties,
  `Flat`, `flat_iff`, and flatness projection/constructor declarations.
  None states the required theorem.
- Source ripgrep across `WeilConjectures` and `lean/Sheaf` first used
  `lift.*[Vv]aluation|[Vv]aluation.*lift|flat_valuation|valuation.*flat`.
  Many irrelevant evaluation matches prompted a narrowed word-boundary search
  in `WeilConjectures` and `lean/Sheaf/AlgebraicGeometry`:
  `\b[Vv]aluation.*lift|lift.*\b[Vv]aluation|flat_valuation`.
  Hits were different Riemann-Zariski, properness, and fibre-component lifting
  statements; no exact match.
- Source grep for the literal blueprint id in `WeilConjectures`: zero hits.
- Name collision search for `exists_flat_valuation_lift` in
  `dag/lean_names_upstream.json`, `WeilConjectures`, and `lean/Sheaf`: zero hits.

No node fault or disputed statement was found. Only the item's `lean` field is
changed. Compilation and delivery checks are performed through the prescribed
wrappers; no global build or direct git operation is used.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
