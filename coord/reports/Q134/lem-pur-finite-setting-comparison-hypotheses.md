## Worker report

The module `Sheaf.Paper.PurityFiniteSettingComparisonHypotheses` states
`WeilConjectures.PurityFiniteSetting.finite_setting_comparison_hypotheses`.
Its sole theorem has proof `by sorry`; no definitions or proofs are added.
The node changes only in `lean`. There are no new nodes, dependency repairs,
statement corrections, or statement disputes.

Source read: main-20261015 blueprint,
`sec-six-functors-basics/sk-prop-cohsm/thm-pur-cohomological-smoothness.proof.md`,
first paragraph, and all six proof steps of the assigned node. The source starts
at a finite coefficient stage and applies the ordinary smooth tensor and ambient
adjoint comparisons. This lemma checks their geometric and coefficient inputs;
it asserts no new comparison functor or comparison isomorphism.

Hypothesis and clause correspondence:

- The fixed algebraic closure k of the finite field, primes p and ell with
  ell distinct from p, finite subextension E of the fixed coefficient closure,
  and positive level n are bundled in `P : PurityFiniteSetting.{u}`. In the
  recorded definition these are `P.field`, `P.coefficients`, `P.extension`,
  its finite-dimensional instance, `P.level`, and `P.level_pos`.
  `P.Ring` is literally `Padic.coefficientExtensionRing` at these parameters,
  the quotient of the recorded integer ring by the power of its chosen
  uniformizer. It is not a new ring or an arbitrary finite coefficient ring.
- X and Y are `Scheme.{u}` with explicit structure maps `aX` and `aY` to
  `Spec (CommRingCat.of P.field.k)`. Each structure map has
  `LocallyOfFiniteType` and `QuasiCompact`, exactly finite type. The morphism
  `f : X ⟶ Y` is a k-morphism by `_hf : f ≫ aY = aX` and has
  `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact`. There is no
  separatedness hypothesis on either structure morphism.
- Noetherianity, quasi-compactness and quasi-separatedness of X and Y are the
  six initial conjuncts: `IsNoetherian`, `CompactSpace` and
  `QuasiSeparatedSpace` for each scheme. `IsNoetherian` already includes
  quasi-compactness, but the node explicitly lists all three properties.
- Compactification existence is `∃ c : Compactification f, QuasiCompact c.i`.
  The existing structure carries the ambient scheme `c.Z`, open immersion
  `c.i`, proper morphism `c.g`, and equation `c.comm : f = c.i ≫ c.g`.
  Thus the open, proper, and factorization clauses are real structure data.
- The next universal quantifier ranges over every compactification. Its
  structure map to k is `c.g ≫ aY`;
  `LocallyOfFiniteType` and `QuasiCompact` state finite type, followed by
  `IsNoetherian c.Z`. The bound is `∃ D : ℕ,
  topologicalKrullDim c.Z ≤ (D : WithBot ℕ∞)`.
  Natural numbers encode the nonnegative integer bounds. When the scheme is
  empty its dimension is bottom, so D = 0 is allowed as the node specifies.
  `QuasiCompact c.i` also explicitly records the open part condition.
  The underlying compactification structure does not itself require the open
  part quasi-compact, but `Compactification.quasiCompact_openImmersion` gives
  it for every c from the existing `QuasiCompact f` hypothesis. Hence this
  quantification is precisely over all compactifications in the node's setting.
- Finiteness of A is `Finite P.Ring`. The positive annihilating integer N is
  written explicitly as `P.coefficients.l ^ P.level`, with positivity as
  `1 ≤ P.coefficients.l ^ P.level` and annihilation as
  `∀ a : P.Ring, (P.coefficients.l ^ P.level) • a = 0`.
  This is multiplication by N in the additive group of A; it is equivalent
  to the image of N being zero in this unital ring.
- Invertibility on EVERY k-scheme is the quantifier over `T : Scheme.{u}`
  and its structure morphism `_aT : T ⟶ Spec (CommRingCat.of P.field.k)`,
  with `IsUnit ((P.coefficients.l ^ P.level : ℕ) : Γ(T, ⊤))`.
  T has no finite-type, Noetherian, nonemptiness or separatedness condition.
  A unit in global sections is precisely a global inverse for the integer
  section, and thus also yields a unit in every local ring.
- The final quantifier takes an arbitrary finite-type k-scheme Y' with
  structure map `aY'`, a k-morphism g with `_hg : g ≫ aY = aY'`, any scheme
  X', and maps g', f' with `_sq : ChosenCartesianSquare g' f' f g`.
  The structure map of X' is the induced `f' ≫ aY'`; finite type of this
  map is a conclusion. Commutativity of the square and `_hf`, `_hg` make
  g' a k-morphism for this structure. The chosen square's
  `isoPullback`, `hom_fst`, `hom_snd` identify this with Cartesian base change.
  No morphism property of g or g' is assumed. The conclusion gives
  `IsSeparated f'`, `LocallyOfFiniteType f'`, `QuasiCompact f'`, finite type
  of `f' ≫ aY'`, all six
  Noetherian/qc/qs properties of X', Y', compactification existence with
  quasi-compact open part, and the same universally quantified finite-type,
  Noetherian, and dimension-bound conclusions for all compactifications of f'.
  The coefficient and universal invertibility conjuncts above use the same
  P and already apply unchanged to these schemes, so need no duplicate clause.
- The final “in particular” sentence is specialization of these conclusions
  to f with `SmoothOfRelativeDimension d f`, `d : ℕ`. Smoothness is not needed
  to establish any of the geometric/coefficient conclusions, and adding it as
  a hypothesis of the theorem would restrict the node. The imported existing
  `SmoothOfRelativeDimension` supplies the source's meaning of this special
  case. The proof docstring explains that the listed conclusions discharge
  the stated ordinary tensor and bounded-below Hom comparison hypotheses;
  there is no additional assertion about comparison functors to formalize.

Dependency declarations used and read:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `.Ring`, `.ringCommRing`, and the existing `.exponent` interface, which was
  checked and deliberately not substituted for ell^n. Its exponent is the
  Kummer-specific ell^(n/e), whereas this node needs no e-divisibility.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, importing the actual quotient
  constructions in `Sheaf.NumberTheory.Padics.CoefficientExtension`.
  Those constructions and their full definitions/docstrings were read.
- `def-weil-scheme-morphism-properties` is explicitly a convention record
  with null declaration/module; its statement directs citers to existing
  Mathlib properties. These are `AlgebraicGeometry.LocallyOfFiniteType`,
  `QuasiCompact`, `IsSeparated` and `IsProper`, rather than another predicate.
- `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification.Refinement` and `.category` import the
  owning `WeilConjectures.Compactification.Defs`. The theorem uses its
  `AlgebraicGeometry.Compactification` with its existing data and properties.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, the supremum of
  chains of irreducible closed subsets, with bottom for the empty space.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`, using its actual chosen pullback
  isomorphism and projection compatibility, not merely `CommSq`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`:
  `AlgebraicGeometry.Smooth` and `SmoothOfRelativeDimension`, as the recorded
  meaning of the final smooth specialization.

Proof-plan imports include the published Nagata construction
`AlgebraicGeometry.NagataCompactification`, the finite-dimension bound
`AlgebraicGeometry.exists_topologicalKrullDim_le`, the scheme/point dimension
module, Noetherian and quasi-separated permanence, and valued finite quotients.
The spectral norm and DVR declarations used in the coefficient argument are
already public through the coefficient-extension dependency imports.

Edge cases checked before writing:

- Empty X, Y or ambient scheme are allowed: no `Nonempty` binder. Empty ambient
  space has dimension bottom and the quantified bound may be zero. The ring
  of sections on the empty scheme is the zero ring, in which the integer
  section is a unit, so the universal invertibility clause remains correct.
- n = 1 is included; n = 0 is excluded exactly by `P.level_pos`.
- Ramified extensions need no identification ell = varpi. The valuation puts
  ell in (varpi); taking the nth power kills A even when e does not divide n.
- A nonseparated finite-type scheme over k is included; only f is separated.
- A compactification with additional proper components disjoint from X is
  included by the unrestricted quantifier over all `Compactification f`.
- Identity and arbitrary Cartesian base changes are included. No smoothness,
  finite type, separation or flatness of the base-change maps g and g' is added.
- Smooth relative dimension zero and empty-source smooth morphisms are included
  by specialization; the lemma also applies without smoothness.
- The field datum and all schemes use the existing common universe u, with
  u explicitly declared and `set_option autoImplicit false`.

Searches actually run (logged by msearch in the sandbox):

1. LeanFinder: “A separated finite type morphism of finite type schemes over
   an algebraic closure of a finite field has noetherian finite dimensional
   compactifications and the finite l-adic coefficient ring has an invertible
   prime power annihilator”. Eight hits on finite morphisms and properness,
   including `finite_appTop_of_universallyClosed`; none states the node.
2. Loogle: `AlgebraicGeometry.Compactification, topologicalKrullDim`.
   Inconclusive: Compactification is upstream, unknown to the Mathlib service.
3. Corrected Loogle: `AlgebraicGeometry.LocallyOfFiniteType,
   AlgebraicGeometry.IsProper`. Seven results about properness implying local
   finite type and the valuative criterion; none states this node.
4. msearch grep: `finiteSettingComparison|finite_setting_comparison|
   coefficientExtensionRing.*[Aa]nnihil|compactification.*[dD]im`.
   One unrelated OnePoint/Sphere hit in Mathlib.
5. LeanSearch: “Finite type schemes over a field are Noetherian and their
   compactifications have finite Krull dimension”. Eight Noetherian scheme
   hits (`IsNoetherian`, `isNoetherian_iff`, etc.), none stating the node.
6. Direct rg over both `lean/WeilConjectures` and `lean/Sheaf` for
   `finiteSettingComparison|finite_setting_comparison|finite_setting.*hypoth|
   comparison_hypoth|coefficientExtensionRing.*[Aa]nnihil|
   compactification.*[dD]im` found comparison users and dimension statements,
   but no existing combined assertion. Searching the assigned node id in
   upstream `lean/WeilConjectures` returned no match.

Resumption audit: the interrupted turn left no running delivery process and
no DELIVERED result. The earlier dry run covered an older signature. This turn
keeps the current explicit-structure-map signature, updates the stale report
and node signature, and reruns the prescribed server compiler and delivery
checks. The final signature binds every variable and universe explicitly.
Only the item's lean record changes; all lines in the module are at most 100
characters. The wrapper logs record the actual validation and delivery results.

## Second reading by Q134

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
