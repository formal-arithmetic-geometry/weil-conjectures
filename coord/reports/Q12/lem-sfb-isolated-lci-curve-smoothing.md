## Worker report

Stage 2: `Sheaf.AlgebraicGeometry.IsolatedLCICurveSmoothing` states
`AlgebraicGeometry.isolated_lci_curve_smoothing`, with its sole proof `by sorry`.
There are no new definitions, new nodes, dependency repairs, or statement corrections.
Only the item's `lean` field changes. Q21's reviewed stage-1 split is preserved in full;
its existence does not supply the absent stage-2 statement. The previous attempt's
empty stage-1 delivery is replaced by this actual stage-2 statement delivery.

Source read: `literature/stacks-project/examples-defos.tex`, Tag 0E7Y,
`lemma-smoothing-proper-curve-isolated-lci`, statement and full proof, lines 3111–3197.
Read the item's complete eight-step proof and all nine statement-dependency records,
and the source signatures and docstrings of the recorded notions. The original
example `Sheaf.CategoryTheory.CompactObject` is now withdrawn; its node records the
canonical upstream definition, illustrating why no duplicate definitions belong here.

Each hypothesis and clause is rendered as follows:

| Node content | Lean rendering |
| --- | --- |
| A field k | `(k : Type u) [Field k]` |
| A proper k-scheme X with specified structure map | `(X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsProper f]` |
| Dimension at most one | `hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)` |
| Affine open cover by spectra of finitely generated k-algebras | `hlci` quantifies over `I`, `A`, algebra structures `aA`, finite-type witnesses `ft`, and open immersions `φ`; its third conjunct says their images cover every point |
| These are the given k-algebra structures, rather than unrelated ones | `φ i ≫ f = Spec.map (CommRingCat.ofHom (@algebraMap k (A i) _ _ (aA i)))` |
| Each chart is lci over k | The last conjunct of `hlci` uses the recorded `@Algebra.IsLocalCompleteIntersection k (A i) _ _ (aA i) (ft i)` |
| Smooth away from finitely many closed points | `hsmooth` gives a finite set `S`, closedness of each singleton in `S`, and an open neighbourhood `U` of each point outside `S` with `Smooth (U.ι ≫ f)` |
| There exists Y over Spec k[[t]] | `∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of (PowerSeries k)))` |
| Flat | `Flat g` |
| Finitely presented | `LocallyOfFinitePresentation g ∧ QuasiCompact g ∧ QuasiSeparated g`, precisely the node's finite-presentation convention |
| Projective in finite-projective-space convention | `IsHProjective g`, the dependency's canonical upstream definition |
| Special fibre | `pullback g (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k))))` |
| Its isomorphism with X is over k | The witness `e` is an isomorphism from this fibre to `X`, and `e.hom ≫ f = pullback.snd g ...` asserts compatibility with the k-structure |
| Generic fibre over k((t)) = k[[t]][1/t] | Base change along `Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (Localization.Away (PowerSeries.X : PowerSeries k))))` |
| The generic fibre is smooth | `Smooth` of that pullback's second projection |

Finite presentation in the source follows from projectivity over the Noetherian
power-series trait, exactly as the node's source note explains. Its expression as
three morphism properties does not assume finite presentation on X as a new hypothesis.
No genus, connectedness, reducedness, perfectness, or pure-dimension hypothesis is added.

Statement-dependency declarations used:

- `Mathlib.Algebra.Field.Defs`: `Field` (available transitively).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`
  (publicly available through the upstream projective module).
- `WeilConjectures.RingTheory.CompleteIntersectionOverField`:
  `Algebra.IsLocalCompleteIntersection`, with its actual finite-type instance argument.
  Its `Algebra.IsGlobalCompleteIntersection` supplies the dependency's zero-ring convention.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsHProjective` (not the distinct projective-bundle predicate).
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`; its finite-presentation convention
  also uses the existing `QuasiCompact` and `QuasiSeparated`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, available through the
  complete-intersection dependency.
- `Mathlib.RingTheory.PowerSeries.Basic`: `PowerSeries`, the recorded one-variable
  specialization of `MvPowerSeries`, and its actual `constantCoeff` homomorphism.
- `Mathlib.RingTheory.Localization.Away.Basic`: canonical `Localization.Away` and
  its algebra map. No arbitrary generic-point map is assumed or chosen.

All recorded, non-Mathlib proof modules have plain (private) imports. They supply
the equidimensional partition, pointwise lci criterion, local dimension comparison,
closed-point ring dimension, projectivity/properness comparison, Fitting base change,
fibrewise smoothness, relative differentials and Fitting ideal sheaf. Unstated proof
prerequisites do not have importable modules; they are named in the eight-step proof
plan without being assumed in the theorem. No proof import cycle was introduced.

Edge cases checked mathematically before writing:

- Empty X is allowed: `I` can be empty, the pointwise hypotheses are vacuous, and
  the empty family is flat, projective, finitely presented and has empty smooth fibres.
  `topologicalKrullDim X = ⊥` satisfies `hdim`.
- Zero-dimensional X and mixed zero/one-dimensional X are retained; `hdim` is an
  inequality and no equidimensionality is assumed. The eight-step split explicitly
  handles both open-and-closed pieces. In particular Artinian lci schemes are allowed.
- The finite exceptional set may be empty and may include smooth closed points;
  the node says smooth away from a finite set, not that every listed point is singular.
- Nilpotent lci special fibres, including `Spec k[ε]/(ε²)`, are not excluded. The
  generic fibre alone is required smooth.
- Arbitrary field characteristic and imperfect fields are allowed. No algebraic
  closure, perfectness, or rationality of the exceptional closed points is assumed.
- The special-fibre isomorphism is over k, rather than merely an isomorphism of
  underlying schemes. The generic fibre uses the specified localization at t.
- Universe u is explicit; affine chart indexing and coordinate rings lie in the
  scheme's universe. This is the existing scheme/Spec convention and does not add
  a smallness hypothesis to any geometric test condition.

Searches actually run:

1. `msearch.py ... leanfinder "A proper local complete intersection curve with
   finitely many nonsmooth closed points admits a projective smoothing over the
   formal power series ring"`: eight hits about smooth charts and standard smooth
   algebras; no projective smoothing theorem.
2. `msearch.py ... loogle "Algebra.IsLocalCompleteIntersection,
   AlgebraicGeometry.IsHProjective, PowerSeries.constantCoeff"`: zero hits and
   diagnostic `unknown identifier 'Algebra.IsLocalCompleteIntersection'`; the
   service does not index that project declaration, which was read directly.
3. `msearch.py ... grep "smoothing|Smoothing" AlgebraicGeometry`: zero hits.
4. `msearch.py ... leanfinder "Formal power series ring in one variable and
   localization by powers of its variable"`: eight hits, including
   `LaurentSeries.of_powerSeries_localization`, confirming the standard localization
   description. The theorem uses the node's literal localization model, not a new ring.
5. `rg -n` over `lean/WeilConjectures` and `lean/Sheaf` for
   `IsLocalCompleteIntersection`, `PowerSeries.constantCoeff`, and curve/smoothing
   patterns found the recorded ring notion, existing affine-cover interfaces, and
   the consumer's proof-docstring citation, but no theorem stating the smoothing.
6. `grep -rn "lem-sfb-isolated-lci-curve-smoothing" lean/WeilConjectures` found no
   existing declaration. A search of both roots for `isolated_lci_curve_smoothing`
   and `proper_curve_isolated_lci_smoothing` also found no existing name.

No STATEMENT-DISPUTED finding or node fault. The stage-1 reviewed statement agrees
with 0E7Y; the additional finite-presentation wording is justified by its source note.
The source proof is not replaced: the theorem docstring follows the node's exact
local/Fitting/formal/algebraization route, including its zero-dimensional extension.

Validation: `scompile.py Q12 lem-sfb-isolated-lci-curve-smoothing` compiled this
file in both sandbox mode (6.7 s) and its actual library module mode (3.9 s) with
exit code zero and no diagnostics. All Lean lines have at most 100 characters;
`autoImplicit` is explicitly false and the only universe is explicitly declared.

## Second reading by Q12

Performed a fresh self-reading with the node, the source lemma and the completed
module open. No independent worker was started: the dispatcher's explicit instruction
for this task forbids starting other agents; the maintainer's independent review is
still required. This paragraph does not claim an independent second agent's review.

The source's four assumptions match `IsProper f`, `hlci`, `hdim`, and `hsmooth`.
Reading `hlci` conjunct by conjunct confirms that the open immersions cover X, that
all charts respect f over k, and that the finite-type instance passed to the existing
lci predicate belongs to that same k-algebra structure. Its quantification introduces
no second complete-intersection definition. Reading `hsmooth` confirms that the
exceptional points are closed and finite, with no imposed residue-field restriction.
The output quantifies a single g over the literal power-series ring. Flatness,
finite presentation and the correct H-projective predicate refer to that same g.
The two pullback maps are respectively constant coefficient and localization at X.
The equation for e uses the second projection to Spec k, so it really states a
k-isomorphism. Generic smoothness is on the second projection to the generic base,
not on the composite to Spec k[[t]]. Empty and dimension-zero cases remain in the
signature. No mismatch was found and no mathematical statement changed.
