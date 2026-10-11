## Worker report

The module `Sheaf.AlgebraicGeometry.NormalizationProperties` states
`AlgebraicGeometry.Scheme.normalization_properties` for an integral scheme `X` over a
field `k`, with explicit structure morphism `q : X ⟶ Spec k` and
`[LocallyOfFiniteType q]` expressing finite type. Its conclusion is a conjunction:

* `IsFinite X.fromNormalization` renders finiteness of ν.
* `Surjective X.fromNormalization` renders surjectivity of ν.
* `Birational X.normalization X` renders birationality.
* `(IsProper q → IsProper (X.fromNormalization ≫ q))` renders properness of the
  normalization whenever X is proper over k.
* `topologicalKrullDim X.normalization = topologicalKrullDim X` renders equality of
  dimensions.
* For every open `U : X.Opens`, the hypothesis
  `∀ x ∈ U, IsIntegrallyClosed (X.presheaf.stalk x)` expresses normality of U,
  and the conclusion `IsIso (X.fromNormalization ∣_ U)` is the induced isomorphism
  over U.
* `PerfectField k → topologicalKrullDim X = 1 → Smooth (X.fromNormalization ≫ q)`
  renders smoothness in dimension one over a perfect field.

The normalization notion is the dependency declaration
`WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`,
`AlgebraicGeometry.Scheme.normalization` (and its canonical map
`AlgebraicGeometry.Scheme.fromNormalization`). The clause-level source statements
are supplied by the recorded declarations in that same module:
`AlgebraicGeometry.Scheme.isFinite_fromNormalization_of_locallyOfFiniteType`,
`AlgebraicGeometry.Scheme.surjective_fromNormalization`,
`AlgebraicGeometry.Scheme.exists_isIso_fromNormalization_restrict`,
`AlgebraicGeometry.Scheme.topologicalKrullDim_normalization`, and
`AlgebraicGeometry.Scheme.isIso_fromNormalization_restrict`; smoothness is supplied
by `WeilConjectures.AlgebraicGeometry.Regular`,
`AlgebraicGeometry.Scheme.smooth_fromNormalization_comp`.

Edge cases checked: the open U may be empty (the universal condition and isomorphism
restriction are then vacuous/trivial); dimension one is required exactly in the
smoothness implication; properness is conditional and is not imposed on X; no
nonemptiness hypothesis is added, so the empty scheme remains covered by the
statement.

Searches made: `msearch.py ... leanfinder` for normalization finiteness,
birationality, normal-locus isomorphism, and smooth curves (normalization
implementations only); `msearch.py ... loogle` for `normalization, Birational,
IsFinite, IsProper, Smooth` (no combined declaration); grep of Mathlib
`AlgebraicGeometry/Normalization.lean` and `AlgebraicGeometry/Birational` (only
component declarations); `rg` over `WeilConjectures` and project `lean/Sheaf`
(no existing combined statement). The module was compiled with `scompile.py` and
reported no errors or warnings.

## Earlier second reading (a previous round; superseded)

The recorded signature was checked against the compiled module. Every binder is explicit: a field k, integral scheme X, structure morphism q, and locally finite type instance. The conjunction renders each clause of the blueprint statement directly; the properness and perfect-field hypotheses occur only in their stated implications. The normal-open condition is expressed by integrally closed stalks, exactly the condition accepted by the dependency declaration `isIso_fromNormalization_restrict`. No additional hypotheses or conclusions are present.

## Second reading by F1

I read the blueprint node, its source place, the dependency declarations, and the
module independently. The objects and hypotheses render as follows:

* An index field `k : Type u` with `[Field k]` is rendered by the theorem binders.
* An integral scheme `X : Scheme.{u}` is rendered by `{X : Scheme.{u}} [IsIntegral X]`.
* The structure morphism `q : X ⟶ Spec (.of k)` is explicit. Finite type over `k`
  is rendered by `[LocallyOfFiniteType q] [QuasiCompact q]`; the quasi-compact
  instance was added in this reading because finite type includes quasi-compactness.
* The normalization and its map are exactly the dependency declarations
  `Scheme.normalization` and `Scheme.fromNormalization`.
* Clause (a) is the conjunction of `IsFinite`, `Surjective`, `Birational`, the
  implication `IsProper q → IsProper (fromNormalization ≫ q)`, and equality of
  `topologicalKrullDim`; these are the exact five terms in the first conjunction.
* Clause (b) quantifies over every `U : X.Opens`, assumes every stalk on `U` is
  `IsIntegrallyClosed`, and concludes `IsIso (X.fromNormalization ∣_ U)`, the
  recorded restriction morphism (the pullback restriction in the source).
* Clause (c) is the implication from `PerfectField k` and dimension equality
  `topologicalKrullDim X = 1` to `Smooth (X.fromNormalization ≫ q)`.

The empty open is covered by the universal stalk hypothesis and restriction
isomorphism theorem; no nonemptiness assumption is added. The zero and empty
scheme cases are not excluded by the binders. Dimension zero is not claimed to
be smooth; smoothness is conditional on dimension one. The field characteristic
is unrestricted except for the explicit perfectness hypothesis in (c), and all
objects use the shared universe `u`.

I searched Mathlib, `WeilConjectures`, and `lean/Sheaf` with `rg`, and ran the
recorded LeanFinder/Loogle searches for normalization, finiteness, birationality,
normal-locus isomorphisms, and smooth normalized curves. Only the separate
normalization declarations and the three cited dependency results exist; no
combined statement exists. The dependency node `def-sc-normalization` records the
single canonical normalization definition.

The mismatch found was that the worker theorem had only
`[LocallyOfFiniteType q]`, which states a weaker finite-type hypothesis than the
node's finite type assumption. I added `[QuasiCompact q]` and updated the recorded
signature. I also expanded the statement docstring with the proof steps and
source blueprint marker. No other clause or dependency was changed.
