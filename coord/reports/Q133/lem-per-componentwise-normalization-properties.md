## Worker report

The module `Sheaf.AlgebraicGeometry.ComponentwiseNormalizationProperties` states
`AlgebraicGeometry.Scheme.componentwiseNormalization_properties`, with its whole proof
`sorry`. No definitions, auxiliary theorems, or nodes are introduced. The node is unchanged
except for `lean`.

I read the node, every statement dependency's statement and Lean/mathlib record, the
recorded signatures and their docstrings, and Stacks `morphisms.tex` at
`lemma-normalization-localization` (035K), `equation-generic-points`,
`lemma-description-normalization` (035P), `lemma-normalization-normal` (035Q), and
`lemma-normalization-trivial` (0H7D). The generic construction uses residue fields even
for nonreduced schemes. The recognition clause uses the reductions footnote of 035Q.

Hypothesis and clause correspondence:

- The arbitrary scheme is `(X : Scheme.{u})`, with explicitly bound universe `u`.
  `[IsLocallyNoetherian X]` is precisely the sole hypothesis on X. In particular there
  is no reducedness, excellence, nonemptiness, quasi-compactness, or finite-normalization
  assumption.
- The named componentwise normalization and its canonical map are the dependency's
  `X.reducedNormalization` and `X.fromReducedNormalization`, with no copied construction.
- Clause (1), normality: `∀ x : X.reducedNormalization, IsDomain (...) ∧
  IsIntegrallyClosed (...)` says every local ring is an integrally closed domain. This
  is the normal-scheme convention already used by the recognition dependency.
- Clause (1), integral and surjective: `IsIntegralHom X.fromReducedNormalization` and
  `Surjective X.fromReducedNormalization`, using the recorded Mathlib morphism classes.
- Clause (1), generic-point bijection: `Set.BijOn X.fromReducedNormalization` between
  the two sets `{x | ∃ C ∈ irreducibleComponents _, IsGenericPoint x C}`. `BijOn`
  includes that every source generic point maps to a target generic point, injectivity
  on this set, and surjectivity onto target generic points.
- Clause (1), the entire generic fibre: for every `η` generic for an irreducible component,
  `IsIso (pullback.snd X.fromReducedNormalization (X.fromSpecResidueField η))`.
  The pullback is exactly X^ν ×_X Spec κ(η); its second projection is its canonical
  κ(η)-structure map. Saying this map is an isomorphism identifies the entire fibre
  canonically with Spec κ(η) over κ(η), rather than only identifying points or residue
  fields. Its inverse is determined uniquely by the canonical structure map.
- Clause (2), every open subscheme: `∀ U : X.Opens`, with no quasi-compactness condition.
  The pullback uses the recorded open inclusion `U.ι` and scheme `U.toScheme`.
  `∃! e : pullback X.fromReducedNormalization U.ι ≅ U.toScheme.reducedNormalization`
  together with `e.hom ≫ U.toScheme.fromReducedNormalization = pullback.snd ...`
  is the canonical normalization identification over U. Uniqueness expresses
  canonicity: an automorphism of a normalization over its base is the identity,
  by agreement on each component function field.
- Clause (2), normal opens: the implication from domain/integrally closed stalks on
  `U.toScheme` to `IsIso (pullback.snd X.fromReducedNormalization U.ι)` states exactly
  that the restricted normalization morphism itself is an isomorphism.
- Clause (3), the source: `∀ (Z : Scheme.{u}) (_ : IsLocallyNoetherian Z)` and its
  normality hypothesis `∀ z : Z, IsDomain (...) ∧ IsIntegrallyClosed (...)` include
  both assumptions on Z. The scheme universe is explicit and no index set is restricted.
- Clause (3), the morphism: `(f : Z ⟶ X) (_ : IsIntegralHom f)` is the arbitrary
  integral map in the statement, not a finite map or an arbitrary chosen comparison.
- Clause (3), generic bijection: the same `Set.BijOn f` formulation between Z and X.
- Clause (3), residue fields: for each component generic point `z`,
  `IsIso (f.residueFieldMap z)` is precisely the induced map κ(f(z)) → κ(z) being
  an isomorphism. The target point is the actual image; no independent residue map
  or identification is assumed.
- Clause (3), existence and uniqueness: `∃! e : Z ≅ X.reducedNormalization,
  e.hom ≫ X.fromReducedNormalization = f` is a unique scheme isomorphism over X.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.ReducedNormalization`: `Scheme.reducedNormalization` and
  `Scheme.fromReducedNormalization`. I read the component construction by its vanishing
  ideal and coproduct of the function-field normalizations, including the empty coproduct.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`;
  the proof also uses `finite_irreducibleComponents_of_isNoetherian` from this module.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, together
  with `IsDomain`, applied to scheme stalks to express normality inline.
- `Mathlib.AlgebraicGeometry.Morphisms.Integral`: `AlgebraicGeometry.IsIntegralHom`
  (the integral half of the finite/integral dependency's record).
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, and `Scheme.fromSpecResidueField`.
- `Mathlib.AlgebraicGeometry.Pullbacks`, with the dependency's
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.snd`
  and existence of scheme pullbacks.
- `Mathlib.Topology.Sober`: `IsGenericPoint`; `Mathlib.Topology.Irreducible`:
  `irreducibleComponents` (this dependency is a Mathlib leaf and needs no Lean repair).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: open-scheme inclusions and
  `isOpenImmersion_stableUnderBaseChange`.
- Proof-only imports: `Mathlib.AlgebraicGeometry.Gluing` (`Scheme.Cover.glueMorphisms`
  and uniqueness by `hom_ext`) and `Sheaf.AlgebraicGeometry.IntegralNormalGenericRecognition`
  (`Scheme.existsUnique_iso_reducedNormalization_of_integral_normal_generic`). The latter's
  entire signature and proof docstring were read; it even allows Z not locally Noetherian,
  while this item explicitly retains that source hypothesis.

The three remaining proof dependencies, `lem-sfb-componentwise-normalization-generic-properties`,
`lem-sfb-normalization-generic-residue-affine-charts`, and
`lem-sfb-normalization-normal-locally-finite`, currently have no recorded declarations;
there are therefore no modules to import for those proof steps. Their statements and
names remain in the docstring proof plan; no definitions needed by this statement are missing.

Edge cases checked before drafting:

- Empty X: the normalization is the empty coproduct, its stalk and generic conditions
  are vacuous, and its map to X is an integral surjection. A map Z → ∅ forces Z empty,
  so the recognition isomorphism is unique. No `Nonempty` instance is required.
- Empty U: its normalization and pullback are empty; the over-U isomorphism is unique,
  and the restricted map is an isomorphism. The normality premise is vacuous.
- Nonreduced X = Spec(k[ε]/ε²): its normalization is Spec k. The generic residue fibre
  is Spec k; using the residue field rather than the nonreduced generic stalk gives
  exactly the asserted canonical isomorphism. No assertion that X itself is reduced
  appears.
- Crossing components Spec(k[x,y]/(xy)): normalization separates the two generic points,
  so no injectivity on all underlying points is asserted. The generic fibres are whole
  residue-field spectra. Opens meeting only one component retain the correct generic set.
- Normal X (including a disconnected normal scheme): normalization is canonically the
  identity over X; the open clause therefore gives isomorphisms on every open.
- Non-quasi-compact locally Noetherian schemes and opens are allowed. Only the proof
  uses finite component sets on quasi-compact affine neighbourhoods.

Searches made (the wrapper records actual outputs):

- `msearch.py leanfinder`, query: "Componentwise normalization of a locally Noetherian
  scheme is normal integral surjective induces generic point bijection commutes with
  open restriction and uniquely recognizes normal integral generic isomorphisms".
  Eight hits, all concerning Mathlib's relative normalization of a morphism; none
  states the three-part theorem for the componentwise construction.
- `msearch.py loogle`, query: "AlgebraicGeometry.Scheme.normalization, IsIntegralHom,
  IsNormal". Zero hits; Loogle reported unknown identifier
  `AlgebraicGeometry.Scheme.normalization`.
- `msearch.py grep`, query: `reducedNormalization|normalization.*(open|generic)|generic.*normalization`
  in `AlgebraicGeometry`. Ten hits in relative-normalization and Zariski-main files;
  no exact statement.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `reducedNormalization|componentwiseNormalization|genericRecognition` found the dependency
  construction, smooth/étale pullback statements, and the recognition proof dependency,
  but not this combined statement. These are used, not redefined.
- Search for the exact node id in `lean/WeilConjectures` returned no match. Searches
  for the proposed declaration name in both Lean trees and `dag/lean_names_upstream.json`
  returned no match. No repair note for this item exists in `coord/repair-notes`.

Validation: the prescribed `scompile.py` compiled this file both as its sandbox module
and its intended library module successfully. No errors or non-sorry warnings occurred.
There is no statement correction or STATEMENT-DISPUTED finding.

## Second reading by Q133

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
