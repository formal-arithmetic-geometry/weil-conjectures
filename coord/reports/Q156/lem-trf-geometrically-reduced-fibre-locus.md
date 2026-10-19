## Worker report

The module `Sheaf.AlgebraicGeometry.GeometricallyReducedFibreLocus` states
`AlgebraicGeometry.geometricallyReduced_fibre_locus_constructible_baseChange`, with
proof `sorry`. No definition, auxiliary theorem, new node or dependency repair is needed.
The natural-language node is unchanged.

Clause-by-clause correspondence:

- Commutative rings and the ring map A → B are `(A B : Type u) [CommRing A]
  [CommRing B] [Algebra A B]`; the map is `algebraMap A B`. Giving an algebra structure
  is equivalent to giving a unital homomorphism between these commutative rings.
- Finite presentation is precisely `[Algebra.FinitePresentation A B]`, the recorded
  declaration of def-weil-pbc-finitely-presented-algebra, with no Noetherian assumption.
- A prime is `p : PrimeSpectrum A`. Its residue field is `p.asIdeal.ResidueField`.
  `Mathlib.AlgebraicGeometry.ResidueField` supplies the recorded scheme residue field
  and `Spec.residueFieldIso`, identifying it with this ring residue field.
- `p.asIdeal.Fiber B` is Mathlib's existing abbreviation `κ(p) ⊗[A] B`.
  Tensor symmetry canonically identifies this with the node's `B ⊗[A] κ(p)`, with
  the same κ(p)-algebra structure. In particular the structure map used here sends
  `c` to `c ⊗ 1`, corresponding to `1 ⊗ c` in the node's ordering.
- Geometric reducedness is the dependency's `AlgebraicGeometry.GeometricallyReduced`
  applied to `Spec.map (CommRingCat.ofHom (algebraMap κ(p) (p.asIdeal.Fiber B)))`.
  By `geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms`, this means that the
  spectrum is reduced after every field extension of κ(p), exactly as requested.
- The first conjunct is `Topology.IsConstructible` of the set comprehension of those
  primes, using def-weil-constructible-subset's existing Boolean-algebra definition.
- The second conjunct quantifies `∀ (A' : Type u) [CommRing A'] [Algebra A A']`.
  This ranges over all ring maps A → A'; no flatness, injectivity, or finite
  presentation is required of that map.
- The base-changed algebra is literally `B ⊗[A] A'`. The explicit application of
  `Algebra.TensorProduct.rightAlgebra` supplies its canonical A'-algebra structure
  (a' maps to 1 ⊗ a'). The `@id` application is just an explicit instance argument;
  it adds no hypothesis and makes no arbitrary choice.
- The equality is between the same fibre-locus comprehension for this base-changed
  algebra and `PrimeSpectrum.comap (algebraMap A A') ⁻¹'` of the original locus.
  `PrimeSpectrum.comap` is the underlying map of the recorded `Spec.map`, so it is
  exactly inverse image along Spec a. Equality gives both inclusions.
- There are no flatness, injectivity, Noetherian, nonemptiness, or characteristic
  hypotheses. All universes and variables are bound explicitly. A common universe
  for the three rings can be enlarged to contain any given triple; the geometric
  predicates use the same ambient scheme universe, so field tests are not vacuous.

Statement dependency declarations read and used:

- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, and the affine identification `Spec.residueFieldIso`.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`: imports and exposes the recorded
  `GeometricallyReduced` from `Mathlib.AlgebraicGeometry.Geometrically.Reduced`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec` and `Spec.map` (transitively imported).
- `Mathlib.Topology.Constructible`: `Topology.IsConstructible`.
- `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`: `Ideal.Fiber`, the existing
  residue-field tensor product, and the canonical tensor algebra structures.

Proof-dependency imports retain the node's proof route: finite-presentation and
quasi-separated morphisms (including quasi-compactness and affine qcqs), affine
pullbacks (`pullbackSpecIso`), scheme properties (sobriety), polynomial Noetherianity,
finite-type Noetherianity, multivariate polynomial rings, ideal quotients, and
`WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits`
(`CommRingCat.isColimitFgSubalgebraCocone`). The three stated side dependencies are
`Sheaf.TraceFormula.GeometricReducedFibreLocusBaseChange`
(`geometricReduced_fibre_locus_baseChange`),
`Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`
(`Scheme.IdealSheafData.reduced_induced_closed_subscheme`), and
`Sheaf.AlgebraicGeometry.NoetherianConstructibleSubsetCriterion`
(`constructible_of_noetherian_affine_cover`). The algebraic-closure test and generic
constancy proof nodes currently have no recorded declaration, so no import is
invented for them. Their mathematical roles are included in the proof docstring.
No statement dependency lacks a usable interface.

The source was read in `literature/stacks-project/more-morphisms.tex`, the full
statements and proofs of `lemma-base-change-fibres-geometrically-reduced` (0576)
and `lemma-geometrically-reduced-constructible` (0579). In the affine case the latter
is global constructibility; the coefficient-ring descent and generic alternatives
in the node's eight-step proof are reproduced in the theorem docstring.

Edge cases checked before drafting:

- A zero ring has empty prime spectrum; its constructibility and base-change clauses
  cause no missing point or excluded case.
- B = 0 gives empty fibres. The geometric-reducedness predicate accepts the empty
  scheme (all local rings reduced), so the locus is the whole base.
- For the identity A → A every fibre is a field and remains reduced after field
  extension; the locus is the whole base, also after arbitrary base change.
- For B = k[ε]/(ε²) over a field, the sole fibre is not geometrically reduced, so the
  locus is empty, consistent with the definition.
- Non-flat maps, quotient maps, the identity base change, zero base change, and all
  characteristics are retained. Empty fibres are never excluded by irreducibility
  or a nontriviality condition.

Searches for an existing statement:

- `msearch.py leanfinder`, query “For a finitely presented algebra the geometrically
  reduced fibre locus in the prime spectrum is constructible and commutes with
  arbitrary base change”: eight hits, including Chevalley image constructibility,
  `Algebra.IsGeometricallyReduced`, and algebraic-closure criteria; no fibre-locus theorem.
- `msearch.py loogle`, query `Algebra.IsGeometricallyReduced, Topology.IsConstructible`:
  zero hits.
- `msearch.py grep`, query `constructib.*(reduced|irreducible)|geometric.*constructib|0579`
  in `AlgebraicGeometry`: zero hits.
- `rg` of upstream `WeilConjectures` and the side `lean/Sheaf` for
  `geometrically.*[Rr]educed|geometricallyReduced|geometricReduced`: definitions,
  smoothness/field criteria, scheme base-change equality, and scheme constructibility.
  The latter scheme theorem cites this ring theorem in its proof and is not an exact
  existing statement of the present combined ring result.
- `grep -rn` for the item id in upstream `WeilConjectures`: no hits.
- Search of `dag/lean_names_upstream.json` for the item and selected declaration:
  no hits. No duplicate notion or declaration is introduced.

Validation: the prescribed `scompile.py` compiled the module as sandbox and library
source, including the needed side overlay. Both checks passed without errors or
warnings. The theorem is the only declaration and its proof is `sorry`, as required
for stage 2. There is no statement dispute or correction.

## Second reading by Q156

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
