## Worker report

The module `Sheaf.TraceFormula.GeometricallyIrreducibleFibreLocus` states
`AlgebraicGeometry.geometricallyIrreducible_fibre_locus_constructible`.  It uses one
universe `u` for the two commutative rings, as is standard for the affine spectrum
construction and does not restrict the mathematical rings.  The hypotheses render as
follows:

- `{A B : Type u}` introduces the source and target rings.
- `[CommRing A]` and `[CommRing B]` make both objects commutative rings.
- `[Algebra A B]` is the ring homomorphism `A → B`.
- `[Algebra.FinitePresentation A B]` is exactly finite presentation of `B` over `A`.

The conclusion renders the fibre locus clause by clause. `p : PrimeSpectrum A` is a
prime of `A`; `p.asIdeal.ResidueField` is its residue field; and
`p.asIdeal.Fiber B` is the canonical tensor fibre
`κ(p) ⊗[A] B`.  The map
`algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B)` induces
`Spec.map (CommRingCat.ofHom ...)`, whose source is the spectrum of the fibre and
whose target is the spectrum of the residue field.  The predicate
`AlgebraicGeometry.GeometricallyIrreducible` is Mathlib's geometric irreducibility
predicate (including irreducibility after every field-valued base change), matching
`def-pc-geometrically-irreducible`.  The outer predicate
`Topology.IsConstructible` is the constructibility of the displayed subset of
`PrimeSpectrum A`, matching `def-weil-constructible-subset`.  There are no flatness or
Noetherian hypotheses in the Lean statement, as required by the node.

The statement dependencies and declarations used are:

- `def-weil-pbc-finitely-presented-algebra`: Mathlib
  `Algebra.FinitePresentation` from `Mathlib.RingTheory.FinitePresentation`.
- `def-weil-residue-field`: Mathlib `AlgebraicGeometry.Scheme.residueField` from
  `Mathlib.AlgebraicGeometry.ResidueField`; the affine prime form uses the equivalent
  `Ideal.ResidueField` in `p.asIdeal.ResidueField`.
- `def-pc-geometrically-irreducible`: Mathlib
  `AlgebraicGeometry.GeometricallyIrreducible` from
  `Mathlib.AlgebraicGeometry.Geometrically.Irreducible`.
- `def-weil-affine-spectrum`: Mathlib `AlgebraicGeometry.Spec` and `Spec.map` from
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-constructible-subset`: Mathlib `Topology.IsConstructible` from
  `Mathlib.Topology.Constructible`.

Edge cases checked: the displayed set may be empty; no nonemptiness of `Spec A` or of
any fibre is assumed; a zero fibre ring is handled by Mathlib's geometric
irreducibility predicate; and no Noetherian or flatness condition has been inserted.
The typeclass finite-presentation hypothesis is the only finiteness assumption.

Searches for an existing declaration were made with:

- `msearch.py ... leanfinder "constructible locus of primes where the geometric fibre
  of a finitely presented ring map is geometrically irreducible"`: returned only general
  Chevalley constructibility declarations (`PrimeSpectrum.isConstructible_range_comap`,
  `PrimeSpectrum.isConstructible_comap_image`) and no fibre-locus theorem.
- `msearch.py ... loogle "Topology.IsConstructible, GeometricallyIrreducible,
  Ideal.Fiber"`: no hits (`GeometricallyIrreducible` was not found by that query).
- `msearch.py ... grep "GeometricallyIrreducible|fibre.*locus"
  Mathlib/AlgebraicGeometry`: no direct hit.
- `rg -n "geometricallyIrreducible_fibre_locus_constructible|lem-trf-geometrically-
  irreducible-fibre-locus"` in the source and existing `lean/Sheaf`: no declaration;
  only a prose reference in `Sheaf/AlgebraicGeometry/LocalNoetherianApproximation.lean`.

The file compiled cleanly with `scompile.py`; its only postponed proof is `sorry`.

## Second reading by Q03

I reread the node and the module independently.  The finite-presentation, commutative
ring, and algebra hypotheses are all present.  For each prime `p`, the module constructs
the canonical residue-field tensor fibre and its canonical spectrum morphism, then
asserts exactly that the set of primes whose geometric fibre is geometrically
irreducible is constructible.  The conclusion has no extra clause and no hypothesis
about flatness or Noetherianity.  The source and blueprint identifiers are present in
both the module and declaration docstrings, and the proof is postponed with `sorry`
only.
