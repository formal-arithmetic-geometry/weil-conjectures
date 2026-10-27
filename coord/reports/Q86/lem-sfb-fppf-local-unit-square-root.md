## Worker report

The module `Sheaf.AlgebraicGeometry.FppfUnitSquareRoot` states
`AlgebraicGeometry.Scheme.exists_fppf_unit_square_root`, with its proof `sorry`.
The existing node is unchanged except for its `lean` record. There are no new
notions, new nodes, dependency repairs, or statement corrections.

Clause-by-clause rendering:

- Any scheme T: `(T : Scheme.{u})`, with arbitrary explicitly declared universe u.
- A global unit s: `(s : Γ(T, ⊤)ˣ)`, the units of the structure sheaf's global sections.
- A family of schemes and morphisms to T: existential `I : Type u`,
  `T' : I → Scheme.{u}`, and `f : ∀ i : I, T' i ⟶ T`.
- The family is an fppf covering:
  `Presieve.ofArrows T' f ∈ fppfPrecoverage T`. Mathlib's `fppfPrecoverage` is
  `Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)`; the read signature
  of `ofArrows_mem_precoverage_iff` identifies this membership with joint
  surjectivity and flatness plus local finite presentation of every member.
  Membership is in the precoverage itself, rather than merely its generated topology.
- Units on each member: `∃ r : ∀ i : I, Γ(T' i, ⊤)ˣ`.
- For every i, the square-root equation:
  `∀ i : I, (r i : Γ(T' i, ⊤)) ^ 2 = (f i).appTop (s : Γ(T, ⊤))`.
  The read definition `Scheme.Hom.appTop` is precisely the canonical ring map
  on global sections induced by f. Equality of the underlying ring elements
  states the requested unit equation, since the units inclusion is injective.
- No assumption that two is invertible, and no reducedness assumption: neither
  appears in the binders. No affine, Noetherian, nonempty or characteristic
  assumption appears either.

Statement dependencies read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, from
  `Mathlib.AlgebraicGeometry.Scheme`; the complete structure signatures and
  docstrings were read, together with `Scheme.Hom.appTop`.
- `def-pc-fppf-site`: `AlgebraicGeometry.Scheme.fppfPrecoverage` and
  `fppfTopology`, from `Mathlib.AlgebraicGeometry.Sites.Fpqc`. Its actual
  precoverage definition and covering-family membership criterion were read.
  The node's existing interface is usable without a repair or a new site.

Proof dependency imports follow the recorded interfaces: `Spec` and
`ΓSpecIso_naturality` in `Mathlib.AlgebraicGeometry.Scheme`; `AlgHom`,
`Ideal.Quotient.algebra`, `Ideal.Quotient.mkₐ` and ideal operations in
`Mathlib.Algebra.Algebra.Hom`, `Mathlib.RingTheory.Ideal.Quotient.Operations`
and `Mathlib.RingTheory.Ideal.Operations`; `Module.FaithfullyFlat` and
`RingHom.FaithfullyFlat` in `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`
and `Mathlib.RingTheory.RingHom.FaithfullyFlat`;
`PrimeSpectrum.comap_surjective_of_faithfullyFlat` in
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`; `Flat.SpecMap_iff` in
`Mathlib.AlgebraicGeometry.Morphisms.Flat`; `LocallyOfFinitePresentation` in
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`; `ΓSpec.adjunction`
in `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`; `Limits.pullback` and its
projections in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`;
and `Precoverage.mem_coverings_of_isPullback` in
`Mathlib.CategoryTheory.Sites.Precoverage`. These proof-only imports are plain
imports. The monic-quotient tensor-coordinate proof dependency has no recorded
Lean declaration or Mathlib match, so there is no published module to import
for that proof dependency. It is not needed to type the present statement.

The declaration docstring reproduces all four DAG proof steps with their node
references: the positive-rank monic quotient, its fppf affine spectrum, base
change along T → Spec Γ(T,O_T), and the section equation with explicit inverse.
The source was read in `literature/stacks-project/etale-cohomology.tex`,
`lemma-kummer-sequence-syntomic` (Tag 040N), including its cover construction.
The theorem specializes only its exponent to two, as the item requires.

Edge cases checked before writing:

- Empty T: its global sections ring can be zero; its unit group is still
  meaningful. The positive-degree quotient is free of rank two even over the
  zero ring, and the empty scheme admits its identity cover.
- Characteristic two: over F₂ with s=1 the quotient is nonreduced,
  F₂[x]/((x-1)²), but remains finite free and faithfully flat. The theorem does
  not substitute an étale cover for the required fppf one.
- Nonreduced T: neither the quotient construction nor its relation uses
  reducedness; e.g. s=1+ε over dual numbers is allowed.
- Nonaffine T: the proof uses base change along the canonical map to Spec of
  global sections; no affineness assumption is introduced.
- The existential index `I : Type u` includes the singleton produced by the
  source construction in every universe. There is no `Nonempty I` or `Finite I`
  restriction; an empty family covers only an empty T. This universe choice
  excludes no T or s, since one covering member suffices in the construction.

Searches actually run:

- `msearch.py ... leanfinder "Every global unit on an arbitrary scheme has a
  unit square root after an fppf covering including characteristic two"`:
  eight hits, including `LocallyRingedSpace.isUnit_res_toΓSpecMapBasicOpen`,
  `Scheme.Hom.cover_I₀`, and approximation cover definitions. None gives the
  stated square-root existence theorem.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.fppfPrecoverage, Units.map"`:
  successful response, zero hits.
- `msearch.py ... grep "square.root|kummer|exists.*sq.*fppf" AlgebraicGeometry`:
  successful response, zero hits.
- Direct `rg` searches of `lean/WeilConjectures` and `lean/Sheaf` for square
  roots, Kummer, and the exact blueprint id; focused searches of their
  AlgebraicGeometry directories found only unrelated square-zero statements,
  square tensor powers, and a field-theoretic Kummer obstruction. The exact
  blueprint id had no upstream occurrence.
- Direct `rg -l` over Mathlib, both project roots, and
  `dag/lean_names_upstream.json` for `square roots of units`,
  `square root.*fppf`, `fppf.*square root`, and the chosen declaration name:
  no existing matching declaration.

No statement dispute or node fault was found. All universes and variables are
explicitly bound; the file starts with `module` and exposes its declaration
through `@[expose] public section`. Validation uses the prescribed server
compiler and delivery preflight only.

## Second reading by Q86

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
