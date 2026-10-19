## Worker report

The module `Sheaf.AlgebraicGeometry.LocalNoetherianApproximation` states
`AlgebraicGeometry.exists_local_noetherian_approximation`, with one theorem and
its entire proof `sorry`. There are no new definitions, auxiliary theorems,
dependency repairs, or changes to the natural statement. The node copy changes
only `lean`. The date follows `date -u +%F` (2026-10-17 on this machine).

Source checked: `literature/stacks-project/flat.tex`, label
`lemma-fibres-irreducible-flat-projective-nonnoetherian` (Tag 05FT), its first
proof paragraph, and `more-morphisms.tex` labels
`lemma-Noetherian-approximation-flat`,
`lemma-Noetherian-approximation-geometrically-reduced`,
`lemma-Noetherian-approximation-geometrically-irreducible`, and
`lemma-Noetherian-approximation-combine` (Tags 05FE, 05FG, 05FH, 05FL).
The theorem docstring carries all six steps of the DAG proof, including the
nonempty-fibre issue, the two constructible loci, eventual image containments,
and the canonical tensor maps. No statement fault or dispute was found.

Clause-by-clause correspondence:

- Commutative rings and the map `R → S`: `(R S : CommRingCat.{u}) [Algebra R S]`.
  The given map is `algebraMap R S`; an algebra structure on a commutative ring
  is precisely the data of this ring homomorphism, with its prescribed scalar
  action. No injectivity, nontriviality, or Noetherian condition is assumed.
- Finite presentation: `[Algebra.FinitePresentation R S]`.
- Flatness of the given ring map: `(hflat : (algebraMap R S).Flat)`.
- For every prime of `R`, geometric integrality of its fibre:
  `hfibres : ∀ p : PrimeSpectrum R, GeometricallyIntegral
  (Spec.map (CommRingCat.ofHom
  (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))))`.
  `Ideal.Fiber` is the existing `κ(p) ⊗[R] S`, canonically symmetric to the
  displayed `S ⊗[R] κ(p)`. Its canonical residue-field algebra map is the
  structure morphism of the fibre spectrum. `GeometricallyIntegral` means
  integral after every field extension, exactly the ring condition. For affine
  schemes integrality is the domain condition; it includes nonemptiness.
- Existence of rings `R₀`, `S₀` and their horizontal map:
  `∃ (R₀ S₀ : CommRingCat.{u}) (_ : Algebra R₀ S₀) ...`;
  the latter map is `algebraMap R₀ S₀`.
- The remaining two maps in the diagram are explicitly quantified as
  `(a : R₀ →+* R) (b : S₀ →+* S)`.
- `R₀` of finite type over the integers:
  `RingHom.FiniteType (Int.castRingHom R₀)`. This is the canonical, unique
  integer ring map, with no chosen or additional integer-algebra structure.
- `R₀ → S₀` of finite type:
  `RingHom.FiniteType (algebraMap R₀ S₀)`.
- Flatness of this map: `(algebraMap R₀ S₀).Flat`.
- Every model fibre geometrically integral: the identical fibre expression
  quantified over `p₀ : PrimeSpectrum R₀`, with `S₀` in place of `S`.
- The diagram is cocartesian, and recovers the original algebra, via
  `IsPushout (CommRingCat.ofHom (algebraMap R₀ S₀)) (CommRingCat.ofHom a)
  (CommRingCat.ofHom b) (CommRingCat.ofHom (algebraMap R S))`.
  Its four corners are `R₀`, `S₀`, `R`, `S`, in this order. Its commutativity
  is `b ∘ (R₀ → S₀) = (R → S) ∘ a`, for the original `R → S`.
  This is a universal-property assertion, not merely a commuting square or
  an unrelated ring equivalence. Mathlib's
  `CommRingCat.isPushout_tensorProduct` constructs the pushout as
  `S₀ ⊗[R₀] R`; uniqueness of the pushout therefore gives exactly the
  canonical recovery `S ≅ S₀ ⊗[R₀] R`, preserving both structure maps.
  The last recovery sentence of the node is the meaning of its cocartesian
  assertion, so it requires no redundant choice of an isomorphism.

Dependency interfaces used and read in the source:

- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`, its
  defining quotient/presentation signature and docstring (finite polynomial
  generators and finitely generated kernel).
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, defined using
  `Module.Flat` for the algebra structure of the ring map.
- `Mathlib.RingTheory.FiniteType`: the recorded `RingHom.FiniteType`, defined
  using `Algebra.FiniteType` (finitely generated top subalgebra).
- `Mathlib.AlgebraicGeometry.ResidueField`: the recorded
  `Scheme.residueField`, `Scheme.Hom.residueFieldMap`, and
  `Spec.residueFieldIso`. The last identifies the residue field at a spectrum
  point with the `Ideal.ResidueField` used by Mathlib's `Ideal.Fiber`.
  Thus the ring-level fibre notation uses the exact affine specialization
  of the recorded residue-field notion, rather than a second definition.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`: the recorded
  `AlgebraicGeometry.GeometricallyIntegral`; its definition through
  `geometrically IsIntegral` and the field-extension characterization in
  `Geometrically.Basic` were read.
- Mathlib's existing `Ideal.Fiber` and `CategoryTheory.IsPushout` are used
  directly; the tensor-product pushout signature was also read in
  `Mathlib.Algebra.Category.Ring.Constructions`.

Every already-stated proof dependency is imported privately, including finite
presentation descent, finite type subalgebra colimits, finite presentation
stability, eventual flatness, affine fibre products, radicial fibre comparison,
integral schemes, affine transition limits and constructible image containment.
The last module's current source was read with
`scompile.py --source WeilConjectures.AlgebraicGeometry.LimitContainedInConstructible`
because it was missing from the older local checkout. No module is imported for
`lem-trf-geometrically-reduced-fibre-locus` or
`lem-trf-geometrically-irreducible-fibre-locus`: neither yet has a `lean` or
`mathlib_match` record. They are proof prerequisites only, so neither is needed
to type this statement; their future modules can be added when stated.

Edge cases checked before writing:

- If `R` is the zero ring, its prime spectrum is empty and the fibre hypothesis
  is vacuous, as in the node. An algebra over it has zero target, and zero model
  rings give the expected instance of the existential conclusion. No explicit
  `Nontrivial` assumptions were inserted.
- If `R` is nonzero and a fibre is zero, its spectrum is empty. It fails
  `GeometricallyIntegral` because integral schemes are nonempty. Empty fibres
  therefore never pass as integral, either in the input or in the model.
- The identity algebra, a field base, and any positive characteristic fit the
  statement without additional assumptions. No relative dimension, properness,
  projectivity, smoothness, or finiteness as a module was introduced.
- All rings/schemes are in the common arbitrary universe `u`. Any pair of ring
  universes can be raised to their maximum; the finite type integer models fit
  this universe too. Geometric integrality uses Mathlib's standard universe
  convention and its existing field-extension quantification, with no smaller
  independent universe of test fields. All variables and `u` are explicitly
  bound. There are no `let` statements, hidden local notation, or new instances.

Searches (the prescribed wrapper recorded the service queries in searches.jsonl):

- LeanSearch: “A finitely presented flat algebra with geometrically integral
  fibers descends to a finitely generated ring over the integers”. Eight hits:
  finite presentation, flat descent, smooth descent and related notions; no
  theorem with the required hypotheses and conclusion. In particular
  `Algebra.Smooth.exists_finiteType` requires smoothness and does not match.
- LeanFinder: “Noetherian approximation of a finitely presented flat ring map
  preserving geometrically integral fibers”. Eight hits including
  `Algebra.Smooth.exists_finiteType`, flatness of smooth algebras, and finite
  presentation over Noetherian rings; none is the requested theorem.
- Loogle: `RingHom.Flat, Algebra.FinitePresentation, GeometricallyIntegral`.
  No hits; its index reports unknown identifier `GeometricallyIntegral`.
- Mathlib grep wrapper: `Noetherian.*approx|noetherian.*approx|geometrically.*[Ii]ntegral`
  in `RingTheory`: zero hits. Direct source inspection found the existing
  fibre and geometric definitions, which the statement uses.
- Direct `rg` over `WeilConjectures`, `lean/Sheaf`, and the upstream name table:
  `noetherian.*approx|Noetherian.*[Aa]pprox|lem-trf-local-noetherian-approximation|geometricallyIntegral`.
  This found scheme approximation and other geometric-integrality theorems,
  but no local ring approximation preserving these fibre conditions.
- Direct `rg` over Mathlib, upstream and `lean/Sheaf`:
  `exists_finiteType.*[Ii]ntegral|exists_flat.*[Ii]ntegral|local_noetherian_approximation|noetherian_approximation.*integral`.
  No hits. Searching upstream for the blueprint id also gave no hits.

Validation: prescribed `scompile.py Q113 lem-trf-local-noetherian-approximation`
compiled the delivered module separately against the published library. Both
sandbox and library checks were clean (4.6 s and 2.5 s respectively); no errors
or warnings. No proof was supplied beyond the expected theorem `sorry`.

## Second reading by Q113

No second reading by a worker: the dispatcher explicitly prohibits starting
other agents and asks the worker to deliver directly. The maintainer's
independent review reads the delivery. A final self-check matched every binder
and conjunct to the node as listed above, checked the orientation of the
pushout, and checked that the fibre conditions exclude empty fibres. It found
no mismatch and required no natural-statement correction.
