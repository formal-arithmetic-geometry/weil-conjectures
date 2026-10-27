## Worker report

The module `Sheaf.RingTheory.SyntomicSmoothComposition` states the three clauses of
`lem-sfb-syntomic-smooth-composition`, as `Algebra.syntomic_comp`,
`Algebra.syntomic_of_smooth`, and `Algebra.syntomic_of_etale_spec`. Each proof is
`sorry`. There are no new definitions, dependency modules, or statement changes.
Only the item's `lean` field changes. The primary signature is copied verbatim
from the file; `lean.declarations` records all three clauses.

Source read: `literature/stacks-project/algebra.tex`, definition-lci (00SL),
lemma-composition-syntomic (00SZ), lemma-smooth-syntomic (00TA), and
lemma-etale-standard-smooth (00U9). These respectively define the three syntomic
conditions, give composition, make smooth maps syntomic, and make etale maps
standard smooth. Also read the recorded declarations and docstrings of all six
statement dependencies and the affine etale criterion used by the proof.

Hypothesis and conclusion correspondence:

- Commutative rings R, S, T: the independent binders `R : Type u`, `S : Type v`,
  `T : Type w` and their `CommRing` instances. There is no nontriviality,
  Noetherian, base-field, or characteristic assumption.
- The two given ring maps: `[Algebra R S]` and `[Algebra S T]`. The extra
  `[Algebra R T] [IsScalarTower R S T]` specifies their composite. Every pair of
  unital ring maps supplies these structures canonically; it imposes no further
  condition on the pair. In particular, the R action on T cannot be unrelated
  to the composite.
- Flatness of each input: `[Module.Flat R S]` and `[Module.Flat S T]`, exactly
  the module form in the recorded flat-ring-map node. `RingHom.flat_algebraMap_iff`
  identifies this with flatness of the corresponding ring map.
- Finite presentation of each input: `[FinitePresentation R S]` and
  `[FinitePresentation S T]`, using the recorded `Algebra.FinitePresentation`.
- Every fibre of the first input is lci: `hRS : ∀ p : PrimeSpectrum R,
  IsLocalCompleteIntersection p.asIdeal.ResidueField (p.asIdeal.Fiber S)`.
  The second input is the same expression with base S and target T, in `hST`.
  `Ideal.Fiber` is the abbreviation `κ(p) ⊗[R] S`. Tensor symmetry identifies
  this with the source's `S ⊗[R] κ(p)` as a κ(p)-algebra. The scalar structure
  is the canonical left-factor structure, not an arbitrary one.
- The composite is syntomic: the conclusion existentially supplies its finite
  presentation instance, then asserts `Module.Flat R T` and the same lci
  predicate at every prime of R. The existential class binder lets the existing
  finite-presentation base-change instance supply the finite-type fibre instance
  required by `IsLocalCompleteIntersection`; it does not assume finite
  presentation in advance or turn the claim into an implication.
- Every smooth ring map: `syntomic_of_smooth` has only the two commutative rings,
  their R-algebra structure, and `[Smooth R S]`, using the dependency's exact
  Mathlib notion. Its conclusion explicitly gives flatness, finite presentation,
  and lci fibres. The finite-type instances are consequences of smoothness's
  finite-presentation field and base change.
- Every ring map with etale spectrum morphism: `syntomic_of_etale_spec` takes
  only R, S, their algebra structure, and the hypothesis
  `AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map
  (CommRingCat.ofHom ((algebraMap R S).ulift.{v, u})))`.
  `RingHom.ulift` is the actual given homomorphism conjugated by the canonical
  `ULift.ringEquiv` isomorphisms. This puts both rings in universe `max u v`
  and permits the exact scheme-level etale notion without equating u and v.
  It is the same affine morphism up to canonical isomorphism; no smoothness,
  flatness, or finite-presentation assumption is inserted. Its conclusion gives
  finite presentation, flatness, and all lci fibres of the original rings.

Dependency declarations used:

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`,
  `RingHom.flat_algebraMap_iff`, and its imported `Module.Flat`.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`.
- `WeilConjectures.RingTheory.CompleteIntersectionOverField`:
  `Algebra.IsLocalCompleteIntersection` (and its underlying
  `Algebra.IsGlobalCompleteIntersection`). The full definitions were read:
  the zero ring is allowed, and the local predicate includes its finite-type
  instance and a principal-open cover by global complete intersections.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`. The affine identification
  `AlgebraicGeometry.Spec.residueFieldIso` identifies these with the
  `Ideal.ResidueField` used in `Ideal.Fiber`; the latter is imported from
  `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`.
- `Mathlib.RingTheory.Smooth.Basic`: `Algebra.Smooth`. Its formal smoothness
  field is projectivity of differentials and vanishing of `H1Cotangent`, and
  finite presentation gives the finite condition, as the dependency records.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
  Its definition and the `HasRingHomProperty` instance were read. The proof
  uses `AlgebraicGeometry.HasRingHomProperty.Spec_iff` to recover ring etaleness.
- `Mathlib.RingTheory.FiniteStability`: finite-presentation and finite-type
  base-change instances on the actual tensor fibres.
- `Mathlib.Algebra.Ring.ULift`: `RingHom.ulift`, `ULift.ringEquiv`.

The module imports the stated proof dependencies as plain imports, using the
current upstream modules where a retired Sheaf path no longer exists. In
particular the relative-presentation definition is imported from
`WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation`;
its old recorded Sheaf module was confirmed unavailable with `scompile.py --source`.
The base-change proof module `Sheaf.Paper.RelativeGlobalCompleteIntersectionBaseChange`
is present, and its current server source was read with `scompile.py --source`.
The sole proof dependency lacking a Lean record or Mathlib match is
`lem-trf-relative-ci-principal-cover-syntomic-gluing`; no module can yet be
imported for it. It is needed only to prove this node, not to state it. The
seven proof steps, including this pending gluing input, are explained in the
three theorem docstrings. The statement dependencies themselves are all usable
and are not repaired or duplicated.

Edge cases checked before writing:

- Zero target rings and zero fibres: retained. The lci definition allows a zero
  global complete intersection and an empty principal-open cover. No
  `Nontrivial` hypothesis excludes them.
- Zero base: there are no primes, but flatness and finite presentation remain
  present; a unital algebra over it is again zero. The fibre quantifier is
  correctly empty.
- Identity maps, polynomial algebras, and localizations at one element, including
  at zero: all lie in the quantified class. Identity and polynomial fibres have
  zero equations; localization at zero has empty spectrum.
- The dual-number tower `k -> k[x]/(x²) -> (k[x]/(x²))[y]/(y²)` is finite free
  in each step and has complete-intersection fibres. Its composite remains a
  complete intersection despite being nonsmooth. No smoothness assumption is
  hidden in the composition clause.
- Arbitrary non-Noetherian bases and arbitrary characteristics are allowed.
- All three ring universes are independent in composition; the etale clause
  uses canonical lifts to a common maximum rather than an equality of universes.

Searches actually run via `msearch.py`:

- LeanSearch: `Syntomic ring homomorphisms compose and smooth ring maps are syntomic`.
  Eight hits, including `RingHom.Smooth`, `RingHom.Smooth.comp`, smooth and flat
  composition results; none states the syntomic assertion.
- LeanFinder: `Composition of syntomic ring homomorphisms; smooth and etale ring
  homomorphisms are syntomic`. Eight hits, including standard-smooth composition,
  smooth composition and etale composition; no syntomic statement.
- Loogle: `Algebra.Smooth, Algebra.Etale`. Two hits:
  `Algebra.Etale.instSmooth` and `Algebra.Etale.iff_formallyUnramified_and_smooth`.
  These help the final proof step but do not give lci fibres or this statement.
- Mathlib grep: `Syntomic|syntomic` in `RingTheory`: zero hits.
- Direct `rg` on `lean/WeilConjectures` and `lean/Sheaf`: syntomic local
  presentation, polynomial-kernel, lifting, descent, and fibre-comparison
  interfaces exist, but no composition theorem or named syntomic predicate.
  The exact item-id search in `WeilConjectures` gave no hit. Searches for all
  three proposed names, including in `dag/lean_names_upstream.json`, gave no hit.

Validation: `scompile.py NW lem-sfb-syntomic-smooth-composition` compiled this
single module both under the sandbox module name and the intended library module
name, in 4.6 and 6.5 seconds respectively, with no errors or non-sorry warnings.
No statement dispute or statement correction was needed.

## Second reading by NW

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
