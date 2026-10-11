## Worker report

The module `Sheaf.RingTheory.EssentiallyFinitePresentationOverIntermediate` states
`RingHom.essentially_finite_presentation_over_intermediate`, with `sorry` as its only proof.
It introduces no new definitions. The compound condition "essentially of finite presentation"
is expanded into its localization presentation, as in the node and Mathlib's Smooth/Fiber.lean.
The item's JSON is unchanged except for `lean`; there are no new nodes or dependency modules.

Hypothesis and conclusion correspondence:

- The commutative rings R, S, S' are `{R : Type u}`, `{S : Type v}`, `{T : Type w}`
  with the three `CommRing` instances; T denotes S'. The named maps are
  `(φ : R →+* S)` and `(ψ : S →+* T)`.
- S is essentially of finite type over R via φ: `(hS : φ.EssFiniteType)`, using
  `RingHom.EssFiniteType`, which installs `φ.toAlgebra` and uses `Algebra.EssFiniteType`.
- The localization presentation of S' over R is unpacked into its witnesses:
  `(P : Type p) [CommRing P] [Algebra R P] [Algebra.FinitePresentation R P]`,
  `(U : Submonoid P)`, `(f : P →+* T)`, and
  `(hT : letI := f.toAlgebra; IsLocalization U T)`.
  `Submonoid` is exactly a multiplicative subset containing 1 and closed under multiplication.
  `IsLocalization` states that the given algebra is isomorphic to the localization, rather
  than requiring literal equality of the underlying rings. Quantifying over the witnesses
  of this hypothesis is the curried form of the node's existential hypothesis: choose any
  localization presentation and obtain the stated conclusion. It does not restrict the
  possible presentations or assume a finite set of denominators.
- "As an R-algebra via ψ ∘ φ" is
  `(hf : f.comp (algebraMap R P) = ψ.comp φ)`. This ensures the localization identification
  respects precisely the given R-structure on T. No injectivity or surjectivity of φ, ψ,
  or f is assumed beyond the localization property on f.
- The conclusion's finitely presented S-algebra P' is the existential Q together with
  its `CommRing Q`, `Algebra S Q`, and `Algebra.FinitePresentation S Q`.
- Its multiplicative subset V and S-algebra localization identification are
  `∃ (V : Submonoid Q) (g : Q →+* T), g.comp (algebraMap S Q) = ψ ∧
  (letI := g.toAlgebra; IsLocalization V T)`. The compatibility equality says the
  identification is over S with its original map ψ. By the localization universal property
  this is equivalent to T ≅ V⁻¹Q as S-algebras; neither direction is omitted.

Dependency declarations read and used:

- `def-weil-pbc-essentially-finite-type-algebra` is a Mathlib leaf:
  `Algebra.EssFiniteType` in `Mathlib.RingTheory.EssentialFiniteness`, and its ring-map
  form `RingHom.EssFiniteType` in the same module. Their docstrings and full definitions
  identify the localization-of-a-finite-type-algebra condition.
- `def-weil-pbc-finitely-presented-algebra` is a Mathlib leaf:
  `Algebra.FinitePresentation` in `Mathlib.RingTheory.FinitePresentation`. Its `out` field
  is a surjective map from an `MvPolynomial (Fin n) R` with finitely generated kernel.
- Localization is Mathlib's `IsLocalization` from `Mathlib.RingTheory.Localization.Defs`
  (available through the essential-finiteness import). The full signature and docstring,
  `isLocalization_iff`, and `IsLocalization.algEquiv` in Localization/Basic.lean were read.
  The latter identifies any two models of the same localization as algebras.

The theorem docstring carries all four proof steps of the node: finite numerator/denominator
choices for the finite generators of B; finite presentation of the base-changed algebra with
finitely many inverse and compatibility relations; the forward localization map; and the
inverse map checked on P, the added inverses, B, W, and the final localized algebra.

Edge cases checked: zero rings are allowed, and a denominator monoid may contain 0;
`IsLocalization` then allows the zero localization. No domain, nontriviality, local-ring,
Noetherian, flatness, or characteristic assumption is imposed. The case of zero generators
of B or P has the empty finite set of added relations. U and V can be infinite, and nothing
requires the structure maps to be injective. All four input universes are explicit and
independent. The output `Type (max v p)` contains the tensor product S ⊗[R] P and its
finite polynomial extension and quotient from the node's proof; it excludes no input case.

Sources checked: the repository's literature checkout does not contain algebra.tex on this
machine. The local full Stacks source `/home/ubuntu/c1-stacks-review/algebra.tex` was read at
Definition `definition-essentially-finite-p-t`, Lemma `lemma-compose-finite-type` (4), and
the first paragraph of `lemma-criterion-flatness-fibre`. The official pages were also opened:
[00QM](https://stacks.math.columbia.edu/tag/00QM),
[00F4](https://stacks.math.columbia.edu/tag/00F4), and
[00R7](https://stacks.math.columbia.edu/tag/00R7).
The node is a general algebraic auxiliary claim, not the local flatness criterion itself;
its four-step proof needs no hypotheses of the latter. No node fault or dispute was found.

Searches performed:

- `msearch.py ... leanfinder "An essentially finite type intermediate algebra preserves
  essentially finite presentation of the target algebra"`: eight hits, including
  `Algebra.EssFiniteType.of_comp`, `.comp_iff`, `Algebra.FinitePresentation.trans`, and
  `RingHom.finitePresentation_algebraMap`; none gives the localized presentation claim.
- `msearch.py ... loogle "Algebra.EssFiniteType, Algebra.FinitePresentation"`: zero hits.
- `msearch.py ... grep "EssFinitePresentation|essentially of finite presentation" RingTheory`:
  six hits, all comments/TODOs in Smooth/Fiber.lean or Extension/Cotangent/Basic.lean.
  Smooth/Fiber explicitly records the absence of an essentially-finite-presentation class
  and uses a supplied localization presentation instead.
- `msearch.py ... leansearch "essentially finite presentation over an essentially finite type
  intermediate algebra"`: service unavailable (Internal Server Error), recorded as unavailable.
- `rg` for `EssFinitePresentation|essentially of finite presentation` over Mathlib/RingTheory,
  WeilConjectures, and lean/Sheaf: the same Mathlib comments only, no existing definition
  or cancellation statement in either project source.
- `rg` for the item id in WeilConjectures: no match. Searches for
  `EssFinitePresentation|essentially.*finite.*presentation|finitePresentation.*intermediate|
  essentially_finite_presentation_of` in `dag/lean_names_upstream.json`, WeilConjectures,
  and lean/Sheaf found only unrelated limit-tower citations in FlatOfFlatClosedFiber.lean.
- The proposed full declaration name was searched in Mathlib, WeilConjectures, lean/Sheaf,
  and the upstream name index: no collision. LSP index not available on this machine.

Validation: server `scompile.py` compiled the module cleanly in 1.3 seconds, with no warnings.

## Second reading by F1

I read the node statement and the complete Lean declaration item by item. The objects and
hypotheses render as follows: commutative rings `R`, `S`, `T` are the explicit universes
`{R : Type u} {S : Type v} {T : Type w}` with `[CommRing ...]`; the maps are
`φ : R →+* S` and `ψ : S →+* T`; “S essentially of finite type over R” is exactly
`hS : φ.EssFiniteType` (the Mathlib `RingHom.EssFiniteType` dependency); and the
localization presentation of `T` over `R` is the explicit `P`, `[CommRing P]`,
`[Algebra R P]`, `[Algebra.FinitePresentation R P]`, `U : Submonoid P`, `f : P →+* T`,
`hf : f.comp (algebraMap R P) = ψ.comp φ`, and
`hT : letI := f.toAlgebra; IsLocalization U T`. Thus the existential presentation
hypothesis in the prose node is represented by arbitrary witnesses together with its
compatibility equation, with no extra injectivity, surjectivity, Noetherian, domain,
flatness, characteristic, or nontriviality assumptions.

The conclusion is rendered exactly by
`∃ (Q : Type (max v p)) (_ : CommRing Q) (_ : Algebra S Q),
Algebra.FinitePresentation S Q ∧ ∃ (V : Submonoid Q) (g : Q →+* T),
g.comp (algebraMap S Q) = ψ ∧ (letI := g.toAlgebra; IsLocalization V T)`.
This supplies a finitely presented `S`-algebra, a multiplicative subset, and an
identification with `T` over `S`, preserving the node's quantifier order and all clauses.
The universe `max v p` accommodates the tensor/base-change construction and imposes no
restriction on the input universes.

Edge cases were checked: empty finite generating sets (including zero generators), zero
rings and zero localizations, monoids containing zero or being infinite, and arbitrary
characteristic are all admitted. No empty scheme or geometric hypothesis occurs in this
ring statement. The source place and its hypotheses were checked against the Stacks
definition of essentially finite type and the localization presentation used in Tag 00R7.
Searches recorded in the worker report were repeated with `rg` over Mathlib, the source
project, and `lean/Sheaf`, plus LeanFinder/Loogle/LeanSearch queries; no existing
essentially-finite-presentation-over-an-intermediate declaration was found, and the
chosen full name has no collision.

No mismatch was found, so no source or Lean correction was necessary. The module compiled
cleanly with only the permitted `sorry` proof warning, and its node `lean.statement` is
verbatim equal to the declaration signature.
