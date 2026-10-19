## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveGenericallyFinite` states
`AlgebraicGeometry.exists_nonempty_open_isFinite_restrict_of_isProjective_generic_dim_le_zero`.
Its only proof is `sorry`; there are no definitions or additional declarations.
The node's statement is unchanged.

Hypothesis and conclusion correspondence:

- A Noetherian domain A: `(A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]`.
- Its fraction field K: `(K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]`.
  The algebra structure specifies the canonical inclusion into the fraction field.
- The projective family: `{D : Scheme.{u}} (f : D ⟶ Spec (.of A)) [IsProjective f]`.
- Generic fibre D_K: `pullback f (Spec.map (CommRingCat.ofHom (algebraMap A K)))`.
  This is precisely the fibre product defining the generic scheme-theoretic fibre;
  because A is a domain, its residue field at (0) is canonically K. This uses the
  same Mathlib pullback as `Scheme.Hom.fiber`, with the chosen fraction field
  rather than the canonically constructed residue field. No alternative fibre
  definition is introduced.
- Dimension at most zero: hypothesis `h : topologicalKrullDim (... : Scheme.{u}) ≤ 0`.
- A nonempty open subset of Spec A: `∃ U : (Spec (.of A)).Opens,
  (U : Set (Spec (.of A))).Nonempty ∧ ...`.
- The morphism becomes finite on this open: `IsFinite (f ∣_ U)`, where Mathlib's
  morphism restriction has source the inverse image of U and target U.

Dependency declarations read and used:

- `def-weil-pbc-scheme-conventions` fixes conventions only and has no declaration
  or module to import. Scheme and morphisms use Mathlib's standard category.
- `def-pc-projective-morphism`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsProjective` (extends `IsHProjective` and `QuasiCompact`).
  The local group clone still contains its former source in
  `lean/Sheaf/AlgebraicGeometry/Morphisms/Projective.lean`; its full signature and
  docstring were read there. The recorded canonical upstream import is available
  on the compilation server and is used by this delivery.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`, `Scheme.Hom.fiber`,
  `fiberι`, `fiberToSpecResidueField`, and `fiberHomeo`. The underlying construction
  is Mathlib's `CategoryTheory.Limits.pullback`, used explicitly along A → K.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim`.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite`.

Proof imports follow the node's three-step proof: projective base change
(`Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange`, `projective_base_change`),
projective properness (`WeilConjectures.AlgebraicGeometry.ProjectiveSpace`,
`ProjectiveSpace.instIsProper`), properness and finite type (Mathlib's `IsProper`
and `LocallyOfFiniteType`), dimension-zero finite-type schemes (Mathlib's
`IsLocallyArtinian.of_topologicalKrullDim_le_zero`,
`IsLocallyArtinian.discreteTopology`, `IsArtinianScheme.finite`, with Noetherian
and quasi-compact instances), locally Noetherian schemes (`IsLocallyNoetherian`),
and `Sheaf.AlgebraicGeometry.ProperFiniteFibreFiniteNeighbourhood`'s
`exists_open_isFinite_restrict_of_isProper_of_finite_fibre`.
All stated proof dependencies have their recorded modules imported.

Edge cases checked: the domain condition excludes the zero ring, so the base
has a generic point. The empty generic fibre has dimension bottom, satisfying
≤ 0, and is included. D itself may be empty. Nonreduced zero-dimensional generic
fibres are allowed; there is no reducedness or integrality assumption on D.
If A is a field, the sole nonempty open is the whole base and the conclusion is
proper zero-dimensional finite-type schemes over a field are finite.
No characteristic, dimension of A, flatness, surjectivity, or nonempty generic
fibre is assumed. One common arbitrary universe permits all schemes and the
chosen ring and fraction field after the usual universe enlargement.

Searches for an existing statement (2026-10-15):

- `msearch.py ... leanfinder` with “A projective morphism over a Noetherian domain
  whose generic fibre has dimension at most zero is finite on a nonempty open
  subset”: eight results on Proj finite type/properness, finite fibres, Noetherian
  finite-type schemes, and global sections. None gives this statement.
- `msearch.py ... loogle 'AlgebraicGeometry.IsFinite, AlgebraicGeometry.IsProjective'`:
  zero hits; the search service does not know the project's IsProjective.
- `msearch.py ... grep 'finite.*(neighbou?rhood|generic)|(neighbou?rhood|generic).*finite'
  AlgebraicGeometry`: three unrelated Mathlib hits (Properties and Smooth).
- `rg` over the upstream WeilConjectures source and the project's lean/Sheaf for
  generically_finite / projective-generic-finite variants found no exact statement.
  The project contains a later finite generic curve model citing this node.
- `grep -rn 'lem-fin-projective-generically-finite'` over upstream WeilConjectures:
  no hits.

The source blueprint lemma and the node's proof were read in full. No node faults,
new nodes, dependency modules, statement correction, or disputed statement.


## Second reading by NW

Independently read the node, its blueprint source at
`sec-smooth-purity/sk-prop-sf-cbc/lem-fin-projective-generically-finite.md`,
all six statement-dependency records and their declarations, the delivered module,
and the relevant Stacks text (especially 01WF and 02OH). The source introduces
no extra standing hypothesis. The node has no `statement_change`; no new nodes
or dependency modules are delivered.

Object/hypothesis/conclusion checklist (each verdict: exact):

1. The object A is a commutative Noetherian domain: `(A : Type u)` with
   `[CommRing A] [IsDomain A] [IsNoetherianRing A]`. `IsNoetherianRing` is
   Noetherianity of A as an A-module, equivalently finite generation of all ideals;
   its recorded Mathlib declaration was opened. No field hypothesis on A is added.
2. K is the fraction field of that same A: `(K : Type u) [Field K]
   [Algebra A K] [IsFractionRing A K]`. The algebraMap is the localization
   embedding, not an arbitrary field map or an extra finite extension.
3. D is an arbitrary scheme and f its projective morphism to Spec A:
   `{D : Scheme.{u}} (f : D ⟶ Spec (.of A)) [IsProjective f]`.
   Opened the project's Projective declaration: `IsHProjective` is a closed
   embedding into some P^n over this base, n in Nat (including zero);
   `IsProjective` adds quasi-compactness, precisely the dependency node's convention.
   The canonical upstream module is the import used by the compiled file.
4. D_K is the scheme fibre product along A -> K:
   `pullback f (Spec.map (CommRingCat.ofHom (algebraMap A K)))`.
   Opened `Scheme.Hom.fiber`, its two projections and `fiberHomeo` in Mathlib.
   That declaration is the same pullback along `fromSpecResidueField`; for the
   generic point of a domain the residue field is canonically its fraction field.
   The explicit chosen K requires this base-change expression rather than literal
   use of the canonical residue-field carrier. It introduces no private notion.
5. The sole fibre hypothesis is dimension at most zero:
   `h : topologicalKrullDim (...) ≤ 0`. Opened `topologicalKrullDim`: it is the
   Krull dimension of irreducible closed subsets with codomain `WithBot ℕ∞`,
   exactly the dependency's chain dimension including the empty space.
6. The conclusion chooses an open of the original base, after all hypotheses:
   `∃ U : (Spec (.of A)).Opens`. Its nonemptiness is
   `(U : Set (Spec (.of A))).Nonempty`. The node does not demand a chosen
   generic point or a specified affine open, and neither does the Lean.
7. The very same morphism becomes finite on that U: `IsFinite (f ∣_ U)`.
   Mathlib's `IsFinite` extends `IsAffineHom` and requires finite coordinate
   ring maps on affine opens; restriction has source f^{-1}(U) and target U.
   No surjectivity, flatness, reducedness, or integrality of D is imposed.

Edge cases: the empty D and empty generic fibre are allowed, with dimension
bottom satisfying ≤ 0. Nonreduced zero-dimensional fibres are included. The zero
ring A is excluded exactly by the source's domain hypothesis. A field base is
included; the nonempty open is then the whole one-point base. All characteristics
and arbitrarily large finite-dimensional projective embeddings, including n=0,
are included. There is no index family to constrain. `u` is arbitrary and all
objects live in its common ambient universe; no separate smaller universe of
test objects creates a vacuous hypothesis. No unbound variable or universe remains.

Independent H4 searches on 2026-10-15:

- LeanFinder via msearch: “A proper morphism whose fibre over the generic point
  is zero dimensional is finite over some dense open subset”: eight hits for
  quasi-finiteness, properness, and finite fibres; no exact statement.
- Loogle via msearch: `AlgebraicGeometry.IsFinite, AlgebraicGeometry.IsProper`:
  nine hits, including finiteness near a finite fibre and proper plus locally
  quasi-finite implying finite. None states this fraction-field dimension criterion.
- `rg` in Mathlib AlgebraicGeometry, upstream WeilConjectures and `lean/Sheaf`
  using genericallyFinite, generically_finite, generic/finite, and exists/open/
  IsFinite variants. Opened upstream `AlgebraicGeometry/GenericFiniteness.lean`:
  its two neighbourhood results require a globally locally quasi-finite morphism
  (and one requires affine source), so neither is this node. Other hits concern
  normalization, generic points, and later model constructions, not this statement.

No mismatch found; preserved the Lean file and node unchanged. There is one named
sorry theorem, no definition, no proved auxiliary result, and no hidden local
notation or instances. Its source-tagged docstring follows all three node proof
steps: finite generic fibre via projectivity/properness and dimension zero,
Stacks 02OH on the locally Noetherian base, then nonemptiness of the neighbourhood.
The recorded signature was checked byte-for-byte against the file and all Lean
lines are at most 100 characters. Server `scompile.py NW
lem-fin-projective-generically-finite lean/Sheaf/AlgebraicGeometry/ProjectiveGenericallyFinite.lean`
passed cleanly in 1.7 seconds, nice 19, two threads, 60-second per-file limit.
