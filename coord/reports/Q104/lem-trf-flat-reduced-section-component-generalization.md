## Worker report

The module `Sheaf.AlgebraicGeometry.FlatReducedSectionComponentGeneralization` states
`AlgebraicGeometry.stableUnderGeneralization_section_component_of_flat_of_geometricallyReduced_fibers`.
Its only proof is `sorry`. There are no new definitions, new nodes, dependency repairs,
or statement corrections. The item JSON changes only in `lean`.

Source read: Stacks Project, `literature/stacks-project/more-morphisms.tex`,
Tag 055Q, `lemma-connected-along-section-open-neighbourhood` (lines 8310–8384),
and the ensuing Tag 055R. The neighbourhood assertion in 055Q implies exactly the
node's generalization conclusion when every fibre is geometrically reduced.
The docstring carries all eight recorded proof steps, with their dependency ids:
affine restriction, noetherian approximation and descent of the section identity,
eventual flatness and reducedness at the distinguished geometric fibre, tracing
by a DVR and faithful-flat descent of reducedness, the two sections, removal of
other closed-fibre components, restriction to a connected open, and return from
the connected generic fibre via the cartesian component identity.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| Schemes P and T | `{P T : Scheme.{u}}`, arbitrary explicitly bound universe `u` |
| Morphism g:P→T | `(g : P ⟶ T)` |
| Flat | `[Flat g]` |
| Locally of finite presentation | `[LocallyOfFinitePresentation g]` |
| Quasi-compact | `[QuasiCompact g]` |
| Quasi-separated | `[QuasiSeparated g]` |
| Every fibre geometrically reduced | `(hred : ∀ t : T, GeometricallyReduced (g.fiberToSpecResidueField t))` |
| Section σ:T→P | `(σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T)` |
| Fibre over g(p) | `g ⁻¹' {g p}`, canonically homeomorphic to `g.fiber (g p)` by `g.fiberHomeo` |
| Component through σ(g(p)) in that fibre | `connectedComponentIn (g ⁻¹' {g p}) (σ (g p))` |
| C is the locus of membership | `{p : P | p ∈ connectedComponentIn (g ⁻¹' {g p}) (σ (g p))}` |
| p specializes to q and q∈C imply p∈C | `StableUnderGeneralization` of that exact set |

`StableUnderGeneralization s` is defined in `Mathlib.Topology.Inseparable` as
`∀ ⦃x y⦄, y ⤳ x → x ∈ s → y ∈ s`. Taking x=q and y=p checks the direction.
There is no extra assumption of smoothness, affineness, noetherianity, nonemptiness,
separatedness, or characteristic. Finite presentation is rendered by all three
properties fixed in the convention node, not only local finite presentation and qc.
The section equation ensures that the component's distinguished point belongs to
its fibre. No separate private definition of the locus or of connectedness is used.

Statement-dependency declarations inspected and used:

- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`,
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`; read its class docstring and full
  affine-open condition and `Flat.iff_flat_stalkMap`.
- `def-sbc-locally-finite-presentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`; read the class and docstring.
- `def-weil-pbc-scheme-conventions` is explicitly a convention, with no declaration.
  Its finite-presentation convention is the three binders above. The declarations
  `AlgebraicGeometry.QuasiCompact` and `AlgebraicGeometry.QuasiSeparated` were read
  in `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` and `.QuasiSeparated`.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`; read structures and source docstrings.
- `def-pc-geometrically-irreducible`: import its recorded
  `Mathlib.AlgebraicGeometry.Geometrically.Integral`, which imports
  `AlgebraicGeometry.GeometricallyReduced` from `.Geometrically.Reduced`.
  Read both class signatures and docstrings. For the residue-field structure
  morphism this is precisely reducedness after every field extension.
- `def-pc-scheme-fibre`: `AlgebraicGeometry.Scheme.Hom.fiber`, `.fiberι`,
  `.fiberToSpecResidueField` and `.fiberHomeo`, `Mathlib.AlgebraicGeometry.Fiber`;
  read their definitions, full types and docstrings. The canonical field structure
  morphism is used for hred; the fibre homeomorphism justifies the topological fibre.
- `def-weil-connected-scheme`: the Mathlib match is `ConnectedSpace` in
  `Mathlib.Topology.Connected.Basic`, not a missing lean record. Read its nonempty
  connectedness definition and `connectedComponentIn`; that existing component
  construction renders the component clause.

Already-stated proof dependencies are imported without `public`: the qcqs,
flat base change, noetherian, pullback, open immersion, reducedness,
faithfully-flat, and DVR Mathlib modules; the upstream
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit` (noetherian
approximation and spreading out) and `WeilConjectures.Mathlib.Topology.NoetherianSpace`
(open noetherian components); and the recorded side modules
`Sheaf.TraceFormula.GeometricReducedFibreLocusBaseChange`,
`Sheaf.AlgebraicGeometry.SectionComponentPullback`,
`Sheaf.AlgebraicGeometry.DescendFlatFinitePresentation`,
`Sheaf.AlgebraicGeometry.NoetherianSpecializationTrait`, and
`Sheaf.AlgebraicGeometry.ConnectedGenericFibreTrait`.
This imports the proof plan while leaving the conclusion as the generalization
statement, without using the downstream openness theorem as a proof dependency.

Edge cases checked before writing:

- Empty T: existence of g forces P empty; the locus is empty and stability is vacuous.
  No nonemptiness binder excludes this case.
- p=q: reflexive specialization reduces to the supplied membership.
- Identity g and identity section: fibres are singletons, C is all of P,
  and stability holds.
- Disconnected fibres: only the component containing the section is selected;
  no global connectedness of either scheme or any whole fibre is assumed.
- The section prevents empty fibres over actual points of T; it does not impose
  an extraneous global nonemptiness assumption when T is empty.
- Reducedness cannot be dropped: over a DVR with uniformizer π,
  `R[z]/(z(z-π))` with section z=0 has a doubled special fibre and two generic
  components; the other generic point specializes to the special section point.
  The stated hred excludes this failure. No restriction on characteristic is needed.

Searches made using the prescribed wrappers (2026-10-18 UTC):

- LeanSearch: “The fibrewise connected component through a section of a flat
  finitely presented geometrically reduced family is stable under generalization”.
  Eight hits including `StableUnderGeneralization`,
  `GeneralizingMap.stableUnderGeneralization_range`,
  `GeneralizingMap.stableUnderGeneralization_image`, `Flat.generalizingMap`,
  and `Flat.isStableUnderBaseChange`; none states the desired relative-component theorem.
- LeanFinder: “flat finitely presented geometrically reduced family section
  component locus stable under generalization”. Eight hits including
  `AlgebraicGeometry.Flat.generalizingMap`, `Algebra.HasGoingDown.of_flat`,
  `Algebra.isOpen_smoothLocus`, `Algebra.isOpen_unramifiedLocus`, and
  `RingHom.Flat.generalizingMap_comap`; no exact theorem.
- Loogle: `AlgebraicGeometry.Flat, StableUnderGeneralization`: zero hits.
- Mathlib grep wrapper, AlgebraicGeometry:
  `connectedComponentIn.*generalization|generalization.*connectedComponentIn`: zero hits.
- `rg` in upstream `WeilConjectures` for section components, connectedComponentIn,
  and generalization found
  `AlgebraicGeometry.stableUnderGeneralization_setOf_mem_connectedComponentIn_preimage_singleton`
  in `WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat`, lines 271–283.
  Its full signature and docstring were read: it assumes `[IsAffine X] [IsAffine Y]`
  in addition to `[GeometricallyReduced f]`, and hence does not state this general
  nonaffine theorem. Its algebraic relative-component input is also an affine result.
- Full upstream `rg` for the exact item id: no match. The upstream declaration-name
  index and `lean/Sheaf` were searched for section/generalization names. The side
  library contains `Smooth.stableUnderGeneralization_section_component`, whose full
  signature requires `[Smooth g]`, and the already-stated downstream openness theorem.
  Neither is this node's statement. The chosen new full declaration name is absent.

Validation: prescribed `scompile.py Q104 lem-trf-flat-reduced-section-component-generalization`
compiled the sandbox view and the final library module in 1.8 s and 1.7 s respectively,
with no errors or warnings. All variables and universes are explicitly bound.

No STATEMENT-DISPUTED flag or node fault remains.

## Second reading by Q104

This is the author's self-check required for direct remote delivery; the maintainer's
independent reader reviews it after delivery. No independent worker was started.
I reopened the node and the completed module and matched every row above. In
particular hred quantifies over every point and uses its residue-field fibre map,
not a stronger chosen affine or smooth presentation. The three finite-presentation
binders retain quasi-separatedness. The section equation has the correct direction
for categorical composition. The locus is literally the same `connectedComponentIn`
expression as the node and the landed flat-family openness module. Unfolding the
existing stability predicate gives exactly p⤳q, q∈C ⇒ p∈C, with no reversed arrow.
The universe is explicit and no edge case is excluded. The proof docstring retains
reducedness only at the distinguished model fibre in the approximation argument;
it does not claim all model fibres are reduced. No mismatch or correction was found.
