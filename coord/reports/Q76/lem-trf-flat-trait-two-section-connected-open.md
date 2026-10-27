## Worker report

The module `Sheaf.AlgebraicGeometry.FlatTraitTwoSectionConnectedOpen` states
`AlgebraicGeometry.exists_connected_open_two_sections_of_flat_trait`, with its sole proof
`sorry`. No definitions, helper axioms, new nodes, dependency repairs or statement corrections
are needed. The item's other fields remain unchanged.

Source read: `literature/stacks-project/more-morphisms.tex`, Tag 055Q,
`lemma-connected-along-section-open-neighbourhood`, especially the final DVR paragraph
(lines 8368–8383), and Tag 055J, `lemma-connected-flat-over-dvr` (lines 8132–8170).
055Q removes the other closed-fibre components, then keeps the connected component meeting
the section; 055J supplies generic-fibre connectedness using reducedness of the closed fibre.
The node spells out the two-section version of this argument. Although the general 055Q
statement assumes geometric reducedness, this DVR argument only uses ordinary reducedness,
exactly as in the node and 055J. No stronger hypothesis is inserted.

Hypotheses and objects, clause by clause:

| Node text | Lean rendering |
| --- | --- |
| DVR R, in particular an integral domain, local, principal, and not a field | `{R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]`; the last class extends the principal-ideal-ring and local-ring classes and requires nonzero maximal ideal |
| S = Spec R | `Spec (.of R)` throughout; S is not an arbitrary additional scheme |
| Generic point η and closed point s | `(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)` and `IsLocalRing.closedPoint R`, respectively |
| Scheme X and morphism f : X → S | `{X : Scheme.{u}} (f : X ⟶ Spec (.of R))` |
| f flat | `[Flat f]`, the recorded affine-local predicate equivalent to flat stalk maps |
| f of finite presentation | `[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]`; all three conditions of the node's convention are retained |
| Sections σ, τ with f ∘ σ = f ∘ τ = id | `(σ τ : Spec (.of R) ⟶ X)`, `hσ : σ ≫ f = 𝟙 (Spec (.of R))`, and the analogous `hτ`; composition in Lean is in traversal order |
| Closed scheme fibre reduced | `[IsReduced (f.fiber (closedPoint R))]` |
| F = f⁻¹({s}) | `f ⁻¹' {closedPoint R}`, the point-set fibre |
| D is the connected component of σ(s) in F | `connectedComponentIn (f ⁻¹' {closedPoint R}) (σ (closedPoint R))`; this is the ambient image of the component in the fibre subtype |
| τ(s) ∈ D | `hτD : τ (closedPoint R) ∈ connectedComponentIn ...` |

Conclusion, clause by clause:

| Node text | Lean rendering |
| --- | --- |
| An open subscheme W ⊆ X | `∃ W : X.Opens`, with its standard scheme `W.toScheme` and open immersion `W.ι` |
| W contains D | First conjunct: `connectedComponentIn ... ⊆ (W : Set X)` |
| W ∩ F = D | Second conjunct: `(W : Set X) ∩ f ⁻¹' {closedPoint R} = connectedComponentIn ...` |
| W connected and nonempty | `ConnectedSpace W.toScheme`; the definition includes `Nonempty`, unlike `PreconnectedSpace` |
| Both sections factor as scheme morphisms through W | Existentials `σW : Spec (.of R) ⟶ W.toScheme`, `σW ≫ W.ι = σ`, and the analogous `τW`; these are morphisms with equality of morphisms, including sheaf maps |
| Restriction h : W → S flat | `Flat (W.ι ≫ f)`; this is the specified restriction, not an arbitrary map |
| Closed fibre W_s reduced | `IsReduced ((W.ι ≫ f).fiber (closedPoint R))` |
| Generic fibre W_η connected and nonempty | `ConnectedSpace ((W.ι ≫ f).fiber (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R))`, including nonemptiness |
| τ(η) in the component of σ(η) in f⁻¹({η}) | Final conjunct outside the W existential is precisely this membership using `connectedComponentIn (f ⁻¹' {η}) (σ η)` with the zero-prime expression expanded |

Definitions are reused through their recorded interfaces (full source signatures and
docstrings read):

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`,
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`, including `Flat.iff_flat_stalkMap`.
- `def-sbc-locally-finite-presentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- `def-weil-pbc-scheme-conventions` is a convention record with no declaration of its own.
  Its finite-presentation phrase is the three predicates above, with
  `AlgebraicGeometry.QuasiCompact` and `AlgebraicGeometry.QuasiSeparated` from their respective
  `Mathlib.AlgebraicGeometry.Morphisms` modules.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`; open restrictions use `Scheme.Opens.toScheme` and
  `Scheme.Opens.ι` from `Mathlib.AlgebraicGeometry.Restrict`, exposed by these imports.
- `def-pc-section`: the equivalent explicit map-plus-section-equation presentation recorded
  by this dependency, as in `CategoryTheory.SplitEpi`, `Mathlib.CategoryTheory.EpiMono`.
  Its equation is used directly; no new section predicate is defined.
- `def-pc-scheme-fibre`: `AlgebraicGeometry.Scheme.Hom.fiber`,
  `Mathlib.AlgebraicGeometry.Fiber`; its `fiberHomeo` identifies the scheme and set fibres.
- `def-pc-reduced-scheme`: `AlgebraicGeometry.IsReduced`,
  `Mathlib.AlgebraicGeometry.Properties`; equivalence with reduced stalks is read there.
- `def-weil-connected-scheme`: `ConnectedSpace` and `connectedComponentIn`,
  `Mathlib.Topology.Connected.Basic`. The latter is the image of the connected component
  in the fibre subtype, with the induced topology, not the component in all of X.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`; the canonical `W.ι` is an open immersion.

The stated proof dependencies are also imported, as proof-only imports where not already
public statement imports: noetherian rings (`Mathlib.RingTheory.Noetherian.Defs`), locally
noetherian schemes and finite-type permanence (`Mathlib.AlgebraicGeometry.Noetherian`), affine
quasi-compactness (`Mathlib.AlgebraicGeometry.AffineScheme`), finite type
(`Mathlib.AlgebraicGeometry.Morphisms.FiniteType`), noetherian minimal closed subsets
(`Mathlib.Topology.NoetherianSpace`, `Mathlib.Order.WellFounded`), finite-presentation
cancellation (`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
`AlgebraicGeometry.locallyOfFinitePresentation_of_comp`), open connected components
(`WeilConjectures.Mathlib.Topology.NoetherianSpace`,
`TopologicalSpace.NoetherianSpace.isOpen_connectedComponent` and
`TopologicalSpace.NoetherianSpace.finite_connectedComponents`), and
`AlgebraicGeometry.connectedSpace_generic_fibre_of_flat_trait`
(`WeilConjectures.AlgebraicGeometry.ConnectedGenericFibreTrait`). Their signatures were read.
The theorem docstring carries all seven proof steps of the node, including the arbitrary-source
open factorization and the closed-fibre comparison.

Edge cases checked mathematically before writing:

- Empty X cannot admit a section from the nonempty DVR spectrum; there is no extraneous
  `[Nonempty X]` or connectedness assumption on X.
- The closed fibre is nonempty from either section; `hσ` places σ(s) in F, so
  `connectedComponentIn` is not its out-of-fibre empty branch.
- For σ = τ no distinctness is required. The same component hypothesis and conclusion apply.
- A disconnected total space and additional closed-fibre components are allowed: W is selected
  by existence; no connectedness of X or its entire closed fibre is assumed.
- Connectedness in each conclusion includes nonemptiness by the definition of `ConnectedSpace`.
- Fields and the zero ring are excluded precisely by the DVR/domain hypotheses already in
  the node; no additional characteristic, residue-field or separatedness restriction occurs.
- Non-geometrically-reduced closed fibres that are reduced are allowed: only `IsReduced` is
  assumed. No reducedness hypothesis is imposed on the generic fibre.
- All schemes and R lie in the same arbitrary universe u, as in the category of schemes and
  the recorded generic-fibre theorem; there are no extra test schemes in a smaller universe.

Searches actually run with `msearch.py Q76 lem-trf-flat-trait-two-section-connected-open`:

- `leanfinder`: "Two sections of a flat finitely presented scheme over a discrete valuation
  ring in the same connected component of the reduced closed fibre lie in a connected open
  with connected generic fibre". Eight hits: valuative criterion eq/existence and related
  declarations, `Flat.generalizingMap`, `ValuativeCommSq.domain`, and
  `exists_lift_of_germInjective_aux`. Their displayed types do not state this assertion.
- `leansearch`: "A flat scheme of finite presentation over a DVR with reduced closed fibre
  has a connected open containing two sections in the same special fibre component and with
  connected generic fibre". Eight hits on `Flat`, `flat_iff`, `flat_appLE`,
  `UniversallyOpen.of_flat`, `IsOpenImmersion.of_flat_of_mono`, and `Flat.instResLE`.
  None states the connected-open assertion.
- `loogle`: `IsDiscreteValuationRing, ConnectedSpace`: zero hits.
- Mathlib `grep`, subdirectory `AlgebraicGeometry`:
  `connected.*generic.*[fF]ibre|section.*connectedComponentIn|two_section`: zero hits.
- `rg` in `lean/WeilConjectures/AlgebraicGeometry` and `lean/Sheaf/AlgebraicGeometry` for
  `two.section|trait_sections_mem_same_generic_component|connected.*generic.*[fF]ibre|connectedComponentIn`
  finds the recorded generic-fibre theorem, the more specialized smooth two-section result
  in `SmoothTraitSectionComponents`, and component/generalization lemmas. The connected-generic-fibre
  theorem and the generalization consumer were read; none is the full present flat
  two-section open assertion.
- `grep -rn lem-trf-flat-trait-two-section-connected-open lean/WeilConjectures`: zero hits.
- A second `rg` across both complete project roots for
  `flat_trait_two_section_connected_open|connected_open.*trait|trait.*connected_open|lem-trf-flat-trait-two-section-connected-open`
  found no existing declaration. The chosen new declaration name is unused.

Validation: prescribed `scompile.py` compiled this one module both in sandbox and at its
library module path, with no errors or warnings (2.2 seconds per compile). `autoImplicit` is
explicitly false and universe u is explicitly bound. Delivery preflight is run separately
through `deliver2.py --no-push`, then delivery through `deliver2.py`.

## Second reading by Q76

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
