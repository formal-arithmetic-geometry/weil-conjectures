## Worker report

The module `Sheaf.AlgebraicGeometry.MarkedFiniteSmoothAffineRefinement` states
`AlgebraicGeometry.exists_marked_finite_smooth_affine_refinement`, with its whole proof
postponed by `sorry`. It adds no definitions and changes only the item's `lean` record.
The source is the proof of Stacks Tag 057L,
`literature/stacks-project/more-morphisms.tex`,
`lemma-local-local-structure-finite-type-affine` (read at lines 13523 onward).
The nine proof steps in the node are reproduced in the theorem docstring with their
dependency names. No statement correction or disputed assertion is needed.

Here is the correspondence for every hypothesis and conclusion. Write, only for this
explanation, `y₁ = π₁ w₁`, `s₁ = h₁ y₁`, `W = (π₁ ⁻¹ᵁ Y).toScheme`,
`π = π₁ ∣_ Y`, `h = h₁.resLE U Y e`, `w = ⟨w₁, hy⟩`, `y = ⟨y₁, hy⟩`,
and `s = ⟨s₁, e hy⟩`. The actual Lean signature contains the full terms and has no lets.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Schemes W₁, V, S₁ | `{W₁ V S₁ : Scheme.{u}}` |
| n ≥ 0 | `(n : ℕ)`; includes zero |
| Finite π₁ : W₁ → V | `(π₁ : W₁ ⟶ V) [IsFinite π₁]` |
| h₁ : V → S₁ smooth of relative dimension n | `(h₁ : V ⟶ S₁) [SmoothOfRelativeDimension n h₁]` |
| Every fibre stays integral after every residue-field extension | `[GeometricallyIntegral h₁]` |
| Marked w₁, y₁ = π₁(w₁), s₁ = h₁(y₁) | `(w₁ : W₁)` and direct substitution of `π₁ w₁`, `h₁ (π₁ w₁)` throughout |
| Original marked fibre a singleton | `hπ : π₁ ⁻¹' ({π₁ w₁} : Set V) = ({w₁} : Set W₁)` |
| Open neighbourhood U of s₁ | `U : S₁.Opens`; `e hy : h₁ (π₁ w₁) ∈ U` |
| Open neighbourhood Y of y₁ contained in h₁⁻¹(U) | `Y : V.Opens`, `e : Y ≤ h₁ ⁻¹ᵁ U`, `hy : π₁ w₁ ∈ Y` |
| Both U and Y affine | `IsAffineOpen U ∧ IsAffineOpen Y` |
| Restricted h surjective on points | `Surjective (h₁.resLE U Y e)` |
| Restricted h smooth of relative dimension n | `SmoothOfRelativeDimension n (h₁.resLE U Y e)` |
| Geometrically integral restricted fibres, nonempty after every extension | `GeometricallyIntegral (h₁.resLE U Y e)` |
| W is exactly the open inverse image and fibre product | The literal source `(π₁ ⁻¹ᵁ Y).toScheme` of `π₁ ∣_ Y`; the canonical identification with `pullback π₁ Y.ι` is Mathlib's `pullbackRestrictIsoRestrict π₁ Y`, with both projections identified by its lemmas. No arbitrary W or comparison map is introduced. |
| W affine and open in W₁ | `IsAffine (π₁ ⁻¹ᵁ Y).toScheme`; openness is already in the type of the open `π₁ ⁻¹ᵁ Y`, and its inclusion is `(π₁ ⁻¹ᵁ Y).ι` |
| Restricted π finite | `IsFinite (π₁ ∣_ Y)` |
| Restricted marked fibre a singleton | `(π₁ ∣_ Y) ⁻¹' ({⟨π₁ w₁, hy⟩} : Set Y) = ({⟨w₁, hy⟩} : Set (π₁ ⁻¹ᵁ Y))` |
| Marked points unchanged under open inclusions | The marked points `w`, `y`, `s` are literal subtype representatives of the original points; `π w = y` and `h y = s` are also explicit conjuncts |
| All three residue fields unchanged | `IsIso ((π₁ ⁻¹ᵁ Y).ι.residueFieldMap w)`, `IsIso (Y.ι.residueFieldMap y)`, and `IsIso (U.ι.residueFieldMap s)` |
| Compatibility with original π₁ residue-field map | The penultimate conjunct is equality of the two composites from `κ(Y.ι (π w))` to `κ(w)`; `V.residueFieldCongr (morphismRestrict_base_coe π₁ Y w)` transports the ambient marked point equality |
| Compatibility with original h₁ residue-field map | The final conjunct is equality of the two composites from `κ(U.ι (h y))` to `κ(y)`; `S₁.residueFieldCongr (h₁.coe_resLE_apply e y)` transports the ambient point equality |
| Both restriction squares commute | `h₁.resLE U Y e ≫ U.ι = Y.ι ≫ h₁` and `(π₁ ∣_ Y) ≫ Y.ι = (π₁ ⁻¹ᵁ Y).ι ≫ π₁` |

The geometric-integrality class includes nonemptiness: its definition requires `IsIntegral`
after every field-valued base change, and `IsIntegral.nonempty` is part of integrality.
`GeometricallyIntegral.iff_geometricallyIntegral_fiber` gives precisely the fibrewise
version in the node. The same class is used in the hypothesis and conclusion. Thus no
separate assumption of geometric reducedness, irreducibility, surjectivity or nonempty
geometric fibres is added. The conclusion does expressly retain the requested surjectivity.

The residue-field equalities use the canonical maps of the actual open inclusions,
not existentially chosen field isomorphisms. The `residueFieldCongr` terms only align
the equal ambient image points; they do not replace the maps. The point equalities in
the conclusion identify the intermediate points in these two squares with `y` and `s`.

Dependency declarations read and used:

| Dependency | Module and declarations |
| --- | --- |
| def-pc-scheme | `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom` |
| def-weil-finite-integral-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite` |
| def-sbc-smooth-morphisms | `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`, `SmoothOfRelativeDimension`; the recorded dimension notion is used directly |
| def-pc-geometrically-irreducible | `Mathlib.AlgebraicGeometry.Geometrically.Integral`: `GeometricallyIntegral`, with its fibrewise equivalence |
| def-pc-integral-scheme | `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`, used through geometric integrality |
| def-weil-affine-spectrum | `Mathlib.AlgebraicGeometry.Scheme`: `Spec`; affineness is `IsAffineOpen` / `IsAffine` |
| def-weil-open-immersion | `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`, instantiated by the standard `Scheme.Opens.ι` inclusions |
| def-weil-surjective-morphism | `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective` |
| def-pc-fibre-product | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`, `pullback.snd`; the canonical open model is `pullbackRestrictIsoRestrict` in `Mathlib.AlgebraicGeometry.Restrict` |
| def-weil-residue-field | `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Scheme.Hom.residueFieldMap`, `Scheme.residueFieldCongr` |

The additional public restriction import supplies the canonical `morphismRestrict` and
`Scheme.Hom.resLE`, including their underlying-point identities. Plain proof imports
provide the stated proof dependencies: `AffineScheme` (affine basis),
`Morphisms.UniversallyOpen` (flat-lfp openness), `Pullbacks` (affine fibre products and
open-immersion pullbacks), `PullbackCarrier` (surjective base change),
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber`
(`Smooth.flat_and_locallyOfFinitePresentation`), and
`WeilConjectures.Mathlib.Topology.KrullDimension`
(`IsOpen.topologicalKrullDimAt_eq`). The other proof dependencies are in the public
modules: open factorization and restriction identities, smooth restriction and base
change, finite base change and affineness, and the geometric-integrality definitions.
No proof dependency with a recorded Lean module is omitted.

Edge cases checked before writing: `n = 0` is included. An empty W₁ has no marked
point, so it introduces no spurious case; V and S₁ cannot be empty in a pointed
diagram either. Empty fibres of h₁ are excluded by the original integrality hypothesis,
not an extra Lean hypothesis. Nonreduced W₁ and inseparable marked residue extensions
remain allowed: neither residue-field map of π₁ or h₁ is assumed invertible; only the
maps of open inclusions are invertible. Arbitrary schemes, arbitrary characteristic,
and arbitrary `u` are allowed, with no Noetherian, separated, finite-presentation or
field-size assumption added. The base and source opens are not required to be proper
subsets. Identity finite maps and singleton fibres satisfy the stated conditions.

Searches for an existing statement, with results retained in `searches.jsonl`:

- `msearch.py ... leanfinder` query: "Affine open refinement of a pointed finite over
  smooth diagram with geometrically integral fibres preserving marked residue fields".
  Eight hits concerned affine transition limits and affine open covers, including
  `Scheme.OpenCover.fromAffineRefinement`; none includes the pointed finite source,
  smooth relative dimension, geometric integrality and residue-field compatibility.
- `msearch.py ... loogle` query: `"AlgebraicGeometry", "affine", "smooth"`.
  Four hits, all on smoothness of affine space; no match.
- `msearch.py ... grep` query:
  `affine.*(smooth|integral).*(refin|neigh)|exists.*[Aa]ffine.*[Ss]mooth`,
  subdirectory `AlgebraicGeometry`: zero Mathlib hits.
- Direct `rg` with that same expression in `lean/WeilConjectures` and `lean/Sheaf`
  found smooth charts, curves and the already recorded larger
  `exists_affine_etale_finite_smooth_local_structure`; none is this refinement
  theorem. The full signature and docstring of that larger theorem were read:
  it constructs a new etale neighbourhood of a finite-type morphism and does not
  refine an arbitrary given finite-over-smooth diagram by the specified opens.
- Direct `rg` for `marked.*[Aa]ffine|affine.*[Rr]efinement` likewise found only
  unrelated refinements. `grep -rn` for the exact node id in
  `lean/WeilConjectures`, and `rg` in `dag/lean_names_upstream.json`, found nothing.

Validation: the required `scompile.py Q57 lem-trf-marked-finite-smooth-affine-refinement`
command compiled the sandbox module and its library-path version cleanly (1.8 s and
1.9 s reported). Every variable and universe is explicitly bound; there is one named
theorem with its whole proof `sorry`, and no helper theorem or data definition.

## Second reading by Q57

The dispatcher explicitly prohibits starting another agent; this is a second reading
by this worker, and the maintainer supplies the independent delivery review. I reopened
the node and compared the complete signature against the source proof and all clauses.
The input point equalities are rendered by substitution rather than extra assumptions;
the final points are the literal subtype representatives. I checked the orientation of
each `residueFieldCongr`: ambient image of restricted point to original image, followed
by the original contravariant residue-field map and the open-inclusion map. Both sides
therefore have the same source and target. I also checked that W is the actual inverse
image open, that the singleton equality is on its underlying points, and that geometric
integrality includes nonemptiness after every field extension. No mismatch was found,
and no node text or dependency interface needed changing.
