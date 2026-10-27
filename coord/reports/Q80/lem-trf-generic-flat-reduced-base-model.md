## Worker report

The module `Sheaf.AlgebraicGeometry.GenericFlatReducedBaseModel` states
`AlgebraicGeometry.exists_integral_affine_genericFlat_reducedBase`, with a single
`sorry` theorem proof and no new definitions. The node is unchanged except for
its `lean` field. No dependency repair or statement correction is needed.

Sources read: Stacks `more-morphisms.tex`, Tag 0578,
`lemma-geometrically-reduced-generic-fibre`, its first proof paragraph;
`morphisms.tex`, Tag 052A, `proposition-generic-flatness`, statement and proof.
The preparation uses neither geometric reducedness of the generic fibre nor
Noetherianity: that hypothesis of the larger 0578 theorem is used only after
this preparation. Reduction is the specified nilradical subscheme, not an
arbitrary scheme with the same underlying space.

Hypotheses and conclusions, clause by clause:

- Schemes and the morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the dependency's
  two-part convention.
- Irreducible base and its specified generic point: `[IrreducibleSpace Y]`,
  `(η : Y) (hη : IsGenericPoint η (Set.univ : Set Y))`.
- Reduction: `Y.nilradical.subscheme` and its canonical map
  `Y.nilradical.subschemeι`, from the recorded Mathlib construction.
- The open `W` of the reduction: `∃ W : Y.nilradical.subscheme.Opens`, with
  `(W : Set Y.nilradical.subscheme).Nonempty`, `IsAffineOpen W` and
  `IsIntegral W.toScheme`. Thus the affine model is an actual open subscheme.
- The map denoted q in the node is always the explicit composite
  `W.ι ≫ Y.nilradical.subschemeι`. No free choice of map is substituted for it.
- The family g is always `pullback.snd f (W.ι ≫ Y.nilradical.subschemeι)`, with
  its actual source `pullback f (W.ι ≫ Y.nilradical.subschemeι)`.
  Its finite type is `LocallyOfFiniteType` and `QuasiCompact`; flatness is
  `Flat`; local finite presentation is `LocallyOfFinitePresentation`.
- Homeomorphism onto a nonempty open V₀ containing η: the conclusion supplies
  `V₀ : Y.Opens`, `η ∈ V₀`, `Topology.IsOpenEmbedding q`, and
  `Set.range q = (V₀ : Set Y)`. An open embedding is a homeomorphism onto its
  image; the range equality identifies that image with V₀, and membership of η
  ensures nonemptiness. This asserts a topological open embedding, not that q
  is an open immersion of schemes (which a reduction generally is not).
- For each point `w : W.toScheme`, the actual induced field map is
  `q.residueFieldMap w`; `IsIso` asserts it is an isomorphism.
- For every w the conclusion supplies `e : g.fiber w ≅ f.fiber (q w)`.
  The first equation says `e.hom ≫ f.fiberι (q w) = g.fiberι w ≫ pullback.fst f q`.
  The second says
  `e.hom ≫ f.fiberToSpecResidueField (q w) =
  g.fiberToSpecResidueField w ≫ Spec.map (q.residueFieldMap w)`.
  These specify both projections of the canonical comparison into the target
  fibre pullback, so they characterize that comparison uniquely. In particular
  the isomorphism lies over precisely the specified residue-field isomorphism;
  this is not a bare abstract isomorphism of schemes.
- The unique point ηW above η: the last existential gives `ηW : W.toScheme`,
  `q ηW = η`, and `∀ w, q w = η → w = ηW`.
- Genericity is `IsGenericPoint ηW (Set.univ : Set W.toScheme)`.
- The generic fibre has its actual structural map
  `g.fiberToSpecResidueField ηW` to `Spec (W.toScheme.residueField ηW)`;
  `LocallyOfFinitePresentation` is asserted for that map.

Recorded statement-dependency declarations read and used (all public imports):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; with
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.Topology.Irreducible`: `IrreducibleSpace`, the whole-space specialization
  of `IsIrreducible` in the irreducible-components dependency's match.
- `Mathlib.Topology.Sober`: `IsGenericPoint`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`:
  `Scheme.IdealSheafData.subscheme`, `Scheme.IdealSheafData.subschemeι`, and
  `Scheme.nilradical` from `IdealSheaf.Basic`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `Scheme.Hom.fiberι`,
  `Scheme.Hom.fiberToSpecResidueField`.

Proof interfaces read: reduction's
`reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism`
in `WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism`;
`exists_nonempty_open_flat_finitePresentation_restrict` in
`WeilConjectures.AlgebraicGeometry.GenericFlatFinitePresentation`; and
`Scheme.Hom.isIso_residueFieldMap_of_isClosedImmersion` in
`Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso`.
These modules are plain proof imports. The other proof dependencies are
Mathlib interfaces: LFT/QC/flat/LFP base-change instances, affine-opens basis
(`Scheme.isBasis_affineOpens` in `AffineScheme`), `IsReduced` in `Properties`,
`Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField` and the open-immersion
residue-field isomorphism in `ResidueField`, and
`isPullback_fiberToSpecResidueField_of_isPullback` in `Fiber`.
The quasiseparated permanence module is included as a plain proof import.

Edge cases checked before writing:

- Empty X is allowed; all fibres can be empty and the conclusion still gives a
  nonempty affine base. Empty Y is excluded by the stated irreducibility and
  specified generic point, just as in the node.
- Y can be nonreduced, including a one-point nonreduced Artinian scheme. q is
  not required to be an open immersion, only a topological open embedding.
- The nilradical need not be finitely generated, and Y need not be Noetherian,
  affine, separated or quasi-separated. None of these is added as a binder.
- Positive characteristic and inseparable residue fields are allowed. The
  field isomorphism is the canonical map of reduction and restriction, with no
  algebraic closure or separability assumption.
- Over an already reduced integral affine base this specializes to the usual
  affine generic-flat shrinking. A zero-dimensional integral base causes no
  exception: its generic point is its only point.
- The single explicit universe u is the library's scheme universe; all opens,
  residue fields, pullbacks and fibres remain in it. There are no test-scheme
  quantifiers, independent small universes, local notation or implicit variables.

Searches actually run:

- `msearch.py ... leanfinder "finite type morphism irreducible base reduction
  nonempty affine open flat locally finite presentation unchanged fibres"`:
  eight hits, including `Flat`, `LocallyOfFinitePresentation`, base-change
  stability, `UniversallyOpen.of_flat` and finite-morphism fibres. None states
  this preparation with reduction and unchanged fibres.
- `msearch.py ... loogle '"Flat", "LocallyOfFinitePresentation"'`:
  four hits concerning flat descent, effective epimorphisms and faithful
  pullback; no matching preparation theorem.
- `msearch.py ... grep "generic.*flat|flat.*generic" AlgebraicGeometry`:
  successful search with zero hits in Mathlib.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for generic-flat/reduced-base
  combinations found the existing generic-flat finite-presentation interface
  and affine/reduced-flat preparation modules, but no theorem combining this
  node's conclusions. The reduced-flat affine preparation reduces the source
  and does not give this node's canonical residue-field and fibre comparisons.
- Searching the exact item id in both project source roots found only the
  downstream proof reference in `GenericFibreAssassinContainmentSpreads`, not
  an existing declaration of the item. Searching the new declaration name in
  both roots and `dag/lean_names_upstream.json` found no collision.

No STATEMENT-DISPUTED flag or mathematical node fault was found. The example
`CompactObject.lean` is withdrawn and contains no declarations; its associated
node was also read, so the current module conventions in the stage brief were
used for the header and documentation.

## Second reading by Q80

Independent second reading (maintainer review service, 2026-10-24), replacing
the worker's self-audit that stood here. Node read against Stacks 0578 (first
proof paragraph), 052A and 054M; Lean read against the node and the Mathlib
declarations of every stmt_dep record.

Node clauses and their Lean rendering (q := W.ι ≫ Y.nilradical.subschemeι,
g := pullback.snd f q):

1. f : X → Y finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`, the
   two-part convention of def-weil-finite-type-morphism. Exact.
2. Y irreducible with generic point η: `[IrreducibleSpace Y]`, `η`, `hη :
   IsGenericPoint η univ` (def-weil-irreducible-components mathlib_match,
   def-sc-generic-point record). Exact; no sobriety/quasi-separation added.
3. r : Y_red → Y: `Y.nilradical.subscheme`, `subschemeι`, the recorded
   def-weil-pbc-scheme-reduction declarations. Exact.
4. ∃ nonempty affine open W ⊆ Y_red, integral: `W : …subscheme.Opens`,
   Nonempty, `IsAffineOpen W`, `IsIntegral W.toScheme`. Exact.
5. g : X ×_Y W → W finite type, flat, LFP: `LocallyOfFiniteType g`,
   `QuasiCompact g`, `Flat g`, `LocallyOfFinitePresentation g` with
   g = pullback.snd f q, the def-pc-fibre-product record. Exact.
6. q homeomorphism onto a nonempty open V₀ ∋ η: `∃ V₀ : Y.Opens, η ∈ V₀ ∧
   IsOpenEmbedding q ∧ range q = V₀`. Exact (topological, rightly not an open
   immersion of schemes).
7. ∀ w, κ(q w) → κ(w) iso: `IsIso (q.residueFieldMap w)`. Exact.
8. Canonical fibre comparison over that field iso: `∃ e : g.fiber w ≅
   f.fiber (q w)` with `e.hom ≫ fiberι = g.fiberι ≫ pullback.fst f q` and
   `e.hom ≫ f.fiberToSpecResidueField = g.fiberToSpecResidueField ≫
   Spec.map (q.residueFieldMap w)`. Since `f.fiber y = pullback f
   (Y.fromSpecResidueField y)` with projections fiberι / fiberToSpecResidueField
   (Mathlib Fiber.lean:38-48), the two equations pin e.hom to the canonical
   pullback.lift; the iso is not arbitrary. Exact.
9. Unique η_W above η, generic in W: `∃ ηW, q ηW = η ∧ (∀ w, q w = η → w = ηW)
   ∧ IsGenericPoint ηW univ`. Exact.
10. Generic fibre LFP over κ(η_W): `LocallyOfFinitePresentation
    (g.fiberToSpecResidueField ηW)`. Exact.

Quantifier order (W first, then V₀, per-w e, ηW) matches the node. No
hypothesis stronger than the node: no Noetherian, reducedness, affineness or
quasi-separatedness of Y; single universe u, all bound.

Mathematical truth: 052A applies to X ×_Y Y_red → Y_red (finite type, integral
base) and gives a dense open with flat + finite presentation; affine shrinking
around η_S; r is a homeomorphism and closed immersion so residue fields agree,
and (X_W)_w = X ×_Y Spec κ(w) ≅ X_{q w}. Edge cases: empty X (fibres empty,
fine), non-reduced Artinian Y (q not an open immersion, only a topological
embedding, as stated), non-Noetherian Y with non-finitely-generated nilradical
(052A needs no Noetherianity), positive characteristic.

One definition per notion: no new definitions; Mathlib/project searches
recorded by the worker were rechecked: no existing theorem with the
reduction + residue-field + fibre clauses. Docstrings carry the source place,
`(blueprint: lem-trf-generic-flat-reduced-base-model)` and the six proof steps;
the single proof is `sorry`. `lean.statement` equals the file's signature
verbatim. Proof imports (ReductionUniversalHomeomorphism,
GenericFlatFinitePresentation, ClosedImmersionResidueFieldIso) exist in the
live source. No mismatch found; nothing in the Lean changed.
