## Worker report

The module `Sheaf.AlgebraicGeometry.Morphisms.AffineEtaleFiniteLocallyFreeMultisection`
states `AlgebraicGeometry.exists_affine_etale_finiteLocallyFree_multisection`.
Its only theorem has proof `sorry`; it introduces no definitions, axioms, or helper nodes.
Source read: Stacks Project, `more-morphisms.tex`, Tag 055W,
`lemma-fibre-geometrically-connected-reduced`, especially the second paragraph
(lines 13228–13252 in this checkout). The six proof steps of the accepted DAG split
are carried into the theorem docstring, including their dependency references.

The previous BLOCKED ending concerned the stage-1 restriction on reopening reviewed
splits. This is a stage-2 assignment: `coord/queue.tsv` lists this item at stage 2,
the live node is split and reviewed with no Lean record, and there is no repair note.
The maintenance handoff in `coord/brief-stage2.md` §0 explicitly permits recording the
Lean statement without reopening the accepted split. Only the item's `lean` field changes.

Hypothesis-by-hypothesis correspondence:

- The schemes are `{Y S : Scheme.{u}}`, with explicitly bound universe `u`.
- Affineness of `S` is `[IsAffine S]`; `h : Y ⟶ S` is the given family.
- Flatness is `[Flat h]`.
- Finite presentation is exactly the three hypotheses `[LocallyOfFinitePresentation h]`,
  `[QuasiCompact h]`, `[QuasiSeparated h]`, as the node specifies.
- Every fibre is geometrically reduced: `hred : ∀ t : S,
  GeometricallyReduced (h.fiberToSpecResidueField t)`.
- The distinguished point is `(s : S)` and its fibre is nonempty by
  `hs : Nonempty (h.fiber s)`.

Conclusion-by-conclusion correspondence:

- `∃ (U : Scheme.{u}) (a : U ⟶ S) (u : U) (hu : a u = s)` supplies the neighbourhood,
  its map, its point, and the specified equality. `IsAffine U` and `Etale a` give
  precisely the affine and étale conditions.
- `IsIso (a.residueFieldMap u)` is the induced residue-field isomorphism.
  Its source is κ(a(u)); transporting it along `hu` identifies this with κ(s).
- `∃ (E : Scheme.{u}) (p : E ⟶ U) (σ : E ⟶ pullback h a)` supplies the finite piece,
  its structural morphism, and the multisection into the chosen scheme fibre product.
- `Scheme.Hom.IsFiniteLocallyFree p` uses the recorded upstream class, exactly finite,
  flat and locally of finite presentation. `σ ≫ pullback.snd h a = p` is h_U ∘ σ = p.
- `Nonempty (p.fiber u) ∧ Subsingleton (p.fiber u)` means E_u has exactly one point.
  It does not assert degree one, reducedness, or an isomorphism E_u ≅ Spec κ(u).
- `Flat (pullback.snd h a)`, `LocallyOfFinitePresentation (pullback.snd h a)`,
  `QuasiCompact (pullback.snd h a)` and `QuasiSeparated (pullback.snd h a)` are exactly
  flatness and finite presentation of h_U.
- `∀ v : U, GeometricallyReduced ((pullback.snd h a).fiberToSpecResidueField v)`
  gives geometrically reduced fibres of the base-changed family.
- The displayed isomorphism `e` has source `(pullback.snd h a).fiber u` and target
  `pullback (h.fiberToSpecResidueField s)
    (Spec.map ((S.residueFieldCongr hu).inv ≫ a.residueFieldMap u))`.
  The ring morphism is the induced κ(s) → κ(u), with its equality transport made explicit.
  The two following equations require compatibility with the projections to Y and
  Spec κ(u). They determine the canonical fibre isomorphism uniquely: the projection
  to Y and the structural map to Spec κ(s) determine the map to Y_s by its pullback
  universal property, and these together with the projection to Spec κ(u) determine
  the map to its base change. Thus this is the canonical identification in the node,
  with no arbitrary replacement map or additional mathematical requirement.
- The last implication is exactly that geometric connectedness of Y_s over κ(s)
  implies geometric connectedness of (Y_U)_u over κ(u). Mathlib's geometric
  connectedness uses `ConnectedSpace`, whose `toNonempty` field includes nonemptiness.

Recorded dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat` (stalkwise equivalence in its docstring).
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-weil-pbc-scheme-conventions` has a convention record, not a declaration.
  Its finite-presentation convention is rendered with the three named classes;
  `QuasiCompact` and `QuasiSeparated` are imported from their Mathlib modules.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`,
  `AlgebraicGeometry.Scheme.Hom.fiber`, `.fiberι`, `.fiberToSpecResidueField`.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField`, `.Hom.residueFieldMap`;
  `.residueFieldCongr` supplies the equality transport.
- `def-pc-geometrically-irreducible`: the recorded
  `Mathlib.AlgebraicGeometry.Geometrically.Integral` publicly imports
  `AlgebraicGeometry.GeometricallyReduced`; its record expressly specifies the
  additional `Mathlib.AlgebraicGeometry.Geometrically.Connected` import for
  `AlgebraicGeometry.GeometricallyConnected`. Both full class signatures and
  docstrings were read, along with `geometrically_iff_forall_fiberToSpecResidueField`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`, `.map`; `IsAffine` is the Mathlib class in `AffineScheme`.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`.
- `def-pc-finite-locally-free`:
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`,
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree`.
- `def-weil-connected-scheme`: its `mathlib_match` is `ConnectedSpace` in
  `Mathlib.Topology.Connected.Basic`; the geometric connectedness import supplies it.

Every recorded proof-dependency module is imported privately unless already a public
statement import. For Mathlib matches, the defining modules are imported too. This includes
local Noetherianity and its localization, the affine-open basis and stalk identifications,
finite-presentation/flatness permanence, the CM locus and slice, the elementary étale
finite piece and its persistence, and the already stated CM density theorem.

Edge cases checked before drafting:

- Empty S or an empty distinguished fibre cannot supply the hypotheses; empty other fibres
  are permitted. The conclusion does not require p to be surjective over all of U.
- A singleton fibre may be nonreduced or have residue field larger than κ(u); the statement
  makes no rank-one or residue-field claim about p.
- The identity family over Spec k admits the identity neighbourhood and multisection.
- Nonperfect residue fields are allowed; geometric reducedness and connectedness use all
  field extensions, not algebraic closure assumptions or rational-point assumptions.
- Non-Noetherian affine bases are allowed; only the fibre local rings need Noetherianity
  in the proof route.
- Every scheme is in the explicitly bound universe u. The standard same-universe geometric
  property classes are used without an independent smaller universe for test fields.
- σ need not be an immersion or a section; no such extra condition is present.

Searches for an existing statement (all on 2026-10-23 UTC):

- `msearch.py ... leanfinder "An affine elementary etale neighbourhood of a nonempty fibre
  of a flat finitely presented scheme has a finite locally free multisection with singleton
  fibre"`: eight hits, on standard smooth charts, the étale category, étale loci and
  descent of an étale algebra. None supplies this multisection existence package.
- `msearch.py ... loogle "AlgebraicGeometry.Flat, AlgebraicGeometry.IsFinite"`: eight hits
  on ranks of an existing finite flat map and pullback rank formulas; no existence result.
- `msearch.py ... grep "multisection|multiSection|exists.*finite.*free" AlgebraicGeometry`:
  zero Mathlib hits.
- `rg -n 'multisection|multiSection|lem-trf-affine-etale-finite-free-multisection|
  exists_affine_etale' lean/WeilConjectures lean/Sheaf`: project hits include the
  connected-open theorem assuming an existing multisection and other affine étale
  neighbourhood results; none has this statement. Read the connected-open and
  geometrically-connected-fibre-neighbourhood modules to compare their full signatures.
- A separate upstream search for this exact blueprint id and finite locally free
  multisection text returned no matches. A duplicate declaration name was not found.
  The prescribed msearch wrapper retained its raw outputs in sandbox `searches.jsonl`.

No statement correction, disputed statement, missing notion, or unusable dependency
was found. No new nodes or dependency modules are delivered.

Validation: `scompile.py NV lem-trf-affine-etale-finite-free-multisection <module>`
compiled both the sandbox probe and the final library module cleanly (16.4 s and 4.9 s).
All module lines are at most 100 characters. Both automatic-implicit options are disabled.

## Second reading by NV

A separate second pass by the same dispatcher worker re-read the node and finished module;
the dispatcher's prohibition on starting other agents is respected. The maintainer supplies
the independent review. This pass checked each binder and conjunct against the correspondence
above. In particular: quasi-separatedness is present on both families, the distinguished
residue-field map is the induced one, the singleton is a scheme-theoretic fibre, the
fibre isomorphism uses κ(s) explicitly with the equality transport in the correct direction,
both projection equations enforce canonicity, and geometric connectedness is conditional
and nonempty. No mismatch was found or change needed. The accepted proof split and all
non-Lean node fields remain unchanged.
