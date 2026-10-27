## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothFibreDenseQuasiCompactSelection` states
`AlgebraicGeometry.Smooth.exists_isCompact_open_fibrewise_dense`, with proof `sorry`.
It introduces no definitions, no new nodes and no dependency repairs. The original
node is unchanged except for its `lean` record.

Source checked: Bosch--Lütkebohmert--Raynaud, Néron Models, §2.5, printed pp.55--57,
especially Lemma 3 on pp.56--57. I downloaded the primary scan named by the node into
the sandbox scratchpad and read these pages using pdftotext. The preliminary paragraph
on p.55 defines S-density by Zariski density in each residue-field fibre. Lemma 3
assumes exactly a smooth quasi-compact S-scheme and an S-dense open U, and concludes
the existence of a quasi-compact S-dense open contained in U. Its proof uses smooth
saturations of affine opens and a finite subcover. The delivered docstring instead
records the accepted node's five-step smooth-slicing proof, including all its cited
proof ingredients.

Hypotheses and conclusions, clause by clause:

- A scheme S and smooth p : X → S: `{X S : Scheme.{u}} (p : X ⟶ S) [Smooth p]`.
  The explicit universe u is arbitrary and all variables are explicitly bound.
- X quasi-compact: `[CompactSpace X]`, the recorded definition of quasi-compact
  underlying topological space, without a Hausdorff or separatedness hypothesis.
- U an open subscheme of X: `(U : X.Opens)`. Mathlib equips such an open with
  `U.toScheme` and canonical open immersion `U.ι`; this encodes precisely an open
  subscheme, rather than an arbitrary morphism or a second notion of immersion.
- For every s, U_s dense in X_s: `hU : ∀ s : S,
  Dense ((p.fiberι s) ⁻¹' (U : Set X))`.
  Mathlib defines `p.fiber s` as `pullback p (S.fromSpecResidueField s)` and
  `p.fiberι s` as its first projection. Thus this preimage is the underlying open
  subscheme U ×_S Spec κ(s) inside X ×_S Spec κ(s). This is topological density,
  with no replacement by schematic or geometric density.
- Existence of an open W: `∃ W : X.Opens`.
- W contained in U: `W ≤ U`, the inclusion of their underlying opens. Its canonical
  open subscheme therefore factors as an open subscheme of U.
- W quasi-compact: `IsCompact (W : Set X)`. The topology on W.toScheme is the
  subspace topology, so compactness of this subset is equivalent to CompactSpace
  of W.toScheme. It does not assert quasi-compactness of the inclusion W → X.
- Every W_s dense in X_s: `∀ s : S, Dense ((p.fiberι s) ⁻¹' (W : Set X))`, with
  exactly the same fibre and projection as in the hypothesis.
- Neither S nor U is assumed quasi-compact: there is no such binder. No
  quasi-separatedness, separatedness, finite presentation of p globally, or
  surjectivity of p is added.

Statement dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`. The relative-dimension and etale clauses of that
  dependency are not additional hypotheses of this item.
- `def-weil-pbc-quasi-compact-scheme`: `Mathlib.Topology.Defs.Filter`, `CompactSpace`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`, instantiated by canonical opens and their
  inclusions; no new immersion definition is introduced.
- `def-pc-base-change`: imported its recorded module
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`. Its record explicitly
  directs scheme-base-change users to `Limits.pullback`, not its module-sheaf
  declaration `Scheme.Modules.moduleBaseChange`. `Scheme.Hom.fiber` and `fiberι`
  in `Mathlib.AlgebraicGeometry.Fiber` are those pullback and first projection.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField`, with canonical map
  `Scheme.fromSpecResidueField`. I also read `Scheme.Hom.residueFieldMap`.

All six recorded statement-dependency modules are public imports. Stated proof
nodes are plain imports, including the recorded upstream slicing and etale-fibre
modules and the Mathlib modules for openness, etale base change, the affine basis,
compact spectra, continuous compact images, and covering base change.
`lem-trf-smooth-connected-fibre-normal-integrality` has no recorded declaration
or mathlib match; it is a proof-only prerequisite and has no import yet. Its role
remains explicit in the docstring, and no replacement statement is invented.

Edge cases checked mathematically before writing:

- Empty X: W = bottom works. Density of the empty subset in each empty fibre is
  automatic, and the empty subset is compact.
- Empty S: a morphism to it forces X empty; the universal fibre conditions have
  no points to quantify over and the same W works.
- Individual empty fibres: Dense is true for the empty underlying space; there
  is no assumption that p is surjective.
- U = top: take W = top, compact by the hypothesis on X.
- U = bottom: density forces every fibre empty, hence X empty by the fibre point
  corresponding to each x. Thus this case is consistent and not excluded.
- Non-quasi-compact U and non-quasi-compact S remain in scope, as in BLR. Compact
  X does not silently turn the statement into one assuming a quasi-compact
  morphism p: no `[QuasiCompact p]` is present.
- No dimension, characteristic, irreducibility, or nonemptiness restriction is
  imposed; arbitrary scheme universe u is retained.

Searches made on 2026-10-24:

- msearch.py, LeanFinder, query `A fibrewise dense open of a quasi compact smooth
  scheme contains a quasi compact fibrewise dense open`: eight hits, concerning
  dominant maps to images, dense rational domains, and compact fibres. None is
  the simultaneous fibrewise selection theorem.
- msearch.py, LeanSearch, query `An open dense in every fibre of a quasi compact
  smooth scheme contains a quasi compact fibrewise dense open`: eight hits,
  including compact fibres, QuasiCompact.mk, dense domains, and the unrelated
  topological `exists_open_dense_of_open_dense_subtype`. No match.
- msearch.py, Loogle, query `"Smooth", "IsCompact"`: one unrelated hit,
  `SmoothBumpFunction.isCompact_symm_image_closedBall`.
- msearch.py, Mathlib grep in AlgebraicGeometry, query
  `dense.*[Cc]ompact|[Cc]ompact.*dense|[Ff]iber.*[Dd]ense`: zero hits.
- rg on `lean/WeilConjectures` and `lean/Sheaf`, the same pattern plus
  `[Ff]ibre.*[Dd]ense`: existing dense opens and generic-fibre density results,
  but no quasi-compact selection theorem. I inspected
  `WeilConjectures.AlgebraicGeometry.GenericOpenFibreDensity` and the fibre
  density encodings in `Sheaf.AlgebraicGeometry.GoodCurvesFibreDensity`; they
  use the same Dense/preimage/fiberι expression, and state different results.
- rg for this node id in `lean/WeilConjectures`: no occurrence. Name search for
  `exists_isCompact_open_fibrewise_dense` and module name in both libraries and
  `dag/lean_names_upstream.json`: no match.

Validation: scompile.py compiled the delivered file in both sandbox and library
module modes successfully, with no errors or unexpected warnings. There are no
statement corrections or STATEMENT-DISPUTED issues.

## Second reading by NX

This is the author's final self-check, not an independent reviewer report; the
maintainer supplies the independent review required by the dispatch brief.
I reread the node, the delivered signature and BLR Lemma 3 together. The binder
`[CompactSpace X]` is on the source X; there is no compactness on S or U. Both
Dense expressions quantify over every s and concern the identical residue-field
fibre of p. The existential W is an open of X, W ≤ U is the containment clause,
and its subset compactness is exactly compactness of its open subscheme. The
preimage formulation does not require a chosen identification of residue fields
of points of U, and adds no geometric-density hypothesis. Empty spaces are not
excluded. No mismatch or change was found in this reading.
