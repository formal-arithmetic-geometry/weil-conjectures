## Worker report

Stage 2, Q15: state `AlgebraicGeometry.exists_isIso_stage_of_limit` in
`lean/Sheaf/AlgebraicGeometry/SchemeLimitIsomorphismDescent.lean` with its proof `sorry`.
The resumed dispatcher explicitly assigned stage 2; coord/brief-stage2.md §0 documents
this handoff from an accepted stage-1 split. There was no interrupted compile or delivery,
and both stage sandboxes contained only dispatcher markers before this work.
Only the item's `lean` field changes. There are no new nodes or dependency modules.
The accepted natural-language statement and proof are preserved.

I read Stacks `limits.tex`, Situation 081D (`situation-descent-property`, lines 1739–1748)
and Lemma 081E (`lemma-descend-isomorphism`, lines 1967–1988), including the proof.
081D requires the distinguished base and the two initial schemes to be qcqs. The accepted
item also assumes every base stage qcqs; the Lean retains that hypothesis on every stage,
rather than silently generalizing the item. The source's initial index 0 is any `i₀`.

Hypothesis and conclusion comparison:

- The small directed set is `{I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]`.
  The actual index `i₀ : I` already witnesses nonemptiness, so a separate Nonempty
  assumption is unnecessary. Scheme and index universes follow the project's convention.
- `D : Iᵒᵖ ⥤ Scheme.{u}` is precisely the inverse system. The two instance families
  over **all** `i : Iᵒᵖ` render quasi-compactness (`CompactSpace`) and quasi-separatedness
  (`QuasiSeparatedSpace`) of each base stage. The arrow-indexed `IsAffineHom (D.map a)`
  family renders all affine transitions.
- `c : Cone D` and `hc : IsLimit c` render the given scheme limit with specified
  projections: the limit scheme is `c.pt` and its projection is `c.π.app (op i₀)`.
  This does not choose a new limit or assume anything about its points.
- `P₀ Q₀ : Over (D.obj (op i₀))` contain exactly the two structure maps to the
  distinguished base. `h₀ : P₀ ⟶ Q₀` includes the required equation making the map
  a morphism over that base. The four source and target topological instances encode
  their qcqs hypotheses, without imposing finite presentation on their structure maps.
- `[LocallyOfFinitePresentation h₀.left]` is local finite presentation of the map
  itself, not of P₀ or Q₀ over the base.
- `hB` asserts `IsIso` of the underlying map obtained by applying
  `Over.pullback (c.π.app (op i₀))` to `h₀`. Mathlib's `Over.pullback` is defined
  at `CategoryTheory/Comma/Over/Pullback.lean:63`: its object is the scheme fibre
  product and its morphism is the canonical induced map between those fibre products.
  Thus the hypothesis concerns the specified base change, not just an isomorphism
  between the source and target objects.
- The existential conclusion supplies `i : I` and `hi : i₀ ≤ i`, then asserts `IsIso`
  for the same induced morphism pulled back along `D.map (homOfLE hi).op`.
  The opposite of the preorder arrow `i₀ ⟶ i` gives exactly `B_i ⟶ B_i₀`.

Recorded dependencies and their declarations:

- `def-weil-size-convention` and `def-weil-pbc-scheme-conventions` are convention
  records. Explicit universe parameters and the standard scheme properties implement
  the portions used here; neither requires a new definition.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and its categorical morphisms.
- `pqf-def-affine-morphism`: `AlgebraicGeometry.IsAffineHom` in
  `Mathlib.AlgebraicGeometry.Morphisms.Affine`, read at lines 47–48.
- `lem-weil-pbc-limit-affine-transition`:
  `AlgebraicGeometry.exists_limit_affine_transition`, module
  `WeilConjectures.AlgebraicGeometry.LimitAffineTransition`. Its module is publicly
  imported, and the theorem accepts the specified limiting cone rather than hiding
  or rebuilding its projections.
- `def-sbc-locally-finite-presentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:45`, the all-affine-pairs
  local property equivalent to the dependency's pointwise affine formulation.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` with its projections,
  used through the existing `CategoryTheory.Over.pullback` functor. No second
  base-change construction is introduced.

The existing proof dependency modules are plain imports. I read the public signatures
of `exists_flat_stage_of_limit`,
`exists_isClosedImmersion_stage_of_locallyOfFiniteType`, and
`exists_surjective_of_isLimit` in their three recorded WeilConjectures modules.
They use this same Over.pullback presentation and qcqs initial objects. Their
requirements are entailed by this statement (local finite presentation supplies local
finite type for the second). The other plain imports expose the existing cartesian
pasting, base-change permanence and flat-surjective-mono criterion. The declaration's
docstring records all four accepted proof steps and their node citations, including
the two pasting arguments retained by the maintainer's stage-1 repair.

Edge cases checked against the statement and source: `i₀` prevents an empty index type
without adding a limit-point nonemptiness assumption; empty schemes and an empty limit
are allowed; a constant singleton-index system is allowed; neither characteristic,
reducedness, Noetherianity nor a nonempty source or target is assumed. A nontrivial
nilpotent closed immersion is not incorrectly covered by an invertibility hypothesis.
The result asks for invertibility of h_i itself and does not replace it with existence
of some isomorphism. No definition contains postponed data, and the only postponed proof
is the named theorem with its source and accepted proof plan.

Existing-declaration searches were run using msearch.py and their actual records are
listed below. I also searched `lean/WeilConjectures`, `lean/Sheaf`, and
`dag/lean_names_upstream.json` for the blueprint id, scheme-limit isomorphism descent,
and `exists_isIso_stage`/`isIso.*stage`/`stage.*isIso`; there is no public exact match.
Private finite-torsor/finite-hypercover comparisons and the two-model isomorphism
existence theorem are not this assertion: they have stronger finite-presentation
conditions or produce a different morphism. The Mathlib natural-language hits supply
finite-presentation definitions and eventual equality of two existing maps, not
invertibility of the prescribed map. I opened the two equality declarations at
`Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean:635` and `:690` to confirm this.

- `grep` query `exists.*[Ii]so|[Ii]so.*exists|descend.*[Ii]so` in `AlgebraicGeometry/AffineTransitionLimit.lean`: available, 5 hits; 318, 751, 999, 1080, 1105. No exact match.
- `leansearch` query `A locally finitely presented morphism of qcqs schemes becomes an isomorphism at a finite stage if its pullback to an inverse limit with affine transition maps is an isomorphism`: available, 8 hits; AlgebraicGeometry.instLocallyOfFinitePresentationOfIsSmooth, AlgebraicGeometry.LocallyOfFinitePresentation.recOn, AlgebraicGeometry.instLocallyOfFiniteTypeOfLocallyOfFinitePresentation, AlgebraicGeometry.Scheme.instIsLocalAtTargetIsomorphismsZariskiPrecoverage, AlgebraicGeometry.locallyOfFinitePresentation_isStableUnderBaseChange, AlgebraicGeometry.LocallyOfFinitePresentation, AlgebraicGeometry.Scheme.Hom.finitePresentation_appLE, AlgebraicGeometry.LocallyQuasiFinite.recOn. No exact match.
- `loogle` query `"IsIso", "IsLimit", "Scheme"`: available, 0 hits; . No exact match.
- `leanfinder` query `Isomorphisms spread out from an inverse limit of qcqs schemes with affine transition maps for a locally finitely presented morphism between schemes over one stage`: available, 8 hits; AlgebraicGeometry.Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType, AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType, AlgebraicGeometry.ExistsHomHomCompEqCompAux.hii', AlgebraicGeometry.ExistsHomHomCompEqCompAux.exists_index, AlgebraicGeometry.ExistsHomHomCompEqCompAux.exists_eq, AlgebraicGeometry.ExistsHomHomCompEqCompAux.i', AlgebraicGeometry.exists_appTop_π_eq_of_isLimit, AlgebraicGeometry.LocallyOfFinitePresentation. No exact match.
- `grep` query `descend.*[Ii]so|[Ii]so.*(limit|stage)|eventually.*[Ii]so` in `AlgebraicGeometry`: available, 25 hits; Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean, Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean, Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean, Mathlib/AlgebraicGeometry/RelativeGluing.lean, Mathlib/AlgebraicGeometry/Modules/Tilde.lean, Mathlib/AlgebraicGeometry/Modules/Tilde.lean, Mathlib/AlgebraicGeometry/Sites/SmallAffineZariski.lean, Mathlib/AlgebraicGeometry/Sites/SmallAffineZariski.lean. No exact match.
- `leanfinder` query `A morphism locally of finite presentation which is invertible after pullback to a filtered affine transition scheme limit is invertible after pullback to some stage`: available, 8 hits; AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType, AlgebraicGeometry.LocallyOfFinitePresentation, AlgebraicGeometry.Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType, AlgebraicGeometry.instHasRingHomPropertyLocallyOfFinitePresentationFinitePresentation, AlgebraicGeometry.locallyOfFinitePresentation_iff, AlgebraicGeometry.locallyOfFinitePresentation_isStableUnderBaseChange, AlgebraicGeometry.HasAffineProperty.descendsAlong_of_affineAnd, AlgebraicGeometry.LocallyOfFinitePresentation.finitePresentation_appLE. No exact match.

## Review by Q15

I compared the completed signature to the accepted item with the source and dependency
modules open. In particular, I checked that qcqs of every B_i had not been reduced to
only B_i₀; that lfp applies to h₀.left; that both occurrences of Over.pullback act on
h₀; and that the stage transition is reversed by `.op`. The existing index `i₀`
accounts for the nonempty index set, and the standard preorder encoding follows the
project's directed-set convention. The complete theorem signature is copied verbatim
into lean.statement. Module mode, public statement imports, private proof imports,
source and blueprint docstrings, and the 100-character line bound were checked.
There is no statement correction or unresolved mathematical dispute.

No independent worker reading is claimed: this is a direct delivery, and the
maintainer performs the independent review as required by the dispatcher.

## Second reading by Q15

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
