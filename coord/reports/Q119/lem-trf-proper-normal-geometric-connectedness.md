## Worker report

The module `Sheaf.AlgebraicGeometry.ProperNormalGeometricConnectedness` states
`AlgebraicGeometry.proper_normal_geometric_connectedness`, with its sole proof `by sorry`.
There are no definitions, helper axioms, new nodes, dependency repairs, or statement changes.
The module docstring and theorem docstring cite Stacks Tag 0AY8,
`lemma-geometrically-connected-fibres-towards-normal`, and the theorem docstring records
all six proof steps of the DAG with their named inputs.

I read the complete item, its statement dependencies and their recorded declarations,
and `literature/stacks-project/more-morphisms.tex`, lines 15358–15387. The source has
exactly the six listed hypotheses and concludes equality of the structure-sheaf
pushforward and geometrically connected fibres. The DAG explicitly interprets the
first equality as the canonical map being an isomorphism and connectedness as nonempty.
The Lean follows this interpretation.

Clause-by-clause correspondence:

- Schemes and morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Properness: `[IsProper f]`. Mathlib defines this as separated, universally closed,
  locally of finite type; universal closedness supplies quasi-compactness, so this
  is the node's finite-type properness. There is no finite-presentation assumption.
- Integral base: `[IsIntegral S]`, including nonemptiness. No normality assumption
  on `X` or irreducibility assumption on `X` is introduced.
- Its generic point: `(ξ : S) (hξ : IsGenericPoint ξ (Set.univ : Set S))` says
  that the closure of `{ξ}` is all of `S`, using the recorded generic-point notion.
- Normality of the base: `hnormal : ∀ x : S, IsDomain (S.presheaf.stalk x) ∧
  IsIntegrallyClosed (S.presheaf.stalk x)`. These are exactly the local rings of
  `S`, being domains and integrally closed in their fraction fields, as the node
  specifies inline. No Noetherian assumption or normal-source replacement is used.
- Reduced source: `[IsReduced X]`, Mathlib's sectionwise reducedness, equivalent
  to the stated stalkwise condition (the recorded dependency includes both forms).
- Dominance of every component: `hgeneric : ∀ Z ∈ irreducibleComponents X,
  ∀ η : X, IsGenericPoint η Z → f η = ξ`. This quantifies over every irreducible
  component and every generic point, rather than merely asserting dominance of
  the whole source or selecting one component.
- The structural equality of generic global sections: `hsections :
  IsIso (f.fiberToSpecResidueField ξ).appTop`. The named map is the actual
  structure map `X_ξ → Spec κ(ξ)`, and `appTop` is its canonical map on global
  sections. Since `Γ(Spec κ(ξ), ⊤)` is canonically `κ(ξ)` by `Scheme.ΓSpecIso`,
  this is precisely the canonical field-algebra map being an isomorphism.
  It does not ask for an arbitrary abstract ring isomorphism.
- First conclusion: `IsIso f.toLRSHom.toHom.c`. By `PresheafedSpace.Hom.c` this
  is the canonical natural transformation `O_S → f_* O_X`. Both presheaves
  are sheaves; the full inclusion of sheaves identifies their isomorphisms
  with isomorphisms of the underlying presheaves. Thus this concludes the
  required sheaf isomorphism, rather than an isomorphism only on global sections.
- Second conclusion: `∀ s : S, GeometricallyConnected
  (f.fiberToSpecResidueField s)`. The fibre and its canonical projection are the
  recorded `Scheme.Hom.fiber` and `fiberToSpecResidueField`. Mathlib's
  `GeometricallyConnected` is `geometrically (ConnectedSpace ·)`, testing every
  field-valued base change and every scheme realizing the pullback. A map
  `Spec L → Spec κ(s)` is the data of the field extension in the node, so this
  says exactly that every `X_s ×_{κ(s)} L` is nonempty and connected.
  `ConnectedSpace.toNonempty` rules out the empty space. The geometric test
  fields use the scheme's universe `u`, as in Mathlib's standard geometric
  properties; this is not an independent potentially too-small test universe.
- No extra hypotheses: no Noetherian, finite-presentation, flatness, smoothness,
  source irreducibility, rational point, or algebraically closed base is assumed.

Statement dependencies used (recorded module and declaration):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`.
- `def-pc-integral-scheme` and `def-pc-reduced-scheme`:
  `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`
  and `AlgebraicGeometry.IsReduced`.
- `def-sc-generic-point`: `Mathlib.Topology.Sober`, `IsGenericPoint`.
- `def-weil-irreducible-components`: the dependency is a Mathlib leaf with no
  `lean` record; its exact `mathlib_match` is `irreducibleComponents` in
  `Mathlib.Topology.Irreducible`. Its source defines `{s | Maximal IsIrreducible s}`.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField` and `Scheme.Hom.residueFieldMap`;
  the fibre construction uses the canonical residue field, rather than a chosen field.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`,
  `Scheme.Hom.fiber` and `Scheme.Hom.fiberToSpecResidueField`.
- `def-weil-connected-scheme`: the dependency is a Mathlib leaf with no `lean`
  record; its `mathlib_match` is `ConnectedSpace` in
  `Mathlib.Topology.Connected.Basic`. The field `toNonempty` is read in the source.
- The inline normal-domain condition uses `IsDomain` and `IsIntegrallyClosed`
  from `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, consistent with
  the normal-ring proof dependency. `GeometricallyConnected` is used directly
  from `Mathlib.AlgebraicGeometry.Geometrically.Connected`; it is not redefined.

Proof-plan imports include the already recorded
`Sheaf.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions`
(`reduced_normal_iff_integrallyClosed_totalFractions`) and
`Sheaf.AlgebraicGeometry.SteinFactorizationAffine`
(`Scheme.Hom.steinFactorization_affine`). The other proof inputs are Mathlib
leaves supplied by the explicit Mathlib imports and their public imports:
properness permanence, qcqs over an affine, component coverage, sobriety,
section nilpotence detected by residues, and affine stalks/function fields.
These are proof-plan imports, not extra assumptions in the statement.

Edge cases checked before finalizing:

- An empty base is excluded by the node's integral hypothesis, and `IsIntegral S`
  includes nonemptiness. An empty source cannot satisfy `hsections`: the generic
  global section ring would be the zero ring, whereas `κ(ξ)` is a nonzero field.
- Empty affine opens in the proof have zero section rings on both sides, so the
  sheaf conclusion is not restricted to nonempty opens.
- `X` can have several components, and the generic-point hypothesis tests all
  of them. A vertical isolated component is not silently ignored.
- Nonreduced source examples fail `[IsReduced X]`; cusp normalization examples
  with a nonnormal base fail `hnormal`. A nontrivial finite field extension
  at the generic fibre fails the structural global-section isomorphism.
- Identity maps of integral normal schemes satisfy the hypotheses; their
  point fibres are spectra of residue fields and remain nonempty connected
  after every field extension. Identity field extensions are included.
- The theorem imposes no dimension, characteristic, Noetherian, or finite-
  presentation restriction. Large non-Noetherian integral normal bases remain
  in its domain, and all explicitly occurring universes and variables are bound.

Searches for an existing statement:

- `msearch.py` LeanFinder query: "Proper morphism to normal integral scheme with
  reduced source dominant components trivial generic global sections has
  geometrically connected fibres". Eight hits included normalization dominance,
  `IsIntegralHom`, `IsIntegral`, universally closed maps and field-valued global
  section results. They do not assert this connectedness theorem under its six
  hypotheses. I read the geometric-connectedness and properness source.
- `msearch.py` Loogle query: `"IsProper", "GeometricallyConnected"`.
  Success with zero hits.
- `msearch.py` grep query:
  `geometricallyConnected.*(normal|proper)|[Ss]tein[Ff]actor|connected.*[Ff]iber`
  in `AlgebraicGeometry`. Five hits in Mathlib's geometric-connectedness module;
  they derive fibre connectedness from assumed geometric connectedness, rather
  than proving it under the node's hypotheses.
- `msearch.py` LeanSearch query: "Proper morphism to a normal integral scheme
  with reduced source and trivial generic global sections has geometrically
  connected fibres". Eight hits: `IsProper`, its constructor, projections,
  eliminators and `isReduced_of_isIntegral`; none is this theorem.
- Text searches of the project's `lean/Sheaf` and upstream `WeilConjectures` for
  the item id, `proper_normal_geometric_connectedness`, and combinations of
  properness, normality and connected fibres found no declaration of this theorem.
  The node id occurs in a proof docstring of the smooth-target exceptional-tree
  theorem, which is a consumer, not a declaration of the present result.
- Earlier interrupted-session searches in `searches.jsonl` are retained. They
  likewise found Mathlib's exact irreducible-component and connectedness notions,
  and no theorem matching the item. No interrupted delivery existed in the sandbox.

Validation: `scompile.py Q119 lem-trf-proper-normal-geometric-connectedness`
compiled the final module as a sandbox and as its library module, with no errors
and no warnings. The only postponed proof is the item theorem itself. No
`STATEMENT-DISPUTED` issue or node fault remains.

## Second reading by Q119

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
