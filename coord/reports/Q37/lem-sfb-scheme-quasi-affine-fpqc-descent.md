## Worker report

The module `Sheaf.AlgebraicGeometry.SchemeQuasiAffineFpqcDescent` states
`AlgebraicGeometry.isQuasiAffineHom_of_fpqc_cover`, with `sorry` as its only proof.
It introduces no definitions and changes only the item's `lean` field.
The source was read in `literature/stacks-project/descent.tex`, lines 6002–6047,
Tag 02L7, `lemma-descending-property-quasi-affine`. The node requests precisely
the descent implication of that lemma, not its separate base-change implication.

Hypothesis and conclusion correspondence:

- The schemes `Y` and `U` and morphism `f : Y ⟶ U` give the node's morphism.
  Both schemes have explicit universe `u`, implementing the size convention;
  the index type has an independent explicit universe `v`.
- `{I : Type v}`, `Uᵢ : I → Scheme.{u}` and `p : ∀ i : I, Uᵢ i ⟶ U` give the
  entire family. No finiteness or nonemptiness assumption is imposed on `I`.
- `hp : Presieve.ofArrows Uᵢ p ∈ Scheme.fpqcPrecoverage U` is exactly the
  recorded fpqc-family interface: flatness, joint surjectivity, and the
  quasi-compact covering condition. It does not require individual members
  to be quasi-compact. Mathlib's `QuasiCompactCover.exists_isAffineOpen_of_isCompact`
  recovers the node's finite affine refinements from this condition.
- `h : ∀ i : I, IsQuasiAffineHom (pullback.snd f (p i))` is the hypothesis on
  every base-changed morphism `Y ×_U Uᵢ i ⟶ Uᵢ i`; the second projection is essential.
- `IsQuasiAffineHom f` is the conclusion. Its recorded definition quantifies
  over every affine open of `U` and requires its preimage to be quasi-affine.
  Mathlib's absolute `Scheme.IsQuasiAffine` includes `CompactSpace` and supplies
  the canonical open immersion into `Spec Γ(X, ⊤)`. Conversely a quasi-compact
  open immersion into an affine scheme gives this property by
  `Scheme.IsQuasiAffine.of_isImmersion`. Thus the explanatory clause about
  quasi-compact open subschemes of affine schemes is retained by this definition.
- There are no separation, Noetherian, finite-type, finite-presentation,
  affineness-of-base, or quasi-compactness-of-base assumptions.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec` and `Spec.map`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fpqcPrecoverage`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; `Mathlib.AlgebraicGeometry.Pullbacks` provides
  the scheme pullbacks. These are the recorded fibre-product declarations.
- `WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine`:
  `AlgebraicGeometry.IsQuasiAffineHom`, whose field is exactly the affine-open
  inverse-image condition. No private replacement is used.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`, used within
  the imported canonical quasi-affine embedding interface.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, within `Scheme.IsQuasiAffine`.
- `def-weil-size-convention` is a metatheoretic convention, so its record has
  no defining declaration to import; the theorem declares all universe levels.

The proof docstring includes all five node proof steps: finite affine refinement,
finite coproduct of canonical affine embeddings, qcqs descent, explicit tensor
flat-base-change identification of the canonical map, and open-immersion descent.
Recorded proof dependencies with Lean modules are imported, including
`Sheaf.AlgebraicGeometry.QuasiAffineBaseChange`,
`WeilConjectures.AlgebraicGeometry.FpqcDescendQuasiCompact` and
`WeilConjectures.AlgebraicGeometry.IsSeparatedOfFlatSurjectiveBaseChange`.
Mathlib modules supplying the remaining recorded proof dependencies are imported
for their coproducts, affine and separated permanence, flat descent, global
sections, affine pullbacks, and quasi-affine canonical embeddings.

Edge cases checked before writing: empty `Y`; empty `U` and empty covering family;
empty components; repeated indices; infinite covering families; non-quasi-compact
covering members; non-separated or non-Noetherian bases. None is excluded.
For an empty index type, fpqc membership forces the target to be empty, which
also forces the source of `f` to be empty. The conclusion therefore remains true.
An independent index universe does not restrict the schemes or make a test
condition vacuous: the family and its actual covering membership are explicit.
No disputed statement or dependency fault was found.

Searches, 2026-10-24, using the prescribed `msearch.py Q37` wrapper:

- LeanFinder: `Quasi affine morphisms of schemes descend along fpqc covering
  families of their target`: eight results, including
  `HasAffineProperty.descendsAlong_of_affineAnd`, absolute
  `Scheme.IsQuasiAffine.of_isAffineHom`, and general local-property descent.
  None states quasi-affine morphism descent for covering families.
- Loogle: `"IsQuasiAffine", "DescendsAlong"`: zero results.
- Mathlib grep, `AlgebraicGeometry`:
  `QuasiAffine.*[Dd]esc|[Dd]esc.*QuasiAffine|quasi.affine.*fpqc|fpqc.*quasi.affine`:
  zero results.
- LeanSearch: `Quasi affine morphisms of schemes descend along faithfully flat
  quasi compact covering families`: eight results on general descent,
  absolute quasi-affineness and quasi-compact covers; no matching statement.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for `IsQuasiAffine`,
  `QuasiAffineHom`, `quasiAffine`, and the descent expression above found the
  recorded upstream relative definition and project base-change/locality/effective
  descent statements. Effective descent concerns effectivity of descent data,
  not the property of an already given scheme morphism. The spaces statement
  uses this node as an input. None is the requested theorem.
- `rg` for `lem-sfb-scheme-quasi-affine-fpqc-descent` on `lean/WeilConjectures`
  found no attached declaration; the project occurrence in
  `SpaceQuasiAffineAffineDescent.lean` is a proof citation, not a declaration.
- `dag/lean_names_upstream.json` confirms the recorded `IsQuasiAffineHom`
  definition and its finite-type consequence, without this descent theorem.

Validation: `scompile.py Q37 lem-sfb-scheme-quasi-affine-fpqc-descent` compiled
the delivered file in sandbox and library module modes against the published
server build, with exit code zero and no errors or unexpected warnings.

## Second reading by Q37

Worker self-check, with the node, dependency definitions and completed module
open; the independent delivery review is performed by the maintainer, as the
dispatcher brief specifies. No other agent was started.

I rechecked `f : Y ⟶ U`, the unrestricted family, fpqc membership, each second
pullback projection, and the relative conclusion against each clause of the
node. In particular, the conclusion is relative quasi-affineness, not absolute
quasi-affineness of `Y` over a possibly non-affine base. The fpqc hypothesis is
family-level membership, not individual quasi-compactness. The relative class
uses the exact recorded upstream definition, and its absolute quasi-affine
condition includes quasi-compactness. All binders and universes are explicit;
`autoImplicit` is disabled. The proof docstring follows all five node steps and
includes the empty-refinement case. No mismatch or correction was needed.
