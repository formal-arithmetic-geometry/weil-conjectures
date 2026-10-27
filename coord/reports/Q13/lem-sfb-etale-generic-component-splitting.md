## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleGenericComponentSplitting` states
`AlgebraicGeometry.exists_finite_etale_irreducible_generic_component_splitting`.
Its sole theorem has proof `sorry`; no definition, helper theorem, or axiom is added.
The accepted natural-language statement, proof, and dependencies are unchanged.
The node copy changes only `lean`.

Source read: `literature/stacks-project/more-morphisms.tex`, Tag 0551,
`lemma-make-components-generic-fibre-geometrically-irreducible`, full statement and proof.
The node packages its diagram using the chosen pullback; the finite étale property
of the induced map to the original family follows by base change and is not a
separate clause of this node's statement.

Hypothesis and conclusion correspondence:

- Schemes and morphism: `{X S : Scheme.{u}}` and `(f : X ⟶ S)`.
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the conjunction
  recorded by `def-weil-finite-type-morphism`.
- Nonempty irreducible base: `[IrreducibleSpace S]`. This class includes
  nonemptiness, so no separate base nonemptiness binder is necessary.
- A nonempty open subscheme: `∃ U : S.Opens, (U : Set S).Nonempty ∧ ...`;
  its scheme is `U.toScheme` and its inclusion is `U.ι`.
- A nonempty irreducible affine scheme: `∃ B : Scheme.{u}, IrreducibleSpace B ∧
  IsAffine B ∧ ...`. IrreducibleSpace again includes nonemptiness.
- The displayed cover: `∃ g : B ⟶ U.toScheme, IsFinite g ∧ Etale g ∧ Surjective g ∧ ...`.
  These are precisely finiteness, étaleness, and surjectivity on points.
- The family P = X ×_S B: `pullback f (g ≫ U.ι)`, with structural map
  `pullback.snd f (g ≫ U.ι)` to B.
- Its generic point: `∃ ξ : B, IsGenericPoint ξ Set.univ ∧ ...`. The predicate says
  `closure {ξ} = Set.univ`; uniqueness in the sober T0 scheme space makes this
  equivalent to referring to the generic point of B.
- Scheme-theoretic generic fibre: `(pullback.snd f (g ≫ U.ι)).fiber ξ`.
- Every irreducible component: `∀ A ∈ irreducibleComponents ↥(...fiber ξ), ...`.
  This is maximal nonempty irreducibility, with no choice of scheme structure.
- Residue field: `B.residueField ξ`, exactly κ_B(ξ).
- Every field extension: `∀ (E : Type u) (_ : Field E)
  (z : Spec (CommRingCat.of E) ⟶ Spec (B.residueField ξ)), ...`.
  Contravariance of Spec identifies these maps with field embeddings κ_B(ξ) → E.
  The same universe u as the schemes and their residue fields follows the existing
  generic-components-split interface; no independent lower field universe occurs.
- Inverse image after extension: `pullback.fst
  ((pullback.snd f (g ≫ U.ι)).fiberToSpecResidueField ξ) z` is the projection from
  the field base change of the generic fibre, and `⁻¹' A` is its inverse image of A.
- Nonempty and irreducible: `IsIrreducible` of this inverse image. Mathlib's
  definition explicitly conjoins nonemptiness and preirreducibility. This is the
  explicit subset interpretation used by the node and by generic-components-split.
- Empty generic fibre is permitted: there is no nonemptiness binder on X, P, or
  the fibre; in that case the universal component assertion is vacuous.
- There is no Noetherian, reducedness, separatedness, or flatness assumption on
  either S or f. In particular neither `IsIntegral S` nor `IsIntegral B` occurs.

Dependency interfaces read and used (no interface repair is required):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its category
  morphisms, `AlgebraicGeometry.Spec`, and `AlgebraicGeometry.Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; together with
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffine`, which
  makes the canonical map to the spectrum of global sections an isomorphism.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`, `IsIrreducible`, and
  `IrreducibleSpace` for the recorded irreducible-components Mathlib match.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, and `pullback.snd`.
- `Mathlib.AlgebraicGeometry.Fiber`: `AlgebraicGeometry.Scheme.Hom.fiber` and
  `AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField`.
- `Mathlib.Topology.Sober`: `IsGenericPoint`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `AlgebraicGeometry.Scheme.residueField`.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral` and its imported
  `Mathlib.AlgebraicGeometry.Geometrically.Irreducible`:
  `AlgebraicGeometry.GeometricallyIrreducible`. Its full signature and field-test
  docstring were checked. Since A is an ambient subset rather than a scheme,
  the conclusion uses its explicit field-extension test, as the node requires,
  rather than duplicating a geometric-irreducibility definition or inventing a
  reduced closed scheme structure. This recorded module is publicly imported.

All stated non-Mathlib proof dependencies are imported privately: the full signatures
and proof docstrings of `AlgebraicGeometry.affine_fibre_sections_tensor`
(`WeilConjectures.AlgebraicGeometry.AffineFibreSectionsTensor`),
`AlgebraicGeometry.Scheme.etale_fibre_iff_forall_etale_neighbourhood`
(`WeilConjectures.AlgebraicGeometry.Morphisms.FlatFibreEtaleNeighbourhoods`),
`AlgebraicGeometry.exists_finite_etale_geometric_component_extension`
(`WeilConjectures.AlgebraicGeometry.GenericComponentsSplit`), and
`AlgebraicGeometry.residue_polynomial_lift`
(`Sheaf.AlgebraicGeometry.EtaleResiduePolynomialLift`) were read. The other stated
proof inputs are Mathlib modules imported directly or transitively. The proof-only
node `lem-sfb-monic-quotient-faithful-tensor-coordinates` currently has neither a Lean
record nor a Mathlib match, so it supplies no module to import. It is not needed to
type the statement; no replacement or new definition is introduced. The nine proof
steps are reproduced in the theorem docstring for stage 3.

Edge cases checked: the empty scheme as X, or an empty generic fibre with X nonempty;
the excluded empty base (IrreducibleSpace is nonempty); a nonreduced irreducible base
such as Spec(k[ε]/ε²), for which B must not be required integral; a non-Noetherian
irreducible base; the identity field extension L = K and degree-one polynomial;
positive characteristic including inseparable further field extensions E/κ(ξ).
None is excluded or changes the statement. U is not required affine, although the
source's construction can choose it affine.

Searches made before writing:

- `msearch.py ... leanfinder` with query "finite etale surjective cover of open
  irreducible base makes generic fibre components geometrically irreducible": eight
  hits (genericPoint_eq_of_isOpenImmersion, surjective_isZariskiLocalAtTarget,
  Scheme.Etale, irreducibleSpace_of_isIntegral, finite-type fibre Jacobson and
  cover/dominance/sobriety results), none stating this conclusion.
- `msearch.py ... loogle` with query
  `AlgebraicGeometry.Etale, AlgebraicGeometry.GeometricallyIrreducible`: zero hits.
- `msearch.py ... grep` with query
  `0551|finite_etale.*generic_component|irreducible.*generic.*splitting` in
  `AlgebraicGeometry`: zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for Tag 0551, generic-component
  constructions, and `generic_component_splitting`, and an exact node-id search in
  `lean/WeilConjectures`. The upstream generic-component field extension theorem
  lacks the finite surjective cover of an open; the compatible/model/spread
  declarations likewise have different outputs. The existing Sheaf theorem
  `exists_finite_etale_generic_component_splitting` in
  `FiniteEtaleGenericComponentSplitting.lean` assumes an integral Noetherian compact
  base and concludes an integral cover. Its full declaration and docstring were read;
  it is a strict specialization, unusable as an existing match for this node.
  The chosen new declaration name has no hit in the live library.

The inherited ending concerned stage-1 duplicate splitting. The current node remains
`split`, has no Lean record, and appears in stage 2 in `coord/queue.tsv`. There is no
repair note for this item. The explicit stage-handoff rule in `coord/brief-stage2.md`
§0 authorizes this statement delivery; no accepted split is reopened.

Validation: scompile.py compiled the sole delivered module in sandbox and library
mode (3.5 s and 5.7 s), with no errors or unexpected warnings. All variables and the
universe are explicitly bound; both auto-implicit options are false. No statement
correction or disputed claim was necessary.

## Second reading by Q13

Performed a separate comparison pass with the live node and completed module open;
the dispatch brief prohibits starting another agent. Checked the complete binder and
conclusion correspondence above, especially nonemptiness of both S and B through
IrreducibleSpace, the direction of the second pullback projection to B, the residue
field of B at ξ (not of S), and inverse images of individual components after every
extension (not merely irreducibility of their union). The only theorem proof is
`sorry`. Checked against the full Tag 0551 text that no integral or Noetherian
specialization slipped in from the nearby existing theorem. Checked that U need
not be affine, that the generic fibre need not be nonempty, and that no extra
flatness/separatedness hypothesis occurs. No mismatch found and no change made.
