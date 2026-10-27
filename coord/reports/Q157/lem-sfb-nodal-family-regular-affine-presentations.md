## Worker report

The module `Sheaf.AlgebraicGeometry.NodalFamilyRegularAffinePresentations` states
`AlgebraicGeometry.nodal_family_regular_affine_presentations`, with its only proof
`sorry`. It introduces no definitions and changes only the item's `lean` record.
The source was read in `literature/stacks-project/algebra.tex`, Tags 00SY (syntomic),
00SV(1) (local regularity), 061L (principal regular neighbourhood), and
`curves.tex`, Tag 0C4E (nodal curves are LCI). The seven-step node proof is reproduced
in the theorem docstring, including placing the equation hy-1 first.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Schemes X and S, morphism f | `{X S : Scheme.{u}} (f : X ⟶ S)` with explicit universe u |
| Locally Noetherian base | `[IsLocallyNoetherian S]` |
| Flat f | `[Flat f]`, Mathlib's equivalent affine-pair/stalkwise notion |
| Finite presentation | `[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]` |
| Geometric fibre at s | `pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫ S.fromSpecResidueField s)` |
| Nonempty, reduced, pure dimension one | The first three conjuncts of `hgeom`: `Nonempty`, `IsReduced`, and `Scheme.IsPureDimension ... 1` |
| Every closed point outside the fibre's smooth locus | `∀ x`, membership in `closedPoints` and nonmembership in the smooth locus of `pullback.snd` |
| Completed local ring at its maximal ideal | `AdicCompletion (IsLocalRing.maximalIdeal (...presheaf.stalk x)) (...presheaf.stalk x)` |
| Isomorphic to Ω[[u,v]]/(uv) over Ω | `∃ e : ... ≃+* (MvPowerSeries (Fin 2) Ω ⧸ Ideal.span {X 0 * X 1})`, followed by the equation for every `a : Ω` |
| The Ω-algebra structure in this equation | The coefficient map is `ΓSpecIso.inv ≫ (pullback.snd ...).appLE ⊤ ⊤ le_top ≫ ...presheaf.germ ⊤ x trivial`, then the canonical map `AdicCompletion.of`; its image under e is `Ideal.Quotient.mk _ (MvPowerSeries.C a)` |
| Every ordinary fibre is pure of dimension one | First conclusion: `∀ s, (f.fiber s).IsPureDimension 1 ∧ ...` |
| Every ordinary fibre is LCI over κ(s) | Every point lies in an affine open U whose canonical κ(s)-algebra of sections is finite type and satisfies `Algebra.IsLocalCompleteIntersection` |
| All affine V and x in their preimage | Second conclusion: `∀ (V : S.affineOpens) (x : X), f x ∈ V.1 → ...` |
| Affine neighbourhood U containing x, within f⁻¹V | `∃ A : NodalCanonicalPresentation f, A.V = V ∧ x ∈ A.U.1`; `A.U` is affine and `A.over` supplies the inclusion |
| Nonnegative c, c+1 variables, c ordered equations | The existing presentation has `c : ℕ`, `quotient : MvPolynomial (Fin (c+1)) ... →+* ...`, and `equations : Fin c → ...` |
| Polynomial quotient presentation | Its `surjective` and `kernel` fields give exactly B as the quotient by its equations |
| Ordered regular sequence in the whole polynomial ring | `A.regular : RingTheory.Sequence.IsRegular ... (List.ofFn A.equations)` |
| Coefficients induced by f | `A.coefficients : A.quotient.comp MvPolynomial.C = (f.appLE ... A.over).hom` |
| Coverage over every specified V | The existential chart is provided for every point of f⁻¹V and has `A.V = V` |
| No connectedness, properness, smooth generic fibre, marking, normal/integral base | No such hypotheses occur |

A ring equivalence with the displayed scalar equation is precisely an Ω-algebra
equivalence for the induced scalar structures; it avoids silently using an unrelated
Ω-algebra structure on a stalk. No extension to arbitrary algebraically closed fields
is assumed: the hypothesis is only at the chosen algebraic closures of residue fields,
as specified by `def-weil-geometric-fibre`. This choice is invariant up to field and
base-change isomorphism. The LCI assertion uses the standard affine-neighbourhood
criterion, with the actual structure morphism `f.fiberToSpecResidueField`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` / `...QuasiCompact`: `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact` (the latter is the clause used here).
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `AlgebraicGeometry.QuasiSeparated`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `CategoryTheory.Limits.pullback`, used for the geometric fibre.
- `Sheaf.AlgebraicGeometry.PureDimension`: `AlgebraicGeometry.Scheme.IsPureDimension`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth` and `Scheme.Hom.smoothLocus`.
- `Mathlib.RingTheory.AdicCompletion.Basic` / `...Algebra`: `AdicCompletion`, `AdicCompletion.of` and its ring structure.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `MvPowerSeries.X`, `MvPowerSeries.C`.
- `WeilConjectures.RingTheory.CompleteIntersectionOverField`: `Algebra.IsGlobalCompleteIntersection`, `Algebra.IsLocalCompleteIntersection`; the latter states the ordinary fibre chart condition.
- `Sheaf.AlgebraicGeometry.NodalDualizingDatum`: `AlgebraicGeometry.NodalCanonicalPresentation`; its full signature and all fields were read and reused. `NodalDualizingDatum` itself is not assumed.
- `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular`, used by the existing chart's regularity field.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, used by the existing chart.

Imports include the recorded modules of all currently stated non-Mathlib proof
dependencies: NodalCurveLCICriterion, LciAffineOpenLocality,
LocalCompleteIntersectionFieldChange, LciPointwiseCriterion,
SyntomicPointwiseLocalModel, RelativeGlobalCompleteIntersectionPresentation,
RelativeGlobalCompleteIntersectionLocalRegularSequence,
RegularSequencePrincipalNeighbourhood, as well as Mathlib's affine and localization
interfaces. The proof-only dimension nodes
`lem-trf-geometric-pure-fibre-point-dimension` and
`lem-trf-field-extension-component-local-dimension` have no recorded Lean module;
there is therefore no module to import for those two. They introduce no notion needed
to type this statement, so no dependency repair is needed.

Searches for existing statements/notions (2026-10-24):

- `msearch.py ... leanfinder "A flat finitely presented family of nodal curves has affine presentations by regular sequences with one more variable than equations"`: eight hits on standard smooth and submersive presentations; none is this nodal-family theorem.
- `msearch.py ... loogle '"IsRegular", "MvPolynomial"'`: four hits concerning regular polynomial elements and regular rings; no family theorem.
- `msearch.py ... grep 'nodal|Nodal|syntomic' AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... leansearch "Flat finitely presented nodal families admit affine regular sequence presentations of relative dimension one"`: eight hits concerning smoothness, finite presentation and faithful-flat regular sequences; no match.
- `rg` across `lean/WeilConjectures` and `lean/Sheaf` for `NodalCanonicalPresentation`, `nodal_family_regular`, `nodalFamilyRegular`, and nodal/presentation terms: the existing presentation structure is in NodalDualizingDatum and a consumer assumes chart coverage in LCICurveFundamentalClass; neither proves this existence theorem.
- Search for the exact item id in `lean/WeilConjectures`: no declaration. Search of `dag/lean_names_upstream.json`: no theorem with the proposed name.

Edge cases checked before writing:

- Empty S: all pointwise hypotheses and conclusions are vacuous; a morphism to the empty scheme also has empty source. No global `Nonempty S` or `Nonempty X` was introduced.
- Nonempty S with an empty fibre is excluded exactly by the node's geometric nonemptiness hypothesis; there is no new nonemptiness assumption elsewhere.
- Disconnected nodal fibres and nonseparated X are allowed: no connectedness or separatedness hypothesis is present (quasi-separatedness is the stipulated finite-presentation condition).
- A smooth affine line permits c=0 (one variable, the empty equation sequence); the existential over `ℕ` does not impose c>0.
- An ordinary node uv=0, including characteristic 2, matches the two-variable power-series quotient. No characteristic or field-perfection hypothesis is added.
- A nonreduced locally Noetherian base is allowed; only geometric fibres are assumed reduced. In the proof plan, hy-1 is a nonzerodivisor even when h is a zero divisor.
- x may be nonclosed: the covering conclusion quantifies over every x; only the nodality test quantifies over closed fibre points.
- The final regular sequence includes nonzero final quotient as required by Mathlib's definition. At a chosen x the neighbourhood is nonempty, so this causes no accidental exclusion.
- The scheme and residue-field universes are explicit and agree with the existing framework; no independent smaller universe is used for test objects. Auto-bound implicits are disabled.

No statement correction, new nodes, dependency modules, or STATEMENT-DISPUTED issue.

## Second reading by Q157

This dispatcher assignment forbids additional agents; this is the same worker's final
rereading, with the independent maintainer review still to follow. I reread the node
against the full signature and `NodalCanonicalPresentation` fields. The ordinary-fibre
LCI and dimension clauses are both present. The prescribed base open is retained by
`A.V = V`; the coefficient map is not arbitrary. I checked specifically that the node's
“over Ω” condition is retained by the scalar equation, not merely a ring isomorphism,
and that x in the conclusion is arbitrary. No mathematical mismatch or change to the
node statement was found. Compiler repairs only made the scheme category explicit in
pullback point types and corrected the Mathlib properties import.
