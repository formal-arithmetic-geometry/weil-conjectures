## Worker report

The module `Sheaf.AlgebraicGeometry.FlatPointedNoetherianComponentModel` states
`AlgebraicGeometry.exists_flat_pointed_noetherian_component_model`, with its entire
proof `sorry`. It introduces no definitions and changes only the item's `lean` record.
The statement follows the first paragraph of Stacks Tag 055Q, read in
`literature/stacks-project/more-morphisms.tex`, lines 8310–8348.

Clause-by-clause correspondence:

- Schemes and their morphism: `{P T : Scheme.{u}} (g : P ⟶ T)`, with an explicitly bound
  universe `u`. The model schemes are also `Scheme.{u}`.
- Flatness: `[Flat g]`. Finite presentation: `[LocallyOfFinitePresentation g]`,
  `[QuasiCompact g]`, and `[QuasiSeparated g]`, all three independently present.
- The specified section: `(σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T)`; Lean's composition order
  writes first σ, then g, so this is exactly g composed with σ equals the identity.
- The point: `(q : P)`, with no component-membership or specialization assumption.
- Geometric reducedness of its fibre:
  `(hred : GeometricallyReduced (g.fiberToSpecResidueField (g q)))`. This is the
  geometric-reducedness class on the scheme-theoretic fibre over its residue field,
  not geometric reducedness of every fibre of g.
- The affine open and containment: `∃ (V : T.Opens) (hq : g q ∈ V), ...` and
  `IsAffineOpen V`. No hypothesis makes T itself affine or Noetherian.
- The models: `P₀ T₀ : Scheme.{u}`, with `IsNoetherian P₀`, `IsNoetherian T₀`, and
  `IsAffine T₀`. Mathlib's `IsNoetherian` is precisely locally Noetherian plus compact.
- The model morphism and section: `g₀ : P₀ ⟶ T₀`, `σ₀ : T₀ ⟶ P₀`, with `Flat g₀`,
  `LocallyOfFinitePresentation g₀`, `QuasiCompact g₀`, `QuasiSeparated g₀`, and
  `σ₀ ≫ g₀ = 𝟙 T₀`.
- The requested maps: `b : V.toScheme ⟶ T₀` and `ρ : pullback g V.ι ⟶ P₀`.
  Thus P_V is the actual chosen scheme fibre product, with g_V = `pullback.snd g V.ι`.
- The cartesian square: `IsPullback ρ (pullback.snd g V.ι) g₀ b`.
- The induced section is the existing canonical
  `sectionBaseChange g σ hσ (Over.mk V.ι)`; compatibility is its composite with ρ
  equal to `b ≫ σ₀`. This uses the recorded dependency, without a new arbitrary lift.
- The point t₀: `b ⟨g q, hq⟩`. The open-immersion base change identifies P_V with
  g inverse image V; its unique point qV over q maps under g_V to `⟨g q, hq⟩`.
  The cartesian square's commutativity therefore gives
  g₀(ρ(qV)) = b(⟨g q, hq⟩). This writes exactly the specified t₀ without introducing
  a noncanonical point or an extra conclusion about a chosen lift.
- The reduced geometric fibre: `IsReduced (pullback g₀ (Spec.map
  (CommRingCat.ofHom (algebraMap (T₀.residueField t₀)
  (AlgebraicClosure (T₀.residueField t₀)))) ≫ T₀.fromSpecResidueField t₀))`, with t₀
  expanded verbatim in the actual signature. This is exactly def-weil-geometric-fibre's
  recorded pullback specialization. AlgebraicClosure stays in universe u and is a
  genuine algebraic closure, including for imperfect residue fields.
- The component locus is written inline using the existing `connectedComponentIn`:
  `{p | p ∈ connectedComponentIn (g ⁻¹' {g p}) (σ (g p))}` and likewise for g₀ and σ₀.
  The equality is `ρ ⁻¹' C₀ = (pullback.fst g V.ι) ⁻¹' C`. Since the first projection
  identifies P_V with the open inverse image g⁻¹(V), its right side is precisely the
  node's C(g,σ) intersected with P_V, expressed as a subset of P_V rather than of P.
  This is a set equality, with no openness or membership assumption added.
- No condition on any other fibre of g₀ appears.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  and scheme open subschemes; the defining signatures and docstrings were read.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, the recorded
  affine-local definition, equivalent to flat stalk maps.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` and `...QuasiSeparated`:
  `AlgebraicGeometry.QuasiCompact` and `AlgebraicGeometry.QuasiSeparated`.
  The convention node fixes no additional construction.
- `Mathlib.CategoryTheory.EpiMono`: `CategoryTheory.SplitEpi`; the node explicitly
  permits the equivalent unbundled section map with its identity, used here.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber` and
  `Scheme.Hom.fiberToSpecResidueField` (the second projection to Spec κ(t)).
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`, through its reduced import:
  `AlgebraicGeometry.GeometricallyReduced`, the recorded geometric-reducedness clause
  of def-pc-geometrically-irreducible. No dependency-interface repair is needed.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, `connectedComponent`, and
  `connectedComponentIn`; the latter is the connected component in the subspace,
  embedded as a subset of the ambient space. The section identity puts the section
  point in the fibre, so its outside-the-subspace empty-set case is inapplicable.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the canonical base-change
  conventions, especially `baseChange_section_characterization`, using
  `AlgebraicGeometry.sectionBaseChange` from `...Picard.Defs`. Its implementation and
  both projection equations were read. `Scheme.Hom.geometricFiberAt` was also read;
  the conclusion uses the geometric-fibre dependency's direct pullback formulation.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; `CategoryTheory.IsPullback` expresses the universal
  property and commutativity of the model square.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`, the chosen
  algebraic closure used in the recorded def-weil-geometric-fibre specialization.

The module also imports the stated proof-plan dependencies:
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`
(`Scheme.NoetherianApproximation.ofIsAffine`, `Scheme.exists_pullback_hom_of_isLimit`,
`Scheme.exists_pullback_fst_comp_eq_of_isLimit`),
`WeilConjectures.AlgebraicGeometry.DescendFlatFinitePresentation`
(`exists_flat_stage_of_limit`),
`WeilConjectures.AlgebraicGeometry.SectionComponentPullback`
(`section_component_preimage_of_isPullback`), and
`Sheaf.TraceFormula.GeometricReducedFibreLocusBaseChange`
(`geometricReduced_fibre_locus_baseChange`). Their statements and docstrings were read.
The Mathlib proof leaves are supplied by the existing statement imports: affine-open
basis, finite-type Noetherian permanence, flat and finite-presentation base change,
qcqs permanence and the pointwise local-finite-type criterion. All seven proof steps
and their cited nodes are explained in the theorem docstring.

Edge cases checked before writing:

- P empty, and hence a supplied q impossible: no artificial Nonempty hypothesis added.
  The section also precludes nonempty T with empty P. T empty gives the same vacuity.
- The identity family: a finite-type integer-subalgebra approximation of an affine
  neighbourhood gives the indicated model; its distinguished geometric fibre is a point.
- A disjoint union of two copies of T, with σ in the first and q in the second:
  the statement does not assume q belongs to the section component, and the locus
  equality still correctly singles out only the first copy.
- A non-Noetherian base: no Noetherian hypothesis on P or T; only the models have it.
- Imperfect residue fields and positive characteristic: the hypothesis is geometric
  reducedness, and the conclusion uses an algebraic closure of the model residue field.
  Ordinary reducedness was not substituted for geometric reducedness.
- Only the chosen fibre is assumed geometrically reduced; the signature places no
  condition on other original or model fibres. The section makes all original fibres
  nonempty, but no redundant nonemptiness assumption is imposed.
- Nonseparated morphisms: quasi-separated is retained, and separatedness is not added.
- The universe u is arbitrary, and AlgebraicClosure does not increase it.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder` query: "A flat finitely presented scheme with section
  admits an affine local Noetherian model preserving the section, a reduced geometric
  fibre, and the section connected component locus". Eight hits: IsLocallyNoetherian,
  an affine characterization of IsFinite, IsIntegral, IsLocallyNoetherian.component_noetherian,
  Flat.instHasRingHomPropertyFlat, LocallyOfFiniteType.isLocallyNoetherian, flat_iff,
  and the Noetherian spectrum instance. No exact statement.
- `msearch.py ... leansearch` query: "A flat finitely presented morphism with section
  has a Noetherian cartesian model retaining a reduced geometric fibre and the connected
  components through the section". Eight hits, including Flat.isIso_of_surjective_of_mono,
  local finite presentation of smooth morphisms, Flat.stalkMap, module projectivity from
  flat finite presentation, IsOpenImmersion.of_flat_of_mono, local finite type from local
  finite presentation, flat_iff, and Scheme.Hom.finitePresentation_appLE. No model theorem.
- `msearch.py ... loogle` query:
  `AlgebraicGeometry.Flat, AlgebraicGeometry.IsNoetherian`: zero hits.
- `msearch.py ... grep` query: `noetherian.*section.*flat|flat.*section.*noetherian`,
  subdirectory `AlgebraicGeometry`: zero hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` with
  `noetherian.*section.*flat|flat.*section.*noetherian|flat.*noetherian.*model` found
  only the unrelated affine ring model `WeilConjectures/RingTheory/FlatPointNoetherianModel`.
- `grep -rn 'lem-trf-flat-pointed-noetherian-component-model' lean/WeilConjectures`:
  zero hits. A wider `rg` for section-component naming found the existing general
  SectionComponentNoetherianModel (no flatness or distinguished reduced fibre), and
  SmoothSectionComponentNoetherianModel (smooth hypothesis and a weaker component-only
  conclusion). Their complete relevant signatures/docstrings were read. Neither states
  this node, and no construction or notion is duplicated by the new theorem.

Validation: scompile.py checked both its sandbox probe and its real module path cleanly
(6.7 s and 9.8 s respectively), with no errors or warnings. An initial extra closing
parenthesis in the geometric-point term was corrected before the clean compilation.
No statement dispute, correction, new node, or dependency repair was necessary.

## Second reading by Q125

I reread the node and the final source side by side in a separate pass. As the dispatcher
prohibits starting other agents, this is a self-check; the maintainer's independent review
remains the independent reading. Checked especially: q has no component-membership
hypothesis; the reduced-fibre assumption is only at g(q); both model schemes are
Noetherian; T₀ is affine; g₀ has flatness and all three finite-presentation properties;
the square uses the actual pullback P_V; the section is the existing canonical base
change; the geometric fibre is at b(g(q)), which equals g₀(ρ(qV)) by commutativity;
and the final equality is of subsets of P_V, using the first projection for restriction.
The fixed AlgebraicClosure choice is expressly allowed by the geometric-fibre node and
requires no extra hypothesis. No missing or extra mathematical clause was found.
