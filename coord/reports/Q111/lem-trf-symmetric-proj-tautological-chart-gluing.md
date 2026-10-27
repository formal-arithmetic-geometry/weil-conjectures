## Worker report

Stage 2, group Q111, item lem-trf-symmetric-proj-tautological-chart-gluing.
The new module is Sheaf.AlgebraicGeometry.SymmetricProjTautologicalCharts.
Its main declaration is
AlgebraicGeometry.SymmetricProjTautologicalCharts.symmetric_proj_tautological_chart_gluing.
Its sole theorem has proof `sorry`. AffineChartFormulas and AffineRestrictionFormulas
are explicit Prop-valued definitions belonging to this node, with real defining formulas.
There are no new independent notions, dependency repairs, or statement corrections.
The item's JSON changes only in lean, and records all three declarations.

I read the full node, all twelve statement dependencies and their recorded declarations,
the canonical symmetric algebra construction, the normalized quotient record, both
existing comparison predicates, the Proj twist construction, its fraction-valued sheaf,
its degreePart localization interface and unitToTwist, the relative-Proj local models,
the relative-projective-space construction, and the standard projective-space twist.
I read constructions.tex at lemma-when-invertible (01MS),
lemma-glue-relative-proj-twists (01NR), definition-projective-bundle and the following
quotient (01OB), and lemma-projective-space-bundle (01OE). The footnote of 01OB explicitly
allows arbitrary quasi-coherent E. The full eleven-step node proof is in the theorem
docstring, with each non-elementary input named.

Hypotheses and clauses, in the order of the node:

- S is exactly `S : Scheme.{u}`; E is `E : S.Modules` with `[E.IsQuasicoherent]`.
  Neither finite type, local freeness, nonemptiness nor a rank assumption is imposed.
- The underlying projective scheme and projection are exactly
  `(SymmetricAlgebraSheaf.gradedAlgebraData E).relProj` and `.relProjHom`, already
  fixed in the type of the existing TautologicalQuotient. This is the canonical
  sectionwise symmetric algebra, with degree n the nth power of the range of iota.
- Existence of the normalized datum is `∃ D : ...TautologicalQuotient E`.
  Its line, quotient, invertible, surjective, chart and generator fields supply Q,
  q, local rank one, surjectivity, identification with Proj.twist 1, and the
  equation taking every pulled m to iota(m)/1. No arbitrary auxiliary map replaces q.
- Every affine U is quantified in the last conjunct; its ring is Γ(S,U.1) and its
  module is E.val.obj (op U.1). Its degree-one map is the actual SymmetricAlgebra.ι.
  The existential hι is only its homogeneity proof, not additional chosen data.
- `AffineChartFormulas` asserts the supremum of all `Proj.basicOpen 𝒜 (ι m)` is top
  and each is affine. The canonical chart is Mathlib's `Proj.basicOpenIsoSpec`,
  whose target is Spec of `HomogeneousLocalization.Away`. Relative-Proj's affine
  restriction identifies this cover with the required cover over U.
- The equivalence φ is H_e ≃ₗ[H_e] degreePart 𝒜 (powers e) 1, with explicit
  underlying formula z.val * e/1 and inverse z * 1/e. On fractions these say
  multiplication by e and a/e^k to a/e^(k+1), without cancellation in A.
- The additive equivalence τ identifies this actual localization submodule with
  the sections of the existing twist on D_+(e). Its scalar equation uses the
  actual ring identification awayToSection, so this is precisely the linear
  section identification. Its pointwise formula takes every a/e^k of degree one
  to that fraction in every prime localization. The hp parameter is the
  homogeneity certificate for e^k, required by degreePart.mk, not a new condition.
  The integer degree equality is discharged arithmetically inside the definition.
- The equation τ(φ c) = awayToSection(c) • twistPowSection(1,e) fixes the frame.
  The next clause writes the coefficient formula for v as iota(v)/e in this frame.
  Combined with D.generator this is exactly the asserted formula for q.
- The scheme basicOpen of the section f/e is D_+(e) intersect D_+(f). This is
  the stated overlap D(f/e) on C_e, expressed intrinsically as an open of Proj.
- The frame equation on every W contained in C_e and C_f is
  res(e) = res(e/f) • res(f). The last clause states (e/f)(f/g)=e/g after
  restriction to any common denominator open; in particular on triple overlaps.
- AffineRestrictionFormulas quantifies all affine inclusions U≤V. It supplies
  the twist comparison t, ties it by an explicit pullback-composition equation
  to D.chart on both opens, and states that every homogeneous degree-one section
  a/1 is carried to res(a)/1. This includes the frame and each quotient generator.
  The last clause gives the actual Away.map formula a/e^k to res(a)/res(e)^k
  on degree-zero coefficients. Since every degree-one section is uniquely a
  coefficient times e by φ and τ, these equations give that same fraction rule
  for arbitrary degree-one sections and its compatibility with the quotient.
  The chart equation uses the section-normalized composition comparison, so
  iterated restrictions agree through their common global line D.line.
- `HasOpenCompatibility D` is the existing explicit predicate for every open V,
  not only affine V. It supplies a normalized datum for E restricted to V, an
  IsPullback square for the two projections, and an isomorphism of the lines
  preserving q through the canonical pullback-composition comparisons. Thus its
  scheme is the fibre product and its entire quotient pair is identified.
- `HasFreeCompatibility D` is quantified for every r : ℕ and every ordered-basis
  identification freeModule S r ≅ E. It gives both the relative-Proj and standard
  projective-space isomorphisms over S, the line comparison with the existing
  ProjectiveSpace.twist 1, and an equation for each basis quotient coordinateSection.
  Its AffineFreeComparison field specifies the actual graded polynomial map,
  fixes scalars and each variable, identifies the affine Projs compatibly with the
  relative charts, and preserves all degree-one homogeneous twist sections.
  Applying the affine frame equations to these variables gives exactly the frames
  T_i and transitions T_i=(T_i/T_j)T_j in the polynomial model.

Dependencies reused (no copied definitions):

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and its morphisms.
- Sheaf.AlgebraicGeometry.CoherentFiniteType: imports Mathlib's
  SheafOfModules.IsQuasicoherent used here. Its recorded finite-type conjunction
  is not substituted for the quasi-coherence-only hypothesis.
- Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra:
  AlgebraicGeometry.SymmetricAlgebraSheaf.gradedAlgebraData.
- WeilConjectures.AlgebraicGeometry.RelativeProj.Basic:
  Scheme.GradedAlgebraData.relProj, relProjHom, relProjι, relProjFunctor,
  relProjFunctor_map_relProjι and the affine restriction isomorphisms.
- WeilConjectures.AlgebraicGeometry.Modules.Invertible:
  Scheme.Modules.IsInvertible, via D.invertible.
- Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction:
  Scheme.Modules.tensorPullback, tensorPullbackSectionComp and the normalized
  adjunction used in D.generator and the existing comparison predicates.
- Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry:
  ProjectiveBundleQuotientGeometry.TautologicalQuotient,
  HasOpenCompatibility, HasFreeCompatibility and AffineFreeComparison.
  These are existing definitions; the parent theorem is not invoked as a proof.
- Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization:
  Away, Away.mk and Away.map.
- WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization:
  degreePart and degreePart.mk, the actual homogeneous localization submodule.
- WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules and its
  public section interface: Proj.twist, unitToTwist and twistPowSection.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback:
  pullbacks, via the IsPullback assertion in HasOpenCompatibility.
- Sheaf.AlgebraicGeometry.RelativeProjectiveSpace:
  RelativeProjectiveSpace.freeModule, scheme and π, via HasFreeCompatibility.
- WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist:
  ProjectiveSpace.twist, via HasFreeCompatibility.

All modules recorded for already stated proof dependencies are imported, with plain
imports where they only serve the postponed proof. The normalized datum and comparison
predicates currently live in the parent's module. Adding a reverse import of this
module to that parent would create an import cycle; the maintainer must move the data
interface to its owning definition module before using this child theorem in that file.
No duplicate data interface or additional theorem is introduced here.

Edge cases checked against the formulas: E=0 gives empty Proj, but still has the
index m=0; its sole basic open is empty and covers the empty scheme. A nilpotent e
has zero localization; the equivalences are the unique maps of zero modules. No
nonzero-divisor or domain hypothesis occurs. The empty base and zero ring are allowed.
For r=0 the index ULift (Fin 1) has one element, H_T=R and coefficient one.
Infinite-rank E is permitted because all local sections index the cover; no finite
subcover or finite generating set is chosen. Modules with torsion are also allowed:
the inverse frame is computed after localization. The only universe u is the
scheme/module/section universe used by the recorded interfaces; no independent smaller
test-scheme universe or artificial universe equality is imposed.

Searches actually run for Q111:

- msearch.py leanfinder: "Relative Proj of symmetric algebra tautological line quotient
  degree one charts restriction free module comparison". Eight hits: Proj.pullbackAwayιIso,
  projIsoSpec, Proj.awayι, projIsoSpecTopComponent, the two ProjIsoSpecTopComponent
  inverse identities, Proj.fromOfGlobalSections_morphismRestrict and
  Proj.pullbackAwayιIso_hom_awayι. These supply absolute chart infrastructure, not
  this normalized quotient existence theorem with all comparisons.
- msearch.py loogle: "AlgebraicGeometry.Proj.twist, SymmetricAlgebra". Service responded
  "unknown identifier AlgebraicGeometry.Proj.twist", with zero hits. This does not
  establish absence: Proj.twist is a project declaration and was inspected directly.
- msearch.py grep: "tautological|SymmetricAlgebra.*Proj|Proj.*SymmetricAlgebra" under
  Mathlib AlgebraicGeometry/ProjectiveSpectrum: zero hits.
- rg of the project and upstream AlgebraicGeometry sources for tautological,
  symmetric Proj and projectiveBundleQuotient found the parent interface and finite
  locally free projective-bundle results, not this standalone theorem for arbitrary E.
  rg of upstream for the exact node id found no occurrence.
- rg of Mathlib, WeilConjectures and Sheaf for all three proposed declaration names
  found no existing declaration. The earlier Q80 report is a stage-1 split only;
  there is no lean binding on the live node and no repair note.

No STATEMENT-DISPUTED flag and no mathematical node fault was found. The previous
attempt's unchanged-node failure is repaired by supplying the actual Lean module and
lean record; the reviewed stage-1 split and all other node fields are retained.

Validation: scompile.py compiled this file separately both as the sandbox module and
as Sheaf.AlgebraicGeometry.SymmetricProjTautologicalCharts, with no errors or warnings.
Auto-implicit variables are disabled; all variables and universes are explicit.

## Second reading by Q111

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
