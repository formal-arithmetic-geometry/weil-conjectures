## Worker report

Item: `lem-sfb-relative-degree-gminusone-theta`; group NV; 2026-10-24 UTC.
Module: `Sheaf.AlgebraicGeometry.RelativeDegreeGMinusOneTheta`.
Main declaration: `AlgebraicGeometry.relative_degree_gminusone_theta`.

The theorem states `Nonempty (RelativeThetaSystem.{u, w})`. This packages the
conclusions for every admissible family and every chosen representation of its
degree-zero Picard sheaf, with comparisons for all cartesian family arrows.
The structures in this module package this node's hypotheses and conclusions;
they do not replace the dependency notions. Their data are actual fields or
explicit constructions. The only postponed proof in this module is the main
theorem, whose docstring contains the node's complete thirteen-step proof.
No statement correction, new node, or dependency-interface replacement is made.

Hypothesis and clause audit (names below are in `AlgebraicGeometry`):

1. A locally Noetherian scheme S: `RelativeThetaCurve.base` is the actual base
   `family.base.left`, and `RelativeThetaCurve.noetherian` is
   `IsLocallyNoetherian family.base.left`. The auxiliary `ambient` only permits
   reuse of the existing moduli definition; any S is accommodated by ambient S
   and its identity base arrow.
2. Genus g >= 2 and a smooth stable unpointed genus-g family: `genus : ℕ`,
   `family : StablePointedModuli ambient genus 0`, and `smooth : Smooth
   family.projection`. The existing stable-family definition includes the
   stability inequality, projective-bundle projectivity, flat finite presentation,
   the required geometric curves and their genus. With zero marked points its
   stability inequality is precisely the genus bound in this node. The module's
   properness and finite-presentation instances extract existing consequences;
   they are not extra hypotheses on the theorem.
3. The given algebraic-space representation J of Pic^0: `RelativeThetaInput`
   contains `jacobian : RelativeThetaRepresentation curve 0`. A representation
   contains an existing `AlgebraicSpace C.base` and an isomorphism to
   `C.degree d`, defined using the existing `picardDegreeSubfunctor`.
   Its degree convention is the recorded geometric Euler-characteristic degree.
   `uliftFunctor` in `identification` reconciles the section-set universes; it
   does not change the represented functor or restrict its test schemes.
4. P is represented: `RelativeThetaDatum.picard` is
   `RelativeThetaRepresentation I.curve (I.curve.genus - 1 : ℤ)`.
   The subtraction is in integers here and in the Picard degree parameter.
5. Tensor action and torsor isomorphism: `RelativeThetaTorsor.action`, `tensor`
   and `naturality` give a natural action on all test schemes, identified with
   multiplication in the existing group-valued Picard sheaf. `simply_transitive`
   asserts bijectivity of `(M,L) ↦ (action M L,L)` on every test scheme.
   Together with naturality this is exactly the stated isomorphism of represented
   fppf sheaves, not merely transitivity on geometric points. The group-to-set
   transport is the actual equality `picardFunctorGrp_comp_forget`.
6. Etale local sections and locally Noetherian covers: `coverIndex`, `cover`,
   `cover_etale`, `cover_noetherian`, and `cover_surjective` supply the jointly
   surjective covering family. `curveSection` and `curveSection_projection`
   supply its curve sections. `beta` supplies an isomorphism of the restricted
   J and P functors for every curve section over every base test, hence in
   particular on this cover. `beta_tensor` specifies the formula using an
   actual Picard class A represented by `(p.ker.toModulesᵛ).tensorPow (g-1)`;
   its evaluations use the canonical iterated-pullback identification. Thus beta
   is tensoring by O((g-1)p), and supplies the corresponding local torsor section
   from the identity of J. Its natural-isomorphism type includes naturality in
   all further tests. Tensor equivariance follows from its specified Picard
   class formula and the group law, rather than being an arbitrary trivialization.
7. The canonical theta pair on P: `RelativeThetaPair.line`, `invertible` and
   `thetaSection` are a line module and section on the existing small etale site
   of P. `testLine`, `testInvertible`, `testSection`, and `restriction` retain its
   ordinary tensor pullbacks on all scheme tests; their section, identity and
   composition equations fix the pullback normalization. `chartIso`, `chartUnit`,
   `chartUnit_one`, and `chart_section` identify these pairs with the actual
   `AlgebraicSpace.schemeRestriction` to each etale chart. The unit comparison
   is pinned by the existing regular-functions ring comparison.
8. Effective Cartier divisor, chartwise flatness, and its divisor line:
   the divisor is the existing real zero-locus construction
   `(testSection T.obj).zeroLocus`. `cartier_flat` says on every etale chart
   that this ideal is `IsRelativeEffectiveCartier` over S (Cartier and flat
   quotient over the base). `divisorLine` identifies the line with the dual of
   the zero-locus ideal module, exactly O(theta) in the recorded dependency.
   The actual regular section already specifies its distinguished section.
9. Derived direct image: `RelativeThetaModel.Computes` uses the recorded
   `schemeDerivedDirectImage` on the single complex of the actual representative
   module. This is the injective-resolution/K-injective construction, with an
   isomorphism in the derived category to `DerivedCategory.Q.obj E.complex`;
   no replacement by a collection of cohomology isomorphisms is made.
10. Local two-term equal-rank finite locally free model in degrees 0,1:
    `RelativeThetaModel` extends the existing `TwoTermDeterminantModel` (which
    supplies the modules, finite ranks, local freeness and differential) and
    asserts `equal_rank`. Its `complex` is the actual double complex in degrees
    0 and 1. `RelativeThetaPair.local_models` gives open neighborhoods covering
    each chart carrying each representing Picard line, with a model computing
    the pullback representative on that neighborhood. The natural-number
    tensor-power exponent and Hilbert rank are g-1; the existing family bound
    ensures agreement with the integer degree parameter.
11. The determinant formula and independence: `RelativeThetaModel.line` is
    `(E.nonneg.exteriorSheaf E.negRank) ⊗
    (E.neg.exteriorSheaf E.negRank)ᵛ`, in the stated order.
    `IsDeterminantPair` identifies the pair with this line and characterizes
    det(d) by its action on every top exterior wedge and the contraction
    equation. This fixes the determinant section, including its sign, without
    a private determinant or a choice of a matrix. `RelativeThetaPair.determinant`
    is quantified over EVERY scheme test, EVERY representative of the same
    Picard class and EVERY model computing its direct image. Thus all those
    pairs identify with the one retained pair. On the Cartier charts these
    section-preserving identifications are unique because the section is regular.
12. Geometric-fibre Abel-image statement: `RelativeThetaPair.GeometricAbelImage`
    quantifies over every algebraically closed field K and every geometric base
    point. It supplies representing schemes Q for P_K and H for the existing
    `hilbertPresheaf` of degree g-1 of the pulled-back curve. `abel : H ⟶ Q`
    is characterized on EVERY test point by the dual ideal module O(D), using
    the canonical `picardFunctorIsoOfIsPullback` to compare Picard classes.
    The last equality is `zeroLocus = abel.left.ker`, equality of ideal-sheaf
    data. It is the scheme-theoretic image assertion, including multiplicities.
13. Arbitrary locally Noetherian base change and family isomorphisms:
    `RelativeThetaArrow` is an arbitrary cartesian family square, with no
    etaleness, flatness, finite-type or extra universe-equality hypothesis on its
    base arrow. Its two family inputs have the required locally Noetherian bases.
    `RelativeThetaComparison.picard` and `jacobian` are restricted-functor
    isomorphisms, pinned by their class equations to canonical Picard pullback.
    `action` preserves the torsor action. The beta class formulas in each datum
    use actual pullbacks of section ideals, so specify the compatible beta maps.
    `lineIso` and `section_eq` compare the actual line pairs on every test.
    For an over-base isomorphism u:C→D this comparison is pullback u* from D
    to C. Its inverse on Picard spaces is the node's b=(u^{-1})*, so it gives
    exactly b*(T_D,s_D) ≅ (T_C,s_C).
14. Identity, composition and naturality:
    `RelativeThetaSystem` retains one simultaneous system of the preceding
    data, with `identity_points`, `identity_lines`, `composition_points`,
    `composition_lines` and `natural`. These require the identity and composite
    comparisons to agree with those of the retained system on points and lines,
    and commute with every test-scheme restriction. `HEq` only suppresses
    reindexing along equal bases and Picard points; it is equality of the
    displayed maps/isomorphisms, not an unspecified existence assertion.
    The J and beta comparisons are fixed by their Picard class formulas, so
    their identity/composition laws follow the same canonical Picard maps.
15. No unchosen line on J: the pair belongs to `RelativeThetaDatum.picard`,
    the degree-g-1 representation. Nothing puts a line on the input jacobian;
    beta makes the specified local identifications available when a section
    has been chosen.

Dependency declarations used (full namespace `AlgebraicGeometry`, unless shown):

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `StablePointedModuli` and its existing family fields.
- `WeilConjectures.AlgebraicGeometry.Picard.Defs`: `picardFunctor`,
  `picardFunctorGrp`, `picardFunctorGrp_comp_forget`, `toPicardFunctor`.
  The node `sk-def-picard-pic` has no `lean` record but its closed upstream
  audit supplies these declarations. No replacement Picard functor was written.
- `WeilConjectures.AlgebraicGeometry.Picard.Degree` and `Picard.DegreeMorphism`:
  `picardDegree`, `picardDegreeSubfunctor`, `picardFunctorIsoOfIsPullback`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `structureSheaf`, `Modules`, `IsLineModule`.
- `WeilConjectures.AlgebraicGeometry.EffectiveCartier`: the invertible-ideal
  effective-Cartier notion and `Scheme.IdealSheafData.IsInvertible`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, `Scheme.Modules.dual`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank`, via the model's existing fields.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `schemeDerivedCategory` (the existing `DerivedCategory` of scheme modules).
- `Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf`:
  `Scheme.Modules.exteriorSheaf`, `exteriorSheafSection`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: its chartwise
  convention, implemented here on every chart's zero subscheme.
- `WeilConjectures.AlgebraicGeometry.Hilbert.Curve`: `hilbertPresheaf` and the
  effective-divisor Hilbert convention of `hilbertPresheaf_curve_representable`.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `schemeDerivedDirectImage`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`:
  `AlgebraicSpace.schemeRestriction`, `schemeOpensRingHom`.
- `Sheaf.TraceFormula.TwoTermPerfectDeterminantData`:
  `TwoTermDeterminantModel` (reused, not copied).
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSectionId`,
  `tensorPullbackSectionComp`.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`:
  `Scheme.Modules.tensorPullbackObjUnitToUnit`.
- `WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus`:
  `Scheme.Modules.zeroLocus`; `Mathlib.Algebra.Homology.Double`:
  `HomologicalComplex.double`; these are existing constructions.

The node gains only the six already recorded dependency ids
`def-pd-degree-morphism`, `def-pc-derived-direct-image`,
`def-trf-space-module-scheme-restriction`, `def-trf-two-term-determinant-data`,
`def-pc-module-pullback`, `def-sfb-tensor-pullback-structure-sheaf-map`.
Its original statement, proof and other fields are unchanged. Other imports
are ordinary proof imports of existing proof dependencies. The module itself
proves none of those dependencies.

Edge cases checked: empty base (empty covering index is allowed); g=2; no
marked points or globally chosen curve section; arbitrary nonreduced locally
Noetherian bases; nonconstant local model ranks (the neighborhoods may have
separate constant ranks); rank-zero two-term complexes (the exterior-power
condition uses Fin 0 and the top exterior unit); different representatives and
acyclic-model changes (the determinant clause quantifies over all); arbitrary
nonflat base change; identity arrows; successive and mixed cartesian arrows;
curve isomorphisms in the stated direction; geometric fibre scheme structure
rather than support. No separability or generic smoothness assumption is
inserted into the Abel-image assertion.

Searches made before construction:

- `msearch.py ... leanfinder "relative degree g minus one Picard torsor theta
  divisor determinant cohomology arbitrary base change"`: eight elliptic
  class-group results, no matching relative theta statement.
- `msearch.py ... loogle "picardFunctor, AlgebraicSpace, exteriorPower"`:
  no match (picardFunctor is not a Mathlib name).
- `msearch.py ... grep "theta|Theta|picardFunctorDegree" AlgebraicGeometry`:
  no Mathlib match.
- `msearch.py ... leansearch "relative Picard theta divisor determinant
  cohomology base change"`: eight linear-determinant/base-change and relative
  Picard-group results, no matching statement.
- Local `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for theta,
  Picard degree components, determinant models, pullback and Abel image found
  the reusable declarations listed above, but no theorem with all this node's
  hypotheses and conclusions. `grep -rn` for the item id in WeilConjectures
  found no declaration. The proposed declaration names had no existing match.
- `tools/blueprint_refs.py ancestor` for this item: no blueprint-unit ancestor.
  Read the current `literature/blueprint/latest/` compact-support direct-image
  stability proof, not an older snapshot.

Sources checked: Milne's local PDF, printed III pp.110--111 (Theorem 8.1 and
following relative discussion); the local Stacks perfect.tex two-term
canonical-section and functorial-determinant passages (Tags 0FJX/0FJY);
the node's full relative expansion and its thirteen proof steps. The source
record's request for a more detailed single relative-theta reference remains
as recorded; this delivery does not invent a citation or weaken that expansion.
No `STATEMENT-DISPUTED` finding.

Compilation uses only the prescribed `scompile.py`, separately for this module.
The final substantive version passed both sandbox and library compilation
(about 30 and 32 seconds respectively), below the 60-second limit. The only
postponed proof is the expected theorem `sorry`. The final delivery dry run
also recompiles the delivered version.

## Second reading by NV

The dispatcher explicitly prohibits starting another agent, and there is no
other worker to ask. This section records a separate self-review pass; it is
not a claim of an independent second reader. The maintainer's independent
review remains the independent reading of this delivery.

With both the node and module open, the second pass checked every clause using
the audit above. It found that pair comparisons also needed naturality under
arbitrary test-scheme restrictions; the final `RelativeThetaSystemData.Natural`
and `RelativeThetaSystem.natural` record precisely that equation. It checked
the pullback unit normalization against the existing tensor-pullback API,
retaining `tensorPullbackObjUnitToUnit` and the section-normalized identity and
composition isomorphisms. It checked that the Abel equality is equality of
ideal-sheaf data, that derived comparison is in the derived category, and that
the line remains on P. It checked that all helper data have real bodies or
are explicit fields; no unproved existence theorem chooses undefined data.
The coherence propositions were separated from the data structure to keep
compilation below the prescribed time limit without changing their statements.

## Returned delivery repair

Return: L, immutable head `c2da9e274fd2`, H2. The statement dependency
`lem-weil-pbc-module-pullback-structure-sheaf` owned the theorem about the
structure-sheaf map, whereas this module uses only its plain definition.
Replaced that id in `stmt_deps` by the live definition owner
`def-sfb-tensor-pullback-structure-sheaf-map`, whose `existing: true` record
names `AlgebraicGeometry.Scheme.Modules.tensorPullbackObjUnitToUnit` in
`WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`. Read the
live node and the full source definition: it is precisely the map used in
`RelativeThetaPair.restriction_section`. Neither its isomorphism theorem nor
data chosen from that theorem are needed by this statement. No proof
dependency was added.

The sandbox was compared with the current shared main node: outside `lean`
and the permitted additional `stmt_deps`, all node fields agree. The Lean
file is unchanged from the returned delivery (SHA256
`7a817caefd1c361c4f51fc2ab392ba5569c513e617065cd4804ac01512048eb0`).
This repair changes dependency ownership only; the mathematical statement,
proof text, declarations and signatures are unchanged. The report's list of
added dependencies has been corrected above. Compilation, dry run and delivery
are repeated through the prescribed wrappers.
