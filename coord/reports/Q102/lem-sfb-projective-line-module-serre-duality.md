## Worker report

Module: `Sheaf.AlgebraicGeometry.ProjectiveLineModuleSerreDuality`.
Main declaration: `AlgebraicGeometry.Scheme.Modules.projective_lineModule_serreDuality`.
This is a stage-2 statement, with its whole proof `sorry`. The only helper,
`lineSerreCohomology`, has real data: the existing module-cohomology functor followed
by restriction of scalars for nonnegative integer degrees, and the constant functor
at the zero vector space `Fin 0 → F` for negative degrees. No existence choice or
postponed construction is involved.

Hypotheses and clauses, checked against the node:

- A field F is `(F : Type u) [Field F]`. Y is `(Y : Scheme.{u})` with
  `[Y.Over (Spec (CommRingCat.of F))]`. The single universe covers any pair after
  the usual common universe lift and is the recorded scheme-module convention.
- Pure dimension n and smoothness are precisely `(n : ℕ)` and
  `[SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of F))]`. Over a field this
  expresses smoothness with every component of dimension n; it also includes
  the empty scheme, with the pointwise condition vacuous.
- Projectivity is `[IsProjective (Y ↘ Spec (CommRingCat.of F))]`, the recorded
  H-projective plus quasi-compact convention. No properness assumption is added.
- The canonical module is written explicitly everywhere as
  `exteriorSheaf (Y ↘ Spec (CommRingCat.of F)).relativeDifferentials n`.
  These are the recorded sheafifications of relative differentials and alternating
  exterior powers, not a variable standing for an unspecified canonical bundle.
  `exteriorSheaf_zero_iso` gives the required structure-sheaf identification at n=0.
- Invertible modules are quantified as `∀ (E : Y.Modules) [IsInvertible E]`, with
  the specified scheme-module predicate, not the separate site-level predicate.
  `dual E` is the existing internal Hom into the structure sheaf.
- `∃ θ : ∀ (E ...) (j : ℕ), ... ≃ₗ[F] Module.Dual F ...` asserts simultaneous
  F-linear isomorphisms in exactly the displayed direction. The domain is
  `scalarCohomology ... (omega ⊗ dual E) j`. The target is the linear dual of
  `(lineSerreCohomology ... ((n : ℤ) - (j : ℤ))).obj E`.
- Thus the complementary degree is genuine integer subtraction, with zero in
  negative degree. For j≤n the helper unfolds to the same recorded right-derived
  global sections as the left side, with scalars restricted by the structure map.
  For j>n it is the actual zero vector space. No replacement of H^(n-j) by H^0
  through truncated natural subtraction occurs.
- Both displayed vector spaces are explicitly `FiniteDimensional F` in the first
  conjunct, for every E and every nonnegative j.
- Naturality quantifies E, E', their invertibility, *every* `v : E ⟶ E'`, every j,
  a class z in H^j(omega tensor E'-dual), and x in H^(n-j)(E). The equation is
  `θ E j (scalarCohomologyMap ... (omega ◁ dualMap v) j z) x =
  θ E' j z (((lineSerreCohomology ...).map v).hom x)`.
  `omega ◁ dualMap v` is exactly id_omega tensor v-dual. The right side is
  precomposition with the cohomology map on v. Pointwise equality is equality of
  the two resulting linear functionals. No invertibility or nonzero assumption
  is imposed on v.
- The last conjunct is `n < j → Subsingleton (scalarCohomology ... j)`, expressing
  the explicit vanishing clause. No connectedness, integrality, nonemptiness,
  characteristic-zero or algebraic-closure assumption occurs.

Dependency interfaces read and reused:

- `Mathlib.Algebra.Field.Defs`, `Field`; `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `Smooth` and
  `SmoothOfRelativeDimension`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`, `IsProjective`.
- `Mathlib.RingTheory.Kaehler.Basic`, `KaehlerDifferential`, its universal
  derivation `KaehlerDifferential.D` and `linearMapEquivDerivation`.
  At scheme level use `WeilConjectures.AlgebraicGeometry.Modules.Differentials`,
  `Scheme.Hom.relativeDifferentials` (with affine and restriction comparisons).
- `WeilConjectures.AlgebraicGeometry.PQFCohomology`,
  `sheafCohomologyAndHigherDirectImages`; its H is the actual
  `RingedSpace.moduleCohomology` of
  `WeilConjectures.Topology.RingedSpaceModuleCohomology`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `Scheme.Modules.IsInvertible`, and the existing symmetric tensor on X.Modules;
  `WeilConjectures.AlgebraicGeometry.Modules.Dual`, `dual` and `dualMap`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` is the recorded
  tensor dependency, publicly imported. Its tensor is the same localization
  tensor, not an additional tensor construction in this delivery.
- `Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf`, `exteriorSheaf` and
  `exteriorSheaf_zero_iso`.
- `WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`,
  `scalarMap`, `scalarCohomology` and `scalarCohomologyMap`.

Added the already landed owning nodes `def-sc-relative-differential-sheaf`,
`def-sc-sheaf-exterior-power`, and
`def-sc-field-linear-module-cohomology-operations` to stmt_deps to record these
interfaces. No new node and no dependency repair is needed. All other node fields
are preserved. All recorded available proof-dependency modules are imported;
the trace-pairing and dimension-vanishing nodes have no Lean record and therefore
no proof import yet. They are not prerequisites to typing this statement.

Source checked directly in `literature/stacks-project/duality.tex`:
0FVV, lemma-duality-proper-over-field, especially (5),(7), lines 6717 onwards;
0FVX, remark-coherent-duality-proper-over-field, lines 6832 onwards;
0FW0, remark-rework-duality-locally-free-CM, lines 6917 onwards.
The perfect pairing in 0FW0 has omega tensor E-dual in exactly this order.
The module docstring includes the five node-proof steps and all their arguments.

Edge cases checked by reading the definitions and source: j=0, j=n, j=n+1;
n=0, including j>0; the empty scheme; disconnected smooth projective schemes
with all components of dimension n; finite nontrivial extensions in dimension 0;
zero and noninvertible maps v; arbitrary positive characteristic and imperfect
fields. The zero functor used in negative degrees maps every v to the unique
linear map between zero spaces. No disputed statement or source correction.

Searches (2026-10-24, via prescribed msearch.py):

- LeanSearch: `Serre duality for line bundles on a smooth projective scheme over
  a field`; eight results, including `CommRing.Pic.mk_dual`,
  `Module.dual_projective`, `Algebra.FormallySmooth.projective_kaehlerDifferential`;
  none is coherent Serre duality.
- LeanFinder: `Serre duality for invertible sheaves on smooth projective schemes
  over a field with functorial cohomology duality`; eight results, including
  `CommRing.Pic.mk_dual`, `CommRing.Pic.inv_eq_dual`, abstract Ext equivalences,
  `CategoryTheory.Sheaf.H`; none states the required theorem.
- Loogle: `"Serre"`; twelve results, parser-resolution names and categorical
  Serre classes; none is Serre duality.
- msearch grep: `serreDuality|Serre.duality|canonicalSheaf`, subdirectory
  AlgebraicGeometry of Mathlib: zero hits.
- rg of project Sheaf and upstream WeilConjectures for Serre duality, relative
  differentials, exterior powers, canonical bundles and field-linear cohomology:
  found the owning interfaces above. Existing `Scheme.serreDuality` in
  `WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch` is only dimension one
  (`p+q=1`), and its zero-dimensional companion is only dimension zero. Neither
  covers the present arbitrary-dimensional result. The recorded curve versions
  use a different existing cohomology carrier, which is not substituted here.
- rg of the item's blueprint id in WeilConjectures: zero hits. rg of
  `lineSerreCohomology|projectiveLineModuleSerreDuality|lineModuleSerreDuality`
  across Mathlib, WeilConjectures and Sheaf: no preexisting declaration clash.
- Read DAG owning nodes for relative differentials, exterior powers and scalar
  cohomology. Their existing definitions are reused, so no new definition node
  is introduced for those notions.

Validation: prescribed scompile.py compiled both its sandbox and library-name
forms cleanly (2.0 s and 2.1 s). No compiler errors or warnings were printed.

## Second reading by Q102

A second in-thread reading was performed with the node and delivered file open;
no other agents were started, as the dispatcher's brief forbids doing so.
The maintainer's independent review remains the separate review of this delivery.

The check matched Field, Scheme/Over, SmoothOfRelativeDimension and IsProjective
to exactly the four geometric inputs; traced relativeDifferentials, exteriorSheaf
and dual to their recorded canonical constructions; and checked the equation's
variance: v-dual reverses E→E', H^(n-j)(v) goes forward, so both sides act on the
same x from E. Checked that θ is existentially quantified outside the naturality
clause, hence one simultaneous natural family is asserted. Checked that both
finite-dimensionality conjuncts concern the two spaces printed in the node,
and that the last conjunct states zero as Subsingleton on the underlying
vector space. Checked the integer subtraction and the negative-degree zero
functor at j=n+1; the n=0 exterior power agrees with O_Y by the owning theorem.
No mismatch found and no source correction needed. A finite nontrivial field
extension and a disconnected scheme are allowed because no H^0(O)=F, integral,
connected or nonempty hypothesis was added. The helper introduces only the
node's explicit grading convention, with no theorem or data chosen by sorry.
