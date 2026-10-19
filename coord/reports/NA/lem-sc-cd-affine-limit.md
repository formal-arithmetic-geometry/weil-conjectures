## Worker report

The module Sheaf.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionAffineLimit states
AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_of_isLimit.
Its sole theorem has proof `by sorry`; it defines no new notion. The node changes only in `lean`.

Read the full node, both statement dependencies and their records, the definition module,
and the source blueprint file sec-smooth-purity/sk-prop-sf-cbc/lem-sc-cd-affine-limit.md,
statement and all three proof paragraphs. The declaration docstring carries the expanded
three-step proof from the DAG, including the finite-cover argument and the qcqs-limit check.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A filtered inverse system is `{I : Type u} [SmallCategory I] [IsCofiltered I]`
  and `D : I ⥤ Scheme.{u}`. Cofiltered is the inverse orientation of filtered:
  its definition includes nonemptiness, common predecessors and equalization of parallel
  arrows. A nonempty directed preorder can be used by taking its opposite category.
  The index and schemes share universe u, as required for inverse-limit statements.
- Each X_i is exactly `D.obj i`, and quasi-compactness is
  `[∀ i : I, CompactSpace (D.obj i)]`. Mathlib compactness assumes no separation axiom.
- Each stage is quasi-separated by `[∀ i : I, QuasiSeparatedSpace (D.obj i)]`.
  This is the scheme's standard topological characterization, not separatedness.
- Affine transition maps are `[∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]`.
- The specified inverse limit X is the vertex `s.pt` of `(s : Cone D)`,
  with `(hs : IsLimit s)` expressing its universal property. No chosen canonical
  limit or additional qcqs hypothesis on X is required.
- The nonnegative bound is `(c : ℕ)`, using exactly the recorded definition's domain.
- The uniform stage hypothesis is
  `(h : ∀ i : I, HasTorsionEtaleCohomologicalDimensionLE (D.obj i) c)`.
- The entire conclusion is `HasTorsionEtaleCohomologicalDimensionLE s.pt c`.
  It uses the identical c, with no shift or new degree restriction. The predicate already
  quantifies over every locally torsion abelian small-etale sheaf and every q > c;
  no uniform annihilator is imposed.

Statement dependencies used:

- def-sc-etale-torsion-cd: Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension,
  AlgebraicGeometry.Scheme.HasTorsionEtaleCohomologicalDimensionLE. Read its full definition
  and docstring: vanishing is Subsingleton of ordinary derived-section cohomology on the
  degree-zero sheaf, with CategoryTheory.Sheaf.IsTorsion as its hypothesis.
- def-weil-pbc-scheme-conventions is explicitly a convention node with null declaration
  and module; it defines no object. Its recorded conventions are used through Mathlib's
  Scheme, CompactSpace, QuasiSeparatedSpace and IsAffineHom. Read the full IsAffineHom
  signature/docstring in Morphisms/Affine.lean:43-48, QuasiSeparatedSpace in
  Topology/QuasiSeparated.lean:43-50, CompactSpace in Topology/Defs/Filter.lean:279-285,
  IsCofiltered in CategoryTheory/Filtered/Basic.lean:570-593, and IsLimit in
  CategoryTheory/Limits/IsLimit.lean:47-58. No dependency module is needed.

The statement imports are public. The following recorded proof dependencies have regular
imports, preserving the stage-3 proof plan: Sheaf.Paper.EtaleFiniteDataDescent
(AlgebraicGeometry.etale_finite_data_descent); Mathlib.AlgebraicGeometry.AffineTransitionLimit
(isAffineHom_π_app, isLimitOpensCone); Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
(the affine-cover criterion, already publicly imported for its statement definitions);
WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs (Etale.upperStar, lowerStar);
Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation (qcqs permanence uses the other
already imported morphism modules as well); Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings
(etale_qcqs_cofinal_finite_affine_coverings); Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity
(Etale.cohomology_continuity_of_isLimit);
WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
(Etale.preservesColimitsOfShape_shiftedHomFunctor_freeSheaf_finalObject);
Sheaf.AlgebraicGeometry.TorsionFilteredUnion
(Scheme.isTorsionAbelianSheaf_of_isTorsion).

Edge cases checked: c = 0 is admitted; q = c is excluded by the existing strict inequality,
exactly as the definition requires. Empty schemes and zero sheaves remain admitted.
There is no field or characteristic restriction, and stages need not be affine or separated.
An empty indexing category is not cofiltered: no accidentally vacuous family of bounds can
assert a bound for an empty-diagram limit. A singleton system reduces to transporting its
stage bound to an isomorphic limit. General torsion sheaves, with unbounded annihilators,
remain covered. No independent smaller index universe was introduced.

Searches actually made:

- msearch.py leansearch: "torsion etale cohomological dimension bound inverse limit schemes
  affine transition maps". Service unavailable: Internal Server Error (not evidence of no match).
- msearch.py leanfinder: "torsion etale cohomology vanishing passes to cofiltered limits of
  schemes with affine transition maps". Eight hits concern affine-transition scheme limits,
  structure-sheaf sections and affine opens; none states torsion-etale cohomological vanishing.
- msearch.py loogle: "AlgebraicGeometry.Scheme, IsLimit, IsAffineHom".
  Unknown identifier IsLimit, zero usable hits; this failed query is not no-match evidence.
- msearch.py grep: "HasTorsionEtaleCohomologicalDimensionLE|torsion.*[Cc]ohomological|[Cc]ohomological.*[Dd]imension".
  Zero Mathlib hits.
- Direct rg of the same expression over WeilConjectures and lean/Sheaf found the dependency
  predicate, finite-type and affine-curve bounds, and different relative/pro-etale bounds.
  Read upstream AlgebraicGeometry/Sites/CohomologicalDimension.lean in full: its theorems
  are finite-type-over-a-field bounds, not this inverse-limit statement.
- grep -rn of lem-sc-cd-affine-limit over upstream WeilConjectures returned no hits.
- rg of hasTorsionEtaleCohomologicalDimensionLE_of_isLimit over Mathlib,
  WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json returned no hits.

No statement correction, new nodes, dependency repairs or disputed statements.

Server validation: scompile.py NA lem-sc-cd-affine-limit compiled the module cleanly,
using nice 19, two threads, the 60-second per-file limit, and read-only live artifacts.
The compiler reported 2.7 seconds for the item (and separately prepared the already recorded
predicate module). No local Lean compiler or Lake build was run.

## Second reading by NA

Independently read the sandbox node and complete Lean file, both statement-dependency
nodes and their recorded declarations, the blueprint source statement and proof, and the
containing unit. The source here is the blueprint markdown, not a Stacks lemma: it imposes
no ambient field, characteristic, Noetherian, separated, or finite-type hypothesis.
The corrected convention node fixes no separate object and needs no dependency module.
There are no new nodes, dependency modules, or statement_change records in this delivery.

Object/hypothesis/conclusion checklist, with verdicts:

- A filtered inverse system: `{I : Type u} [SmallCategory I] [IsCofiltered I]`
  and `(D : I ⥤ Scheme.{u})`. Read Mathlib's IsCofiltered definition: nonempty,
  common predecessors, and equalization of parallel arrows. This is exactly the inverse
  orientation of filteredness; directed-set systems are included. PASS.
- Stage schemes X_i: `D.obj i`, in the same Scheme universe as the limit. PASS.
- Every stage quasi-compact: `[∀ i : I, CompactSpace (D.obj i)]`.
  CompactSpace means compactness of the whole underlying space, without Hausdorffness.
  This is scheme quasi-compactness. PASS.
- Every stage quasi-separated: `[∀ i : I, QuasiSeparatedSpace (D.obj i)]`.
  Read the definition: compact open intersections are compact, the standard absolute
  scheme quasi-separatedness condition. No separatedness is imposed. PASS.
- Affine transition maps: `[∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]`.
  Read IsAffineHom: preimages of affine opens are affine. All transitions and exactly
  the required property are covered; the stages need not themselves be affine. PASS.
- The specified inverse limit X: `(s : Cone D) (hs : IsLimit s)` and `s.pt`.
  The cone records projections and their compatibility; IsLimit records the universal
  property. No additional limit existence assumption or qcqs assumption is added. PASS.
- Nonnegative integer bound c: `(c : ℕ)`, exactly the domain of the recorded
  HasTorsionEtaleCohomologicalDimensionLE predicate. PASS.
- Uniform bound on every stage: `(h : ∀ i : I,
  HasTorsionEtaleCohomologicalDimensionLE (D.obj i) c)`. Same c for every stage. PASS.
- Whole conclusion: `HasTorsionEtaleCohomologicalDimensionLE s.pt c`. Opened the
  dependency definition: all torsion abelian small-etale sheaves, not just bounded-exponent
  sheaves; all natural q with c < q; Subsingleton of ordinary derived-global-section
  cohomology of the sheaf placed in degree zero. Read Etale.cohomology in
  WeilConjectures/SixFunctors/Etale/Derived/LowerShriek.lean: RΓ followed by homology.
  Thus the conclusion is precisely the unchanged torsion dimension bound. PASS.

Edge cases: c = 0 is included, and degree q = c is intentionally not constrained.
Empty schemes, the zero sheaf, arbitrary characteristic, and torsion sheaves with no
uniform annihilator are included. The empty indexing category is excluded by
IsCofiltered itself, as required for a filtered inverse system; a singleton system is
included. The shared universe u for the small index category and Scheme follows the
project's limit convention and does not introduce a smaller independent test universe.
All universe and object variables are explicitly bound.

Independent searches used different phrasing from the first worker:

- msearch.py leanfinder: "uniform vanishing of higher etale cohomology inherited by an
  inverse system limit of qcqs schemes". Eight hits, chiefly Mathlib affine-transition
  global-section descent lemmas; none concerns this torsion cohomological dimension bound.
- msearch.py loogle: `"IsCofiltered", "IsLimit"`. Successful query, zero hits.
- Direct rg across Mathlib, WeilConjectures, project lean/Sheaf, and the upstream name
  index for `hasTorsionEtaleCohomologicalDimensionLE_of_isLimit`,
  `torsion.*cohomological dimension`, and `cohomological.*dimension.*limit`:
  only the dependency predicate, finite-type bounds, and unrelated mentions.
- Broader rg for `cohomologicaldimension|cohomological_dimension|cohomology.*limit|limit.*cohomology`
  in algebraic-geometry sources found continuity and filtered-colimit tools, not this
  theorem. Opened upstream Sites/CohomologicalDimension.lean in full: its field/finite-type
  dimension bounds are different statements. Opened Sites/CohomologyContinuity.lean:
  its fixed-base-sheaf continuity vanishing theorem is a proof tool, not this result.

No mismatch found, and no Lean or node change was needed. The signature in lean.statement
is verbatim the file signature. The sole proof is sorry; there is no definition, hollow
construction, private notation, local instance, or extra proved assertion. The declaration
and module docstrings have their source and blueprint id. The declaration's three proof
steps track the DAG's qcqs check, finite-data descent and reconstruction, continuity,
filtered colimits, and removal of the fixed exponent. Imports retain the recorded proof
plan; no file-local convention is needed to read the statement.

Fresh server validation with scompile.py NA lem-sc-cd-affine-limit on the sole delivery
module passed cleanly: predicate dependency 1.3 s, item 2.7 s; nice 19, two threads,
60 seconds per file. No local compiler or lake build was run.
