## Worker report

The module `Sheaf.AlgebraicGeometry.MarkedNodalTowerCartesianExtension` states
`AlgebraicGeometry.marked_nodal_tower_cartesian_extension`, with one `sorry` and no
new definitions. The natural-language node statement is unchanged. The only DAG
changes are its Lean record and two added statement dependencies for existing,
already-landed notions: `def-weil-pure-dimension` and
`def-sfb-dominant-function-field-map`.

Source read: de Jong, *Families of curves and alterations* (1997), publisher PDF
https://www.numdam.org/item/10.5802/aif.1575.pdf, Situation 5.8, printed
pp. 615--616, and the proof of Theorem 5.9, p. 617. The final paragraph forms the
ordinary fibre product and appends its curve projection. Situation 5.8 supplies
the boundary recursion and allows permutation of the markings. Also read the
current blueprint direct-images proof under
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`.
This auxiliary node is not a blueprint unit's own statement.

Hypothesis-by-hypothesis correspondence:

* Fields and finite extensions: `k e F : Type u`, their `Field` and `Algebra`
  instances, `IsScalarTower k e F`, and `Module.Finite k e`, `Module.Finite e F`.
  The explicit third algebra is compatible with the two inclusions; it adds no
  independently chosen field extension.
* Finite groups and surjection: `G : Type v`, `J : Type w`, `Group`, `Finite`,
  `ρ : J →* G`, `hρ : Function.Surjective ρ`. No injectivity of any action.
* Compatible field actions: `σk`, `σe`, `σF`, and `hke`, `heF` on the algebra maps.
  Scheme actions are monoid homomorphisms into `Aut`; inverse field
  automorphisms in the Spec equations give the usual covariant left action.
* Integral finite-type e-schemes: `B V`, `IsIntegral`, structure map `b`, and
  `LocallyOfFiniteType` plus `QuasiCompact` for `b` and `v ≫ b`.
* Family: `IsHProjective v`, `Flat v`, `LocallyOfFinitePresentation v`.
  H-projectivity gives properness, hence quasi-compactness and
  quasi-separatedness, so this is finite presentation, not merely local finite
  presentation. Redundant compactness/separation hypotheses were removed.
* Geometric fibres: `hnodal : HasNodalGeometricFibres v` includes nonemptiness,
  connectedness, dimension one and completed nodal local rings; `hfibres`
  separately states reducedness and pure dimension one for every algebraically
  closed field and every geometric point.
* Generic fibre: `Smooth` and `GeometricallyIntegral` of
  `v.fiberToSpecResidueField (genericPoint B)`.
* Quasi-splitting: `hquasi : HasQuasiSplitNodalFibres v`, exactly rational
  singular points and two rational normalization branches in every residue-field
  fibre, with no smooth-component condition.
* Action compatibility on the family: `σB`, `σV`, `hB`, `hv`.
* Finite disjoint smooth marking: `m`, `s`, `hs`, `hdisj`, `hsm`.
  `hmarks` imposes invariance of the union, not of each individual section.
* Exceptional boundary: `D : Closeds B`, `hD : IsNowhereDense`, `hDst`, and
  `hvsmooth` on its open complement.
* Given tower: `r`, `T : Fin (r+1) → Scheme`, integral instances, structure maps
  `q` of finite type over F, and `e₀` with `hq₀ : q 0 = e₀.hom` identify its bottom
  with Spec F. Using an explicit isomorphism avoids dependent casts.
* Tower maps over F: `f` and `hq`. The H-projective, flat, locally finitely
  presented instances give finite presentation by the same properness argument.
  `hfnodal`, `hffibres`, `hfgeneric`, `hfquasi` state all the same fibre clauses
  for every old stage, without imposing smoothness of any total space.
* Tower actions: `τ`, `hτq` (semilinearity), and `hτf` (equivariance).
* Old markings: `n`, `t`, `ht`, `htdisj`, `htsm`, `htstable` give finite
  disjoint smooth sections whose union is stable.
* Boundaries: `Zt`, `hZ₀`, `hZt` give exactly the displayed recursion. Their
  closedness is intrinsic to `Closeds`; this is a consequence of the assumptions
  since every section of an H-projective morphism is a closed immersion.
  `hfsmooth` states smoothness over their complements.
* Top map: `h`, its H-projective, surjective, dominant instances, `hh` (over e),
  `hheq` (equivariant through ρ), and `hhD` (inverse-image containment).
* W is literally `pullback (C := Scheme.{u}) v h`, not a reduction, normalization,
  component or arbitrary replacement. Its integrality is an explicit instance.
  `hfield` is finiteness of its function field over V under the canonical algebra
  from the projection `pullback.fst v h`; surjectivity of h gives dominance of
  that projection by base change.
* C and X: their integral instances and finite-type structure maps `pC`, `pX`.
  `c`, `π` are H-projective surjective; `hck`, `hπk` make them k-morphisms.
  `σC`, `σX`, `hC`, `hX`, `hceq`, `hπeq` give compatible semilinear actions.
* Target boundary: `Z : Closeds X`, `hZ` invariant, `hcontain` the exact required
  inverse-image containment under c followed by π.
* `hcfield` is finite k(V)/k(C), using c's canonical generic-stalk algebra.
  `hbirational` is an isomorphism of π over a dense target open. Since C, X are
  integral and π is dominant, this is the node's birationality notion and
  identifies their function fields; no arbitrary field isomorphism is assumed.

Conclusion-by-conclusion correspondence:

* The first conjuncts give H-projectivity, flatness, finite presentation (the
  existential `hfp` together with quasi-compactness and quasi-separatedness),
  nodal, reduced, pure one-dimensional geometric fibres, quasi-splitness and
  smooth geometrically integral generic fibre of `pullback.snd v h`.
* Finite type over F is asserted for `pullback.snd v h ≫ q (Fin.last r)`.
  Smoothness is asserted over the complement of the old top boundary.
* `τW : J →* Aut W` is a genuine action. Its equations with BOTH projections
  uniquely determine it as the diagonal action. Its structure-map equation
  explicitly states semilinearity over F.
* `s'` is specified by BOTH projection equations: first `h ≫ s j`, second the
  identity. Fibre-product uniqueness makes these exactly the pulled-back
  sections. Pairwise disjointness, containment in the actual relative smooth
  locus, and stability of the union are separate conjuncts.
* Every old boundary is shown J-stable; `Z' : Closeds W` has exactly the stated
  inverse-image-plus-marking union as underlying set, is J-stable, and contains
  `(pullback.fst v h ≫ c ≫ π) ⁻¹' Z`.
* The final composite a is explicitly equivariant through ρ, H-projective,
  surjective, finite on the canonical function-field extension, and projective
  in the separate `IsProjectiveBundle` convention.
* Since the old tower is unchanged and each of its conditions is in the
  hypotheses, the listed new-stage conditions append exactly one stage to it.
  There is no regularity assertion and no pointwise triviality assertion about
  the markings.

Dependency interfaces read and used:

* `Sheaf.AlgebraicGeometry.NodalGeometricFibres`:
  `AlgebraicGeometry.HasNodalGeometricFibres`.
* `Sheaf.AlgebraicGeometry.QuasiSplitNodalFibres`:
  `AlgebraicGeometry.HasQuasiSplitNodalFibres`; it uses the recorded
  `Sheaf.AlgebraicGeometry.ReducedNormalization` construction and canonical map.
* `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
* `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`.
* `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`: `IsProjectiveBundle`,
  defined using the actual symmetric graded algebra and relative Proj.
* `Sheaf.TraceFormula.LocalDimensionFormula`:
  `Scheme.Hom.dominantFunctionFieldAlgebra`, the existing real generic-stalk map.
* `WeilConjectures.AlgebraicGeometry.FunctionField` and Mathlib's function-field
  module: the arbitrary integral-scheme clause is `Scheme.functionField`.
* `Sheaf.FieldTheory.FieldTower`: its docstring records `Module.Finite` for the
  finite-extension clause; the degree definition is not redefined.
* Mathlib modules `Algebra.Algebra.Defs`, `Algebra.Field.Defs`,
  `AlgebraicGeometry.Properties`, `Morphisms.FiniteType`, `Morphisms.QuasiCompact`,
  `Morphisms.Flat`, `Morphisms.FinitePresentation`, `Morphisms.Smooth`,
  `Morphisms.UnderlyingMap`, `Morphisms.ClosedImmersion`, `Geometrically.Integral`,
  `Fiber`, `Restrict`, and `CategoryTheory.Limits.Shapes.Pullback.HasPullback`
  supply the recorded field, algebra, integral, morphism-property, fibre,
  smooth-locus, pullback and projection definitions. Full signatures/docstrings
  of the recorded declarations were read.

Proof-only imports retain the recorded projective properness, projective base
change, H-projective composition, free-projective-bundle comparison, section of
separated morphism, and surjective base-change/composition modules. The generic
function-field interface is a public import because it appears in the statement.
`lem-sfb-marked-nodal-boundary-control` has no Lean module recorded on the read
base, so there is no module to import for that proof-only dependency; its role is
preserved in the theorem docstring. Finite-type composition/base change,
surjective composition, sections of separated morphisms, and surjective base
change are already Mathlib leaves and their recorded modules are imported.

Edge cases checked before writing: r=0 leaves no old curve hypotheses and
identifies P with Spec F; m=0 and n_i=0 give empty unions, with all section clauses
vacuous; trivial groups and nonfaithful actions are allowed; markings may be
permuted; empty D and empty Z are allowed; a nonempty boundary complement is not
assumed separately. Integral schemes are nonempty by definition. Geometric tests
use the scheme universe, matching the recorded nodal/geometric definitions.
Group universes v and w are independent. Self-nodes are permitted by the precise
quasi-split predicate. Characteristic zero and positive characteristic both occur;
no separability assumption is imposed on the finite constant extensions.

Searches actually run with msearch.py (Q104, this item):

* LeanFinder query: “Base change a marked quasi split nodal curve along an
  equivariant tower preserves sections boundary and projectivity”. Eight hits,
  consisting of Weierstrass base-change and nonsingularity facts; none states
  this equivariant tower extension, boundary or composite alteration assertion.
* Loogle query: `CategoryTheory.Limits.pullback, AlgebraicGeometry.Flat`.
  Ten hits including `Flat.instFstScheme`, `Flat.instSndScheme` and geometric
  reducedness/integrality pullback instances; none supplies this statement.
* Mathlib grep query: `markedNodal|NodalTower|quasi.split` in AlgebraicGeometry.
  Zero hits.
* LeanSearch query: “Base change of an equivariant marked quasi split nodal tower
  with invariant boundary and finite function field extension”. Eight generic
  finite/quasi-compact base-change and algebraic scalar-extension hits; no match.
* Local `rg` searches in `lean/WeilConjectures` and `lean/Sheaf` for marked nodal,
  tower, equivariant and semilinear interfaces, plus a literal node-id search in
  WeilConjectures. No exact statement. The projective nodal tower definition was
  read but has extra finite-singular-complement conditions; it is not substituted
  for the actual input tower. Existing quasi-split and pure-dimension predicates
  and the canonical generic-stalk algebra are reused instead.

No statement correction, new node or dependency repair was needed. No
STATEMENT-DISPUTED flag. Compiler-guided repair made the category of W explicit
where Set/coercion elaboration otherwise inferred an unrelated pullback. No
proof was attempted or added.

Validation: scompile.py compiled both the sandbox probe and the actual library
module successfully, with no errors or warnings. The final file has no line over
100 characters, has `autoImplicit false`, and contains exactly one named theorem
with its expected postponed proof.

## Second reading by Q104

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
