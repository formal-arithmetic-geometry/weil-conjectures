## Worker report

This delivery states the top Ext consequence of the normalized derived Koszul comparison.
`Chart.topExtIso` constructs the actual isomorphism; `exists_lciAdjunctionTopExt` states its
existence and normalization for the comparison furnished unconditionally by the dependency.
The theorem uses the dependency's existing atlas interface to state all charts together.
A one-chart cover of U gives the node's single-immersion statement, with d = n-c.

Hypothesis and clause correspondence:

- Schemes and the morphism to S are `X S : Scheme.{u}` and `f : X ⟶ S`. A chart
  `T : LciKoszulDuality.Chart f d` has the open subscheme `T.chart.U`, ambient scheme
  `T.chart.P`, and its specified open immersion into `AffineSpace (ULift (Fin n)) S`.
  `T.chart.i` is the closed immersion; `T.chart.closed` is its actual closed-immersion class.
- The integers are `T.chart.n`, `T.c`, and `d : ℕ`, with `T.dimension : n = c+d`.
  This is equivalent to 0<=c<=n and d=n-c, including equality and zero.
- `T.regular` means locally on affine ambient opens that a length-c sequence is
  `RingTheory.Sequence.IsKoszulRegular` and spans the actual kernel ideal of the immersion.
  `T.conormal_free` is `IsFiniteLocallyFreeOfRank c` on the actual conormal module.
- The conormal C is `CotangentPresentation.conormalTerm T.chart.i`; V is
  `CotangentPresentation.ambientDifferentials T.chart.i T.chart.base`, the existing
  tensor pullback of relative differentials. The exact displayed determinant expression
  is `T.line`, using `exteriorSheaf`, the existing sheaf dual, and the existing tensor.
- `T.imageLine` is ordinary direct image into the ringed space (P,i_*O_U), and
  `T.scalars.obj T.imageLine` is therefore precisely the O_P-module i_*D_i.
  `T.quotientModule` is the scalar restriction of that ring's unit, namely i_*O_U.
  `T.omega` is `exteriorSheaf T.chart.base.relativeDifferentials T.chart.n`.
- The result uses the recorded `moduleSheafExt T.chart.P (T.c : ℤ)` with these exact
  module arguments. Thus its Ext is the cohomology of the existing derived internal Hom,
  rather than an unrelated isomorphic coinduction object or global Ext group.
- `topExtIso` applies `DerivedCategory.homologyFunctor` to the actual `rho`, after the
  canonical underlying-Hom comparison and scalar-single comparison, then uses
  `singleFunctorCompHomologyFunctorIso` and inverts. The theorem specifies this inverse
  exactly, so there is no rescaling or sign ambiguity. Its unique existence expresses
  the word canonical, rather than merely Nonempty of the two objects being isomorphic.
- `B.rho`, `B.normalized`, `B.normalized_atlas`, `B.determinant`, and `B.atlas.restriction`
  are the existing dependency's normalized family. `B.normalized` quantifies over all
  ordered regular generators and all coefficient sections, without selecting a frame.
  Its restriction square and the determinant restriction identify these same rho maps
  on opens. Exact cohomology and inversion then specify the asserted generator/frame
  independence and open compatibility for the defined top maps. No new free transition
  maps are introduced.
- C, kappa, D, F, E and delta are precisely the existing canonical cotangent/determinant
  construction interfaces of the comparison dependency. Their properties are supplied
  as in that node. They are auxiliary mathematical construction interfaces, not a
  geometric regularity hypothesis on the schemes. In particular the theorem imposes
  no flatness, separatedness, finite-presentation or Noetherian condition and assumes
  no relative dualizing object.

Dependency declarations read and used:

- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback` and its normalized section adjunction (via the chart).
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, its morphisms and opens.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`, `homObjMap`, `homFunctor`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the existing tensor
  structure retained in the determinant line; no replacement tensor is defined.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials`.
- `Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf`: `Scheme.Modules.exteriorSheaf`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, `homologyFunctorFactors`.
- `WeilConjectures.RingTheory.KoszulRegularSequence`: `RingTheory.Sequence.IsKoszulRegular`.
- `Sheaf.AlgebraicGeometry.SheafExt`: `moduleSheafExt` and its defining derived Hom functor.
- `Sheaf.TraceFormula.LciKoszulDualityDeterminantComparison`:
  `exists_lciKoszulDualityDeterminantComparison`, `ComparisonData`, its rho and normalization.
- `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`:
  `singleFunctorCompHomologyFunctorIso`.

Edge cases checked before writing: c=0, n=c, n=c=0, empty U and empty ambient open,
zero rings on empty opens, unbounded coefficient representatives and arbitrary characteristic.
No Fintype or nonempty generator assumption is inserted. Degree c is represented directly
by `singleFunctor _ (c : ℤ)`, so the [-c] shift has precisely the stated sign convention.
The empty wedge is the existing degree-zero exterior sheaf; no inversion by c or n occurs.

Searches: msearch LeanFinder queried top Ext of a regular closed immersion with ambient top
differentials (8 cotangent/differential hits, none the statement); Loogle queried
`"Ext", "KaehlerDifferential"` (two equality-extensionality results only); Mathlib grep queried
`Koszul.*Ext|[Ee]xt.*[Cc]onormal|[Ee]xt.*[Kk]aehler` (24 differential/algebra hits, no match).
Project rg searched `top.*Ext|adjunctionTopExt|lci.*[Ee]xt` and the exact item id in both
WeilConjectures and Sheaf; no exact normalized top sheaf Ext isomorphism exists. The broad
regex also returned unrelated occurrences, which were not treated as matches. The source
Tag 0BQZ was read locally, including its ordered-contraction sign computation.

## New nodes

`def-trf-lci-coinduction-hom-comparison` defines the uniquely specified scalar-forgetting
comparison between the chart's actual derived coinduction and ambient RHom from i_*O_U.
It uses Stacks 0BUZ, 0BV1 and 0A95. The existing generic unary-Hom theorem supplies an
uncharacterized Nonempty isomorphism and cannot by itself fix the normalization required
here. The new comparison is characterized on every representative by the defining
localization factorization, the ordinary evaluation-normalized comparison and the actual
source-degree-zero product projection. Its unique-existence theorem determines its data;
there is no selection from an undetermined existence statement. The single-source natural isomorphism is selected from a named existence theorem for
`SingleHomComparison`, which includes the exact degreewise formula using the shared
`homComplexπ`. Its source proof gives commutativity, invertibility, naturality and uniqueness.
The ordinary comparison is likewise selected together with its determining evaluation formula.
The new definition node includes those properties as well as uniqueness of the derived comparison.

Searches for this bridge: LeanSearch queried derived sheaf coinduction forgetting its action
as internal Hom (8 generic forgetful/sheafification hits); Loogle queried
`"derivedInternalHom_single_comparison"` (0 hits); rg of Mathlib, DAG, WeilConjectures and
Sheaf found the ordinary coinduction adjunction and ordinary-ring derived comparisons,
not this sheaf-level canonical comparison. `blueprint_refs.py search coinduction` returned
0 blueprint nodes. The search records in the node retain the wrapper results.

## Second reading by Q29

This is the dispatcher's single-worker self-audit; the maintainer performs the independent
reading after delivery, as specified in this task. The audit checked the node and both
modules together. The key potential mismatch was the coinduction object versus the defined
sheaf Ext; the new uniquely normalized comparison repairs precisely that interface. The
ordinary direct image and derived direct image were checked separately: the source of the
Ext arrow uses ordinary imageLine with scalar restriction; the derived model is used only
before H^c. The rank-zero and empty-chart cases remain covered by the binders and the
single-degree construction. Every postponed theorem is listed in its owning node's lean
record and has a source and natural-language proof docstring. No statement correction or
STATEMENT-DISPUTED flag is required.

## Compile repair

The resumed dry run reproduced the earlier 60-second timeout. The raw projection
`homComplex_exists.choose_spec.choose` forced repeated reduction of the large chosen
bifunctor. Replaced it with the upstream `homComplexπ` API from
`WeilConjectures.Algebra.Homology.HomComplexComponents`, whose projection specification
exists precisely to avoid this reduction. `SingleHomComparison` retains the exact
projection formula and its natural isomorphism together. `OrdinaryHomComparison` retains
the normalized ordinary comparison with the formula evaluating its value at a local
algebra section as the counit applied to that section times the input. These formulas
determine the respective data uniquely, so their named existence theorems postpone only
proofs of canonical data, rather than choosing arbitrary isomorphisms.

The selected maps use `@[no_expose]`, and every `DerivedCategory.Q` in the representative
formula specifies the existing localization universe `w`. The owning module now uses
`Opens.grothendieckTopology`, the live library's root namespace, and the shared chart
derived-category instances. Scalar additivity uses the exact existing `SheafOfModules.instAdditiveRestrictScalars`
instance explicitly. The termwise coinduction comparison is selected together with its
exact inverse-component formula: `homComplexπ` followed by the ordinary comparison
inverse. This determines the full complex isomorphism and avoids expanding the chosen
ordinary functor while lifting it through the generic complex API. Its existence theorem
is listed in the new node, with its full natural-language proof. The single-source comparison is
now selected as a full natural isomorphism and evaluated by its user, avoiding kernel
expansion of its chosen components. The top Ext map and its normalization are unchanged.

The comparison helpers are split into two further definition nodes, each with its own
module: `def-trf-lci-coinduction-ordinary-hom` owns the normalized ordinary comparison
and single-source projection; `def-trf-lci-coinduction-complex-hom` owns their termwise
complex comparison and exact inverse-component formula. The original derived comparison
node imports both. Their notions, formulas, sources and search history are unchanged
by the split. Loogle additionally searched `"coinductionComplexIso", "ordinaryHomComparison"`
with zero hits; DAG/project regex and blueprint search found no chart-specific comparison.

The self-audit was repeated after the module split. Each new node cites all definition
interfaces it uses, each module is owned by exactly one node, and the declaration lists
cover all structures, named existence theorems and real-data definitions. The ordinary
formula fixes evaluation on all local sections, the complex formula fixes every inverse
component, and the derived formula fixes the map after precomposition with localization.
These formulas preserve uniqueness without assuming an arbitrary comparison.
