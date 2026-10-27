## Worker report

The module `Sheaf.AlgebraicGeometry.CyclicRootCoverEigenforms` states
`AlgebraicGeometry.cyclic_root_cover_eigenforms`. Its sole postponed proof is the
main theorem. The auxiliary records unpack the clauses of this node; they do not
choose objects from an unproved existence theorem. All helper definitions have
actual bodies. No statement correction, dependency replacement or new independent
notion is required.

Source read: Popa, *Kodaira dimension of algebraic varieties*, Proposition 1.6.5,
proof of Theorem 1.6.6, and Lemma 1.6.7, printed pages 24–27, at
https://people.math.harvard.edu/~mpopa/271/Kodaira-posted.pdf. The local logarithmic
presentation and residue were also checked against Stacks Tag 0FMW, the degree-one
part of `lemma-log-complex` in `literature/stacks-project/derham.tex`.

Hypotheses, one by one:

* `F : Type u`, `[Field F]`, `[IsAlgClosed F]`, `[CharZero F]` express the specified
  algebraically closed characteristic-zero field.
* `Y : Scheme.{u}` and `p : Y ⟶ Spec (.of F)` express an F-scheme.
* `[SmoothOfRelativeDimension n p]`, `[IsProjective p]`, and
  `[GeometricallyIntegral p]` express smoothness, pure dimension n, projectivity,
  and geometric integrality. Over a field, for a smooth pure-dimensional scheme,
  fixed smooth relative dimension is the equivalent recorded convention.
* `n : ℕ` includes n=0 without a positive-dimensional restriction.
* `L : Y.Modules`, `[L.IsInvertible]`, `m : ℕ`, `hm : 2 ≤ m` are the line bundle
  and specified exponent.
* `s : 𝟙_ Y.Modules ⟶ L.tensorPow m` is a global section, `hs : s ≠ 0` its
  nonvanishing, and `hD : Smooth (s.zeroLocus.subschemeι ≫ p)` is precisely the
  smoothness of its zero scheme. No nonemptiness assumption is made on D.

Conclusion, clause by clause:

* `cyclicRootNegativePower` is the tensor power of the existing internal-Hom
  dual; `cyclicRootSectionPower` constructs actual powers of sections recursively.
* `cover.functions` and `functionsBilimit` are the finite direct sum of those
  inverse powers. `functionsIso` compares it to the actual structure sheaf of W.
* `charts.rootChart` gives the A-algebra chart `AdjoinRoot (X^m-C b)`, fixes the
  A-map, and sends each inverse-frame power to t^a. Thus the multiplication,
  including reduction by s, is specified, rather than replaced by an arbitrary
  module decomposition. The frame and dual-frame quantifiers include their
  free-generator and evaluation hypotheses. Quantification over all affine
  trivializations fixes the gluing and not merely one unrelated affine chart.
* `cover.finiteLocallyFree` is the recorded rank-m predicate.
  `affinePreimage` includes every affine open, and `smoothDimension` and
  `projective` give exactly the claimed geometry of W. W is never assumed
  integral, geometrically integral, or connected.
* `logarithmic.log`, `regular`, `logGenerator`, `logGenerated`, and `logRelations`
  give the full presentation `(Ω ⊕ O)/(du,-u)` on each affine principal-divisor
  chart. Under the theorem's hypotheses this is the rational subsheaf generated
  by Ω and du/u: u is a nonzerodivisor and Ω is locally free, and the smooth
  divisor makes du part of a basis along D. The presentation identifies the
  object uniquely compatibly with regular forms and the logarithmic generator;
  it is not an unspecified existence choice. `regularMono` records the inclusion.
  `emptyDivisor` makes that inclusion an isomorphism when D is empty.
* `residue` is an O-linear module morphism to the actual direct image of O_D.
  `residueFormula` sends α+b du/u to the image of b in O_D, using the actual
  closed-immersion ring map.
* `decomposition.forms`, `formsBilimit`, and `formsIso` give the differential
  sum. The invariant inclusion is `cyclicRootPullDifferentials` constructed
  from the existing universal derivation. The two differential chart equations
  fix the positive inclusion on α and on du/u, including the factor m t^(a-1).
* `characters.functionAction`, `formAction` are roots-of-unity representations.
  Their equations give eigenvalue ζ^a on the specified inclusions, and identity
  on invariant differentials. Together with the root-chart basis normalization
  these are exactly the actions t↦ζt and its induced differential action.
* `differentials.dY`, `dW` are maps of underlying abelian sheaves, specified on
  every open to equal the existing universal `sectionsD`; these derivations are
  F-linear. `connection` is also an underlying abelian sheaf map and
  `connectionLinear` explicitly requires F-linearity. `connectionFormula` is
  `(dc+(a/m)c du/u)⊗e^-a`, with a and m mapped to F and then to sections.
  `differentialBlock` and `differentialInvariantBlock` state the actual block
  equations on every open, not just affine trivializations.
* `Scheme.Modules.H` is the existing Ext-model of underlying abelian sheaf
  cohomology. The module imports the recorded right-derived module cohomology
  and uses `moduleCohomologyExtResolutionEquiv` to identify the two canonically.
  The two comparison functions are bijective and additive for every q:ℕ; their inverse
  normalization fixes them as the canonical additive isomorphisms.
  The invariant factor is separated from the positive characters; the finite
  product of positive groups is canonically their finite direct sum.
  The normalization conjuncts of `CyclicRootCohomologyBlocks` say the comparisons invert the sums of actual
  summand inclusions followed by the canonical finite-morphism edge map.
  Thus these are the canonical comparisons, not arbitrary group isomorphisms.
* `cyclicRootH` is an abbreviation for the existing `Sheaf.H` with the
  coefficient module visible. Thus `Sheaf.H.map dW`, `Sheaf.H.map (connection a)`
  and `Sheaf.H.map dY` are the actual additive coefficient maps, without an
  O-linearity assertion. The canonical module/abelian equivalences in
  `cyclicRootCohomologyEdge` fix the agreement with ordinary module cohomology.
  The last two conjuncts of `CyclicRootCohomologyBlocks` give H(∇a) on positive
  characters and H(dY) on invariants in every degree, including zero.


Dependency interfaces used:

* Mathlib `Field`, `IsAlgClosed`, `Scheme`, `Smooth`,
  `SmoothOfRelativeDimension`, `GeometricallyIntegral`, `KaehlerDifferential` and
  its universal derivation, from the field, algebraic-geometry and Kähler modules.
* `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsProjective`.
* `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`; `Modules.Dual`: `dual`, `dualEvaluation`;
  `Modules.TensorSection`: `tmulSection`, `unitSectionsEquiv`;
  `Modules.FreeGenerator`: `IsFreeGenerator`.
* `WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus`:
  `Scheme.Modules.Hom.zeroLocus` and its actual ideal and closed immersion.
* `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials`, `relativeDifferentialsHomEquiv`,
  `pushforwardDerivation`; `Modules.DifferentialsSections`: `sectionsD`,
  `specStructureMap`.
* `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `Scheme.Hom.IsFiniteLocallyFreeOfDegree`.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, using the existing sheaf tensor.
* `WeilConjectures.AlgebraicGeometry.PQFCohomology`:
  `sheafCohomologyAndHigherDirectImages` and `RingedSpace.moduleCohomology`;
  `ModuleCohomologyFMap`: `moduleCohomologyEdgeMap`;
  `ModuleCohomologyExtResolutionNaturality`:
  `moduleCohomologyExtResolutionEquiv`;
  `CategoryTheory.Sheaf.H.map` for additive coefficient maps.
* The stated proof dependencies are imported as plain proof imports. The theorem
  docstring gives the twelve-step proof and names its supporting DAG nodes.

Edge cases checked mathematically before writing:

* D empty: its equation is a unit locally, du/u is regular, residue is zero;
  `emptyDivisor` applies and the cover can be disconnected.
* n=0: a nonzero section on the geometrically integral smooth zero-dimensional
  projective F-scheme has empty zero scheme. The cover is a disjoint union of
  m points; the differential terms vanish. Nothing requires n≥1.
* m=2: exactly one positive character; natural subtraction in a-1 is valid
  because positive indices exclude zero. a=0 appears only in the invariant block.
* Trivial L and an mth power section with empty D do not force connected W.
* The empty scheme is excluded exactly by geometric integrality; empty affine
  opens are harmless (the local presentations are presentations of zero modules).
* Characteristic zero supplies invertibility of m; no extra invertibility binder
  or primitive-root choice is added. q=0 is included in both comparisons.

Searches actually run (full msearch output is retained in sandbox searches.jsonl):

* LeanFinder: “Cyclic root cover of a line bundle logarithmic differential
  eigensheaves and cohomology”: eight unrelated cotangent/Hilbert-90 results;
  no matching theorem.
* Loogle: `KaehlerDifferential, AdjoinRoot`: zero hits.
* Mathlib grep: `logarithmic.*differential|cyclic.*cover|eigensheaf`: only a
  logarithmic derivative in differential field theory, not this sheaf.
* LeanSearch: “Logarithmic one forms along a smooth divisor defined by generators
  and relation”: presentation/Kähler/scalar dlog results, no logarithmic sheaf.
* LeanFinder: “Cyclic root cover of section of invertible sheaf algebra local
  polynomial root charts”: affine-chart results, no root-cover package.
* rg in `lean/WeilConjectures` and `lean/Sheaf` for cyclic root, log differential,
  eigensheaf names: no equivalent declaration. Existing logarithmic étale
  structures concern a different site/notion.
* DAG search for cyclic root/logarithmic forms: no separate duplicate node;
  `tools/blueprint_refs.py search 'cyclic root cover'` returned zero units.
  The item's recorded blueprint ancestor is null. The current blueprint was
  used, not an old snapshot.

No statement is disputed. The node's statement and dependency lists are unchanged.

## Validation

All compiler invocations use the prescribed scompile.py wrapper with the default
60-second limit. The final source compiled cleanly in 31.2 seconds as the sandbox module and
41.8 seconds under its library module name; no warnings or errors. Delivery
preflight is run separately by deliver2.py. Independent mathematical review is left to the
maintainer as specified by the dispatcher's brief; no second-reader claim is made.

Delivery dry run passed: `deliver2.py ... --no-push` printed
`OK (dry run): commit c2378eb5031 passes the preflight and compiles; nothing pushed`.
The node copy differs from the repository only in `lean`; one module, one sorry,
no overlength source lines, and no scratch Lean files are included.

## Second reading by Q127

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
