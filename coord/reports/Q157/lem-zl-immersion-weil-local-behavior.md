## Worker report

The delivery states `WeilConjectures.zlImmersionWeilLocalBehavior` in
`Sheaf.Paper.ZlImmersionWeilLocalBehavior`. Its single theorem has proof `sorry`.
The other declarations compute the recorded operations or package clauses of this
node; `zlClosedWeilStalk` specializes the geometric-point stalk, and
`zlOpenStalkIso` constructs the inside-open comparison as a composite. No definition chooses data from the theorem's existence conclusion. The
natural-language statement, proof and proof dependencies are unchanged.

Hypotheses and objects, clause by clause:

- `D : FiniteFieldDatum.{u}` supplies the prime p, positive exponent, q, arbitrary
  finite base field with that cardinality, and its chosen algebraic closure.
  `c : D.CoefficientDatum` supplies the prime l, `l ≠ p`, and the fixed algebraic
  closure of `Padic l`. No choice of an integral Frobenius-stable lattice is made.
- `W₀ X₀ U₀ : Over (Spec (.of D.k₀))` are the actual schemes over the finite
  base. The ambient binders `LocallyOfFiniteType` and `QuasiCompact` express finite
  type; the theorem's `IsSeparated` binders express separatedness for each scheme.
- `h₀ : W₀ ⟶ X₀` has `IsImmersion h₀.left`. Mathlib's
  `isImmersion_iff_exists` is exactly the closed-then-open factorization in the
  node. `j₀ : U₀ ⟶ X₀` has `IsOpenImmersion j₀.left`. Both are morphisms over k₀.
- `zlGeometricMap` is the morphism given by the actual `Over.pullback` functor
  along `Spec (algebraMap D.k₀ D.k)`. `zlPullback` is the recorded
  `commonStageDerivedPullback` on that morphism, with the prime-invertibility
  data already derived by `sfWeilPrimeInvertible`.
- The coefficient categories and Weil pairs are the recorded
  `generalAlgebraicallyClosedConstructibleCategory`, `sfCommonStageWeilComplex`
  and `sfCommonStageWeilSheaf`. `zlHeart`, `zlStandard` and `zlFrobenius` are
  specializations of their recorded predicates, t-structure and endofunctor.

Clause 1:

- `ZlImmersionPullback.commutes` is the Frobenius square over the base-changed
  h₀. `equivariance_normalization` specifies its pullback comparison on every
  finite stage by `zlRationalFrobeniusComparison`: inverse composition across
  g_W then h, the equality of composite scheme maps, then composition across
  h then g_X. `IsoAlgebra.mapOfNatIso` therefore supplies precisely the induced
  Weil structure, alpha followed by h-star(theta).
- `operation.comparison.tExact` is t-exactness of the actual underlying pullback.
  `operation.sheaf` restricts its fixed-pair lift to the recorded full heart;
  `sheaf_fac` identifies that restriction as a functor, including its maps.
  `sheaf_limits` and `sheaf_colimits` express exactness on the Weil heart.
- For every integer a, `operation.cohomology a` is a natural isomorphism of Weil
  functors between h-star(H^a K) and H^a(h-star K). The inverse is the displayed
  direction in the node. `cohomology_map` identifies its forgotten map with the
  canonical truncation comparison. `zlWeilCohomology` uses the induced structure
  through the canonical Frobenius/cohomology comparison itself.
- `closed_image` states closedness of h₀(z) for every closed z. `residue_iso`
  concerns the actual `h₀.left.residueFieldMap z`; it identifies the residue
  fields in the correct contravariant direction. `degree_eq` equates the actual
  degrees over k₀, hence the sizes q^r.
- Compatible geometric points are represented by the two residue-field
  embeddings into D.k, their k₀-compatibility equations, and
  `ιz.comp (h₀.left.residueFieldMap z).hom = ιx`. `localClosedPoint` is the
  dependency's actual lift to the geometric fibre.
- `stalk` is the natural stalk isomorphism; `stalk_normalization` identifies its
  finite-stage maps with `zlRationalStalkComparison`, namely H^0 of the point
  fibre of the inverse specified pullback-composition comparison. The HEq only
  transports the object equalities in the recorded common-stage functors.
  `stalk_frobenius` states equality of the two composites for every constructible
  Weil sheaf, using the same `stalk` isomorphism.

Clause 2:

- `ZlOpenExtension.geometric_open`, `geometric_qc`, `geometric_ft`,
  `geometric_sep`, `geometric_over` and `prime_unit` are conclusion data. They
  are the inherited geometric hypotheses needed by the already recorded
  compact-support action; they are not extra assumptions on the model schemes.
- `action` is `SfCompactSupportCoefficientAction` for the compactification
  `Compactification.ofIsOpenImmersion j`, which is exactly (j,id). Its system
  functor uses the recorded `sfQbarCompactSupportValue`, the fixed integral
  action, pure-tensor rational maps and normalized coefficient comparisons.
  `functor_eq` ties the short functor field literally to this action on both
  objects and arrows. It is not an unconstrained functor with the same object values.
- `equivariance_mate` fixes the inverse Frobenius comparison as the adjoint
  transpose of Frobenius of the actual unit followed by the normalized
  restriction comparison. `IsoAlgebra.mapOfNatIso` supplies its Weil lift.
  `operation.comparison.tExact`, the exact full-heart restriction, and
  `operation.cohomology`/`cohomology_map` give all the t-exactness, constructible
  heart and natural Weil H^a clauses, as for pullback.
- `adjunction`, `unit_isIso`, `weilUnit` and `weilUnit_map` retain the open
  extension/restriction adjunction and require its actual unit to lift to a Weil
  isomorphism. `zlOpenStalkIso` constructs the inside-open stalk comparison
  as inverse restriction followed by inverse open unit. `openStalk_frobenius`
  states commutation for that comparison. The `restriction.degree_eq` field
  retains the equal residue degree and size for the open immersion.
- `outside` quantifies over every closed point x outside `Set.range j₀.left`,
  every compatible residue embedding/geometric point and every constructible
  Weil sheaf G. It asserts `IsZero` of the actual module stalk of its extension.
  Every closed x inside the range is the image of a closed point of U₀ because
  an open immersion is a topological embedding; thus the inside and outside
  clauses cover all the node's closed points.

The local operators are not existentially arbitrary endomorphisms: the
`ZlWeilLocalOperators.normalization` field fixes their components at *every*
finite-stage Weil pair to H^a of scalar extension of the already defined
`localClosedFrobenius`. That definition includes iterated point transport, the
return comparison and iterated Weil structure. Naturality and representation
of a Weil pair, its inverse structure and inverse equations at one finite
coefficient field determine the result on every common-stage object. Equality
of operator composites, rather than equality only of traces, is asserted.

Dependency declarations read and used:

- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilPrimeInvertible`,
  `sfCommonStageWeilFrobeniusPullback`, `sfCommonStageWeilComplex`,
  `sfCommonStageWeilForget`, `sfCommonStageWeilSheaf`, `sfWeilStageObject`.
- `Sheaf.Paper.SfConstructibleHeart`: `sfCommonStageHeartProperty`,
  `sfCommonStageStandardTStructure`.
- `Sheaf.Paper.LocalFrobeniusTrace`: `localPullbackComposition`,
  `localClosedPoint`, `localClosedPointDegree`, `localClosedFrobenius`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`: `IsImmersion` and
  `isImmersion_iff_exists` identify precisely the node's factorization.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedPullback`,
  `commonStageDerivedPullback` and their object/representative specifications.
- `Sheaf.Paper.IntegralRationalQbarCompactSupport`: `sfQbarCompactSupportValue`,
  used through its already normalized coefficient action.
- `Sheaf.Paper.ConstructiblePullbackTExact`:
  `ConstructiblePullbackComparison`; the package retains the truncation-unit and
  counit normalization and the explicit cohomology formula. This landed node is
  added to stmt_deps because the signature uses its clause package.
- `Sheaf.Paper.CompactSupportCoefficientAction`:
  `SfCompactSupportCoefficientAction`; this already landed definition is added
  to stmt_deps because the signature retains the canonical action on maps.
- Point fibres, cohomology and finite scalar realization are the dependency
  chain's `pointRationalFibre`, `pointQbarFibre`, `pointFdScalarExtension`,
  `pointFdQbarStage`, `pointFdQbarRealization` and Mathlib's homology functor.

Proof-only imports retain the available recorded interfaces for integral
pullback composition, closed point fields, truncations and heart triangles,
Noetherianity, exact functors and complex cohomology, independent-universe site
localization, integral compact-support constructibility, open extension through
products and completed open exchange. The four proof nodes without a Lean
record or Mathlib match (Frobenius point-transport naturality, integral open
reduction comparison, open tensor normalization, and integral/completed pullback
comparison) remain proof prerequisites, not silently replaced statement inputs.

Edge cases checked: empty W₀ or U₀ (closed-point clauses vacuous, outside stalks
zero), empty X₀, identity immersions, a closed immersion, zero sheaves and zero
complexes, all positive and negative cohomological degrees, rational closed
points of degree one, non-rational closed points of any positive finite residue
degree, and common-stage Weil arrows represented after field enlargement. There
is no nonempty scheme hypothesis or restriction on residue degree. The only
characteristic restriction is c.different, as in the node. Universes u,uC,vC,uB,vB,uV,vV
and all binders are explicit; the geometric and coefficient datum use their
recorded common size convention.

Searches:

- `msearch.py ... leanfinder`: "Pullback and open extension by zero of
  constructible Weil sheaves are exact and commute with cohomology and local
  Frobenius on stalks" returned eight module pullback/derived-category hits;
  none states the common-stage Weil assertion.
- `msearch.py ... loogle`: "WeilSheaf, IsoAlgebra, PreservesFiniteLimits"
  returned zero hits (unknown Mathlib identifier WeilSheaf).
- `msearch.py ... grep`: "WeilSheaf|localFrobenius|extensionByZero.*stalk|
  stalk.*extensionByZero" returned zero Mathlib hits.
- `msearch.py ... leansearch`: "Pullback of constructible Weil sheaves is exact
  and extension by zero has Frobenius equivariant stalks" returned ordinary
  module/sheaf pullback, adjunction and topological stalk maps, not this assertion.
- `rg` in the upstream WeilConjectures tree and side Sheaf tree for local
  Frobenius, common-stage compact support, Weil pullbacks and open extension
  found the dependency modules above and the upstream
  `WeilSheaf/OpenImmersion.lean`; the latter is a different coefficient/sheaf
  category and does not supply this fixed-pair common-stage statement.
- Exact item-id search in upstream WeilConjectures found no declaration.
  Searches for the proposed declaration names in Mathlib, upstream, side Sheaf
  and dag/lean_names_upstream.json found no collision.

No statement correction, new independent definition node or dependency-record
repair is needed. The helper structures are clause packages of this item,
recorded in lean.declarations with source and blueprint docstrings.

## Second reading by Q157

The dispatcher explicitly prohibited starting another agent and assigns an
independent maintainer review after delivery. This section records the worker's
second pass, not a claim of independent review. I reread the node and module,
checked the hypothesis and clause matching above, and checked that pullback
cohomology is given in the inverse direction of the displayed node isomorphism
(an equivalent natural isomorphism), that induced Weil structures have the
correct comparison orientation, and that outside stalks are `IsZero` of modules.
I replaced implicit finite-stage instance synthesis by explicit coefficient and
prime-invertibility arguments, typed every closed-point variable in the open
Frobenius equation, and kept all geometric open-functor properties in the conclusion.
The open Frobenius comparison is its specified adjunction mate; its inside stalk
isomorphism is constructed rather than left as an independent witness. The final compile and delivery-preflight results are recorded
below when available.

## Validation

The prescribed `scompile.py Q157 lem-zl-immersion-weil-local-behavior` check
passed both the sandbox module and the actual library module with exit code 0
and no warnings. The delivery dry run below recompiles the final packet,
including the final docstrings and direct public dependency import.

The prescribed `deliver2.py Q157 lem-zl-immersion-weil-local-behavior --no-push`
returned `OK (dry run): commit ee3be0b70b passes the preflight and compiles;
nothing pushed`. The final packet compiles cleanly and passes the server
preflight. The delivery command reruns these checks before pushing.
