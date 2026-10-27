## Worker report

The module `Sheaf.AlgebraicGeometry.DiagonalPlaneSmoothAtlas` states
`AlgebraicGeometry.DiagonalPlaneCurve.smooth_atlas`. Its only theorem proof is `sorry`.
The other twelve declarations are concrete helpers belonging to this same hypersurface
and its explicitly described atlas; they are listed in `lean.declarations`. There are no
new DAG nodes and no statement correction.

Hypothesis and clause correspondence:

- An arbitrary scheme S is `(S : Scheme.{u})`. There is no field, Noetherian,
  separatedness, reducedness or nonemptiness hypothesis on S.
- The positive integer n is `(n : ℕ) (hn : 1 ≤ n)`.
- The ordered triple of coefficients is `a : Fin 3 → Γ(S, ⊤)`; `ha` says each
  of its three entries is a unit. `hdegree` says `IsUnit (n : Γ(S, ⊤))`.
- `equation S n a` is the actual sum of the pulled-back coefficients times the nth
  tensor powers of the three existing coordinate sections of O(1). The existing
  `homOfGlobalSection` turns this global section into a morphism out of O. `curve`
  is its existing `Hom.zeroLocus.subscheme`, without taking a radical. `ι` is that
  zero scheme's specified embedding and `π` is its composite with the structural
  projection. Thus no arbitrary scheme or arbitrary equation is substituted for D.
- Smooth of relative dimension one is `SmoothOfRelativeDimension 1 (π S n a)`,
  precisely the recorded interface of def-sbc-smooth-morphisms, which includes
  smoothness. H-projectivity is the existing `IsHProjective (π S n a)`.
- Every affine open of the base is quantified as `(V : S.Opens) (_ : IsAffineOpen V)`.
  Its coordinate ring is the canonical `Γ(S, V)`. This includes every description
  V ≅ Spec R: the canonical global-sections equivalence transports the assertion
  to that R, without a choice of coordinates on the base or a restriction on R.
- `e : Equiv.Perm (Fin 3)` ranges over all coefficient/coordinate permutations.
  The distinguished projective coordinate is e(2); the other two, in order, are
  e(0) and e(1). `chartOpen` is exactly the preimage of its standard projective
  open, intersected with the preimage of V. All three charts and both orders of
  their remaining coordinates are included.
- `chartCoefficients` restricts a along V and reorders by e. `affinePolynomial`
  is literally lambda*s^n + mu*t^n + nu. `ChartRing` is its polynomial quotient.
  The first local conclusion is that the actual chart is affine. The ring
  equivalence E identifies its global functions with this quotient.
- E is specified on coefficients by `(π S n a).appLE ...` and on both coordinate
  classes by `(ι S n a).appLE ... (ratio ...)`. `ratio` uses the existing
  `Proj.awayToSection` and `MvPolynomial.awayXRatio` on the integral model, pulled
  back by `ProjectiveSpace.toProjInt`. E is therefore the required coordinate map,
  not merely an abstract isomorphism of rings.
- `HasChartAtlas` first asserts that the basic opens of the two coordinate classes
  have supremum top. For each i=0,1 it then supplies a Mathlib
  `Algebra.SubmersivePresentation` of the ACTUAL ring
  `Localization.Away (coordinate n b i)`, with variable type Fin 3 and relation
  type Fin 2. Its selected variable map is `Fin.castLE (2 ≤ 3)`, so the
  determinant is taken with respect to the FIRST TWO variables.
- The presentation relation is explicitly `localizedRelations n b i`. For i=0 it
  is (lambda*s^n + mu*t^n + nu, s*z-1), with variable order (s,z,t); for i=1
  it is (mu*t^n + lambda*s^n + nu, t*z-1), with order (t,z,s).
  A presentation identifies its target with the quotient by its relations by
  definition of `Algebra.Presentation`. Thus these are exactly the two displayed
  quotient presentations, as R-algebras. The equalities for `P.val 0` and
  `P.val 2` specify the two original coordinate classes. `P.val 0 * P.val 1 = 1`
  specifies z as the inverse of the selected coordinate.
- The final equality in `HasChartAtlas` is the explicit Jacobian computation:
  `P.jacobian = algebraMap R _ (b i.castSucc * (n : R)) * P.val 0 ^ n`.
  For i=0 this is lambda*n*s^n; for i=1 it is mu*n*t^n. The determinant is a
  unit because P is a `SubmersivePresentation`, whose field `jacobian_isUnit`
  states precisely this. The presentation dimension is 3-2=1.
- For EVERY algebra structure on an arbitrary `R' : Type (max u v)` over Γ(S,V),
  the next conclusion gives an R'-algebra isomorphism from
  `R' ⊗[Γ(S,V)] ChartRing ...` to the polynomial quotient with the mapped
  coefficients. It sends each `1 ⊗ coordinate` to the corresponding primed
  coordinate, and its coefficient map is fixed by being an algebra equivalence.
  The final `HasChartAtlas` on those mapped coefficients gives the same relations,
  invertible ordered determinants and principal-open cover after base change.
  There is no flatness or nontriviality hypothesis on R'. The additional universe
  v permits arbitrary larger rings; no small independent test universe is used.
- The last conclusion quantifies over EVERY field L and map `Spec L ⟶ S` and
  EVERY point x of the actual scheme pullback `pullback (π S n a) h`. It says
  `topologicalKrullDimAt x = 1`, the recorded dimension at a point, not the
  dimension of its local ring. Restricting to any of the resulting open charts
  gives the same dimension at a point (as explained in proof step 7). Empty
  fibres impose no pointwise conditions.

Dependency declarations read and reused:

- def-pc-scheme and def-weil-affine-spectrum: `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, `Spec` and `Spec.map`, Mathlib.AlgebraicGeometry.Scheme.
- def-pc-proj: `AlgebraicGeometry.Proj`, `projIsoSpec` and
  `ProjectiveSpectrum.basicOpen`; the ratio helper uses the concrete Proj
  standard-open API from Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic.
- def-nagata-projective-space-base-change:
  `AlgebraicGeometry.ProjectiveSpace`,
  WeilConjectures.AlgebraicGeometry.ProjectiveSpace, with three homogeneous
  coordinates `ULift.{u} (Fin 3)` so the construction works in every base universe.
- def-pc-zero-scheme: `Scheme.Modules.Hom.zeroLocus`,
  WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus. Its ideal and subscheme
  constructions are used directly.
- def-pc-projective-space-twist: `ProjectiveSpace.twist`,
  WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist; the coordinate
  sections are the existing `ProjectiveSpace.coordinateSection` from
  WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection, and their
  tensor powers use `Scheme.Modules.tensorPowSectionOne` from
  WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators.
- def-sbc-smooth-morphisms: `SmoothOfRelativeDimension` in
  Mathlib.AlgebraicGeometry.Morphisms.Smooth (same node's recorded interface).
- def-kun-projective: `AlgebraicGeometry.IsHProjective`,
  WeilConjectures.AlgebraicGeometry.Morphisms.Projective.
- def-weil-pbc-standard-smooth-algebra:
  `Algebra.SubmersivePresentation`,
  Mathlib.RingTheory.Extension.Presentation.Submersive, publicly available from
  the recorded module Mathlib.RingTheory.Smooth.StandardSmooth.
- def-kun-dimension: `topologicalKrullDimAt`,
  WeilConjectures.Mathlib.Topology.KrullDimension.
- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs.

All recorded proof-dependency modules are imported, including the projective chart
statement and zero-locus pullback theorem. Mathlib proof interfaces are imported
through OpenImmersion, Localization.Defs, Extension.Presentation.Submersive,
Smooth.StandardSmoothCotangent, Morphisms.Basic, Morphisms.RingHomProperties,
Morphisms.Smooth, and Topology.KrullDimension. The statement docstring gives all
eight DAG proof steps and their dependency names.

One pre-existing proof attachment is not the advertised general theorem:
lem-pc-zero-scheme-properties is attached to
`exists_isEffectiveCartierCenter_hilbertPresheaf`, a specialized Picard theorem.
The local formula actually needed in proof step 1 is already available as
`Scheme.Modules.Hom.ideal_zeroLocus` in the canonical ZeroLocus module. This
proof-only attachment does not affect the present signature or require a second
definition; the recorded module is still imported as required. No statement
dependency has an unusable interface, and no dependency node is modified.

Edge cases checked before writing:

- n=1 gives a line; on each chart 1=s*(-nu^-1*lambda)+t*(-nu^-1*mu), so the
  principal-open cover and the stated determinants remain valid.
- n=0 is excluded exactly by the original positive-degree hypothesis.
- A characteristic dividing n is excluded exactly by hdegree, except on an empty
  base where the unit condition remains valid and the conclusion is vacuous.
- Empty base, empty chart, zero quotient ring, and zero base-change ring are all
  admitted; there is no Nontrivial ring assumption. The zero ring has no primes,
  so field-point dimension assertions on an empty chart are vacuous.
- No assumption that an individual coordinate is a unit on all of Q is made:
  it is inverted only in its own localization. No assumption that both coordinates
  are nonzero is imposed; their two principal opens cover by the unit constant term.
- No algebraic closedness, perfectness, or separability is required of L.
- The three-variable/two-relation order gives exactly the determinant in the node;
  the t-chart swaps the original coefficients together with the coordinates.

Searches for an existing statement (actual tools, 2026-10-24):

1. `msearch.py NM ... leanfinder "Diagonal projective plane hypersurface with unit
   coefficients and invertible degree is smooth of relative dimension one"`:
   8 hits, all Weierstrass projective equations/nonsingularity. None states the
   requested arbitrary-degree diagonal relative hypersurface or its explicit atlas.
2. `msearch.py NM ... loogle "Algebra.SubmersivePresentation,
   AlgebraicGeometry.SmoothOfRelativeDimension"`: 0 hits.
3. `msearch.py NM ... grep "Fermat|diagonal.*hypersurface|binomial.*smooth"`:
   25 hits, concerning number-theoretic Fermat results, not this statement.
4. `rg -n 'Fermat|fermat|diagonal.*[Hh]ypersurface|binomial'
   lean/WeilConjectures lean/Sheaf`: the relevant existing module is
   Sheaf.AlgebraicGeometry.RelativeFermatKummerCurve. Its equation is the special
   coefficient triple (1,-1,-1); its theorem concerns normalization, genus and the
   Kummer morphism, not this arbitrary unit-coefficient atlas. It cannot replace
   this node. Its existing tensor-power coordinate-section construction is reused
   conceptually, through the same upstream declarations, without importing this
   downstream consumer and creating a cycle.
5. `grep -rn 'lem-sfb-binomial-chart-smooth-relative-dimension'
   lean/WeilConjectures`: no hits.
6. `rg -n 'DiagonalPlaneCurve|HasChartAtlas' dag/lean_names_upstream.json
   lean/WeilConjectures lean/Sheaf`: no prior declarations or name conflicts.

Validation: prescribed scompile.py compiled the complete module cleanly in both
sandbox and library-module mode, with no errors or warnings. Every variable and
universe is explicit and autoImplicit is disabled. Every declaration has its
source and blueprint docstring; all lines have at most 100 characters.

No STATEMENT-DISPUTED flag: the original statement agrees with the unit-coefficient
Jacobian computation, and its small and degenerate cases are consistent.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
