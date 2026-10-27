## Worker report

The new module `Sheaf.RingTheory.CurveCofactorSmoothCriterion` states
`Algebra.AffineConormal.curve_cofactor_smooth_criterion`. Its only postponed proof
is this named theorem. All six helper definitions have real data and belong to
the explicit objects and conclusion clauses of this node. No new nodes,
dependency repairs, or statement corrections are needed.

Hypothesis and object correspondence:

- A commutative ring R is `(R : Type u) [CommRing R]`. An arbitrary natural
  codimension is `(c : ℕ)`, with no positivity restriction.
- The ordered equations are `f : Fin c → PolynomialRing R c`; the recorded
  `PolynomialRing R c` is `MvPolynomial (Fin (c + 1)) R`, `ideal f` is
  `Ideal.span (Set.range f)`, and `QuotientRing f` is its actual quotient.
- Ordered regularity is `_hr : RingTheory.Sequence.IsRegular
  (PolynomialRing R c) (List.ofFn f)`, retaining the dependency's nonzero-final-
  quotient convention. The empty sequence is allowed over a nonzero base.
- C, V and u are precisely the negative term, zero term and differential of
  `complex f`, from the recorded affine conormal realization. On the identity
  chart the same objects are their canonical scalar extensions along `AlgHom.id`.
  This is canonically the original complex, not another presentation.
- The structure `H : Chart f C κ (CommRingCat.of (QuotientRing f)) (AlgHom.id ...)`
  supplies the recorded canonical conormal and ambient bases and the canonical
  cokernel identification `H.omega` with `KaehlerDifferential R B`. Its basis
  and Jacobian fields state exactly the equation/coordinate differential
  normalizations. Here the binder `C : Coherence` is resolution infrastructure,
  not the conormal module denoted C in the prose; `κ` is the recorded comparison.
  The derived-category instance is likewise the dependency's size infrastructure.
  These impose no new ring-theoretic hypotheses: the dependency theorem
  `exists_affineConormalJacobianRealization` provides these charts for every
  regular sequence, including the identity chart. The theorem works for every
  such canonical realization, rather than choosing unrelated maps.
- `H.w` is the dependency's differential-valued cofactor map, not a newly
  postulated linear map. `H.cofactor.formula` fixes its basis-free wedge value;
  the recorded finite bases recover the displayed dual-basis formula.
- D(E) is `(chartComplex f ...).cofactorLine c`, i.e. the dual of the c-th
  exterior power tensored with the (c+1)-th exterior power, in that order.
- Flatness is `[Module.Flat R (QuotientRing f)]`. This is exactly the recorded
  `RingHom.Flat (algebraMap R B)`, via `RingHom.flat_algebraMap_iff`.
- `_hfib` quantifies over every base point and every irreducible component Z
  of `curveGeometricFibre f y`, with `topologicalKrullDim Z = 1`. The helper is
  literally the pullback of Spec B along Spec of the algebraic closure of the
  residue field, followed by `fromSpecResidueField`. This uses the recorded
  geometric-fibre pullback and dimension; it does not use total dimension as
  a substitute for purity. Empty fibres have no irreducible components.

Conclusion correspondence:

- Every prime is `p : PrimeSpectrum (QuotientRing f)`.
- The stalk map is `H.w.baseChange (Localization.AtPrime p.asIdeal)`. Tensor
  scalar extension to B_p is canonical module localization. `Function.Bijective`
  is exactly invertibility of this linear map; `Function.Surjective` is its
  surjectivity. The first conjunction is their equivalence.
- `curveJacobianMinor f s` is the polynomial determinant with equation rows
  and the selected variable columns. `s : Fin c ↪ Fin (c + 1)` lists c distinct
  selected columns, in any order. Taking its quotient image and then its
  algebra-map image in B_p, `IsUnit` gives the third condition. The next two
  equivalences connect this condition to surjectivity and `IsSmoothAtPrime R p`.
- `Algebra.IsSmoothAtPrime` means there is a principal open containing p whose
  algebra is smooth over R. For a polynomial quotient this is equivalent to
  smoothness of Spec B → Spec R at p, by the recorded affine comparison and
  locality/restriction of smoothness. The existing landed definition node
  `def-weil-pbc-singular-ideal` is added to stmt_deps solely to cite this
  declaration; the original dependencies and statement are preserved.
- The second main conjunction handles every selected minor avoiding every prime.
  Its `P : Algebra.SubmersivePresentation R (Localization.Away ...) ...` is
  a presentation of B_h itself. The field `P.relation = curveLocalizationEquations
  f s` fixes all original equations renamed into the enlarged polynomial ring,
  followed by `X_z * h - 1`. A Mathlib presentation includes surjective generation
  and exact equality of the relation ideal and the evaluation kernel, so this
  states the specified quotient presentation, not merely an abstract isomorphism.
- `P.val j.castSucc` is the image of the old variable; the last generator is
  the canonical `IsLocalization.Away.invSelf` of the minor. The selected-variable
  map is `curveLocalizationColumns s`, namely the selected old variables followed
  by z. The sole remaining old variable is unselected. This encodes the stated
  reordering without changing the polynomial indexing type.
- `P.jacobian = (...) ^ 2` is exactly the displayed determinant h-bar squared.
  `SubmersivePresentation.jacobian_isUnit` supplies its invertibility, and the
  explicit final `IsStandardSmooth R (Localization.Away ...)` gives standard
  smoothness in the recorded definition. No arbitrary localization map is used.
- The third main conjunction quantifies over all affine open immersions
  `Spec A → Spec B`, their canonical chart realizations H', and `Smooth R A`.
  Thus these charts form a basis of every smooth open, including nonprincipal
  ones. The algebraic smoothness condition is scheme smoothness on that chart.
- `H'.CurveSmoothSplitting` spells out injectivity of u, surjectivity of the
  canonical quotient projection, equality `ker projection = range u`, a left
  inverse of u and a section of the projection. The projection is defined from
  the dependency's `H'.omega` and the actual cokernel quotient map. Local
  splitting on a smooth open gives these global affine splittings because
  the finite locally free quotient is projective; this is the equivalent
  affine-module formulation, not an additional smoothness assumption.
- The line property is the explicit linear equivalence between
  `A_p ⊗[A] Ω[A/R]` and `A_p` at every prime. Since Ω is finitely presented,
  these local rank-one conditions give exactly a line bundle. There is no
  incorrect demand that the line be globally free on an arbitrary affine open.
- The existential linear equivalence `e : D(E) ≃ₗ[A] Ω[A/R]` satisfies
  `e.toLinearMap.comp H'.w = LinearMap.id`. Its equation on every conormal
  basis b and every lifted ambient differential v specifies the inverse of
  the relation-first determinant comparison. The sign is +1, with no omitted
  sign convention or freely chosen isomorphism.
- The last clause of `CurveSmoothSplitting` takes every conormal basis b,
  differential basis a indexed by `Fin 1`, and lift v of `a 0`, and asserts
  that their relation-first concatenation is an ambient basis d. The displayed
  top-wedge equality gives `H'.w (a 0)` in that exact basis. This states the
  equivalent basis-and-wedge clause on every open admitting those bases.
- The final main conjunction treats `c = 0` explicitly: every empty selected
  minor is 1 and the coordinate differential maps to the canonical dual-empty-
  wedge tensor the ambient top wedge. The preceding explicit chart specializes
  to z-1 with Jacobian 1; the projection and line statements then recover
  B = R[x_0] and w = id.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`, with
  the affine ring-hom property; `SmoothOfRelativeDimension` was also inspected.
- `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic`: `ExteriorAlgebra`, `exteriorPower`,
  `ExteriorAlgebra.ιMulti`; `topDual` and `cofactorLine` reuse these constructions.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, `flat_algebraMap_iff`;
  `Mathlib.RingTheory.Flat.Basic`: `Module.Flat`.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `D`,
  `linearMapEquivDerivation`.
- `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular`.
- `Mathlib.RingTheory.Smooth.StandardSmooth`: `Algebra.IsStandardSmooth`;
  `Mathlib.RingTheory.Extension.Presentation.Submersive`:
  `Algebra.SubmersivePresentation`, including relation and generator fields,
  selected-column map, Jacobian and unit-Jacobian field.
- `Sheaf.RingTheory.AffineConormalJacobianRealization`:
  `Algebra.AffineConormal.PolynomialRing`, `ideal`, `QuotientRing`, `complex`,
  `chartComplex`, `Chart`, `Chart.w`, and
  `exists_affineConormalJacobianRealization`. Signatures, full Chart data,
  formula and existence docstrings were read.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `WeilConjectures.RingTheory.SingularIdeal`: `Algebra.IsSmoothAtPrime`.

Proof dependencies are imported as ordinary (nonpublic) imports when not
already present as a public statement dependency: `Matrix.adjugate_mul` and
`mul_adjugate` from `Mathlib.LinearAlgebra.Matrix.Adjugate`;
`Algebra.instSmoothOfIsStandardSmooth` from
`Mathlib.RingTheory.Smooth.StandardSmoothCotangent`;
`Algebra.smooth_localization_conormal_split` from
`WeilConjectures.RingTheory.SmoothLocalizationConormalSplit`;
`Matrix.scalar_left_inverse_maximal_minors` from
`WeilConjectures.LinearAlgebra.Matrix.LeftInverseMinors`. The affine comparison
and smooth restriction proof dependencies are already present through the
public smooth-morphism import. The six proof steps are in the theorem docstring.

Edge cases checked before writing: c=0, including the empty determinant and
z-1 chart; zero base/quotient versus the nonzero quotient required by the
regular-sequence dependency; empty geometric fibres and empty smooth opens;
arbitrary characteristic, in particular characteristic 2; a nonsmooth node
xy=0 (the two cofactors lie in the node's maximal ideal); a smooth graph
x_1-x_0^2 (a derivative is 1); all selected-column permutations (the minor
may change sign but its square and unit condition do not). At a zero-ring
open the zero modules have the appropriate finite-index bases and there are
no primes. No nonempty-fibre assumption or extraneous characteristic is added.
No STATEMENT-DISPUTED issue was found.

Searches (prescribed msearch wrapper, group Q23 and this item):

- leanfinder: `cofactor map Kahler differentials smooth primes` returned 8
  hits, including `Algebra.IsStandardSmooth.of_basis_kaehlerDifferential`,
  `free_kaehlerDifferential`, and Kähler universal-property results; none
  states the cofactor criterion or the full normalization and chart clauses.
- An earlier leanfinder query used the full natural-language statement,
  `For a polynomial complete intersection curve the cofactor map on Kahler
  differentials is an isomorphism precisely at the smooth primes`.
  It likewise returned standard-smooth and Kähler results, not this statement.
- loogle: `"Algebra.Smooth", "KaehlerDifferential"` returned 0 hits.
- grep, Mathlib/RingTheory: `cofactor.*smooth|smooth.*cofactor` returned 0 hits.
  The broader `cofactor.*smooth|smooth.*cofactor|isUnit.*jacobian` was also run.
- rg on `lean/WeilConjectures` and `lean/Sheaf`: cofactor/smooth and Jacobian
  searches found the recorded affine realization, two-term cofactor naturality,
  lci fundamental-class consumer and existing Jacobian criterion for relative
  global complete intersections. The latter detects smoothness by minors but
  does not state this cofactor map, inverse normalization or all clauses here.
  Its source was read in full. No complete existing declaration was found.
- Search for this node id in `lean/WeilConjectures` returned none. The current
  blueprint unit `latest/.../sk-thm-sf-ctf-stability/_section.md` and Stacks
  duality.tex (0E9Y/0E9Z) and algebra.tex (00T8) were read. There is no repair
  note for this item. The withdrawn CompactObject example has no declarations;
  its node record and the current affine-conormal module supplied the format.

Validation: prescribed `scompile.py` compiled the exact module in sandbox and
library naming modes, cleanly (4.5s and 5.0s). The file has no line over 100
characters, uses explicit universes and binders with autoImplicit disabled,
and leaves only the expected main theorem sorry. Delivery preflight follows.

## Second reading by Q23

The dispatcher explicitly prohibits starting another agent and assigns the
maintainer's independent review to the delivery. Accordingly this is an honest
separate reread by the assigned worker, not a claim of an independent reviewer.
I reopened the node, the Lean statement, and the recorded dependency signatures.
The correspondence above enumerates every hypothesis and conclusion clause.
In particular I checked the dual-first tensor order, relation-first wedge order,
selected column order including z, the square rather than h for the enlarged
Jacobian, purity of every component rather than total dimension, arbitrary
smooth affine opens, both splittings, the rank-one assertion, and the empty
sequence identity. There was no statement change. The only graph change adds
the already-landed singular-ideal node to name its exact smooth-at-prime
predicate. Independent review is to be performed by the maintainer as the brief
specifies; no second-reader identity is fabricated.
