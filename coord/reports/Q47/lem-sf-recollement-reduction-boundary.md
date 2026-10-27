## Worker report

Item: `lem-sf-recollement-reduction-boundary`, group Q47, stage 2.
Module: `Sheaf.Paper.SfRecollementReductionBoundary`.
Main declaration: `WeilConjectures.sfRecollementReductionBoundary`.
The companion `sfRecollementReductionBoundary_naturality` states the componentwise
naturality of the specified triangle comparison. Both theorem proofs are `sorry`.
The nine helper definitions contain actual functor compositions, adjunction maps,
composites of existing isomorphisms, and the existing triangle construction. No
operation, coefficient category, reduction, or comparison is selected anew.

Read sources: the complete DAG item and its seven statement-dependency statements
and Lean records; their recorded source signatures and docstrings; the additional
proof-dependency records and the all-stages recollement module. The source for this
item is the CURRENT `literature/blueprint/latest/blueprint/sec-six-functors/
sk-thm-sf-package/prop-functor-package.proof.md`, clause (3). That clause takes the
image of open-closed recollement under an exact functor. Also read the current
`lem-fix-operation-reduction.md` and its preservation of units/counits, and the
all-stages recollement statement and proof. The imported generic change-of-rings
interface includes independent site and coefficient universes; the small pro-etale
site is not replaced or identified with a same-universe site.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The fixed algebraic closure of a finite field is the existing
  `D : FiniteFieldDatum.{u}`. `D.p`, `D.a`, `D.q`, `D.k₀`, and `D.k` are exactly the
  global datum. `C : D.CoefficientDatum` supplies the prime `C.l`, its primality
  instance and `C.different : C.l ≠ D.p`. It also contains the common-stage
  coefficient closure required by the operation datum; it is not a restriction on
  the integral input.
- `E : Type u`, `[Field E]`, `[Algebra (Padic C.l) E]`, and
  `[FiniteDimensional (Padic C.l) E]` give the finite coefficient extension.
  The ring of integers, chosen uniformizer and quotient are the dependency's
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, and
  `coefficientExtensionRing`. They are reused through the operation and reduction
  APIs, with no extra valuation or uniformizer choice.
- The level in the theorem is `m : ℕ`, representing the positive exponent `m+1`.
  `m=0` is quotient exponent 1. Every positive exponent occurs. The unrelated
  positive `n, hn` index the given operation datum `S`; its integral normalization
  records operations and comparisons at EVERY `m+1`.
- `X : SixFunctorSpace D` is an object over `Spec D.k` with its
  `LocallyOfFiniteType` and `QuasiCompact` proofs. `[IsSeparated X.obj.hom]` is the
  required separation of X over k. `Z,U` use the same existing category, appropriate
  to a closed subscheme and complementary open of a finite-type scheme over a
  field. Such strata are finite type even if their names are arbitrary isomorphic
  presentations of the immersions.
- `i : Z ⟶ X`, `[IsClosedImmersion i.hom.left]`, `j : U ⟶ X`, and
  `hj : IsOpenImmersion j.hom.left` give the closed and open immersions over k.
  `_hij : Set.range j.hom.left.base = (Set.range i.hom.left.base)ᶜ` gives exactly
  complementarity. No nonempty, smooth, reduced, or finite-Tor condition appears.
- `S : SixFunctorOperationDatum D C E n hn` is the RECORDED small pro-etale
  operation datum, including its `higher.integral` operations and
  `integralNormalization.finiteLevels m` and `reduction m` comparisons. The
  finite operations here are the very finite levels to which the datum specifies
  its integral reduction comparisons, not separately supplied functors.
- `K : sfIntegralConstructibleCategory C.l E X.obj.left` is the recorded full
  subcategory: derived completeness, finite constructible positive reductions and
  a common cohomological interval. Its underlying ambient object is `K.obj`.
- `scalarReductionDerivedExtension C.l E X.obj.left m` is precisely derived tensor
  along the projection from the completed coefficient sheaf to the constant
  `(m+1)`-quotient sheaf. `sixFunctorIntegralReduction D C E m X` is the SAME
  reduction restricted to integral constructible inputs, with finite
  constructibility proved in the definition of that input category. There is no
  separately assumed finite-constructibility hypothesis on K_n.
- `sfReductionIntegralOpen S j hj` is `j*` followed by `j!` in the datum and then
  the existing integral ambient inclusion. `sfReductionIntegralClosed S i` is
  `i*` followed by `i_*` and that inclusion. These are A and C in the node proof.
- `sfReductionIntegralTriangle S i j hj K δ` has first arrow exactly the ambient
  image of `(S.higher.integral.openAdjunction j hj).counit.app K`, second arrow
  exactly the ambient image of
  `(S.higher.integral.pullDirectAdjunction i).unit.app K`, and third arrow the
  arbitrary ambient `δ` supplied in the theorem. `_hδ` is exactly distinguishedness
  of this triangle in `DerivedCategory (scalarReductionSource ...)`.
- `sfReductionFiniteOpen S j hj m` and `sfReductionFiniteClosed S i m` first apply
  that actual reduction to K and then the datum's finite operations and existing
  finite ambient inclusion. `sfReductionFiniteTriangle ... δn` has the finite open
  adjunction counit, closed adjunction unit, and arbitrary ambient connecting arrow
  `δn`; `_hδn` is its distinguishedness. This is the dependency's ordinary finite
  recollement definition in the datum's specified operation coordinates:
  `SixFunctorFiniteOperations.finiteOpenAdjunctionNormalization` identifies the
  two open functors and their counit with `exceptionalOpenAdjunction`, and
  `finiteDirectAdjunctionNormalization` identifies the closed functors and unit
  with `finiteRecollementDerivedAdjunction`. These actual natural adjunction
  comparisons, not merely object isomorphisms, make this equivalent to
  `FiniteOpenClosedRecollementTriangle`. There is no new private recollement
  definition or changed choice of finite counit/unit.
- `sfRecollementReductionOpenIso S j hj m K` is a_n. It composes the ambient
  inclusion of `((S.integralNormalization.reduction m).openExtension j hj).app`
  at the integral pullback of K with finite open extension applied to the
  specified pullback comparison
  `((...reduction m).directAdjunction j).left.app K`.
- `sfRecollementReductionClosedIso S i m K` is b_n. It composes the direct-image
  reduction comparison `((...reduction m).directAdjunction i).right.app` at the
  integral pullback with finite direct image applied to the same datum's closed
  pullback comparison `.left.app K`. Both are real `Iso` compositions; neither is
  an arbitrary comparison quantified as a hypothesis.
- `sfRecollementReducedTriangle ...` applies Mathlib's `Functor.mapTriangle` for
  the actual ambient reduction. Its `CommShift` is transported by
  `Functor.CommShift.ofIso (PurCompactSupport.finiteReductionIso ...) ℤ`. This is
  the existing canonical identification of the universal ringed-site derived
  quotient tensor with `scalarReductionDerivedExtension`, normalized by their
  scalar adjunctions. It is the same shift convention used by the existing
  `ConcreteIntegralProjection.reductionShift`; no new shift datum is assumed.
- The main conclusion supplies `e : r_n Δ_K ≅ Δ_Kn` in the actual category of
  triangles. Its `.hom.hom₁`, `.hom.hom₂`, and `.hom.hom₃` are explicitly a_n,
  the identity of the actual reduction K_n, and b_n. Since the target is
  distinguished and the triangles are isomorphic, this is an isomorphism of
  distinguished triangles, not only three vertex isomorphisms.
- The next conjunct is exactly the node's third square. Lean's `≫` is written in
  application order: `r_n.map δ ≫ s_n.hom.app A ≫ (shiftFunctor _ 1).map a_n.hom
  = b_n.hom ≫ δn`, which in the node's composition convention is
  `a_n[1] s_n r_n(δ_K) = δ_Kn b_n`.
- `sfRecollementReductionBoundary_naturality` quantifies over every integral
  constructible `K,L` and EVERY `f : K ⟶ L`. It states the naturality squares for
  a_n and b_n. The middle component is the identity natural transformation of
  the actual reduction functor. Triangle morphisms and their equalities are
  componentwise, so these two equations and identity naturality are exactly
  naturality of the triangle isomorphism when the source and target triangles
  use the functorial completions from the all-stages theorem. No restriction to
  isomorphisms, representative-complex maps, or a fixed coefficient lift occurs.
- Empty U, empty Z, and empty X are admitted: there is no `Nonempty` or
  nonzero-object assumption. The existing datum operations, natural
  comparisons, and arbitrary distinguished-boundary quantifiers remain defined.

Recorded dependency declarations reused:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; its public coefficient-construction
  module gives the integers, uniformizer and finite quotient rings.
- `Sheaf.Paper.SixFunctorOperationDatum`:
  `WeilConjectures.SixFunctorOperationDatum`, its `higher`, `integralNormalization`,
  and the recorded stage fields. Its public stages module provides
  `sixFunctorIntegralReduction`, `SixFunctorCoefficientComparison`, and the
  finite adjunction normalization fields used above.
- `Sheaf.Paper.SfIntegralConstructible`:
  `WeilConjectures.sfIntegralConstructible` and
  `sfIntegralConstructibleCategory`, reached through the operation datum.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `WeilConjectures.scalarReductionDerivedExtension`, reached through the recorded
  datum. The module's n-index is quotient exponent n+1, respected throughout.
- `Sheaf.AlgebraicGeometry.FiniteOpenClosedRecollement`:
  `AlgebraicGeometry.Scheme.finiteRecollementDerivedAdjunction` and
  `FiniteOpenClosedRecollementTriangle`, with the canonical finite counit and unit.
- `Sheaf.Paper.BasicOperationsCoefficientReduction`:
  `WeilConjectures.basicOperationsCoefficientReduction`, private proof import.
  Its actual normalized operation comparisons are already carried in the datum.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`: private proof import of
  the recorded dependency module; it publicly retains the ringed-site
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and the independent-coefficient
  derived-change-of-rings interface. We do NOT replace the sheaf category by
  its additional ordinary-ModuleCat specialization.
- `Sheaf.Paper.IntegralCompactSupportCoefficientComparison`:
  `WeilConjectures.PurCompactSupport.finiteReductionIso`, the existing canonical
  derived-tensor identification used for the shift structure, not a new tensor.
- `Sheaf.Paper.SfOpenClosedTriangleAllStages`: private proof import;
  `sfOpenClosedTriangle_finite`, `sfOpenClosedTriangle_integral_rational` and
  `SfRecollementConclusionOn` provide uniqueness and functoriality.
- Mathlib `CategoryTheory.Pretriangulated.Triangle`, `Triangle.mk`,
  `TriangleMorphism`, `Functor.mapTriangle`, `Functor.commShiftIso`, `distTriang`.
  The recorded triangle and triangulated-category Mathlib signatures and
  relevant docstrings were read in `Triangulated/Basic.lean` and the functor API.

Searches actually run with the prescribed `msearch.py Q47 <item>` wrapper:

1. LeanFinder: `Derived coefficient reduction preserves the open closed
   recollement triangle and its connecting morphism` — eight hits, headed by
   `DerivedCategory.triangleOfSESδ` and `triangleOfSESIso`; generic short-exact
   sequence triangles, no operation-specific reduction theorem.
2. Loogle: `CategoryTheory.Functor.map_distinguished` — four hits, including
   `map_distinguished` and `Triangulated.Octahedron.map`; generic exact-functor
   facts, no specified integral-to-finite recollement comparison.
3. Mathlib grep: `recollement|Recollement` — zero hits.
4. LeanSearch: `Coefficient reduction preserves the connecting morphism in an
   open closed recollement distinguished triangle` — eight generic short-exact
   sequence/mapping-cone/homology-boundary hits; no exact match.
5. Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, and the upstream
   declaration-name index, for `sfRecollementReduction`, `sfReductionIntegral`,
   `sfReductionFinite`, `sfRecollementReducedTriangle` — no existing declaration
   with any proposed name. Direct project search for recollement and reduction
   found the separate all-stages triangles and existing normalized operation
   reduction interfaces, which are reused. No declaration states this item.
6. Plain `grep -rn 'lem-sf-recollement-reduction-boundary'
   lean/WeilConjectures` — no upstream attachment or declaration.

Edge checks: quotient exponent 1 is m=0; every positive exponent is present;
K=0 and all zero maps are allowed; neither stratum nor X need be inhabited;
arbitrary distinguished completions are quantified, not one chosen boundary;
the comparisons have the direction reduction-of-operation to operation-of-reduction;
the tensor shift has direction r(A[1]) to (rA)[1]; the third-square equation uses
exactly those directions; both comparison naturality equations accept any f.
All universes are bound explicitly and use the existing small pro-etale site
(object level u+1, morphism level u), not an imposed universe equality.

No statement correction, disputed statement, new DAG node, or dependency repair.
The node copy changes only its `lean` field. The two postponed theorems are the
triangle/boundary clause and the naturality clause of this same DAG statement;
there are no postponed helper facts belonging to another node.

Validation: the prescribed scompile.py run compiled the single module separately
in sandbox and library modes with no errors or warnings. The mandated deliver2.py
dry run and delivery are run after writing this packet; their output is the final
validation and delivery receipt.

## Second reading by Q47

This is a separate self-review pass with the final node and file open. The
assignment explicitly prohibits starting other agents; independent review is
performed by the maintainer on the delivery, not claimed here as another worker's
review.

I checked every binder against the node: fixed finite-field/coefficient data are
in the existing datum; X is separated finite type; i and j are complementary
immersions; K is exactly the recorded integral full subcategory; both boundary
arrows are arbitrary with distinguishedness hypotheses. The first two arrows
are the actual datum adjunction counit/unit. Finite realization is normalized by
adjunction comparisons, so transporting a canonical finite recollement triangle
into those coordinates gives precisely the finite triangle used in the file.
There is no extra preservation assumption on K_n or finite-Tor requirement.

I expanded both comparison definitions: open extension uses `openExtension`
followed by finite j! of the pullback comparison; closed image uses
`directAdjunction.right` followed by finite i_* of `.left`. Their endpoints
match the ambient triangle endpoints definitionally. I read the existing
`finiteReductionIso` signature: it goes FROM `pbcDerivedExtend` TO the recorded
scalar reduction, so `CommShift.ofIso` transports the canonical tensor shift in
the correct direction. The equation is `r(δ) ≫ s ≫ a[1] = b ≫ δn`; the ordering
agrees exactly with the node. The isomorphism specifies all THREE components,
including identity in the middle, and naturality checks arbitrary morphisms.

Changes in this reading: the all-stages theorem import was made private because
it is a proof dependency; the finite recollement definition is imported publicly
for the statement's normalization interface. No mathematical correction was
needed. No data definition contains a sorry, no theorem is proved, no local
notation/instance/private helper is introduced, and all lines are at most 100
characters. Final recompile and delivery preflight must include this import change.
