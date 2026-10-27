## Worker report

The module `Sheaf.Paper.RelativeProfiniteTestLabels` states
`AlgebraicGeometry.ProEtale.relative_profinite_test_labels`, with one `sorry` and
no new definitions. The natural-language statement is unchanged. The theorem
simultaneously supplies the canonically normalized comparison isomorphisms `e`
and continuous labels `r` in universe `u`. Both are specified by actual existing
projections; neither is an unspecified comparison substituted for the named one.

Clause-by-clause correspondence:

- Compatible universes: explicit `universe u`, `Scheme.{u}` and `Profinite.{u}`;
  `set_option autoImplicit false` rules out undeclared variables. Test spaces and
  schemes share the smaller universe, with no nonemptiness restriction.
- Arbitrary scheme X: all scheme binders have no affineness, qcqs, flatness or
  etaleness assumption on X or on a base-change morphism f.
- The ring LC(S,Z) and its spectrum a(S): existing `LocallyConstant S ℤ` and
  `profiniteToScheme.obj S`; the latter is definitionally `Spec LC(S,Z)`.
- The inverse-limit test X[S]: existing `((profiniteToProEtOf X).obj S).left`,
  with structure map `.hom`; its finite-quotient-limit interpretation is supplied
  by `profinite_test_object_functor` and is not replaced by another model.
- Canonical isomorphism X[S] ≅ X × a(S): `e X S`, whose composites with both
  pullback projections equal the existing X[S] projections. These two equations
  uniquely determine the isomorphism. Thus the comparison is natural in X and S:
  applying either projection to either naturality square gives the same maps,
  and the pullback universal property makes the square commute. This renders the
  canonical natural comparison without introducing another independent choice.
- Evaluation-prime normalization of r: the next conjunct evaluates `r X S z`
  as the first coordinate of `LocallyConstant.homeomorphPrimeSpectrum.symm`
  applied to the actual absolute-test projection of z. Continuity is in its
  type `C(X[S],S)`. The dependency's homeomorphism has precisely the evaluation
  ideal formula, including the empty space and zero ring.
- Finite S, with its disjoint open summands: the finite conjunct supplies a
  colimit cofan `j : S → (X ⟶ X[S])`, over X. Its absolute projection is
  `toSpecZ X ≫ Spec.map` of evaluation at s, transported to `ULift ℤ` by the
  unique integer homomorphism. Thus j is the prescribed coproduct, not an
  arbitrary permutation of its summands. `r.comp (j s).base.hom = const X s`
  states the exact label on each summand. Scheme coproducts are disjoint open
  unions, as given by the recorded coproduct dependency.
- Continuous v:S→T: the next conjunct is the equality
  `r X T ∘ |X[v]| = v ∘ r X S`, using the actual upstream functor map.
- Arbitrary f:Y→X: b compares `pullback f X[S].hom` with Y[S]. Its inverse
  preserves the Y projection and the absolute-test projection. These determine
  the canonical isomorphism uniquely. The final equality in this conjunct is
  exactly `r X S ∘ |pr_X[S]| = r Y S` after this identification.
- Affine X-scheme U: `[IsAffine U]` and `uX : U ⟶ X`, with no constraint on uX.
  The `Over` Hom type enforces the X-morphism condition. `Function.Bijective`
  is applied to exactly `φ ↦ (r X S).comp φ.left.base.hom`.
- Naturality of this bijection in S: the next conjunct gives postcomposition
  by the actual `X[v]` on Hom and v on continuous maps.
- Naturality in affine U: the following conjunct allows arbitrary affine U,V
  and an `Over` morphism k, and gives precomposition by k on both sides.
- Component quotient: `ConnectedComponents U`, with its existing quotient
  topology, bundled using `Profinite.of`; `ConnectedComponents.mk` and
  `ConnectedComponents.continuous_coe` give the specified q_U. The component
  instances come from the existing spectral-component implementation, using
  affine compactness and quasi-separatedness, not extra hypotheses.
- The inverse at q_U: the last conjunct supplies φU over X with label q_U.
  Its uniqueness follows from the preceding bijection. For every continuous
  g:π₀(U)→S and every φ with label g q_U, it states the literal `Over`
  equality `φ = φU ≫ X[g]`, in Lean's composition order.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `AlgebraicGeometry.Spec` (also through its existing imports).
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.specZ`, `toSpecZ`, `profiniteToScheme`,
  `profiniteToProEt`, `profiniteToProEtOf`. Their actual implementation uses
  `Spec (ULift ℤ)` as the terminal scheme and the indicated pullback order.
- `Sheaf.Paper.ProfiniteTestObjectFunctor`:
  `AlgebraicGeometry.ProEtale.profinite_test_object_functor`, including its
  finite cofan, finite-quotient limit and Spec-Z comparison clauses.
- `WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant`:
  `LocallyConstant.homeomorphPrimeSpectrum`, `toPrimeSpectrum`,
  `homeomorphPrimeSpectrum_apply`, `mem_toPrimeSpectrum_asIdeal`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, and its universal property.
- `Sheaf.Topology.SpectralSpace.ConnectedComponentsProfinite`:
  `spectralSpace_connectedComponents_profinite`; its upstream proof implementation
  is exposed for the component topology instances by the public import of
  `WeilConjectures.Topology.SpectralSpace.ConnectedComponent`.
- `Mathlib.AlgebraicGeometry.Properties`, `.Morphisms.QuasiSeparated`:
  scheme prespectrality and affine compactness/quasi-separatedness.
  No dependency interface is replaced or weakened.

The other recorded proof inputs already lie in this import closure: scheme
coproducts and finite product spectra in `Mathlib.AlgebraicGeometry.Limits`, finite
extensivity, and the affine-ring correspondence. The upstream ring Hom equivalence
is private and is therefore cited only in the natural-language stage-3 proof plan;
no attempt is made to bind to an inaccessible private name.

Edge cases checked before writing: S empty (no finite summands; X[S] empty),
X empty, U empty (both Hom and continuous-map sets have one member), S empty with
nonempty U (both sets empty), singleton S (X[S] is X), finite multi-point S
(evaluation picks the stated summand, not a permutation), connected nonempty
U (constant labels), disconnected affine U and zero coordinate rings. Arbitrary
base-change f, identity maps, and arbitrary structure map U→X are all retained.
There is no assertion identifying arbitrary scheme fibre products with products
of their underlying topological spaces.

Searches executed:

- `msearch.py leanfinder`: "Relative profinite test schemes represent continuous
  maps from affine schemes to profinite sets with evaluation prime labels".
  Eight hits, on affine-space Hom and affine-transition limit constructions;
  none is the complete normalized relative-test statement.
- `msearch.py loogle`: `"profiniteToProEtOf", "homeomorphPrimeSpectrum"`;
  OK, zero hits.
- `msearch.py grep`: `profiniteToProEtOf|relativeProfinite|homeomorphPrimeSpectrum`;
  OK, zero Mathlib hits.
- `rg` in `lean/WeilConjectures` for this node's id: no hit. Concept/name searches
  found the existing Basic.lean test functor and private affine-ring equivalence.
- `rg` in `lean/Sheaf` for relative profinite labels found
  `TotallyDisconnectedCoefficientRealization.lean`, whose
  `continuousSetRelativeTestProjection` supplies the same label function but no
  theorem asserting the clauses here. This declaration is not duplicated:
  our theorem asserts existence with the literal same normalized formula.
  `ComponentRelativeProfiniteSite.lean` concerns a different relative site.

Sources opened: HRS Example 3.1, printed p.6; Bhatt--Scholze Lemmas 4.2.12--13
and their proofs, printed pp.30--31; current main-20261015 blueprint
`def-sfb-profinite-test-objects.md`. These agree with the existing node.

Validation: the prescribed scompile.py passed for both the sandbox and actual
module path (3.7 seconds and 5.7 seconds). The first pass exposed that `IsColimit`
is data rather than a proposition and that the component Hausdorff instance was
private to an import; these were repaired with `Nonempty (IsColimit ...)` and
explicit public imports of the existing topology/affine instances. All remaining
variables and universes are explicit and all lines are at most 100 characters.
No mathematical statement dispute, new node, dependency replacement, or statement
correction is needed.

## Second reading by Q47

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
