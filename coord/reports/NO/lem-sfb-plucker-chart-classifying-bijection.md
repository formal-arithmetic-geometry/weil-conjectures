## Worker report

The module `Sheaf.AlgebraicGeometry.PluckerChartClassifyingBijection` states
`AlgebraicGeometry.Plucker.chart_classifying_bijection`. It gives the unique
scheme-theoretic factorization of the determinant quotient-line map, its exact
pivot-chart formulas, the quotient-preserving comparison, both inverse identities,
equivalence invariance, naturality, and the labeled determinant-line identification.
The natural bijection is expressed by the universal-element characterization
`∃! b, Classifies qX q b` together with its inverse and naturality clauses, rather
than by introducing a second quotient-class/setoid implementation.

Only this node's `lean` field changes. No statement correction, dependency repair,
or new independent notion/node is needed. All setup helpers belong to this node's
explicit coordinate and classifying-map notation, and are listed in
`lean.declarations`. Every definition has real data. Both the main theorem and
`largeQuotientMap_surjective` have `sorry` proofs, with their source and complete
proof instructions in their docstrings. The latter is the surjectivity of the
actual B → B/H map already specified in the node, after the canonical size transport;
it is not an assumed map or a new independent prerequisite.

### Size transport and exact objects

The recorded determinant presentation has `CoordinateRing N r : Type` and its
Proj lives in `Scheme.{0}`. Scheme morphisms and the recorded tensor pullback
require source and target in one universe. Restricting all test schemes to
universe zero would silently specialize the node. Instead `largePolynomialGrade`
and `largeGrade` are the actual `Submodule.baseChange` of the recorded components
along `ℤ → ULift.{u} ℤ`. Mathlib's `GradedAlgebra.baseChange` supplies the grading.
This scalar extension is along the canonical ring isomorphism, so its rings are
canonically isomorphic to the original rings, with exactly the original ideal
and grading; it introduces no flatness assumption, saturation, radical, or
new determinant equation. The target is now in `Scheme.{u}` for arbitrary `u`.

`largeQuotientMap` is the actual tensor extension of `Ideal.Quotient.mkₐ`, via
`GradedAlgHom.liftEquiv`. `largeImmersion` is `Proj.map` of that map, using its
surjectivity. `largeInclusion` sends a coordinate to `1 ⊗` that coordinate.
`largeRatio` applies `HomogeneousLocalization.Away.map` to the existing `fraction`.
Thus all ordered signs and repeated-index zeros come from the existing
`orderedCoordinate`; no minor coordinate has been independently redefined.

The theorem's final clause includes a section-preserving isomorphism κ between
this polynomial Proj model and the recorded
`ProjectiveSpace (ULift (Index N r)) (Spec (ULift ℤ))`, and a section-preserving
comparison of `Proj.twist` with **the recorded `ProjectiveSpace.twist`**. The final
isomorphism uses the latter, pulled back along `largeImmersion ≫ κ.hom`.
This comparison specifies each labeled coordinate, so it cannot absorb an
arbitrary projective automorphism. No noncanonical comparison is chosen in a
definition. This is a change of presentation and universe, not a change to the
mathematical statement.

### Hypotheses and clauses

- Integers `0 < rank < N`: natural `N r`, with positive rank written `r + 1`
  and `_hrN : r + 1 < N`. This parametrizes every positive integer rank exactly
  once. Column labels `Fin N` shift the paper's labels 1,...,N by one.
- Increasing rank-subsets: the dependency's `PluckerDeterminantLocus.Index N r`
  and increasing enumeration `columns`. No new indexing convention or subsets.
- B, ordered p, C, F, H, A and X: the dependency's `PolynomialRing`,
  `orderedCoordinate`, `replacementMatrix`, `relation`, `relationsIdeal`,
  `CoordinateRing`, and `quotientGrade`, with only the canonical scalar
  extension just explained. `largeChart I` is exactly `D₊(1 ⊗ p_I)`.
- Normalized matrix: `largeMatrixOn I W hI` restricts the image of each recorded
  single-column replacement fraction; in particular it includes the identity
  pivot columns. It does not use an arbitrary matrix or an abstract coordinate.
- j induced by B → A: `largeImmersion`, and `largeImmersion ≫ κ.hom` when using
  the recorded projective-space target; κ and its line comparison preserve all
  p_J labels.
- Any universal quotient: explicit binders `QX`, `qX`, `_hqX : Epi qX`,
  `_hQX : QX.IsFiniteLocallyFreeOfRank (r + 1)`.
- Its local frames: `φX I` is an actual module-sheaf isomorphism on `largeChart I`.
  `_hφX` is equality of its quotient matrix with the recorded normalized matrix.
  `_hchange` specifies on every common subopen the exact inverse K-column
  matrix. These are precisely the supplied local-frame assumptions; no
  classification property is assumed.
- Arbitrary test scheme and quotient: `T : Scheme.{u}`, `Q : T.Modules`,
  `q : SheafOfModules.free ... (ULift.{u} (Fin N)) ⟶ Q`, followed by `Epi q`
  and `Q.IsFiniteLocallyFreeOfRank (r + 1)`. There are no affine, nonempty,
  quasi-compact, reduced, or base-field restrictions.
- L and s_J: the existing `exteriorSheaf Q (r + 1)` and helper `quotientWedge q J`.
  The helper applies existing `exteriorSheafSection` to the actual global
  generator images `freeHomEquiv Q q (ULift.up (columns J a))` in their given
  order. This is sheafified exterior power, not merely exterior powers of
  global sections or an unspecified line.
- L invertible: `(exteriorSheaf Q (r + 1)).IsInvertible`.
- Generation by the s_J: `∀ t, ∃ J, t ∈ nonvanishingLocus ... (quotientWedge q J)`.
  For an invertible sheaf this is exactly fibrewise generation by the named
  sections, including empty schemes.
- Corresponding quotient-line map: `∃! a ...` with `DeterminantClassifies q a`.
  The latter is an actual tensor-pullback isomorphism taking every coordinate
  section to `quotientWedge q J`. The separate `∀ a', DeterminantClassifies ... →
  a' = a` states uniqueness of the projective universal pair alone, independently
  of the later factorization assertions.
- Scheme-theoretic unique factorization: `∃! b, b ≫ largeImmersion N r = a`.
  These are equalities of scheme morphisms, not just topological factorizations.
- Chart clauses: `ClassifyingChartFormula q b` first identifies the inverse
  image of `largeChart I` with the dependency's intrinsic `pivotLocus q I`.
  For every smaller open V and **every** local frame φ, it asserts the pivot
  determinant is a unit, the exact maximal-minor ratio formula, and the exact
  normalized single-replacement-entry formula. `Ring.inverse` appears only for
  this asserted unit determinant; no division by arbitrary elements is used.
  These formulas are given on all framed subopens of the pivot locus, which is
  precisely how the node's phrase 'in any local frame' is interpreted.
- Quotient-preserving isomorphism: `Classifies qX q b` gives an actual
  `(tensorPullback b).obj QX ≅ Q` preserving every labeled standard generator
  via the section-normalized tensor-pullback unit. The free-sheaf universal
  property makes this equivalent to the full quotient-map commuting square.
- Unique classification: the second main conjunct is `∃! b, Classifies qX q b`
  for every admissible quotient, making independence of auxiliary frames explicit.
- Converse `b_(b* qX) = b`: the third conjunct constructs a quotient p whose
  generator images are the canonical pullbacks, asserts `Epi p` and the pulled
  module's rank, and states `Classifies qX p c ↔ c = b` for every c.
- Equivalent quotients: the fourth conjunct assumes an actual `e : Q ≅ Q'`
  with `q ≫ e.hom = q'` and gives equality of any two classifying maps.
- Naturality: the fifth conjunct quantifies over arbitrary `T'`, `f : T' ⟶ T`
  and the canonically pulled-back generator map p. It asserts admissibility,
  `Classifies qX p (f ≫ b)`, and equality of every classifying c with `f ≫ b`.
  Such p is uniquely determined by its displayed generator images and is
  constructed by `Sigma.desc` and `homOfGlobalSection`; it is not arbitrary
  comparison data. The preceding inverse clause explicitly gives its existence
  when pulling back the universal quotient.
- Mutually inverse natural bijections on quotient isomorphism classes follow
  exactly from existence/uniqueness, the converse, equivalence invariance and
  naturality above. This is the same universal-element formulation already used
  in the project's free-quotient Grassmannian statement, without importing that
  downstream theorem or creating an import/dependency cycle.
- Final determinant-line identification: the last conjunct gives an actual iso
  from the tensor pullback of **`ProjectiveSpace.twist ... 1`** along the induced
  projective map to `exteriorSheaf QX (r + 1)`. Each
  `ProjectiveSpace.twistOneSection ... (ULift.up J)` maps to
  `quotientWedge qX J`. Both the line and every section are identified.

### Dependency declarations and proof plan

Read all statement-dependency records and the signatures/docstrings in their
source modules, including the full two Plücker modules. The statements use:

- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, through the recorded
  presentation; its grading is `MvPolynomial.homogeneousSubmodule`.
- `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`: `Matrix.det`.
- `Mathlib.Algebra.Algebra.Hom` and `Mathlib.RingTheory.Ideal.Quotient.Operations`
  (and its imported quotient API): `AlgHom`, `Ideal.Quotient.mkₐ`, quotient algebra.
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme` and `.Basic`:
  `AlgebraicGeometry.Proj`, `Proj.basicOpen`, `Proj.awayToSection`;
  the node's `projIsoSpec` is its canonical basic-open affine description.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, scheme morphisms.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, transparently
  the underlying `SheafOfModules` category specialized here by `Scheme.Modules`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `tensorPullback`, `tensorPullbackSectionAdjunction` and its actual section unit.
- `Sheaf.AlgebraicGeometry.PluckerDeterminantLocusCharts`: the listed coordinate
  declarations and `closedImmersion_and_charts`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`
  for the already established quotient Proj embedding.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `ProjectiveSpace`.
- `Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf`:
  `exteriorSheaf`, `exteriorSheafSection`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`:
  `ProjectiveSpace.twist`, `ProjectiveSpace.twistOneSection`.
- `Sheaf.AlgebraicGeometry.PluckerChartQuotientGluing`: `quotientMatrix`,
  `frameChange`, `pivotLocus`, and the theorem `chart_quotient_gluing` for the
  proof. The supplied frames are exactly those used by this interface.

Public imports expose statement dependencies. Plain imports supply the recorded
proof plan: exterior free comparison/basis; adjugate/Cramer identities; affine
morphism correspondence and morphism gluing; projective-space universal pairs;
sections-to-Proj polynomial construction; quotient-twist comparison; twisting
charts; and module-sheaf gluing. The main docstring follows all nine node steps,
including unique scheme factorization and labeled section preservation.

### Edge cases

Rank one is `r = 0`: the relation exponent is zero and determinant is a 1×1
minor, giving the usual projective quotient-line case. Ranks `N-1` are included.
Rank zero, rank N, and N=0 are excluded by the node's strict rank inequalities,
not by additional Lean restrictions. Arbitrary empty and nonaffine test schemes,
empty pivot charts, arbitrary characteristic, nilpotents and zero divisors remain
allowed. Ratios only occur where the relevant determinant is a unit. Repeated
indices in a replacement wedge use the recorded zero coordinate. The statement
has no separate, potentially smaller test-scheme universe and no equality of
unrelated universes. Every variable and universe is explicitly bound, with
both auto-implicit options disabled. No local notation or local instances occur.

### Searches and verification

Searches were run with the prescribed `msearch.py NO
lem-sfb-plucker-chart-classifying-bijection` wrapper and are in `searches.jsonl`:

- LeanFinder query: `Normalized quotient matrix charts classify locally free
  quotient sheaves Grassmannian Plucker determinant line`. Eight hits, including
  `Module.Grassmannian`, `Module.Grassmannian.mk.inj`,
  `Module.Grassmannian.projective_quotient`, `Module.Grassmannian.rankAtStalk_eq`,
  `Module.isOpen_freeLocus`, and free sheaf generator/presentation APIs.
  None states this classification by the fixed determinant Proj and its line.
- Loogle query: `"Grassmannian", "functor"`. Three hits:
  `Module.Grassmannian.functor`, `.functor_obj`, `.functor_map`, the ring/module
  Grassmannian rather than the specified scheme/quotient-sheaf result.
- Mathlib grep query: `Grassmannian|[Pp]lucker`, subdirectory `RingTheory`.
  Five hits, all in `Mathlib/RingTheory/Grassmannian.lean`; no matching theorem.
- LeanSearch query: `Locally free quotients classified by normalized Plucker
  charts with determinant line bundle`. Eight hits, principally module
  Grassmannians, projectivization and localization of quotient modules; no match.
- `rg` of Plücker/Grassmann/classifying terms in both live source trees found
  the two usable Plücker dependencies and the downstream
  `FreeQuotientGrassmannProjective`. The downstream theorem describes existence
  of an unspecified representative and uses this item in its DAG proof, so it
  is not an exact existing declaration for this fixed-Proj classification.
- Search for this node ID in `lean/WeilConjectures` found no declaration.
  Search of every newly introduced name in Mathlib, upstream, Sheaf and
  `dag/lean_names_upstream.json` found no declaration at its full name in
  `AlgebraicGeometry.Plucker`. Unrelated namespaces have their own `Classifies`.
- Read the local primary sources `literature/stacks-project/constructions.tex`,
  labels `lemma-gkn-representable` (089T) and `lemma-projective-space` (01NE).
  The first supplies normalized quotients on arbitrary schemes and their pivot
  subfunctors; the second supplies invertible modules with labeled generators.
- `scompile.py` compiled the complete module cleanly in both sandbox and library
  modes; the final completed check took 24.8 s / 24.3 s. Expected `sorry` warnings
  are permitted; no other warning or error remained.

No STATEMENT-DISPUTED issue remains. The mathematical node text is unchanged.

## Second reading by NO

The delivered section was the worker's own self-check: it said that the dispatcher did not
allow a separate agent. The maintainer's independent reviewer wrote this reading on 2026-10-24.
It replaces that section and leaves the Worker report unchanged. The delivered Lean module and
the node record are not changed.

Node clauses and the Lean that renders each one
(`AlgebraicGeometry.Plucker.chart_classifying_bijection`):

1. Integers 0 < r < N: positive rank written `r + 1`, `_hrN : r + 1 < N`. Same as the
   two Plücker dependencies. OK.
2. Increasing r-subsets, B, ordered p, C, F, H, A = B/H, X = Proj A, U_I = D₊(p_I): the recorded
   `Index N r` (`Finset (Fin N)` of card r+1), `columns`, `orderedCoordinate` (incidence-matrix
   determinant: sorting sign, zero on repeats), `relationsIdeal`, `quotientGrade`. These are
   scalar-extended along the ring isomorphism ℤ → ULift.{u} ℤ (`largePolynomialGrade`,
   `largeGrade`, `GradedAlgebra.baseChange`). The recorded Proj is in `Scheme.{0}`, and scheme
   morphisms T ⟶ X need one universe. Without the extension every test scheme would be forced
   into universe 0 (H3). The extension changes no equation, ideal or grading. `largeChart I` is
   D₊(1 ⊗ p_I). OK.
3. M^(I) with identity pivot columns and entries x_aj = p_{i_1..j..i_r}/p_I:
   `largeMatrixOn I W h` is the image of the recorded `fraction I (update (columns I) a j)`.
   This is entrywise the recorded `normalizedMatrix`. The pivot columns give fraction 1, and the
   other columns of I give 0 because of the repeated index. OK.
4. j : X → P^{C(N,r)-1}_Z induced by B → A: `largeImmersion = Proj.map largeQuotientMap`.
   `largeQuotientMap` is the `GradedAlgHom.liftEquiv` of includeRight ∘ `Ideal.Quotient.mkₐ`.
   Its surjectivity, needed by `Proj.map`, is the named sorried theorem
   `largeQuotientMap_surjective` (H5-conform). The node writes the target as P_Z. The last
   conjunct identifies it with the recorded `ProjectiveSpace (ULift (Index N r))
   (Spec ULift ℤ)` by κ. κ is pinned by θ, which sends every `twistOneSection J` to
   `largeCoordinate J`. By the functor of points such a pair is unique, so κ is not arbitrary. OK.
5. q_X: a locally free rank-r quotient with frames on U_I, matrices M^(I) and frame changes
   ((M^(I))_K)^{-1}: `QX`, `qX`, `Epi qX`, `IsFiniteLocallyFreeOfRank (r+1)`, `φX`, `_hφX`,
   `_hchange`. `frameChange` has the convention of the landed `chart_quotient_gluing` clause
   `frameChange (φ I) (φ K) W hI hK = (pivot I K W hI)⁻¹`. Quantifying over all common
   subopens W is equivalent to the overlap statement, because restrictions are compatible. OK.
6. Arbitrary scheme T and a locally free rank-r quotient q, with no extra assumptions:
   `T : Scheme.{u}`, `Epi q`, `IsFiniteLocallyFreeOfRank (r+1)`. OK.
7. L = ∧^r Q and s_J the ordered wedges: the recorded `exteriorSheaf Q (r+1)` and
   `quotientWedge q J` = `exteriorSheafSection` of the global generator images in the order
   `columns J`. OK.
8. L is invertible and generated by the s_J: `IsInvertible` together with
   `∀ t, ∃ J, t ∈ nonvanishingLocus … (quotientWedge q J)`. For an invertible module, the germ
   lying outside m·stalk is exactly generation at t. OK.
9. The quotient-line morphism a_q: `∃! a, DeterminantClassifies q a ∧ …`. This uses a
   section-preserving tensor-pullback iso a^*O(1) ≅ L, and uniqueness is stated separately.
   OK.
10. a_q factors scheme-theoretically through a unique b_q: `∃! b, b ≫ largeImmersion = a`,
    an equality of scheme morphisms. OK.
11. Pivot-locus ring formulas: in `ClassifyingChartFormula`, b⁻¹(U_I) = `pivotLocus q I`.
    For every framed V ⊆ b⁻¹(U_I) and every frame: the pivot minor is a unit,
    b^*(p_J/p_I) = det M_J · det(M_I)^{-1}, and b^*x_aj = (M_I^{-1} M)_aj. This is the node's
    "in any local frame". On empty V the section ring is zero and every clause holds. OK.
12. Quotient-preserving b_q^* q_X ≅ q: `Classifies qX q b` (a pullback iso fixing every
    labeled generator, equivalent to the commuting square by the free universal property),
    together with `∃! b, Classifies qX q b`. OK.
13. b_{b^*q_X} = b: the third conjunct (pulled quotient p, its rank, Epi, and
    `Classifies qX p c ↔ c = b`). OK.
14. Equivalent quotients give the same b_q: the fourth conjunct. It omits admissibility
    hypotheses, but `Classifies` already makes q isomorphic to a pulled-back admissible
    quotient, so the clause is still true. OK.
15. b_{f^*q} = b_q ∘ f: the fifth conjunct, with the canonical generator map p. OK.
16. Mutually inverse natural bijections: they follow from 12–15. This is the same
    universal-element formulation as the landed project statements. OK.
17. j^*O(1) ≅ ∧^r Q_X carrying j^*p_J to the ordered wedge: `e` on the recorded
    `ProjectiveSpace.twist`, pulled back along `largeImmersion ≫ κ.hom`, with each
    `twistOneSection J` going to `quotientWedge qX J`. OK.

Edge cases: rank one (r = 0) and rank N−1 are included. Empty and non-affine T, empty pivot
opens, nilpotents and any characteristic are allowed. Universes: one universe u is used for T
and X, and it is arbitrary.

Searches: Mathlib has only module Grassmannians (`Module.Grassmannian`, with scheme
representability marked TODO). No `AlgebraicGeometry.Plucker` declaration of these names exists
in Sheaf or WeilConjectures. `Classifies` elsewhere lives in other namespaces. The downstream
`FreeQuotientGrassmannProjective` does not define these notions.

Mismatches: none in the Lean or the record. Only this section was rewritten (H11).
