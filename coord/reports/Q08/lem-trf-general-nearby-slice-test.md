## Worker report

The delivery states `AlgebraicGeometry.OrientedNearbyCycles.general_nearby_slice_test`
in `Sheaf.Paper.GeneralNearbySliceTest`. Its only postponed theorem is the owning
DAG statement, with its complete four-step proof plan in its docstring. All helper
definitions have real data. There are no new axioms, hollow definitions, auxiliary
postponed theorems, private copies of a coefficient or derived category, or chosen cones.

I read the item and its proof, every original statement dependency and its recorded
interface, and the proof-dependency statements. I read the actual nearby-cycle,
strict-localization, evaluation and closed-lift sources, together with the relevant
Mathlib declarations. The recorded nearby-cycle module supplies no geometric slice
morphism or independent sliced comparison. Those are introduced as owning-node helpers:
they are precisely the diagrams, maps, slice isomorphism and cone condition introduced
in this item's text. They are not new independent mathematical notions needing new
nodes. In particular no general unstated theorem is assumed as a hypothesis.

I opened the author's Orgogozo PDF at the node's URL and read §1, §3.1, and the first
paragraph of Lemma 3.1.1 on printed p. 6:
https://www.cmls.polytechnique.fr/perso/orgogozo/articles/Modifications%20et%20cycles%20proches%20sur%20une%20base%20g%C3%A9n%C3%A9rale.pdf
The displayed comparison uses the entire generic strict localization and tests all
geometric pairs above a base-change morphism. The source's French degree convention
is inclusive, as the paper explicitly explains near the end of §1. The delivered
criterion therefore uses `q ≤ r`, with no shift or loss of a degree.

Hypotheses and clauses, matched individually:

- Schemes and finite type: `{X S : Scheme.{u}}`, `f : X ⟶ S`,
  `[LocallyOfFiniteType f] [QuasiCompact f]`, using the recorded conjunction.
- Finite commutative coefficients: `(Λ : Type v) [CommRing Λ] [Finite Λ]`.
  Scheme and coefficient universes are independent; `Coeff.{u,v}` is the existing
  canonical `ULift` of the coefficient ring to their common sheaf universe.
- Annihilating integer invertible on S: `(m : ℕ) (hm : 1 ≤ m)`,
  `hmΛ : ∀ x : Λ, m • x = 0`, `hmS : IsUnit (m : Γ(S, ⊤))`.
  Taking the positive absolute value of a nonzero integer gives this equivalent
  usual convention. The empty-base case also admits a positive annihilator since Λ
  is finite and its global-section ring is the zero ring.
- `K ∈ D^b(X_Et,Λ)`: the natural isomorphisms use
  `sliceBoundedInclusion X Λ`, the full subcategory of the existing
  `IsBounded (etaleDatum X) (Coeff Λ)` objects. Compatibility and cone detection
  quantify explicitly over every `K : EtaleDerived X Λ` with this boundedness.
  Thus boundedness is cohomological, not a chosen bounded representative.
- Geometric points a,b: `SliceSpecialization.A/B`, their `Field` and `IsAlgClosed`
  instances, and scheme morphisms `a/b`. This packages the recorded inline
  geometric-point convention; it does not redefine fields or geometric stalks.
- Specialization: `c : strictHenselizationScheme b ⟶ strictHenselizationScheme a`
  and `over`. `genericTube` is the pullback with the structural map from the
  *entire* strict localization of b. It is never the pullback with b itself.
- The three schemes: `fibre f = pullback f a`, `specialTube f` and `genericTube f`
  are exactly `X_a`, `X_(a)` and `X_(b)`. `i` and `j` are `pullback.map` using
  canonical evaluation at a and the specified specialization c, respectively.
- The geometric slice e: the theorem concludes the existence of a family `E` of
  actual `GeometricMorphism`s. It does not assume one. Every member satisfies
  `IsSpecializationSlice`: at every geometric x of `X_a`, its point functor on
  every oriented triple is naturally equivalent to the explicit pairs of lifts
  `(u,w)` at `(x,b,c)`. The condition includes naturality for *every* triple arrow,
  not just a bijection of stalk cardinalities. The lift to an étale V from `S_(a)`
  is characterized by its structural and geometric closed-point equations; strict
  henselian lifting makes it unique. No arbitrary natural transformation stands
  for the geometric specialization.
- Natural slice formula: `SliceFormula E f Λ d` is a natural isomorphism of
  functors on the bounded full subcategory between `RΨ_f` followed by the actual
  derived module inverse image of `E f d`, and `d.complex f Λ`. The latter is
  exactly restriction to `X_(b)`, `Rj_*`, then `i^*`. `sliceModules` uses the
  dependency's existing canonical constant-module lift; its exactness is inherited.
- Compatible specializations after arbitrary `g : T ⟶ S`: `SliceChange` allows
  independent geometric fields upstairs and downstairs, scheme maps of their
  spectra, and pointed strict-local maps. Its structural and evaluation equations
  specify the induced maps; the specialization square commutes. The six projection
  equations determine `fibreMap`, `specialMap` and `genericMap` uniquely as the
  corresponding fibre-product maps. The i/j commutations record the same diagram.
  These are data describing compatibility, not additional finiteness hypotheses.
- Identification of comparisons: `ordinarySliceComparison` is defined *before*
  `SliceFormula` and independently of it: apply the canonical inverse-image
  composition square, transpose the `j` counit under the `j_T` adjunction, then
  identify restriction of K with restriction of `K_T`. In
  `GeneralNearbySliceStatement`, the two composites from
  `e_T^* v^* RΨ_f K` to the sliced target are required equal. The left side uses
  this independently defined ordinary arrow; the right side uses precisely the
  recorded `baseChange`, the counit mate. The source identification `sliceSquare`
  is the existing generator-normalized `derivedSquare` of the compatible geometric
  square. The statement asserts a geometric comparison isomorphism γ; it does not
  allow an arbitrary derived arrow as a comparison. The boundedness witness for
  `K_T` is a conclusion of this clause, not an added assumption.
- Cone criterion: `sliceConeVanishing` quantifies over all distinguished triangles
  with the specified first arrow. The standard cohomology predicate is
  `∀ q : ℤ, q ≤ r → IsZero ((DerivedCategory.homologyFunctor _ q).obj C)`.
  The iff uses the ordinary comparison on `V_(f_T)` on the left and the independently
  defined ordinary sliced arrow on the right. On the right **both d over S and d'
  over T vary**, with every compatible `SliceChange`. Every specialization of T
  occurs by taking its image in S. A fixed d is not substituted for this quantifier.
  Expressing all distinguished cones avoids a functorial cone choice and is
  equivalent to the vanishing of any cone of the given map.
- Arbitrary preliminary base change: the theorem's final `∀ (U : Scheme.{u})
  (a : U ⟶ S)` asserts the same statement for `pullback.snd f a`. Its predicate
  then quantifies over every subsequent scheme base change, every bounded input,
  and every integer r. In particular it includes the pulled-back original input;
  no condition on U or T is added. The family of geometric slices is common to
  the original and base-changed assertions.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` and the
  existing base-change instances; `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `QuasiCompact` and its base-change instances.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; standard cohomology and distinguished triangles from the
  imported Mathlib derived-category interface.
- `Sheaf.Paper.OrientedNearbyCycles`: `EtaleSite`, `etaleTopology`,
  `VanishingSite`, `vanishingTopology`, `VanishingTopos`, `etaleDatum`,
  `vanishingDatum`, `Coeff`, `EtaleDerived`, `IsBounded`, `moduleMorphism`,
  `etaleModules`, `nearbyCycles`, `squareDirect`, `squareMorphism`, `squareModules`,
  and `baseChange` with their actual signatures and counit convention.
- `Sheaf.Paper.CompletionMateComparison`: existing `Site`, `Morphism.pull/push/adj`
  and generator-normalized `derivedSquare`; these are already public imports of
  the nearby-cycle interface.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the recorded geometric
  point convention is the field and `Spec Ω ⟶ S` binders. I also read the recorded
  `Scheme.SpecToEquivOfField` signature in `ResidueField.lean`.
- `Sheaf.AlgebraicGeometry.StrictHenselization`: `strictHenselizationScheme` from
  the node's recorded construction. The imported closed-lift module reexports it.
- The already landed evaluation, structural-map and functoriality nodes supply
  `Scheme.strictHenselizationPointEvaluation`,
  `Scheme.strictHenselizationStructuralMap` and
  `Scheme.strictHenselizationClosedLift_over`. Their IDs are added to `stmt_deps`
  under the standing permission to cite already landed nodes. No existing node's
  record is changed. The structural-map wrapper imports its current upstream owner.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its
  two projections and `pullback.map`, always in the scheme category.
- `Scheme.pointSmallEtale` and `GrothendieckTopology.Point.presheafFiber` give
  the actual stalk colimit used in the oriented-point normalization.
- Proof-only imports retain the recorded Mathlib exact-functor derived and
  cohomology interfaces. `lem-trf-nearby-specialization-slice` currently has no
  Lean record or published module (confirmed by `scompile.py --source
  Sheaf.Paper.NearbySpecializationSlice`). It is not needed to type this statement;
  its mathematical result remains the documented stage-3 proof dependency and no
  assumption or private replacement for that theorem is introduced here.

Edge cases read against the definitions: empty X, empty S or T; zero Λ (including
m = 1); zero K; identity g; negative and zero r; equal a,b and identity c; points
with different geometric fields; and arbitrary T or preliminary U without Noetherian,
quasi-compactness, finite-type or separatedness assumptions. There is no nonempty
index requirement. In an empty base, the specialization quantifier is empty and
all module-sheaf objects are zero, giving the intended criterion. The generic tube
remains the strict localization in every case.

Searches (no exact existing declaration found):

- `msearch.py ... leanfinder "Nearby cycles restricted to geometric specialization
  slices identify with i inverse image R j direct image and detect comparison cone
  cohomology"`: 8 hits, all ordinary complex restriction/opcycle statements; none
  gives an oriented geometric slice, sliced base change or its cone test.
- `msearch.py ... loogle "nearbyCycles, baseChange"`: 0 hits; `nearbyCycles` is
  not a Mathlib identifier in this search index.
- `msearch.py ... grep "nearby.?[Cc]ycle|[Vv]anishing[Tt]opos|specializationSlice"`:
  0 Mathlib hits.
- `rg` in the upstream source and `lean/Sheaf` for nearby/specialization slices:
  no slice API; only the existing nearby-cycle definitions and unrelated
  specialization constructions. `grep -rn` of this item ID in upstream found none.
- `rg` for the selected new declaration names in Mathlib, upstream and `lean/Sheaf`:
  no collision. `dag/lean_names_upstream.json` contains no matching slice interface.
- `tools/blueprint_refs.py search "specialization slice"`: no blueprint node match.
  DAG text search found the existing general specialization-slice theorem, which
  has no Lean declaration, and its nearby-cycle consumers. No duplicate definition
  node was created.

The final file compiled cleanly with the required `scompile.py` in both its sandbox
and its actual library module path. All universes and variables are explicit, with
`autoImplicit false`. The only locally disabled linter is `checkUnivs` on the
abbreviation for the family of geometric morphisms: the family has the inherited
`max (u+1) v` topos universe; the suppression changes no elaboration or hypotheses.
No mathematical statement was corrected or disputed.

## Second reading by Q08

This is the author's explicit self-check, not an independent agent review. The
maintainer's separate reader supplies the independent review required by the brief.
I reopened the item and the complete module and matched each clause above. In
particular I checked that the generic scheme in `complex` is `genericTube`, that
`ordinarySliceComparison` takes the direct-image counit with the correct direction,
that the statement compares this actual arrow to `baseChange`, and that both
specialization diagrams remain inside the final iff quantifier. I checked the
full natural isomorphism on bounded objects, the exact constant-module inverse
image, independent geometric-point fields in `SliceChange`, and both levels of
base change. There is no proof of the theorem in this stage. During checking I
repaired the direction of the inverse-image j-square, and gave the vanishing
helpers a general site/coefficient universe rather than imposing any equality on
the independent scheme and coefficient universes. The final compile has no errors
or unexpected warnings. The new helper definitions are all part of the item's own
specified interface and appear in `lean.declarations`.
