## Worker report

The module `Sheaf.Paper.P1SplittingScalar` states
`AlgebraicGeometry.Etale.p1SplittingScalar`. Its only postponed theorem is this
node's theorem, with the complete six-step natural-language proof in its docstring.
Four real helper definitions expose the canonical degree-zero scalar comparison,
its shifted version, its ordered biproduct version, and the proper coefficient
map followed by the shifted-line identification. No new mathematical notion,
new node, dependency repair, or statement correction is needed.

The comparison is stated as an existence of the explicitly normalized balanced
identifications together with the two equalities. The normalizations determine
these maps, rather than merely asserting isomorphism of the endpoints. In
particular none of the balanced maps, splittings, traces or coefficient arrows
is an unconstrained parameter or an additional hypothesis.

Hypothesis and clause correspondence:

- A prime ell is `(ell : ℕ) [Fact ell.Prime]`. The field of positive characteristic
  p is `(p : ℕ) (_hp : 0 < p) (k : Type u) [Field k] [CharP k p]`;
  `_hne : ell ≠ p` is precisely the unequal-characteristic assumption.
- The standing base is `S : Scheme.{u}`, with `S.Over (Spec (.of k))`,
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on its structural map.
  Local finite type plus quasi-compactness means finite type. The projective
  line and its projection are the existing `ProjectiveLine S` and
  `ProjectiveLine S ↘ S`; the projection is the canonical morphism over S and
  hence over k. There is no extra Noetherian or invertibility hypothesis:
  the theorem supplies their proof witnesses `_hNoetherian` and `hS` from the
  standing assumptions, for use by the recorded normalized splitting API.
- Finite commutative coefficient rings are `A B : Type (u + 1)`, with
  `[CommRing A] [CommRing B] [Finite A] [Finite B]`. The unital coefficient
  map is `φ : A →+* B`. The common annihilator is `ell ^ n`, with
  `n : ℕ`, `hA : ((ell ^ n : ℕ) : A) = 0` and `hB : ((ell ^ n : ℕ) : B) = 0`.
  Its positivity is the explicit existing proof
  `pow_pos (Fact.out : ell.Prime).pos n`. Choosing this common exponent implies
  exactly the asserted ell-power annihilation of both rings.
- Ordinary small-etale constant-ring categories are the existing
  `Etale.DerivedCategoryModule`, used throughout `ordinaryFiniteUnit`,
  `ordinaryFiniteLine`, `ordinaryFinitePushforward` and `scalarExtension`.
  There is no replacement category, bounded-below restriction, pro-etale twist,
  or added Dctf assumption. The node introduces Dctf as terminology but imposes
  no arbitrary-input Dctf hypothesis in either of its two equations.
- `ordinaryFiniteLine R (ell ^ n) hR T` is the single complex of the recorded
  `Scheme.finiteEtaleTateLine`, namely the sheafification of
  `R ⊗[ZMod (ell ^ n)] μ_N`. This is the symmetric presentation of the node's
  `μ_N ⊗[ZMod N] R`. Shift by two is literal `⟦(2 : ℤ)⟧`.
- The three sheaf isomorphisms `c0`, `c1`, `cP` are ordinary balanced extension
  on the constant sheaf of S and on the Tate lines of S and P. The first
  three conjuncts characterize their adjoints on every constant generator and
  every `finiteEtaleTateOneGenerator`: `a` goes to `φ a`, and
  `a ⊗ z` goes to `φ(a) ⊗ z`. B-linearity of the original maps determines
  `(a ⊗ z) ⊗ b` as `b φ(a) ⊗ z`, which under symmetry is exactly the formula
  `(z ⊗ a) ⊗ b ↦ z ⊗ φ(a)b` in the node. Sheafification introduces no arbitrary
  section choices; the formulas apply on every etale object.
- The isomorphisms `d0`, `d1`, `dP` are the derived identifications. Their three
  hom equations fix them to `p1ScalarSingleMap` applied to the corresponding
  ordinary map. This helper uses the existing derived extension/restriction
  adjunction and exact restriction's `mapDerivedCategorySingleFunctor`.
  Flatness of the constant sheaf and twist makes this precisely the K-flat
  ordinary-tensor comparison. No existence theorem with undetermined data is
  used to define any helper.
- `p1ScalarShiftedLine` uses the adjunction-compatible shift structure
  `leftAdjointCommShift` of exact derived restriction. `p1ScalarSourceMap`
  assembles the direct-sum version using the images of `biprod.fst` and
  `biprod.snd`, followed by the shifted twist and unit identifications.
- `s_R` is exactly `(projectiveLineTraceDatum ... R ... S hS).decomposition`.
  That existing datum fixes its components to the twisted shifted unit and the
  actual scalar Kummer class of the canonical `ProjectiveSpace.twist ... 1`.
  `t_R` is the existing `projectiveLineTrace`, definitionally the second
  projection after the inverse of this very same decomposition.
- The beta in `p1ScalarPushforwardMap` is the existing
  `(scalarMate φ (ProjectiveLine S ↘ S)).app L_A`, the counit-transpose proper
  coefficient map used in the recorded coefficient-compatibility module.
  It is followed only by `Rq_{*,B}` of the specified shifted Tate identification.
- The first final conjunct is
  `T_S.map s_A.hom ≫ beta_with_line_identification = source_identification ≫ s_B.hom`.
  This is the first displayed equation with all its boundaries explicit,
  in Lean's left-to-right composition order.
- The second final conjunct is
  `beta_with_line_identification ≫ t_B = T_S.map t_A ≫ d0.hom`.
  This is the second displayed equation, with its constant-object boundary.
  Both are equalities of morphisms in the derived category, not only maps
  on cohomology or existence of endpoint isomorphisms.
- No `Flat`, Tor-dimension, or projective-dimension assumption is made on B/A.
  Every universe and variable is explicit, and the module sets `autoImplicit false`.

Dependency interfaces read and reused:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`, the
  setting convention; no compactification choice is needed for the canonical q.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule` via its public coefficient import.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `nonempty_derivedChangeOfRingsCochainModel`, retaining separate localization
  universes and K-flat computations. The ordinary constant-coefficient
  specialization is `Etale.scalarExtension` and its actual adjunction in
  `Sheaf.Paper.EtaleDerivedScalarTensor`, publicly reached through the
  coefficient-compatibility module.
- `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer`:
  `AlgebraicGeometry.ProEtale.AdjunctionTransfer.etaleProperty`, the node's
  Dctf terminology; no arbitrary Dctf variable occurs in this assertion.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`:
  `Scheme.finite_etale_torsion_twist_line`, using its existing Tate sheaves.
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction`:
  `Etale.exists_ordinaryFiniteP1Adjunction`, reexported through the trace module.
- `Sheaf.AlgebraicGeometry.ProjectiveLineTrace`:
  `Etale.projectiveLineTraceDatum`, `Etale.projectiveLineTrace`.
- `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility`:
  `ProEtale.CoefficientCompatibility.etaleCoefficientMap` and its proper
  constituent `Etale.scalarMate` from `Sheaf.Paper.PurEtaleScalarMateProjection`.
- Proof imports: `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`
  (`Scheme.etaleFiniteTwistPullback`),
  `Sheaf.Algebra.Homology.KFlatTelescopeClosure` (`CochainComplex.kFlat_closure`),
  `Sheaf.CategoryTheory.DerivedCategory.AdjunctionMateTranspose`
  (`CategoryTheory.adjunctionMate_transpose`),
  `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
  (`CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons`),
  and Mathlib's `LocallyOfFiniteType.isLocallyNoetherian` and
  `QuasiCompact.compactSpace_of_compactSpace`.

Edge cases checked mathematically before stating:

- The empty base S is allowed; all maps are the canonical maps in its zero
  sheaf category, and invertibility in the zero section ring is valid.
- Either coefficient ring may be the zero ring whenever a unital map exists.
  The generator equations and isomorphism assertions continue to make sense.
- `n = 0` means N = 1 and forces both coefficient rings to be zero; this case
  is retained, not excluded by a positive-exponent assumption.
- A nonflat quotient such as Z/ell^2 -> Z/ell is allowed with common N = ell^2.
  The computation uses K-flat source objects, not flatness of the ring map.
- No orientation or primitive root is selected: every root generator occurs
  in the normalization, retaining the source's Kummer sign convention.

Searches for an exact existing assertion:

- msearch leanfinder: "Derived extension of finite coefficient rings preserves
  the normalized projective line Kummer splitting and integration trace";
  eight unrelated hits (normalized algebra trace, Galois norms, integral
  Weierstrass curves), no match.
- msearch loogle: `"Kummer", "scalarExtension"`; zero hits.
- msearch grep: `kummer|chernClass|tateTwist` in Mathlib AlgebraicGeometry;
  zero hits.
- msearch leansearch: "Projective line Kummer splitting and trace commute with
  derived change of finite coefficients"; eight hits about linear algebra trace
  and polynomial base change, no etale splitting/trace equality.
- `rg` in both project Lean roots for scalar/splitting combinations, and
  `grep -rn` for this node id in WeilConjectures: no existing assertion.
  The downstream `Sheaf.SecSmoothPurity.ReductionExceptional` has Tate-only
  scalar maps, but does not state the two splitting and trace equalities.
  Its module belongs to a consumer of this item, so importing it here would
  reverse the proof dependency. No Tate map from that module is redefined:
  the new degree-zero helper is the general adjunction construction on an
  arbitrary specified sheaf scalar map; the theorem supplies the uniquely
  generator-normalized maps as conclusions.
- `rg` for all five new declaration names in WeilConjectures and Sheaf: no hits.

No statement dispute or node fault was found. The node changes only in `lean`.

Validation: the prescribed `scompile.py Q22 lem-sp-p1-splitting-scalar` passed both
sandbox and library-module compiles (26.3 s and 23.7 s), with no warnings or errors.
The node record's signature is verbatim from the final module; only `lean` differs
from the repository node; every Lean line is at most 100 characters. The one
named theorem has the sole `sorry`; all four helper definitions contain real data.

## Second reading by Q22

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
