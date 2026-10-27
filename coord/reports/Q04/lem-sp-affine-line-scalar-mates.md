## Worker report

The module `Sheaf.Paper.AffineLineScalarMates` states
`AlgebraicGeometry.Etale.affineLineScalarMates` and supplies seven real definitions
assembling the canonical functors, actual adjunction and specified comparison components.
Only the theorem has `sorry`. The natural-language statement is unchanged. No new DAG
node, dependency repair or statement correction is needed.

Hypothesis and clause correspondence:

- The positive characteristic and distinct prime are `ell p n : ℕ`, `[Fact ell.Prime]`,
  `_hp : 0 < p`, `_hEll : p ≠ ell`, `[Field k]`, `[CharP k p]`.
- The finite commutative coefficient rings and unital map are `[CommRing A]`,
  `[CommRing B]`, `[Finite A]`, `[Finite B]`, `φ : A →+* B`. The common annihilator
  is `ell ^ n`, with `hA` and `hB` asserting its cast is zero. A unital ring killed
  by N has every element killed by N, and conversely evaluate at 1. Prime ell makes
  this N positive even at n=0. There is no flatness or finite projective dimension binder.
- The standing base is `T : Scheme.{u}`, `[T.Over (Spec (.of k))]` with structure
  morphism locally of finite type, quasi-compact and separated. These are exactly finite
  type and separated over k. The canonical affine/projective spaces and chart/projection
  are over this base; no independent hypotheses on them are added.
- Ordinary small etale constant-module derived categories are `DerivedCategoryModule R T`.
  Every input assertion uses `ProEtale.AdjunctionTransfer.etaleProperty`, the existing
  intersection of bounded constructibility and finite Tor amplitude tested against every
  degree-zero module sheaf. Universes are `Scheme.{u}` and `R : Type (u+1)`, exactly the
  existing ordinary module-sheaf coefficient convention; finite rings admit this size.
- `scalarExtension φ T` is the published derived scalar extension. The actual root line
  is `ordinaryFiniteLine R N hR`, and its shift by 2 is the factor in
  `ordinaryFiniteP1Right`. No twist or Tor predicate is redefined.
- `ProjectiveLine.affineChart T` is j, `ProjectiveLine T ↘ T` is q, and
  `affineTraceLineCompactification T` is exactly their standard compactification.
- `affineLineSumPushforward R T` is J_R followed by Q_R. J_R uses the recorded etale
  sum-extension functor's exact derived functor. `affineLineTwistedRestriction` is V_R
  followed by exact H_R. `affineLineCompositeAdjunction` is literally the recorded
  sum/evaluation adjunction `.comp d.adjunction`. Thus its counit is Q_R(v_R V_R)
  followed by w_R by `Adjunction.comp_counit_app`; an arbitrary adjunction is never used.
  Universal quantification over `OrdinaryFiniteP1Datum` is over the already normalized
  projective-line data, including its actual projection/trace counit equation. Transport
  records are normalized at roots and pure tensors, as in the dependency's statement.
- `affineLineScalarMap` is the proper `scalarMate` at J_A M followed by Q_B applied
  to `sumCoefficientIso.hom` at M, exactly b^u. Its first theorem clause asserts
  `IsIso` on every ctf input and its identification with the actual `etaleCoefficientMap`
  for the standard compactification. The boundaries use `affineLineCompactSupportIso`:
  the unique left-adjoint comparison for the common exact H_R, whiskered with the same
  Q_R. This comparison preserves the sum/evaluation counit and labels and identifies
  sum extension with open extension; no other compactification is substituted.
- `affineLineProjectiveScalarIso` is precisely the projective dependency's a_K:
  `ExceptionalCoefficients.tensorIso`, inverse `scalarPullbackIso`, the scalar shift
  comparison and the same-annihilator `CoefficientLineComparison.derivedIso`.
  The latter record constrains roots, pure generators and the actual derived scalar
  counit, so e is not an arbitrary line isomorphism. Existence is asserted, not assumed.
  `hT` likewise asserts the automatic invertibility of ell^n on T, not an added hypothesis.
- `affineLineRightScalarIso` first applies
  `properOpenCoefficientPullbackIso.inv` at V_A K (h), then H_B of the preceding a_K.
  It is exactly a^u. These are the natural components of the recorded natural comparisons.
- The second main clause is `affineLineScalarMap ≫ L_B.map a^u.hom ≫ e_B = T_T.map e_A`,
  at every K satisfying the recorded ctf predicate. Lean composition applies the leftmost
  arrow first; this is exactly the node's rightmost-first displayed equation.
- The final clause gives `IsIso b^u(W_A K)` and identifies a^u with the composite
  B-adjunction's `homEquiv` applied to its inverse followed by T_T(e_A). This is the
  defining transpose characterization in `def-weil-pbc-adjunction-mate`, so it asserts
  the mate of the inverse b^u, with the required orientation. All statements are on
  every object of the full ctf subcategories. Their inclusions are fully faithful,
  so these ambient equations are equivalent to equations after restricting; preservation
  of those objects is exactly `lem-sp-etale-ctf-chart-domain`, imported for the proof.

Dependency declarations read and used (including proof imports):

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  standing setting and `ProEtale.CondensedRing.compactificationOverField`; the canonical
  standard compactification here is used instead of its Nagata choice.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: `Etale.DerivedCategoryModule`
  and the ordinary module derived-category convention.
- `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer`: `ProEtale.AdjunctionTransfer.etaleProperty`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and its existence theorem; scalar
  extension here is the existing fixed ordinary-module presentation used by both scalar
  counit dependencies, rather than a new construction.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`:
  `Scheme.finite_etale_torsion_twist_line`; its existing concrete root line is used.
- `Sheaf.AlgebraicGeometry.AffineTraceTower`: `affineTraceLineCompactification`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`: `Etale.etaleLowerShriek`.
- `Sheaf.Paper.EtaleSumCounitScalar`: `Etale.etaleSumCounitScalar`, with actual
  `derivedEtaleLowerShriekUpperStarAdjunction` and canonical pullback comparison.
- `Sheaf.Paper.P1CounitScalar`: `Etale.p1_counit_scalar`, whose normalized data and
  canonical comparison expression are used verbatim.
- `Mathlib.CategoryTheory.Adjunction.Basic`: `Adjunction.comp`, `comp_counit_app`.
- `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility`: `etaleCoefficientMap`,
  `sumCoefficientIso`, `etaleProEtaleCoefficientCompatibility_sum`; the proper map
  is the recorded `Etale.scalarMate` in its defining expression.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`;
  canonical scalar, pullback and tensor comparisons retain its representative normalization.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv`; the conclusion uses the
  equivalent defining Hom-transpose characterization explicitly, as the node allows.
- `Sheaf.Paper.EtaleCtfChartDomain`: `ProEtale.AdjunctionTransfer.etaleCtfChartDomain`
  and `etaleCtfChartScalarDomain`, the supplied preservation results for the proof.

Edge cases checked before writing: the empty base and zero complex are admitted; there is
no nonempty or nonzero assumption. Zero coefficient rings are admitted. At n=0, N=1
forces both coefficient rings zero, with all comparisons still defined. Identity coefficient
maps are admitted. Arbitrary nonflat finite quotients (e.g. Z/ell² to Z/ell) are admitted,
including infinite projective dimension over A. All inputs remain ctf, rather than arbitrary
bounded-below complexes. The composite counit and mate orientations were checked by following
the domains and codomains. No node fault or disputed mathematical assertion was found.

Searches performed through msearch.py (actual results in searches.jsonl):

- LeanFinder: "The coefficient comparison for the standard affine line compactification
  is compatible with the actual composite adjunction counit and its mate": 8 hits,
  headed by `mateEquiv_counit` and `mateEquiv_counit_symm`; these are general mate
  identities and do not give the geometric comparison of the specified normalized maps.
- Loogle: `CategoryTheory.mateEquiv_hcomp`: one exact hit, general horizontal mates.
- Mathlib grep: `affine.*(scalar|coefficient).*counit|counit.*(scalar|coefficient).*affine`:
  no hits.
- LeanSearch: "Composite adjunction affine line coefficient compatibility normalized counit":
  8 hits, headed by `Adjunction.comp_counit` and `comp_counit_app`; no geometric theorem.
- rg on both `lean/WeilConjectures` and `lean/Sheaf` for affine/scalar names and this node
  id found unrelated affine scalar constructions, and the already-read dependencies,
  but no existing affine-line scalar-mates theorem. Targeted source searches found no
  existing sum/open comparison with this functor signature, so the helper is the standard
  `Adjunction.leftAdjointUniq`, with no postponed data or extra theorem.

Validation: scompile.py checked the sandbox and library module presentations separately;
clean server result (16.6 s and 19.7 s), no warnings. The module uses `autoImplicit false`,
explicit universe u and no diagnostic commands. Every line is at most 100 characters.

## Second reading by Q04

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
