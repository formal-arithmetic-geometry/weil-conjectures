## Worker report

The module `Sheaf.Paper.UniformConstructibleExtIntegral` states
`AlgebraicGeometry.ProEtale.CondensedRing.uniformConstructibleExtIntegral`.
Its only theorem has proof `sorry`. There are no new definitions, dependency repairs,
or changes to the natural-language node. The node copy changes only `lean`.

The source is the current blueprint main-20261015,
`sec-six-functors-basics/sk-lem-uniform-constructible-ext/`, especially
`sk-lem-uniform-constructible-ext-integral.md`, the torsion detail, and the parent
proof's Integral targets paragraph. The declaration docstring spells out all six
DAG proof steps, including restriction of finite coefficients to the integral category,
the actual coefficient-change adjunction, and the final Milnor argument.

Hypothesis-by-hypothesis and clause-by-clause match:

| Node or inherited hypothesis/clause | Lean rendering |
| --- | --- |
| Prime ell | `(ℓ : ℕ) [Fact ℓ.Prime]` |
| Finite extension E/Q_ell | `(E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]` |
| Integral coefficient ring O_E with its continuous topology, pulled back to each pro-etale site | `DerivedNakayama.integerRing ℓ E` inside `FormalSupportModules`; these are the existing continuous condensed integers and actual inverse-image coefficient module category |
| Field k of positive characteristic p different from ell | `(k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)` |
| The separated finite-type k-scheme setting inherited from torsion | `S Z V X T B : Over (Spec (.of k))`, each with `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on its structure map, exactly as in `uniformConstructibleExtTorsion` |
| a = i composed with u, u open and i closed | `u : S ⟶ Z`, `i : Z ⟶ X`, `IsOpenImmersion u.left`, `IsClosedImmersion i.left` |
| j is the open complement of Z in X | `j : V ⟶ X`, `IsOpenImmersion j.left`, and `hij : Set.range i.left.base = (Set.range j.left.base)ᶜ` |
| b locally closed, with the stipulated open/closed factorization | `vb : T ⟶ B`, `kb : B ⟶ X`, `IsOpenImmersion vb.left`, `IsClosedImmersion kb.left`; these are morphisms over k |
| L_0 and M_0 are integral lisse lattices, including rank zero | `L₀`, `M₀` in the respective `FormalSupportModules`, with `hL₀` and `hM₀ : IsLisseCoefficientModule ...` |
| a_!L_0 and b_!M_0 | The existing `lowerStar` after `openImmersionLowerShriek`, first for `(i.left,u.left,L₀)` and then for `(kb.left,vb.left,M₀)` |
| Ext is in D(X_proet,O_E), with both module sheaves placed in degree zero | The two `DerivedCategory.singleFunctor (FormalSupportModules ... X.left) 0` expressions, with target shifted by the integer q; the Hom is in this unbounded derived category, with no constructibility subcategory or finite-coefficient substitution |
| q > cd_ell(j) + cd_ell(S) + 2 | `(q : ℤ)` and `hq : torsionStratumRelativeDimension ℓ k j + torsionStratumDimension ℓ k S + 2 < (q.toNat : WithTop ℕ)` |
| Ext^q = 0 | `Subsingleton (Q ⟶ N ⟦q⟧)`, where Q and N are the preceding explicit degree-zero objects; this is precisely vanishing since the additive Hom group has zero |

The cutoff is nonnegative and at least two, so a negative integer can never satisfy
`hq`; on every degree in the node's asserted range, `q.toNat` is exactly q. Infinite
cohomological dimensions produce `⊤ < ...`, which is false, as stipulated by the
torsion dependency. Thus this encoding adds no finite-dimension assumption and drops
no degree. No assumption about a reduction exponent n belongs to this integral result.

Dependency declarations read and used:

- `Sheaf.Paper.UniformConstructibleExtTorsion`:
  `AlgebraicGeometry.ProEtale.CondensedRing.uniformConstructibleExtTorsion`,
  `torsionStratumDimension`, and `torsionStratumRelativeDimension`. These dimension
  wrappers supply qcqs instances from the standing finite-type setting and use the
  recorded absolute and relative cohomological dimensions, with codomain `WithTop ℕ`.
- Its existing coefficient and lattice interfaces:
  `Sheaf.Paper.DerivedNakayamaResolution`,
  `AlgebraicGeometry.ProEtale.DerivedNakayama.integerRing`;
  `Sheaf.AlgebraicGeometry.FormalClosedSupportAdjunction`,
  `AlgebraicGeometry.ProEtale.CondensedRing.FormalSupportModules`;
  `Sheaf.Paper.CoefficientHeartCommonStratification`,
  `AlgebraicGeometry.ProEtale.IsLisseCoefficientModule`.
- The read-only upstream framework modules
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs` and
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar` and
  `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek`.
- Statement objects use Mathlib `DerivedCategory.singleFunctor` and the standard shift.
  Mathlib's `Abelian.Ext` definition in
  `Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic` was also read: it is a shrunk
  form of exactly this localized shifted Hom. Using the Hom directly avoids requiring
  any additional small-Ext structure or extra universe constraint.

The stated proof prerequisites are imported without `public`: `FormalClosedSupport`
(`formalClosedSupportAssertions`), `FormalClosedSupportII` (`formalClosedSupportII`),
`RGammaDerivedLimit` (`CategoryTheory.site_rgamma_derivedLimit`), `MilnorSequence`
(`CategoryTheory.milnor_shortExact`), and upstream `ChangeOfCoefficients`
(`AlgebraicGeometry.ProEtale.coefficientMap`). The torsion prerequisite is a public
import because its definitions occur in the signature. `sk-lem-integral-models` and
`sk-def-pe-derived-completion` have no recorded Lean module on the read base; they are
used only in the natural-language proof plan and are not assumptions in the statement.
No imports are omitted for an import cycle.

Edge cases checked before writing: zero lattices and rank-zero local models; empty S,
T, or X; identity open/closed immersions; Z empty and Z = X; integer degrees zero,
negative, exactly the cutoff, and strictly above it; either dimension infinite;
arbitrary b-factorization; and finite extensions E of any finite degree. For a
geometric point the bound q > 2 is consistent with the integral coefficient theory.
No nonemptiness, fixed positive lattice rank, finite-dimension bound, flat quotient,
or Mittag-Leffler hypothesis is imposed.

Searches for an existing statement (all through the prescribed msearch wrapper unless
marked direct):

- LeanFinder, `Ext vanishing between extensions by zero of lisse integral l-adic lattices with cohomological dimension bound`:
  eight hits on `HasInjectiveDimensionLT`/`HasProjectiveDimensionLT` and their
  `subsingleton`/`mk` characterizations; none gives this geometric bound.
- LeanSearch, `Ext vanishes above cohomological dimension for integral l-adic lattice extensions by zero`:
  eight generic injective/projective dimension hits, including
  `isZero_Ext_succ_of_projective`; no matching stratum theorem.
- Loogle, `"Ext", "vanish"`: zero hits.
- Mathlib grep, `uniformConstructibleExt|integralStratum|lisse.*Ext`: zero hits.
- Direct `rg` of slopmaster2 `WeilConjectures` and side `lean/Sheaf` for
  `uniformConstructibleExt|integralStratum|uniform.*constructible.*[Ee]xt`:
  the side torsion theorem and the rational parent theorem exist, but neither states
  the integral lattice bound. The parent docstring mentions this still-missing node.
- Direct `grep -rn det-uniform-constructible-ext-integral` of the upstream
  `WeilConjectures` tree: zero hits. Direct search of `dag/lean_names_upstream.json`
  and both Lean trees for `uniformConstructibleExtIntegral|integralStratum` found
  no declaration collision.

Validation: all compilation uses the prescribed `scompile.py`, with no global build.
The initial shift-notation lexer error was repaired by separating the closing
parenthesis from the shift token. Final per-file compilation and delivery preflight
are recorded by the delivery wrapper.

## Second reading by NX

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
