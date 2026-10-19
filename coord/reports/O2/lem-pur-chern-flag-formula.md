## Worker report

The module `Sheaf.Paper.ChernFlagFormula` states
`WeilConjectures.PurityFiniteSetting.chern_flag_formula`, with a sorry proof.
The polynomial formula is rendered by equality of every coefficient in degrees
0 through r, followed by the explicitly requested top Chern class identity.
There is no statement correction, new DAG node, or dependency repair.

The three helper definitions are expressions belonging to this formula, with
real data: `ordinaryFiniteFlagRoot` uses the recorded Kummer construction;
`ordinaryFiniteFlagProductCoefficient` expands the product of the linear
factors by recursion; `ordinaryFiniteFlagTopProduct` multiplies the roots using
the same recorded full-support cup product. They do not assert any new theorem
or introduce a replacement coefficient category or an arbitrary multiplication.

The hypothesis and clause correspondence is as follows.

| Node text | Lean rendering |
| --- | --- |
| Finite coefficients, twists, ordinary Chern classes of the conventions | `P : PurityFiniteSetting.{u}`, `P.Coefficient`, `ordinaryFiniteCohomology P S i`, and `P.ordinaryFiniteChernClass a F r i`. The positive twist already includes [2i], so no further shift is applied. |
| S a separated finite-type k-scheme | `S : Scheme.{u}`, `a : S ⟶ Spec (.of P.field.k)`, `[IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]`. The last two classes together mean finite type. |
| F locally free of constant rank r, r >= 0 | `F : S.Modules`, `r : ℕ`, `[F.IsFiniteLocallyFreeOfRank r]`. |
| Levels F_0,...,F_r of the filtration | `H : Fin (r + 1) → S.Modules` and ambient maps `ι : ∀ i, H i ⟶ F`. |
| Each level is a subsheaf | `hmono : ∀ i, Mono (ι i)`. |
| Increasing filtration | `d : ∀ j : Fin r, H j.castSucc ⟶ H j.succ` with `hcompat : ∀ j, d j ≫ ι j.succ = ι j.castSucc`. These steps are automatically monic because their composites with the ambient monomorphisms are monic. |
| 0=F_0 | `hzero : IsZero (H 0)`. An arbitrary zero-object presentation is allowed. |
| F_r=F | `hfull : IsIso (ι (Fin.last r))`. An arbitrary isomorphic presentation is allowed. |
| Vector subbundles, in the precise sense of the flag dependency | `hsub : ∀ i, (cokernel (ι i)).IsLocallyFree`. These are the actual sheaf quotients F/F_i. Local freeness of the levels also follows from the zero initial level and invertible successive quotients by local adapted frames. |
| Invertible successive quotients Q_j | `hQ : ∀ j : Fin r, (cokernel (d j)).IsInvertible`. The indices 0,...,r-1 correspond to the node's 1,...,r. These are sheaf cokernels, not sectionwise quotients of presheaves. |
| x_j=c_(1,A)(Q_j) | `P.ordinaryFiniteFlagRoot a (cokernel (d j)) (hQ j)` is the etale Kummer representative. `ordinaryFiniteHyperplaneStep` applies exact pro-etale comparison to it inside every cup multiplication. It therefore uses precisely the node's pro-etale first Chern class. |
| c_0=1 | Both helper recursions start with `P.ordinaryFiniteCohomologyOne S`; the left side uses the existing Chern definition with its prescribed c_0. |
| Sum_i c_i(F)u^i = product_j (1+x_j u) | First conjunct: `∀ i : Fin (r + 1), ... = ordinaryFiniteFlagProductCoefficient ... i.val`. The helper has b'_0=1 and b'_(i+1)=b_(i+1)+b_i cup x_last, exactly multiplication by the final linear factor. Equality of all these homogeneous coefficients is equivalent to the polynomial identity in the direct-sum cohomology ring. Both polynomials have no coefficient beyond r. Embedding H^(2i)(S,A(i)) in its i-th direct summand is injective, so this encoding loses no information. |
| In particular c_r(F)=product_j x_j | Second conjunct is equality with `ordinaryFiniteFlagTopProduct S r ...`, the ordered cup product of every root. |
| Empty-product convention | Rank-zero branches of both recursions return the degree-zero unit. |
| Nonsplit filtrations and singular S | There is no splitting datum, smoothness, regularity, reducedness, or nonemptiness hypothesis. |

Dependency declarations used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`
  provides the finite-field and finite-coefficient datum, at every positive level.
- `Sheaf.Paper.PurityChernClasses`: `ordinaryFiniteChernClass`,
  `ordinaryFiniteCohomology`, `ordinaryFiniteCohomologyOne`, and
  `ordinaryFiniteHyperplaneStep`. The last is the existing full-support cup
  product with an etale Kummer representative, using the exact comparison and
  the canonical ordered shifted Tate-power identification.
- `Sheaf.Paper.KummerAdditivity`: `AlgebraicGeometry.Etale.kummerFirstChern`
  and `ProEtale.kummerFirstChern`, the Kummer class and its comparison image.
  The helper uses the canonical Picard class `Scheme.Pic.ofIsInvertible` from
  `WeilConjectures.AlgebraicGeometry.Picard.Group`.
- `Sheaf.AlgebraicGeometry.CompleteFlagBundle`: the recorded complete flag
  construction and its vector-subbundle convention. The theorem quantifies over
  arbitrary levels and compatible monomorphisms satisfying these properties;
  it does not restrict the node to the universal filtration. The actual cokernel,
  IsZero, IsIso, local freeness, and invertibility predicates are the existing
  category-theoretic and scheme-module predicates used by that dependency.

Proof-only dependencies already stated are imported explicitly:
`Sheaf.Paper.ProjectiveBundleFormula`,
`Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry`,
`WeilConjectures.AlgebraicGeometry.EffectiveCartier`, and
`Sheaf.Paper.SupportedCohomologyHom`. Three proof-only nodes have no recorded
Lean declarations at the time of writing and consequently cannot supply imports:
`lem-pur-supported-cup-functoriality`, `lem-amb-cartier-kummer-map`, and
`lem-pur-closed-supported-cup-vanishing`. These are still named in the complete
proof docstring; none is needed to elaborate the statement. They were not
restated or silently substituted.

The source read was `literature/stacks-project/weil.tex`,
`proposition-chern-class` and `lemma-splitting-principle` (Tags 0FI5 and 0FI7).
The node's eight-step proof, including its corrected coefficient indices in the
line-subbundle calculation and verification of the divisor-annihilation input,
is carried into the theorem docstring. No Whitney axiom is introduced as a
hypothesis. No section, Euler class, or purity isomorphism defines the Chern classes.

Edge cases checked before writing:

- r=0: `Fin r` is empty; the zero and final levels coincide. All successive-quotient
  requirements are vacuous. Both conclusions become c_0=1, without forming P(0).
- r=1: the cokernel of the unique step identifies with F, and the formula has
  constant coefficient 1 and linear coefficient its Kummer first Chern class.
- r=2: the recurrence gives coefficients 1, x_0+x_1, and x_0 cup x_1; its top
  product is the same ordered cup product. Degrees and twists are respectively
  (0,0), (2,1), (4,2).
- Empty schemes are admitted: there is no Nonempty hypothesis and IsZero/IsIso
  endpoints continue to express the correct filtration.
- Singular and nonreduced bases and globally nonsplit extensions are admitted.
- All positive coefficient levels are admitted, using exponent ell^level as in
  the recorded Chern definition; no ramification-divisibility assumption is added.
- The single explicit universe u agrees with the dependency interfaces, and the
  coefficient ring is the recorded size lift in Type (u+1).

Searches for an existing statement (all conducted for N2 / this item):

- `msearch.py ... leanfinder` with query “The Chern polynomial of a vector bundle
  filtered by invertible subquotients is the product of one plus each first
  Chern class times the variable”: eight hits about characteristic polynomials,
  including `LinearMap.polyCharpolyAux` and `LinearMap.charpoly_prodMap`; no
  finite-coefficient scheme-cohomology Chern statement.
- `msearch.py ... loogle '"chern"'`: two Lean matcher-name hits only.
- `msearch.py ... leansearch` with query “Chern polynomial of a vector bundle
  with a filtration by line quotients equals the product of linear factors”:
  eight ordinary polynomial/characteristic-polynomial hits, including
  `Polynomial.splits_iff_exists_multiset'`; no matching scheme statement.
- `msearch.py ... grep 'Chern|Whitney|splitting.principle'`: 19 unrelated hits,
  mostly Chernoff bounds and Whitney terminology; no matching Chern formula.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and in the shared
  `lean/Sheaf` for Chern/flag, ordinaryFinite flag names, and filtration interfaces:
  no existing Chern flag formula. Existing general filtered-complex and sheaf
  filtrations are different notions; the complete flag module only constructs
  the universal filtration, with no arbitrary-filtration Chern formula.
- `rg` for the exact item id in upstream: no hits. Exact-name collision searches
  for all four delivered declarations in upstream, shared `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no hits.

No statement fault or disputed assertion was found.

## Second reading by N2

This section records a second pass by the same worker, with the node, source,
and module reopened; no independent worker or sub-agent was started. The
maintainer's independent review remains the independent reading for this delivery.

The pass checked every row of the correspondence table against the signature.
In particular it checked that the ambient maps are monomorphisms, the steps
commute with them, both endpoints are imposed, ambient quotients are locally
free, and successive quotients are the actual invertible cokernels. These are
arbitrary filtrations, not only the flag bundle's chosen filtration. It checked
that finite type is represented by both locally-finite-type and quasi-compact,
and that the fixed finite coefficient datum retains every positive level.

The pass expanded the coefficient recursion through ranks zero, one, and two,
and checked that its multiplication is the existing ordinary full-support cup
with exactly the same Kummer exponent as the recorded Chern construction. It
checked that the shifted positive Tate objects receive no extra [2i], that the
top identity is present, and that no global splitting or smoothness assumption
has slipped into the signature. No mismatch or source-based correction was found.

Validation: the prescribed standalone `scompile.py` call completed with exit
code zero for both sandbox and library locations, with no errors or warnings.
All Lean lines are at most 89 characters. Every universe and variable is explicitly
bound, and the only postponed proof is the named theorem for this DAG node.
