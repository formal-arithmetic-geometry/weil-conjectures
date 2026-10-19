## Worker report

The item is stated by `ToricMonoid.complete_toric_facet_valuations` in `Sheaf.RingTheory.CompleteToricFacetValuations`; its proof is `by sorry` with the complete theorem statement. The repaired model dependency is `def-trf-complete-toric-model` in `Sheaf.RingTheory.CompleteToricModel`. Its complete-model helpers reuse the published `AddMonoidAlgebra.CompletedLocalModel`, `localModelBoundaryIdeal`, `localModelCompletionIdeal`, and `completedLocalModelBoundaryIdeal`; the independent-universe canonical monomial is the same algebra-map construction as `completedLocalModelMonomial`. The module also defines the lattice, rationalization, cone, facet, primitive-normal, rational-extension, and boundary-ideal notation used by the theorem.

The theorem binders render the fs monoid hypothesis, sharpness, integer parameter count, normal-domain ring, chart monomials, and complete-model predicate exactly. Its conclusion renders Noetherianity, monomial nonvanishing, finite facets, unique primitive normals and rational extensions, the half-space cone description, distinct boundary ideals, height-one prime classification, DVR localizations and normalized valuation formula, together with the subsingleton rank-zero clause. Edge cases checked: P = {0}, n = 0, q = 0, rank-one and rank-two cones, and both coefficient alternatives. The model module has no `sorry`; only the named theorem is postponed.

Dependencies used: `Sheaf.RingTheory.LogRegularSaturationNormality` for the existing complete local model and ideals; `Sheaf.AlgebraicGeometry.LogRegularCompletedChart` for the canonical model monomial construction; Mathlib Grothendieck groups, tensor products, finite dimensions, convex cones, noetherian rings, localization, and discrete valuation rings. Searches found no existing combined toric-facet declaration. The returned H4/H12 repair was completed by removing duplicate complete-model definitions and reusing the published declarations. `scompile.py` compiled both files cleanly; `deliver2.py --no-push` reached preflight after the repair.

## New nodes

`def-trf-complete-toric-model` supplies the model and facet notation required by the item. Its model helpers alias the existing complete-local declarations; its facet notation is constructed directly from Mathlib.

## Returned-delivery repair

The returned issue identified duplicate definitions in `CompleteToricModel.lean`. The replacement imports the existing model module and aliases its completion and ideals, while retaining the required independent-universe monomial and facet notation.

## Second reading by Q147

The group delivered without a second reader ("No second worker was started"). This section is the reading done by the maintainer's independent reviewer (cc review service, 2026-10-18), which replaces it in the FIX; it was written with the node, the source place and both modules open.

Node clauses and their Lean (`ToricMonoid.complete_toric_facet_valuations`):

- $P$ fg, integral, saturated, additive: `[AddCommMonoid P]`, `hfs : IsFineSaturatedMonoid (Multiplicative P)` (the recorded predicate of def-trf-fs-log-blowup: finite generation, injective `GrothendieckGroup.of`, saturation). Verdict: exact.
- sharp: `hsharp : ∀ q, IsUnit (Multiplicative.ofAdd q) → q = 0`. Exact (same as `IsAddUnit q → q = 0`).
- $n\ge0$: `n : ℕ`. Exact, $n=0$ allowed.
- $B_L(P,n)$, completion at $(\mathfrak m_L, z^q\ (q\ne0), t)$: `Complete L P n = AddMonoidAlgebra.CompletedLocalModel`, the `AdicCompletion` (def-weil-pbc-adic-completion record) of `MvPolynomial (Fin n) (AddMonoidAlgebra L P)` at `map (maximalIdeal L) ⊔ localModelBoundaryIdeal`. Exact.
- case (i) field $k$; case (ii) Cohen ring $C$, residue char. $p$, $p$ prime, residue field arbitrary, $\theta-p\in(z^q\,(q\ne0),t)B_C$: `IsCompleteModel` disjunction with a ring isomorphism carrying the model monomials to `z`; `IsCohenRing p C` contains `Nat.Prime p`; `completedChartIdeal` is the extension of the chart ideal. Coefficient universe `v` independent of `u`, `w`. Exact, no extra assumption.
- chart monomials $z^q$ in $R$: `z : P → R` with `z q = e (monomial …)`. Exact.
- $R$ normal domain: `[IsDomain R] [IsIntegrallyClosed R]`, the recorded inline form of def-weil-pbc-normal-ring. Exact.
- $G$, $V=G\otimes\mathbf Q$, $\sigma$: `Lattice`, `RationalSpace = ℚ ⊗[ℤ] G`, `cone = ConvexCone.hull` of the images (contains $0=1\otimes0$, so equal to the pointed hull). Exact.
- facet ($h\ne0$, $h\ge0$ on $\sigma$, $F=\sigma\cap\ker h$, $\dim F=\dim V-1$): `IsFacet` with `finrank (span F) + 1 = finrank V`; for $V=0$ no facet. Exact.
- $R$ Noetherian; every $z^q\ne0$: first two conjuncts. Exact.
- $\mathcal F$ finite: `Set.Finite {F | IsFacet P F}`. Exact.
- unique $\nu_F$ nonnegative on $P$, image $\mathbf Z$, $F=\sigma\cap\ker\nu_F$: `IsPrimitiveNormal F (ν F)` plus uniqueness over all `μ`, with the rational extension `h F`. Exact.
- $\sigma=\{v:\nu_F(v)\ge0\ \forall F\}$: `cone P = {v | ∀ F, 0 ≤ h F v}`. Exact.
- $\mathfrak p_F$ distinct height-one primes: `Function.Injective (boundaryIdeal z)`; prime, `≠ ⊥`, every prime strictly below is `⊥` (equals "no prime strictly between"). Exact.
- exactly the height-one primes containing a monomial: the `↔` clause. Exact.
- $R_{\mathfrak p_F}$ DVR: `IsDiscreteValuationRing (Localization.AtPrime …)` (recorded declarations). Exact.
- $v_F(z^q)=\nu_F(q)$, normalized: `-WithZero.log` of the adic valuation of `IsDiscreteValuationRing.maximalIdeal` on `FractionRing R` (uniformizer ↦ `exp (-1)`, so value one). Exact.
- $P=\{0\}$: `Subsingleton P →` no facets, `V` subsingleton, no boundary ideals, `cone = univ`. Exact.

Edge cases: $P=0$ (no facets, $V=0$), $n=0$, $q=0$ ($z^0=1$), field coefficients ($\mathfrak m_k=0$), Cohen case with $P=0,n=0$ ($R=C/p$). Universes: `u, v, w` all bound; no equality imposed.

Searches: `rg` for facet/toric/primitive normal/GrothendieckGroup/ConvexCone in the side clone `lean/Sheaf` and Mathlib; the only near notions are `PointedCone.hull` in `SharpConeLatticeIntersection` (a theorem hypothesis, same set) and `completeToricChart` in `CompleteToricKatoRecognition`, the same map as `ToricMonoid.monomial`; importing it here would create an import cycle once kato-recognition is proved from this item, so the local monomial is kept and documented as the universe-independent form of `completedLocalModelMonomial`.

Changes made in the FIX: H8 — module docstrings with `# title`, `Source:` place and blueprint id; a docstring with source place and `(blueprint: def-trf-complete-toric-model)` on every declaration of `CompleteToricModel.lean`; the theorem docstring now carries the source place and the node's 18 proof steps. H12 — the statement of `def-trf-complete-toric-model` is now self-contained TeX defining each declared notion, with a precise source place. H11 — this section. No signature, record statement or definition body changed; both files recompiled cleanly with `nt_compile.py`.
