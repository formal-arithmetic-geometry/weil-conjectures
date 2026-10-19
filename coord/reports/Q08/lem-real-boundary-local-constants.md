## Worker report

The module `Sheaf.Paper.RealBoundaryLocalConstants` states
`RealSheaves.boundary_local_constants`, with `sorry` as its entire proof. It formalizes
lem-real-boundary-local-constants without changing the node's statement or dependencies.
No other theorem or definition is introduced.

Hypothesis-by-hypothesis correspondence:

- The finite field, its specified algebraic closure, and the chapter conventions are the
  existing `D : RealSheaves.Setup.{u,v}`. The curve is `C₀`, with its structure over
  `Spec D.k₀` and `hC : D.IsCurve C₀`. The predicate contains nonemptiness, separatedness,
  smoothness, finite type, pure dimension one, and connected geometric base change.
- The open immersion is `U₀.ι` for `U₀ : C₀.Opens`; `hU` says the open is nonempty,
  `hS` says its complement is finite, and `hs : s ∉ U₀` is membership in that complement.
- The field `k_s` is precisely `C₀.residueField s`. Its supplied algebra structure is
  forced by `hks` to be `(C₀ ↘ Spec (.of D.k₀)).residueFieldAlgebraMap s`.
- The local ring is the actual stalk `C₀.presheaf.stalk s`. `H`, `hH` use the recorded
  generalized henselization universal property at its maximal ideal, with the compatible
  stalk and localization algebra structures. `IsDomain H` exposes the property of this
  henselization needed to present its fraction field. `K`, `IsFractionRing H K`, and the
  scalar tower present the specified `K_s` and its canonical stalk map.
- `es` identifies the henselization residue with `k_s`. Its equation `hes` specifies it
  on the surjective residue map of the stalk, so this is the canonical unchanged-residue
  identification, not an additional choice of residue map.
- `Ω`, its field/algebra structures, `IsAlgClosed Ω` and `Algebra.IsAlgebraic K Ω` present
  the chosen algebraic closure. `integralClosure H Ω`, its local structure and local
  structural map are the integral closure used in the recorded decomposition interface.
  `a`, `ha` describe the restriction of each `K`-automorphism to that closure pointwise.
- The algebra structure of `D.k` over `k_s` and the scalar tower express the chosen
  embedding of `k_s` into `k` over `k₀`. `IsAlgClosure (C₀.residueField s) D.k` expresses
  the compatible algebraic closure. `e` is the identification of the integral-closure
  residue field with `k`; `he` forces its compatibility with the structural residue
  field. `r`, with the equation `hr` on every integral element, is exactly the residue
  homomorphism of the dependency, now with the residue closure identified with `k`.
- `ξ`, `hξ` give the canonical factorization `Spec K_s → U₀` of the local generic point.
  `Ωu`, `b` are an arbitrary geometric base point on the geometric open. `u₀`, `hu₀`
  give its arithmetic image. `i`, `hi` are exactly its map of constants to `Ωu`.
- `G₀`, `e₀` use the same small profinite-model interface as the decomposition-landing
  dependency. `e₀` identifies the group with `Aut (fiber u₀)`. The path is the actual
  natural isomorphism `γ`. The map `θ` is arbitrary subject to its defining action `hθ`
  on every finite étale fibre, copied from the dependency's characterization. Thus no
  preferred path, Frobenius normalization, or extra landing assertion is assumed.
- `p` is characterized by `hp` on every finite constant cover using the existing
  `fiberConstantCoverEquiv`. A fibre point with embedding `i ∘ μ` is sent to the point
  with embedding `i ∘ p(g) ∘ μ`. This is the field-valued presentation of the existing
  `constantCoverAction`. It is not an unconstrained group homomorphism: finite étale
  embeddings into `Ωu` factor through the algebraically closed constant subfield `i(k)`,
  so these equations determine its entire constant-cover action, and hence `p` uniquely.

Clause-by-clause correspondence:

- Finite residue extension: `Module.Finite D.k₀ (C₀.residueField s)`.
- Positive degree: `0 < Module.finrank D.k₀ (C₀.residueField s)`.
- Residue Galois surjectivity: `Function.Surjective r`.
- The full commuting square: `p.comp θ = (AlgEquiv.restrictScalarsHom D.k₀).comp r`.
  Restriction of scalars is precisely the inclusion `Gal(k/k_s) → Gal(k/k₀)`; it leaves
  every automorphism's underlying function unchanged.
- The subgroup image assertion is the equality of `MonoidHom.range (p.comp θ)` with
  the range of that same inclusion, as subgroups of `D.k ≃ₐ[D.k₀] D.k`.

Recorded statement dependencies read and used:

- d-real-setup: `Sheaf.Paper.RealSheavesSetup`, `RealSheaves.Setup`,
  `RealSheaves.Setup.IsCurve`, and `RealSheaves.Setup.geometricCurve`.
- def-weil-pbc-henselization-at-prime:
  `Sheaf.RingTheory.GeneralizedHenselizationAtPrime`, `Algebra.IsHenselizationAtPrime'`.
- lem-real-boundary-decomposition-landing:
  `Sheaf.Paper.RealBoundaryDecompositionLanding`,
  `RealSheaves.exists_boundary_decomposition_landing`: its complete signature and
  docstring supply the models of the local field, closure, residue map and path formula.
- def-wf-weil-group: `WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup`,
  `AlgebraicGeometry.Scheme.FiniteEtale.constantCover`, `constantCoverAction`,
  `geometricFrobenius`, `weilGroup` and `weilGroupDeg`. Its full source explains the
  arithmetic projection through finite constant covers. The imported upstream module
  `FundamentalGroup.ConstantCover` supplies `fiberConstantCoverEquiv` for that action.
- The residue characterization follows the already imported
  `Sheaf.RingTheory.HenselianResidueGaloisAction`,
  `HenselianLocalRing.exists_residue_galois_action`, with its compatible residue closure
  transported to `D.k`. No private definition of the residue action is introduced.

The module imports the stated proof dependencies for closed-point fields, regular-normal
irreducibility, smooth regular local rings, strict henselization local structure, the
regular dimension-one DVR criterion, and henselian root lifting. Smoothness, Noetherianity,
field-extension surjectivity, finite-field Frobenius and surjective base change are already
available through these imports. The proof-dependency nodes
lem-wf-arithmetic-lift-fibre-path and lem-wf-strict-henselian-fraction-inertia have neither
Lean records nor Mathlib matches in the shared snapshot; no nonexistent module is imported.
They are needed only for the future proof, whose eight-step plan remains in the docstring.

Edge cases checked: `U₀ = ⊤` has no boundary point `s` and is consistently excluded by `hs`;
an empty open is excluded exactly by `hU`. Degree one is included, as are all positive
residue degrees. The statement concerns every automorphism, with no restriction to integer
Frobenius powers. The algebraic closure may have positive characteristic and is not
replaced by a separable closure. The base-point field may be a proper extension of `k`.
All paths satisfying the defining transport formula are covered. Both sides of the final
equality are bundled subgroups, not merely an inclusion of sets. All universes and variables
are explicit; `autoImplicit` is disabled. The single scheme universe and small profinite
model convention agree with the recorded decomposition interface.

Searches made:

- `msearch.py ... leanfinder`, query “Surjectivity of the local residue Galois homomorphism
  and compatibility with the arithmetic projection for the decomposition group of a
  boundary point of a curve over a finite field”: eight hits, including `arithFrobAt`,
  `IsFractionRing.stabilizerHom_surjective`, finite polynomial Galois restriction and
  valuation inertia. None states this local-to-global square with this henselized field.
- `msearch.py ... loogle`, query `AlgEquiv.restrictScalarsHom, MonoidHom.range_comp`:
  zero hits. Direct source search subsequently found the exact restriction-of-scalars
  homomorphism in `Mathlib/Algebra/Algebra/Tower.lean`, which is reused here.
- `msearch.py ... grep`, query `henselian.*(Galois|residue)|residue.*Galois|restrictScalarsHom`
  in `RingTheory`: zero hits.
- `msearch.py ... leansearch`, query “A local residue Galois map for the henselian fraction
  field at a closed boundary point is surjective and its decomposition homomorphism
  commutes with arithmetic projection”: eight hits on residue-ring quotient maps and
  residue-field functoriality; none states the node.
- `rg` of `WeilConjectures`, `lean/Sheaf`, Mathlib and `dag/lean_names_upstream.json` for
  the item id, `boundary_local_constants`, `boundaryLocalConstants`, arithmetic projection,
  boundary constants and residue surjectivity found no existing statement. Read the
  upstream `BoundaryConstruction` and searched `BoundaryInertia`: their inertia groups
  use the global function-field closure and do not state this henselian local square.
- Read the blueprint boundary definition and first proof paragraph, and Stacks
  `pione.tex`, lemmas `identify-inertia` and `structure-decomposition-separable-closure`.

No statement correction, new node, dependency repair, or mathematical dispute is needed.
Validation: `scompile.py Q08 lem-real-boundary-local-constants` compiled the sandbox
module and its library-path probe cleanly, with no errors or warnings (29.3 s and
5.6 s respectively). `deliver2.py Q08 lem-real-boundary-local-constants --no-push`
reported `OK (dry run): commit ab442fb927 passes the preflight and compiles; nothing pushed`.
The report was then updated with these results before final delivery; the Lean and node
files are unchanged from that passing dry run.

## Second reading by Q08

Replaced by the maintainer's reviewer: the delivered section was an author's self-check
(H11). This reading was made with the node, the source place, the dependency records and
`lean/Sheaf/Paper/RealBoundaryLocalConstants.lean` open. No Lean or node change was needed.

Objects and hypotheses of the node, with their Lean and verdict:

- Curve `C₀/k₀` of d-real-setup, fixed closure `k`: `D : Setup`, `C₀`, its `Over` instance,
  `hC : D.IsCurve C₀` (nonempty, separated, smooth, finite type, pure dimension one,
  connected `D.geometricCurve C₀`). Exact.
- Nonempty open `U₀` with finite complement `S₀`, `s ∈ S₀`: `U₀ : C₀.Opens`, `hU`, `hS`,
  `hs : s ∉ U₀`. Exact; the open immersion `j` is `U₀.ι`.
- `k_s = κ(s)` over `k₀`: `C₀.residueField s`, its algebra structure pinned by `hks` to the
  structural `residueFieldAlgebraMap`. Exact.
- `K_s = Frac(O^h_{C₀,s})` with def-weil-pbc-henselization-at-prime: `H`, `hH :
  Algebra.IsHenselizationAtPrime'` at the maximal ideal of the actual stalk, the stalk and
  localization towers, `K` with `IsFractionRing H K` and the stalk tower. `IsDomain H` is a
  property of the actual henselization of the regular (normal) local stalk, needed to form
  `Frac`; it is the same binder as in the recorded landing theorem. Exact.
- `es`, `hes`: the residue identification `κ(H) ≅ k_s`, determined by `hes` because the
  stalk's residue map is surjective. No choice added.
- `K̄_s`: `Ω` algebraically closed and algebraic over `K`. `integralClosure H Ω` local with
  local structure map, and `a`, `ha` (restriction, determined pointwise) are the
  presentation data of the landing/residue-action interface. Exact.
- Compatible closure of `k_s` identified with `k` over `k₀`: the `k_s`-algebra structure of
  `D.k` with `IsScalarTower D.k₀ k_s D.k` is the embedding of `k_s` as the unique subfield
  with `|k_s|` elements; `IsAlgClosure k_s D.k` is derivable, not stronger. `e`, `he`
  identify the residue field of the integral closure with `D.k` over `k_s`; through `hes`,
  `hks` and the tower, `he` also makes it a map over `k₀`. Exact.
- `r_s : D_s → G_s` of the landing node: `r` into `D.k ≃ₐ[k_s] D.k`, fixed by `hr` on every
  element of the integral closure (reduction is surjective and `e` bijective, so `r` is
  unique). Exact.
- Geometric base point `ū` on `U₀ ×_{k₀} k`: `Ωu` separably closed, `b`, with `u₀`, `hu₀`
  its image in `U₀` and `i`, `hi` its constants map; `i` is a `k₀`-map by the pullback
  square, so `i ∘ μ` satisfies the `baseRingHom` condition of `fiberConstantCoverEquiv`.
- Decomposition homomorphism from any étale path: `γ` an arbitrary isomorphism of fibre
  functors (def-real-boundary-decomposition-path), `G₀`, `e₀` the small model of
  `Aut (fiber u₀)` as in the landing theorem, `θ` constrained by `hθ`, which is verbatim the
  landing formula `θ(σ)_P = γ_P ∘ a_{σ,P} ∘ γ_P⁻¹` with `a_σ(z) = z ∘ Spec σ`. `hθ`
  determines `θ` (e₀ injective, every component given), so no continuity binder is needed.
- Arithmetic projection `p` of def-wf-weil-group: upstream gives only
  `constantCoverAction` into permutations of constant-cover fibres; `hp` says `g` acts on
  `Hom_{k₀}(A, Ωu) = i ∘ Hom_{k₀}(A, k)` by postcomposition with `p g`. This is the
  convention of upstream `arithmeticFrobenius` (postcomposition with `x ↦ x^q`) and of
  `weilGroup`/`geometricFrobenius`, so `g ∈ W` with degree `n` iff `p g = F^n`. Every
  `k₀`-embedding of a finite étale algebra into `Ωu` lands in the algebraically closed
  `i(k)`, so `hp` determines `p` uniquely, and such `p` exists. Not arbitrary.
- `ι_s`: `AlgEquiv.restrictScalarsHom D.k₀`, identity on underlying maps. Exact.

Conclusions: `Module.Finite D.k₀ k_s` and `0 < finrank` (finite of positive degree);
`Function.Surjective r`; `p.comp θ = (restrictScalarsHom D.k₀).comp r` (the square, for
the arbitrary path); equality of the subgroups `(p.comp θ).range` and the range of `ι_s`
(that is, `Gal(k/k_s)` inside `Gal(k/k₀)`). All four clauses, none weakened or strengthened.
Sign check: for `σ ∈ D_s`, writing local fibre points as `t ∘ λ`, `a_σ` is postcomposition
by `r σ`; `γ` restricted to constant covers is postcomposition by some `τ ∈ Gal(k/k₀)`
by naturality, and `Gal(k/k₀)` is abelian, so `θ σ` acts as `r σ`, matching `hp`.

Edge cases: `U₀ = C₀` (no `s`, excluded by `hs`), empty `U₀` (excluded by `hU`), residue
degree one, every characteristic `p`, `Ωu` a proper extension of `k`, every path. All
hypotheses are jointly satisfiable in the source situation (generic point of `Spec H` maps
to the generic point of `C₀`, which lies in `U₀`, giving `ξ`; `U₀` connected gives `γ`; the
landing theorem gives `θ`). Universes: one scheme universe `u`, `v` only through `D`; no
variable unbound (`autoImplicit` false).

Searches: grep of `lean/Sheaf` and `WeilConjectures` for a Galois-valued arithmetic
projection (`arithmeticProjection`, `→* (… ≃ₐ[k₀] …)`) and other users of
`fiberConstantCoverEquiv`: none; the worker's leanfinder, loogle, grep and leansearch
records stand. Compile: `nt_compile.py --json` on the module, rc 0, no diagnostics;
an error probe confirmed that diagnostics are reported. Mismatches found: none in the Lean
or the node; only this section was rewritten.
