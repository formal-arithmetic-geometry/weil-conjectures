## Worker report

The module `Sheaf/Paper/TraitNearbyBaseChange.lean` states
`AlgebraicGeometry.OrientedNearbyCycles.trait_nearby_base_change`.  It does not define a
new notion: the conclusion reuses the dependency definition
`AlgebraicGeometry.OrientedNearbyCycles.IsPsiGood` from
`Sheaf.Paper.OrientedNearbyCycles`.

The Lean statement is:

```lean
theorem trait_nearby_base_change
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (m : ℕ) (hm : 1 ≤ m)
    (Λ : Type v) [CommRing Λ] [Finite Λ]
    (hmΛ : ∀ x : Λ, m • x = 0) (hm_unit : IsUnit (m : R))
    (T : Scheme.{u}) (f : T ⟶ Spec (.of R))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (L : EtaleDerived T Λ)
    (hL : IsBounded (etaleDatum T) (Coeff Λ) L) :
    IsPsiGood f Λ L :=
  by sorry
```

The binders render the source clause by clause.  `R` with `[CommRing R]`, `[IsDomain R]`,
and `[IsDiscreteValuationRing R]` is the discrete valuation ring (Mathlib's DVR class
includes the local principal-ideal valuation structure); `Spec (.of R)` is the base
`B`.  `m : ℕ` and `hm : 1 ≤ m` encode the integer (m\geq1).  `Λ` is a finite
commutative ring through `[CommRing Λ] [Finite Λ]`; `hmΛ` is exactly (mΛ=0), written
pointwise as `m • x = 0`.  `hm_unit : IsUnit (m : R)` says that (m) is invertible on
`Spec R`.  `T` and `f : T ⟶ Spec (.of R)` are the source scheme and its structure map;
`[LocallyOfFiniteType f] [QuasiCompact f]` are Mathlib's two classes making `f` of finite
type, matching `def-weil-finite-type-morphism`.  `L : EtaleDerived T Λ` is the underlying unbounded étale derived object, and
`hL : IsBounded (etaleDatum T) (Coeff Λ) L` states exactly the source's
`L ∈ D^b(T_Et, Λ)` clause.  The conclusion `IsPsiGood f Λ L` expands to
`∀ B' g, IsIso (baseChange ... )`, i.e. for every `g : B' ⟶ Spec (.of R)` the canonical
map `v^* RΨ_f L ⟶ RΨ_{f'} h^* L` is an isomorphism, with `T'`, `h`, `f'`, and `v`
being the canonical pullback data in `OrientedNearbyCycles.IsPsiGood`.  No flatness,
properness, or smoothness class is added.

Dependencies used:

* `def-trf-oriented-nearby-cycles`: module `Sheaf.Paper.OrientedNearbyCycles`,
  declaration `AlgebraicGeometry.OrientedNearbyCycles.IsPsiGood` (and the abbreviations
  `EtaleDerived` and `baseChange` used by its type).
* `def-weil-finite-type-morphism`: Mathlib module
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, declarations
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`.

Edge cases checked: `m = 1` (the torsion hypothesis forces the zero coefficient ring,
while `IsUnit (1 : R)` is automatic); zero complexes and zero coefficient objects are
allowed; boundedness is explicit through `hL`; no nonemptiness of `T` or of the trait is imposed; the identity base change is
included by the universal quantifier in `IsPsiGood`; arbitrary, including non-flat, base
changes `g` are included; the finite-type assumptions are only the two recorded Mathlib
classes.  Independent universes `u` and `v` are retained, while `T` and `Spec R` share
`u` as required by `IsPsiGood`.

Searches made:

* `msearch.py ... leanfinder "nearby cycles over a discrete valuation ring commute with arbitrary base change"` — eight Mathlib hits, all generic valuative criterion or sheaf pushforward/pullback declarations; no nearby-cycle theorem.
* `msearch.py ... loogle "IsPsiGood, IsDiscreteValuationRing"` — zero hits (`IsPsiGood` is project-specific).
* `msearch.py ... grep "nearby.*baseChange|IsPsiGood|trait_nearby" Mathlib` — zero hits.
* `rg` over `WeilConjectures/` and project `lean/Sheaf/` found only the defining
  `OrientedNearbyCycles.IsPsiGood` and no trait base-change theorem.
* The dependency modules and declarations were read in full, including the complete
  `IsPsiGood` definition and the Mathlib finite-type class records.

Compilation with `scompile.py Q116 lem-trf-trait-nearby-base-change` succeeded with no
errors or warnings (the expected `sorry` warning is suppressed by the module option).

## Second reading by Q116

The group did not do a second reading (2026-10-17 workflow). This reading was done in its place by the
maintainer's independent reviewer (NT-cc, stage-2 review of ef08d9fd7706), with the node, its
dependencies and the module open.

Node clauses against the Lean:

1. $R$ is a DVR (a local PID of dimension one): `[CommRing R] [IsDomain R] [IsDiscreteValuationRing R]`.
   Mathlib's class extends `IsPrincipalIdealRing R` and `IsLocalRing R` and requires `maximalIdeal R ≠ ⊥`.
   That is exactly a local PID that is not a field. Matches.
2. $B=\operatorname{Spec}R$: `Spec (.of R)` in `Scheme.{u}`. Matches.
3. $\Lambda$ is a finite commutative ring: `(Λ : Type v) [CommRing Λ] [Finite Λ]`. Its universe `v` is
   independent. Matches.
4. An integer $m\ge1$ with $m\Lambda=0$ that is invertible on $B$: `m : ℕ`, `hm : 1 ≤ m`,
   `hmΛ : ∀ x : Λ, m • x = 0`, `hm_unit : IsUnit (m : R)`. Since $\Gamma(B,\mathcal O_B)=R$, this is
   invertibility on $B$. `hm` follows from `hm_unit` because R is a domain, so it is harmless and not
   stronger. Matches.
5. $f:T\to B$ is of finite type [def-weil-finite-type-morphism]: `[LocallyOfFiniteType f] [QuasiCompact f]`,
   the node's recorded Mathlib rendering. Nothing more is assumed (no flatness, separatedness, properness
   or smoothness). Matches.
6. $L\in D^b(T_{\mathrm{Et}},\Lambda)$: `L : EtaleDerived T Λ` and `hL : IsBounded (etaleDatum T) (Coeff Λ) L`.
   These are the dependency's own derived category and bounded predicate (`isBounded_iff`: cohomology is zero
   outside a finite interval). Matches.
7. Conclusion: $(f,L)$ is $\Psi$-good, i.e. for every $g:B'\to B$ the comparison
   $v^*R\Psi_fL\to R\Psi_{f'}h^*L$ is an isomorphism. This is `IsPsiGood f Λ L`, which is
   `∀ B' g, IsIso (baseChange f (pullback.snd f g) (pullback.fst f g) g pullback.condition Λ L)`, the
   counit-transpose comparison of def-trf-oriented-nearby-cycles. The quantifier and its order are the
   node's. Matches.

Edge cases: when `m = 1`, Λ is the zero ring. T may be empty, and L may be zero. The identity base change
and non-flat base changes are both included in the ∀. Universes: T, B and B' share `u`, as `IsPsiGood`
requires, and Λ has its own `v`. No variable or universe is left unbound.

Searches: rg over lean/Sheaf finds `IsPsiGood` only in its defining module, and finds no trait or DVR
base-change theorem for nearby cycles. The worker's Mathlib searches found no nearby-cycle notion.

Source: Lu–Zheng Example 4.26(2), case (a) (arXiv 1712.10216v7, p. 37). The source proves the statement for
any valuation ring and L ∈ D⁺. The node is the special case of a DVR, finite Λ, finite-type f and D^b, so
the node is no stronger than the source.

Compile: the server's per-file compile `nt_compile.py` gives a clean result, with no error and no warning.

No mismatch was found, and the module and node record are unchanged.
