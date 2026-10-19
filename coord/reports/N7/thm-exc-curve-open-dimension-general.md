## Worker report

States `AlgebraicGeometry.Etale.isZero_higherDirectImage_of_open_curve` in
`Sheaf.AlgebraicGeometry.CurveOpenDimensionGeneral`. The sole theorem has proof `sorry`.
No definitions, new nodes, or statement corrections are needed. The item node changes only
in `lean`. The previous worker had left no statement files: being split and reviewed in
stage 1 does not supply a stage-2 Lean record.

The source statement and its three proof paragraphs were read from the server copy of
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/`
`thm-exc-curve-open-dimension-general.md` (the literature is not populated in this local
read-only clone). They agree with the DAG. The theorem docstring carries all eight expanded
DAG proof steps, including scalar forgetting, empty strict-local opens, reduction,
branch-field comparisons, and geometric-stalk conservativity.

Each hypothesis and clause is rendered as follows:

| Node clause | Lean |
| --- | --- |
| k is a field | `(k : Type u) [Field k]` |
| k is finite or an algebraic closure of a finite field | `hk : Finite k ∨ ∃ k₀ : Subfield k, Finite k₀ ∧ IsAlgClosure k₀ k` |
| T is a scheme over k | `{T U : Scheme.{u}} [T.Over (Spec (.of k))]` |
| finite type over k | `[LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]` |
| topological Krull dimension at most one | `hdim : topologicalKrullDim T ≤ 1` |
| any open immersion j from U to T | `(j : U ⟶ T) [IsOpenImmersion j]` |
| finite commutative coefficient ring A | `(A : Type (u + 1)) [CommRing A] [Finite A]` |
| prime ell | `(ℓ : ℕ) (hprime : ℓ.Prime)` |
| ell invertible on T | `hinv : IsUnit (ℓ : Γ(T, ⊤))` |
| A killed by a power of ell | `hkill : ∃ n : ℕ, (ℓ ^ n : ℕ) • (1 : A) = 0` |
| arbitrary etale A-module sheaf M on U | `M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)` |
| every integer q greater than one | `(q : ℤ) (hq : 1 < q)` |
| R^q j_* M is zero | `IsZero` of `DerivedCategory.Plus.homologyFunctor _ q` applied to `rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) j` applied to `DerivedCategory.Plus.singleFunctor _ 0` of M |

The algebraic-closure alternative introduces a finite subfield, not an additional chosen
structure on k: any algebraic-closure embedding of a finite field identifies that field
with its image subfield of k. Conversely `IsAlgClosure k₀ k` says exactly that k is an
algebraic closure of the finite field k₀. `Subfield` and `IsAlgClosure` are Mathlib notions.
Killing 1 by ell^n is equivalent to killing every element of the unital ring A, and hence
every A-module, by that integer. An integer is invertible on a scheme precisely when its
global section is a unit: its local inverses uniquely glue. This works for empty schemes too.

Dependency declarations read and used:

- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and `AlgebraicGeometry.QuasiCompact`
  in `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` (reexported by FiniteType).
- `def-kun-topological-krull-dimension`: `topologicalKrullDim` in
  `Mathlib.Topology.KrullDimension`, defined as `Order.krullDim (IrreducibleCloseds T)`.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion` in
  `Mathlib.AlgebraicGeometry.OpenImmersion`, the open-immersion predicate for underlying
  locally ringed spaces.
- `def-weil-pbc-etale-sheaves`: `CategoryTheory.Sheaf`, `Scheme.smallEtaleTopology`, and
  `ModuleCat`, using exactly the ModuleCat encoding authorized in this dependency's record
  for six-functor statements, with coefficient universe u+1. The recorded
  `WeilConjectures.AlgebraicGeometry.EtaleSheaves` module is publicly imported. The extra
  locally constant/constructible predicates in that mixed node are not assumptions here.
- `def-weil-pbc-direct-image`: `AlgebraicGeometry.Etale.lowerStar` from
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` and
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus` from its actual defining module
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`, publicly imported
  (it reexports lowerStar). The recorded direct-image module names lowerStar correctly;
  the bounded-below derived functor is in the latter module in the current source.
  Both full signatures and docstrings were read. The Plus single/homology functors are
  the existing degree-zero embedding and degree-q cohomology functor.

All recorded proof-dependency modules are imported, along with
`Mathlib.AlgebraicGeometry.Noetherian` for the two Mathlib-only Noetherian dependencies.
The unstated proof lemmas (excellence, punctured branches, and DVR Galois cohomology) are
only named in the proof plan; they introduce no notion needed to type this statement.

Edge cases checked: empty T and U (dimension bottom is allowed, invertibility is a unit
in the zero global ring); U empty with T nonempty; j the identity; isolated points and
zero-dimensional schemes; reducible and nonreduced schemes; a non-dense open; the zero
coefficient ring (n=0 is allowed and forces 1=0); any positive prime characteristic;
q=2 and all higher integers; arbitrary, possibly infinite and nonconstructible M.
No connectedness, smoothness, reducedness, density, torsion-on-M, or finiteness-on-M
hypothesis has been added. All variables and the universe are explicitly bound.

Searches made (prescribed msearch.py, recorded in searches.jsonl):

- LeanFinder: “For an open immersion into a curve over a finite field or its algebraic
  closure, higher etale direct images of finite prime power torsion module sheaves vanish
  above degree one”. Eight hits about etale loci and etale morphisms; none states the theorem.
- Loogle: `"rightDerivedLowerStar"`. No hits.
- Mathlib grep: `curve.*(dimension|vanish)|isZero.*[Ll]owerStar`. Only an unrelated
  Weierstrass discriminant hit.
- LeanSearch: “Higher etale direct images under an open immersion into a curve vanish in
  degree greater than one”. Service unavailable (Internal Server Error); this is recorded in searches.jsonl.
- Direct rg of the upstream WeilConjectures tree for the node id, prospective declaration
  name, curve-open naming, and higher-image/derived pushforward names found the canonical
  derived functors and related results, but no statement of this theorem.
- Direct rg of lean/Sheaf and dag/lean_names_upstream.json found related specialized
  higher-image statements and no occurrence of the node id or prospective theorem name.
  In particular the G_m curve-boundary theorem treats different coefficients/degrees.

No mathematical statement dispute. Initial compilation through scompile.py succeeded
without errors or warnings. The prescribed delivery dry run validates the final packet.

## Second reading by N7

I independently read the node statement, its Stacks/blueprint source place, and
`Sheaf/AlgebraicGeometry/CurveOpenDimensionGeneral.lean` item by item.

- The field is rendered by `(k : Type u) [Field k]`; the finite-field or algebraic-closure
  alternative is exactly `hk : Finite k ∨ ∃ k₀ : Subfield k, Finite k₀ ∧ IsAlgClosure k₀ k`.
- The scheme and its base are rendered by `{T U : Scheme.{u}} [T.Over (Spec (.of k))]`.
  Finite type over the field is the pair of recorded dependency instances
  `[LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]`.
- The dimension hypothesis is exactly `(hdim : topologicalKrullDim T ≤ 1)`.
- The arbitrary open immersion is exactly `(j : U ⟶ T) [IsOpenImmersion j]`; no density,
  separatedness, reducedness, or connectedness condition is added.
- The coefficient datum is exactly `(A : Type (u + 1)) [CommRing A] [Finite A]`, followed by
  `(ℓ : ℕ) (hprime : ℓ.Prime)`, invertibility `hinv : IsUnit (ℓ : Γ(T, ⊤))`, and the
  power-killing condition `hkill : ∃ n : ℕ, (ℓ ^ n : ℕ) • (1 : A) = 0`.
- The arbitrary coefficient sheaf is exactly
  `M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)`.
- The quantifier is exactly `(q : ℤ) (hq : 1 < q)`, and the conclusion is `IsZero` of
  `DerivedCategory.Plus.homologyFunctor _ q` applied to
  `rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) j` applied to
  `DerivedCategory.Plus.singleFunctor _ 0` of `M`, matching (R^q j_*M=0).

No mismatch was found and no source or node correction was needed. The statement keeps
all universes explicit and has no hidden variables (`set_option autoImplicit false`). The
empty scheme and empty open are included; the zero coefficient ring and exponent `n = 0`
are allowed; the identity immersion, non-dense opens, reducible/nonreduced schemes, any
positive characteristic, and all integers `q > 1` are included. No finiteness or
constructibility is imposed on `M`.

I searched the Mathlib tree, the upstream `WeilConjectures` tree, `lean/Sheaf`, and the
DAG name index with alternate direct-image, cohomology, and curve-dimension queries; no
existing declaration states this theorem. LeanFinder found only unrelated etale-locus
results, Loogle found no matching direct-image theorem, and LeanSearch was unavailable.
The recorded dependency declarations were opened and agree with the uses in the module.
The module compiled cleanly with the prescribed `scompile.py`; the only proof placeholder
is the required theorem `sorry`.
