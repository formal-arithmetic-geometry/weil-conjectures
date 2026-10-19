## Worker report

The module `Sheaf.RingTheory.UniformPerfectQuotientBound` states the common finite-projective
resolution bound and its Tor formulation. Both declarations have `sorry` proofs; there are
no new definitions and no proved statements. The first declaration gives both bounds with
one witness `r`. The second states the equivalence of the uniform resolution and Tor bounds
for any fixed `r`, making the node's equivalence clause explicit.

Clause-by-clause match:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Commutative Noetherian ring A | `{A : Type u} [CommRing A] [IsNoetherianRing A]` |
| Ideal I | `(I : Ideal A)` |
| Each integer n ≥ 1 | `∀ n : ℕ, 1 ≤ n →`; positive natural numbers are precisely these integers |
| P_n = A/I^n | `ModuleCat.of A (A ⧸ I ^ n)` with the canonical quotient A-action |
| Finite as a set | `hfinite : ∀ n : ℕ, 1 ≤ n → Finite (A ⧸ I ^ n)` |
| Degree-zero complex perfect | `hperfect` applies `DerivedCategory.IsPerfect` to `(DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A (A ⧸ I ^ n))` |
| One integer r ≥ 0, independent of n | Outer `∃ r : ℕ`, preceding `∀ n` |
| Resolution of each P_n | `P : ProjectiveResolution (ModuleCat.of A (A ⧸ I ^ n))`; its fields supply a projective chain complex and quasi-isomorphic augmentation to the degree-zero module |
| Finitely generated terms | `∀ i : ℕ, Module.Finite A (P.complex.X i)` |
| Projective terms | `ProjectiveResolution.projective`; the recorded `Module.Projective` agrees with categorical projectivity via `ModuleCat.IsProjective.iff_projective` |
| Cochain degrees [-r,0] | `∀ i : ℕ, r < i → IsZero (P.complex.X i)` in a natural-number chain complex; reindex homological i as cochain -i |
| Every A-module M | `∀ M : ModuleCat.{u} A`, without finite generation or nonzero assumptions |
| Derived tensor has cohomology only in [-r,0] | `∀ i : ℕ, r < i → IsZero (((Tor' (ModuleCat.{u} A) i).obj (ModuleCat.of A (A ⧸ I ^ n))).obj M)`; these are precisely H^{-i} of the tensor resolution, which has no positive cochain terms |
| Same bound | The Tor conjunct uses the same outer `r` as the resolution conjunct |
| Equivalence | The second declaration is an `↔` between the uniform finite-resolution and uniform Tor-vanishing predicates for the identical `(r : ℕ)` |
| Zero quotient allowed | No `Nontrivial` condition on A or a quotient |

`[HasDerivedCategory.{u} (ModuleCat.{u} A)]` records the ambient derived-category model used by
the dependency's `IsPerfect`; it is the standard available construction, not a mathematical
restriction on the ring. All universes and variables are explicit. The one universe `u`
contains the ring, quotients, resolution terms, and arbitrary test modules, matching the
recorded perfect-complex and Tor-bound interfaces. No independent smaller test universe is used.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.Ideal.Operations` and `Mathlib.RingTheory.Ideal.Quotient.Operations`:
  ideal powers, `Ideal.Quotient`, and `Ideal.Quotient.algebra` for the A-action.
- `WeilConjectures.CategoryTheory.DerivedCategory.Perfect`: `DerivedCategory.IsPerfect`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.Algebra.Module.Projective`: `Module.Projective`, identified with projectivity of
  module-category objects by `Mathlib.Algebra.Category.ModuleCat.Projective`,
  `ModuleCat.IsProjective.iff_projective`.
- `Mathlib.CategoryTheory.Monoidal.Tor`: `CategoryTheory.Tor'`, derived in the first variable.
- `Mathlib.CategoryTheory.Preadditive.Projective.Resolution`: `ProjectiveResolution` and
  its `complex`, `projective`, `π`, and `quasiIso` fields.

The proof-only imports follow every stated proof dependency: localization at a prime,
module localization and exactness, localization of projectives, depth, Auslander–Buchsbaum,
local-global projective dimension, resolution/Ext characterization, projective syzygies,
and the finite-module Tor-bound criterion. Their recorded modules are imported without
`public`. No proof dependency requires an import cycle or an omitted import.

Edge cases checked: for I = A every quotient is the zero module, for which the zero
resolution works with r = 0. The zero ring is included. For I = 0, the hypotheses demand
finiteness of A and the quotient is A, with its length-zero projective resolution.
For r = 0 the support condition kills exactly the positive homological degrees and the
Tor condition kills exactly positive Tor. For n = 1 the quotient supplying the proof's
initial common bound is included. No n = 0 hypothesis or conclusion is imposed. There
is no dimension, locality, nonzero, or characteristic restriction.

Searches performed (2026-10-15):

- `msearch.py ... leanfinder "Uniform bound on finite projective resolutions of finite perfect quotients by ideal powers"`:
  eight hits, including `HasProjectiveDimensionLT/LE`, `Ideal.finite_quotient_pow`, adic
  completion lemmas and local cohomology; no uniform projective-resolution theorem.
- `msearch.py ... loogle '"projectiveDimension"'`: twelve hits for generic projective dimension
  predicates and bounds; none is this uniform ideal-power-quotient statement.
- `msearch.py ... grep 'uniform.*(perfect|projective)|quotient.*bound'`: eight unrelated
  quotient dimension, topology, p-adic and ideal norm hits; no match.
- `rg -n 'uniform.*(perfect|projective)|uniform_perfect|lem-weil-pbc-uniform-perfect-quotient-bound'`
  in the source `WeilConjectures` and project `lean/Sheaf` trees: only unrelated global
  dimension, relative tensor and adic trace text; no declaration for this node.
- Searched `dag/lean_names_upstream.json` for both proposed theorem names: no match.

Read the source's `proposition-Auslander-Buchsbaum` in `literature/stacks-project/algebra.tex`:
its local Noetherian, nonzero finite-module and finite-projective-dimension assumptions
are exactly those checked in the node's localized argument. The uniform statement is the
node's explicitly identified assembly, not a misquotation of Tag 090V.

Validation: the server single-file compiler accepted this module with no warnings or errors
(1.5 seconds, nice 19, two threads, 60-second limit). The dry delivery check printed OK: server compilation and preflight passed except for
the independent second-reading section, which the second reader supplies. No node correction, new node, unusable dependency, or
STATEMENT-DISPUTED issue was found.


## Second reading by NA

Independent reading of the node, both theorem signatures, and the cited source on
2026-10-15. No mathematical mismatch found; no Lean or node change was needed.
The only delivery change is this second-reading report and its independent validation.

Objects, hypotheses, and conclusions, listed before comparison:

| Node item | Lean rendering and verdict |
| --- | --- |
| A commutative Noetherian ring, with no locality or dimension condition | `{A : Type u} [CommRing A] [IsNoetherianRing A]`: exact. Read `IsNoetherianRing` and `isNoetherianRing_iff_ideal_fg` in Mathlib. |
| An arbitrary ideal I of A | `(I : Ideal A)`: exact; no properness assumption. |
| For every integer n at least 1, P_n is A/I^n | `∀ n : ℕ, 1 ≤ n →` and `ModuleCat.of A (A ⧸ I ^ n)`: exact positive-integer indexing and canonical A-module quotient. Read `Ideal.Quotient.algebra` and the quotient dependency's Mathlib match; the node has no Lean record but is a usable Mathlib leaf. |
| Every P_n has finite underlying set | `hfinite : ∀ n : ℕ, 1 ≤ n → Finite (A ⧸ I ^ n)`: exact, not merely finite generation. |
| Every degree-zero P_n is perfect | `hperfect` with `DerivedCategory.IsPerfect ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj ...)`: exact. Opened upstream `Perfect.lean`: its definition is existence of a bounded cochain complex with every term `Module.Projective` and `Module.Finite`, isomorphic to the given derived object. |
| A single nonnegative integer r, independent of n | `∃ r : ℕ` outside both universal n binders: exact. Natural numbers encode precisely the requested nonnegative integers. |
| A projective resolution of each P_n | `∃ P : ProjectiveResolution (ModuleCat.of A (A ⧸ I ^ n))`: exact. Opened the structure: a natural-number chain complex, degreewise projectivity, augmentation to `single₀`, and a quasi-isomorphism. This supplies exactness and the quotient augmentation, not just a complex of projectives. |
| Every term is finitely generated projective | Projectivity is `P.projective`; finite generation is `∀ i : ℕ, Module.Finite A (P.complex.X i)`: exact. Read `Module.Finite` and `ModuleCat.IsProjective.iff_projective`; the latter equates categorical and module projectivity with `Small` automatic at these universes. |
| Cochain support [-r,0] | `∀ i : ℕ, r < i → IsZero (P.complex.X i)`: exact under homological i = cochain -i. There are no negative homological terms, hence no positive cochain terms. `IsZero` is applied to module-category objects, not bare types. |
| Every A-module M and derived-tensor cohomology only in [-r,0] | `∀ (M : ModuleCat.{u} A) (i : ℕ), r < i → IsZero (((Tor' ... i).obj ...).obj M)`: exact using the node's explicit Tor formulation. Opened `Tor'`: it left-derives tensoring in the first argument, so this resolves P_n, exactly as specified. Positive cochain degrees vanish automatically for these degree-zero inputs. |
| Same r and equivalence of formulations | Both conjuncts of the first theorem share the existential r. The second theorem gives `↔` for each fixed `(r : ℕ)` under the identical hypotheses: exact, not a separate unrelated bound. |
| Zero quotients are allowed | No `Nontrivial` or nonzero quotient binder: exact. |

Source check: read `proposition-Auslander-Buchsbaum` in `algebra.tex` at Tag 090V,
including its surrounding section. It assumes a Noetherian local ring and a nonzero
finite module of finite projective dimension. These are requirements on the localized
applications in the node's proof, not extra global hypotheses. The node explicitly
labels its uniform theorem an assembly; neither the module nor report treats 090V as
literally asserting uniformity. The seven numbered proof steps in the first docstring
follow the node: cancellation, localization, depth zero, two applications of
Auslander–Buchsbaum, local-global projective dimension, finite shortening, and tensor.
The second docstring includes the converse Tor criterion and finite shortening.

Edge cases: I = top and the zero ring give zero quotients and allow zero resolutions
with r = 0. I = bottom gives A itself; the finiteness hypothesis then requires A finite,
and a degree-zero free resolution suffices. n = 1 is included and provides the initial
bound; n = 0 is intentionally outside both hypotheses and conclusions. r = 0 kills
exactly positive chain degrees and positive Tor. No characteristic condition is imposed.
There is no arbitrary index set or scheme in this statement, so empty families and
empty schemes introduce no additional case. The module fixes an arbitrary universe u,
with A, its quotients, projective terms, and test modules in the same module-category
universe as the recorded IsPerfect/Tor interfaces. There is no independently smaller
test universe. `HasDerivedCategory.{u}` is the standard ambient construction required
by the dependency signature, not a finiteness or ring-theoretic restriction. All
variables/universes are bound explicitly.

Independent searches used different wording from the worker:

- LeanFinder: "Projective dimensions of finite cardinal ideal-power quotients are
  uniformly bounded when each is perfect". Eight generic projective-dimension hits;
  no uniform ideal-power theorem.
- Loogle: `"HasProjectiveDimensionLE"`. Eleven hits, including the maximal-localization
  criterion and generic finite-resolution equivalence, but no common-bound theorem.
  An initial `"Tor" "Ideal"` query was rejected by the search parser and was replaced
  by this successful query.
- LeanSearch: "The projective dimensions of the finite perfect modules A/I^n have a
  common bound". Service unavailable (Internal Server Error); no mathematical verdict
  is inferred from that search.
- Direct `rg` across Mathlib, upstream WeilConjectures and this project's lean/Sheaf:
  `quotient_pow.*(projective|perfect)|projective.*quotient_pow|uniform.*resolution|uniform.*Tor|uniform.*projective`.
  Only unrelated global dimension, integral-coefficient, and relative-Tor material.
  Opened `GlobalDimensionFiniteModules.lean`: it concerns global dimension for all
  cyclic quotients, not this family of finite perfect ideal-power quotients.

No new definition nodes, dependency modules, private notions, hollow definitions, or
statement corrections occur in this delivery. Both theorem bodies are exactly `sorry`.
Source/blueprint docstrings are present, and the recorded `lean.statement` was checked
by literal substring comparison against the first signature and is verbatim equal.
