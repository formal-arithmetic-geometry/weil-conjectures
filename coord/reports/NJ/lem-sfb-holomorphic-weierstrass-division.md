## Worker report

Item: `lem-sfb-holomorphic-weierstrass-division`; group NJ; stage 2.

The module `Sheaf.Analysis.Complex.HolomorphicWeierstrassDivision` states
`Complex.exists_holomorphic_weierstrass_division` with one `sorry`. It supplies two
real helper definitions for the notions explicitly introduced by this node:
`Complex.IsAnalyticAtZeroGerm` and `Complex.linearPullbackAtZeroGerm`. No other
mathematical statement is postponed. The node changes only in `lean`.

Representation of germs: `Filter.Germ (𝓝 0) ℂ` is Mathlib's quotient of functions
by eventual equality at zero. At a neighbourhood filter, eventual equality is
agreement on some open neighbourhood of zero. Every function on an open
neighbourhood extends to a total function, and different extensions define the
same germ. `IsAnalyticAtZeroGerm f` says that `f` has a representative `F` with
`AnalyticAt ℂ F 0`. This uses exactly the dependency's convergent-power-series
notion. Such a representative is analytic throughout a smaller neighbourhood
(the Mathlib change-of-origin theorem), so it represents a holomorphic germ,
and every holomorphic germ supplies such a representative.

The holomorphic germ algebra is expressed as a predicate on the ambient ring of
function germs. This is the same set of objects as the subtype, with membership
hypotheses and conjuncts in place of subtype binders. All arithmetic and equality
in the theorem are Mathlib's existing pointwise ring operations on this quotient.
Closure of holomorphic germs follows from the recorded analytic-operations
statements; no second multiplication, quotient relation, or power-series notion
is introduced. The predicate and pullback helpers belong to this node's explicit
introduction of G_d and its coordinate substitutions; they do not need a separate
missing-notion node.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Complex ground field and d-dimensional coordinate space | `ℂ` and `Fin d → ℂ` with the usual normed complex vector-space structures |
| G_d consists of holomorphic germs at zero | `Germ (𝓝 (0 : Fin d → ℂ)) ℂ` together with `IsAnalyticAtZeroGerm` |
| Germ equivalence is equality on a smaller neighbourhood | Existing `Filter.Germ` equality, characterized by `Filter.Germ.coe_eq` |
| Pointwise operations and scalar multiplication | Existing ring/module operations on `Filter.Germ`; analytic membership restricts to G_d |
| d ≥ 1 | `n : ℕ` and dimension `n + 1`, covering every positive integer dimension |
| f belongs to G_d | The binder `f` and hypothesis `hf : IsAnalyticAtZeroGerm f` |
| f is nonzero as a germ | `hfn : f ≠ 0`, rather than just a nonzero representative function |
| Invertible complex-linear coordinate change | `L : (Fin (n + 1) → ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ)`; finite dimension makes continuity automatic for every linear isomorphism |
| Order k ≥ 0 | `k : ℕ`, existentially bound after f |
| h = f composed with L | `linearPullbackAtZeroGerm L.toContinuousLinearMap f` |
| Last-axis restriction h(0,w) | Pullback along `ContinuousLinearMap.pi` with the identity in coordinate `Fin.last n` and zero in the other coordinates |
| One-variable holomorphic u | `u : Germ (𝓝 (0 : ℂ)) ℂ` and `IsAnalyticAtZeroGerm u`; ℂ is the canonical one-coordinate space |
| u(0) ≠ 0 | `u.value ≠ 0`, using `Filter.Germ.value` |
| h(0,w) = w^k u(w) | Equality of one-variable germs with `Germ.ofFun (fun w : ℂ ↦ w) ^ k * u` |
| Every g in G_d | `∀ g : Germ ..., IsAnalyticAtZeroGerm g → ...`, inside the chosen L,k,u existential |
| A quotient and coefficient family exist uniquely | `∃! qa : Germ ... × (Fin k → Germ ...), ...`; uniqueness is for the pair, hence both q and every coefficient |
| q is holomorphic in all d variables | `IsAnalyticAtZeroGerm qa.1` |
| Each a_j is holomorphic in d-1 variables | `∀ j : Fin k, IsAnalyticAtZeroGerm (qa.2 j)` with transverse domain `Fin n → ℂ` |
| a_j is regarded in G_d by the coordinate projection | Pullback along `ContinuousLinearMap.pi fun i : Fin n ↦ ContinuousLinearMap.proj (R := ℂ) i.castSucc`, which sends x to its first n coordinates |
| Last coordinate w | `Germ.ofFun (fun x : Fin (n + 1) → ℂ ↦ x (Fin.last n))` |
| Division equation g = q h + sum a_j(z) w^j | The final equality, with `qa.1 * ... + ∑ j : Fin k, ... ^ (j : ℕ)` |
| k = 0 has empty remainder | `Fin 0` is empty, so its sum is zero and its coefficient family is unique |
| d = 1 has coefficients in G_0 = ℂ | `n = 0`; `Fin 0 → ℂ` is a singleton, so every germ on it is uniquely a complex constant and is analytic |

The canonical pullback uses `Filter.Germ.compTendsto` along the specified map.
Its filter condition is obtained directly from continuity and `L.map_zero`.
It is independent of representatives, introduces no arbitrary choice and
contains no `sorry`. The analytic-membership predicate is a literal existential
over representatives, so it likewise contains no postponed data or proof.

Dependency declarations read and used:

- `lem-sfb-complex-analytic-function-operations` is a Mathlib node with no Lean
  record, as allowed by the brief. Read its whole statement and `mathlib_match`.
  The declarations are `analyticAt_const`, `AnalyticAt.add`, `AnalyticAt.mul`,
  `AnalyticAt.inv`, and `AnalyticAt.pi` from
  `Mathlib.Analysis.Analytic.Constructions`; `ContinuousLinearMap.analyticAt`
  from `Mathlib.Analysis.Analytic.Linear`; `AnalyticAt.comp` from
  `Mathlib.Analysis.Analytic.Composition`; `AnalyticAt.continuousAt` from
  `Mathlib.Analysis.Analytic.Basic`. The source signatures and adjacent
  docstrings were opened, including the nonvanishing hypothesis on inversion.
  Their modules are public imports; Basic is publicly imported by the others.
- `Filter.Germ`, `Filter.Germ.ofFun`, the ring/module instances,
  `Filter.Germ.coe_eq`, and `Filter.Germ.compTendsto` from
  `Mathlib.Order.Filter.Germ.Basic` supply the quotient, arithmetic, and pullback.
  `Filter.Germ.value` comes from the public import `Mathlib.Topology.Germ`.
- `ContinuousLinearMap.pi` and `ContinuousLinearMap.proj` were read in
  `Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd`.
- The already stated proof dependencies are privately imported:
  `MvPolynomial.funext` from `Mathlib.Algebra.MvPolynomial.Funext`, and
  `isUnit_one_sub_of_norm_lt_one` plus
  `ContinuousLinearMap.isUnit_iff_bijective` from
  `Mathlib.Analysis.SpecificLimits.Normed` and
  `Mathlib.Analysis.Normed.Operator.Banach`. Their signatures were read.
- `lem-sfb-weighted-taylor-banach-model` has no recorded declaration or Mathlib
  match in the read clone. It is a proof dependency, not a statement dependency;
  no unavailable import is fabricated. Its role is recorded in proof steps 1,
  3--6 in the theorem docstring. The maintainer can add its proof import when stated.

Edge cases checked before and after writing:

- Nonzero constant f permits k=0; a nonzero value makes the divisor a unit,
  with unique quotient and the empty coefficient family.
- d=1 is n=0: the transverse coordinate space is the singleton, its coefficients
  are constants, and the transverse projection is the unique map to that space.
- g=0 permits the zero quotient and every coefficient zero; the uniqueness
  assertion still applies and does not assume g nonzero.
- f=w^k has the expected truncation remainder; coefficients of degree below k
  are uniquely determined. A mixed divisor such as w^k+z_1 remains covered.
- A representative nonzero only away from zero has zero germ, so `hfn` correctly
  excludes it. A representative's arbitrary off-neighbourhood values cannot
  affect either the axis identity or the division equation.
- No fixed convergence neighbourhood is imposed on a competing quotient. All
  equations are germ equations, as required by the uniqueness proof.
- The positive dimension parameter excludes only d=0 for the division theorem;
  the coefficient space and the analytic predicate still include dimension zero.
- No hypothesis requires f(0) nonzero: the general k>0 case is retained.

Source checked: [Frenkel, Cartan seminar 1951--52, exp. 10](https://www.numdam.org/item/SHC_1951-1952__4__A10_0.pdf),
Proposition 4 on printed p.5 gives linear regularization; Theorem 1 on pp.2--3
supplies unique formal division; Theorem 1 bis on pp.7--9 supplies convergence.
The module docstring records every step of the node's weighted Banach proof,
including rechoosing radii for uniqueness. No source correction is needed.

Searches for reuse (2026-10-24):

- `msearch.py ... leanfinder`: "Analytic Weierstrass division for holomorphic
  germs after invertible linear coordinate change gives unique convergent quotient
  and polynomial remainder" returned eight formal-power-series hits, including
  `PowerSeries.exists_isWeierstrassDivision` and its uniqueness declarations.
- `msearch.py ... loogle`: `"IsWeierstrassDivision"` returned twelve related
  declarations, all for formal power series over adic rings. Read
  `Mathlib/RingTheory/PowerSeries/WeierstrassPreparation.lean`, including its
  assumptions and main theorem documentation. It does not assert convergence.
- `msearch.py ... leansearch`: "Holomorphic analytic germs at a point form a
  complex algebra of locally convergent power series" returned `AnalyticAt`,
  `HasFPowerSeriesAt`, and their convergence lemmas. It did not return an
  existing analytic germ algebra or the analytic division theorem.
- `msearch.py ... grep`: `analytic.*[Gg]erm|[Gg]erm.*analytic|Weierstrass` in
  `Analysis` returned unrelated Stone--Weierstrass and elliptic-function hits.
  `Weierstrass|convergent.*division` in `RingTheory/PowerSeries` returned five
  lines in the formal Weierstrass module.
- `rg` of the analytic-germ phrases in Mathlib's `Analysis/Analytic` found no
  germ construction. Read the full `Order/Filter/Germ/Basic` germ API and
  `Topology/Germ` value/pullback API rather than inventing a quotient.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for Weierstrass division found
  only proof-plan citations in `AnalyticLocalCompletionComparison` and the
  unrelated affinoid division reference. The item's exact id has no declaration
  in `lean/WeilConjectures`. Analytic germ references in the project describe
  stalks or representatives; none supplies this theorem or a reusable G_d.
- `rg` of all three new full declaration names in Mathlib, the source project,
  `lean/Sheaf`, and `dag/lean_names_upstream.json` returned no existing name.

Validation: prescribed `scompile.py NJ lem-sfb-holomorphic-weierstrass-division`
compiled the sandbox and final module cleanly, with no errors or warnings.
An initial missing public complex-number import was repaired before this success.
No library files or launcher scripts were edited; all authored files are in the sandbox.
No `STATEMENT-DISPUTED` issue, statement correction, new node or dependency repair.

## Second reading by NJ

A separate reading pass by this single worker reopened the node and the finished
Lean file; no sub-agent was started, as the dispatch brief forbids it. Independent
review is left to the maintainer's delivery review.

Checked the ambient-germ membership encoding against all the G_d binders: f and
arbitrary g require analytic membership, u is explicitly analytic and nonzero at
zero, and both components of the unique pair carry the required membership.
The pair's equality forces equality of the entire coefficient function, not just
of its sum. The axis map has only the last coordinate w; the coefficient projection
uses `i.castSucc`, hence removes that coordinate. Multiplication order is q*h,
as in the node. Dimension n+1 and family Fin k preserve d=1 and k=0. The existential
L,k,u is outside the universal g binder, so the same coordinate change and order
work for every dividend. Equality throughout is equality of germs, not a chosen
representative or formal series. The nonvanishing condition is on the germ f,
not on f's value at zero. No mathematical mismatch found and no statement field
changed. The only implementation correction was the missing public complex import.
