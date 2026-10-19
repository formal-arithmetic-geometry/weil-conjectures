## Worker report

The module `Sheaf.RingTheory.DvrLatticeDistanceDeterminant` states
`IsDiscreteValuationRing.lattice_distance_determinant`, with its sole proof `sorry`.
No definition, dependency repair, new node, or statement correction is needed.
The source was read in `literature/stacks-project/algebra.tex`, lines 29803–30039:
Tags 02MD (order), 02MF (comparison of lattices), 02MG (distance), and 02MI
(determinant identity). The node's proof list is empty; the declaration docstring
supplies the full source proof route for stage 3.

Hypothesis and clause correspondence:

- A discrete valuation ring is `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`. Its fraction field is `(K : Type v) [Field K]
  [Algebra R K] [IsFractionRing R K]`.
- The finite-dimensional vector space is `(V : Type w) [AddCommGroup V]
  [Module K V] [FiniteDimensional K V]`. The compatible restricted R-action
  is `[Module R V] [IsScalarTower R K V]`; these express the R-module structure
  inherited through the specified inclusion R → K, without a new mathematical assumption.
- The lattice is `(M : Submodule R V) [Module.Finite R M]`. Its full K-span
  is `hspan : Submodule.span K (M : Set V) = ⊤`.
- The K-linear isomorphism is `(g : V ≃ₗ[K] V)`. Its image lattice is precisely
  `M.map (g.toLinearMap.restrictScalars R)`.
- For H = M ∩ g(M), the submodule H inside M is
  `(M.map (g.toLinearMap.restrictScalars R)).comap M.subtype`.
  Indeed its members are x : M whose value lies in g(M); membership in M is
  already supplied by x's subtype. Inside g(M), H is
  `M.comap (M.map (g.toLinearMap.restrictScalars R)).subtype`.
  Thus the two quotient types are exactly M/H and g(M)/H, using Mathlib's
  submodule quotient, with their canonical R-module structures.
- The first two conjuncts say `Module.length R (M/H) ≠ ⊤` and
  `Module.length R (g(M)/H) ≠ ⊤`, respectively: both lengths are finite.
- The final conjunct casts each `Module.length` through `ENat.toNat` to ℤ
  and takes the difference in the node's order. Because the preceding conjuncts
  exclude infinity, these are the actual finite lengths, with signed subtraction.
- The determinant is the recorded `LinearMap.det g.toLinearMap`.
  Its normalized valuation is `WithZero.log (Ring.ordFrac R ...)`.
  Mathlib's `Ring.ordFrac_irreducible` makes a uniformizer's order `WithZero.exp 1`;
  `WithZero.log_exp` reads this as integer 1. `Ring.ordFrac_of_isUnit` gives value 0
  on R-units, and multiplicativity gives the integer exponent for u t^r.
  The determinant is nonzero because g is an automorphism, so the totalization
  of `WithZero.log` at zero is never involved. This agrees with the convention
  in the existing `Sheaf.RingTheory.DvrNormValuationSum` consumer.

Dependency declarations read and used:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, lines 55–60.
- `def-weil-finite-dimensional-subspace`: `FiniteDimensional`,
  `Mathlib.LinearAlgebra.FiniteDimensional.Defs`, lines 73–77.
- `def-weil-finitely-generated-module`: `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs`, lines 116–119.
- `def-weil-pbc-module-length`: `Module.length`,
  `Mathlib.RingTheory.Length`, lines 28–33; finiteness equivalence at line 94.
- `def-weil-endomorphism-determinant`: `LinearMap.det`,
  `Mathlib.LinearAlgebra.Determinant`, lines 173–181.

The recorded Mathlib leaves are used directly, including those having no `lean` record.
All five defining modules are public imports. The additional public import
`Mathlib.RingTheory.OrderOfVanishing.Noetherian` supplies `Ring.ordFrac` and its
DVR normalization. The item has no proof dependencies to import.

Edge cases checked mathematically before writing:

- V = 0 is allowed: M = H = g(M) = 0, both lengths are 0, the determinant is 1,
  and its valuation is 0. No Nontrivial V or positive-rank assumption appears.
- g = identity, or any g preserving M: both quotients vanish and the determinant
  is an R-unit, so the right side is zero.
- Rank one, M = R and g multiplication by a uniformizer: H = tR, the lengths
  are 1 and 0, and the right side is +1. This checks the sign.
- Multiplication by t⁻¹ gives lengths 0 and 1 and valuation −1. Integer subtraction
  is essential; the statement uses no truncated natural subtraction.
- Multiplication by u t^r works for every integer r, including r = 0 and negative r.
  There is no restriction on characteristic or residue characteristic.
- R, K, and V have independent explicitly declared universes u, v, w. A lattice
  need not already be supplied with a basis; finite generation and full span suffice.

Searches for an existing exact statement:

- `msearch.py ... leanfinder` query: “The signed difference of lengths of a lattice
  and its image modulo their intersection equals the valuation of the determinant
  over a discrete valuation ring”. Eight hits: principally
  `Submodule.natAbs_det_basis_change`, `Submodule.natAbs_det_equiv`, and additive
  subgroup index formulas over ℤ. Their signatures were returned by the tool:
  they concern cardinal indices over ℤ, not arbitrary DVR module lengths.
- `msearch.py ... loogle "LinearMap.det, Module.length"`: zero hits.
- `msearch.py ... grep "length.*det|det.*length|ord.*det" RingTheory`:
  one irrelevant comment in Kaehler/JacobiZariski.lean; no match.
- `msearch.py ... leansearch` query: “DVR lattice relative module length equals
  order of vanishing of determinant”. Eight hits including `Module.length_submodule`,
  `Module.length_quotient`, `Ring.ord`, `Ring.ordFrac`, and additive valuation
  divisibility. These supply constructions and elementary length formulas, not
  the determinant identity.
- `rg` of the item's id in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`:
  no hits. `rg` of `length.*det|det.*length|lattice.*distance|distance.*lattice`
  in upstream and `lean/Sheaf`: no existing theorem matching this node.
- `rg` of `ordFrac` in upstream and `lean/Sheaf` identified the existing order
  construction and the norm-valuation consumer. Their actual source was read.
- `rg` of `lattice_distance_determinant|length.*det|det.*length` in
  `dag/lean_names_upstream.json`: no hits for the proposed theorem or identity.

No STATEMENT-DISPUTED flag is needed. The supplied node currently has `status: unsplit`
and an empty proof list; these fields were preserved verbatim, as the worker is only
allowed to change `lean` for this delivery. This metadata does not change its statement.

Validation: `scompile.py` compiled the sandbox and library forms cleanly (1.5 s and
1.7 s). `deliver2.py Q112 lem-exc-dvr-lattice-distance-determinant --no-push` printed
`OK (dry run)` for commit `21956e1a09`: compilation and preflight pass except for the
independent second reading, which the wrapper explicitly leaves to the second reader.
Nothing was pushed; no second-reading section was written by this worker.


## Second reading by Q112

I independently opened the sandbox node and Lean file, all five statement-dependency
nodes and their actual Mathlib declaration sources, the current nine proof steps and
the declarations used by them. I read Stacks `algebra.tex`, the orders-of-vanishing
section, definitions and lemmas 02MD, 02ME, 02MF, 02MG, 02MH, and 02MI (including
the complete proof of 02MI). The tags file confirms their labels. No repair note exists
for this item. The following is my object/hypothesis/conclusion checklist.

1. **R is a DVR.** `(R : Type u) [CommRing R] [IsDomain R]
   [IsDiscreteValuationRing R]` is precisely the node's local, nonfield PID.
   `IsDiscreteValuationRing` in `DiscreteValuationRing/Basic.lean:58` extends the
   principal-ideal and local-ring classes and requires a nonzero maximal ideal.
   Verdict: exact. The source's Noetherianity and dimension-one assumptions hold for
   every DVR; neither has been added as an independent restriction.
2. **K is its fraction field, with its specified inclusion.** `(K : Type v) [Field K]
   [Algebra R K] [IsFractionRing R K]`. Fraction-field localization makes the map from
   the domain injective, realizing the source's subring notation. Verdict: exact.
3. **V is a finite-dimensional K-vector space.** `(V : Type w) [AddCommGroup V]
   [Module K V] [FiniteDimensional K V]`. The dependency's `FiniteDimensional`
   is Mathlib's abbreviation for `Module.Finite K V` in
   `FiniteDimensional/Defs.lean:75`, expressing finite spanning. Verdict: exact.
4. **The R-action is restriction of scalars.** `[Module R V]
   [IsScalarTower R K V]` fixes this compatibility rather than imposing an extra
   property: for each r and x the tower equation with `1 : K` forces
   `r • x = (algebraMap R K r) • x`. Every vector space in the node has that action.
   Verdict: no extra mathematical hypothesis.
5. **M is a finite full R-submodule of V.** `(M : Submodule R V)
   [Module.Finite R M]` and `(hspan : Submodule.span K (M : Set V) = ⊤)`.
   `Module.Finite` is the finitely-generated-top class at `Finiteness/Defs.lean:117`.
   The node explicitly uses full span, agreeing with the remark after source 02ME.
   No freeness, chosen basis, or saturation is assumed. Verdict: exact.
6. **g is a K-linear isomorphism and g(M) is its actual image.**
   `(g : V ≃ₗ[K] V)` and `M.map (g.toLinearMap.restrictScalars R)`.
   Restriction is legitimate by the tower in item 4. No independently chosen image
   lattice or map occurs. Verdict: exact.
7. **H is the intersection, inside each numerator.** Inside M the denominator is
   `(M.map (g.toLinearMap.restrictScalars R)).comap M.subtype`: an element x : M
   belongs exactly when its value belongs to g(M). Inside g(M) it is
   `M.comap (M.map (g.toLinearMap.restrictScalars R)).subtype`: an element of g(M)
   belongs exactly when its value belongs to M. These are the two inverse images of
   the same ambient intersection, so the quotients are M/H and g(M)/H.
   Verdict: exact; no intersection has been taken in the wrong module.
8. **Both lengths are finite.** The first two conjuncts use
   `Module.length R (...) ≠ ⊤` for those two quotients, respectively.
   I read `Module.length` at `Length.lean:32` (Krull dimension of the submodule
   lattice) and its finite-length equivalence. This is the dependency's chain length
   in ℕ∞ and finiteness from 02MF. Verdict: both clauses present, no weakening.
9. **The signed integer equality.** The final conjunct converts each length using
   `.toNat`, then casts each separately to ℤ and subtracts in the order M/H minus
   g(M)/H. The preceding finiteness clauses ensure `.toNat` retains each value.
   Verdict: exact signed subtraction, with no truncation or reversed sign.
10. **The determinant and its normalized valuation.** `LinearMap.det g.toLinearMap`
    is the recorded dependency from `LinearAlgebra/Determinant.lean:179`; finite
    dimension gives a finite basis, so its fallback for modules without a finite
    basis cannot occur. The equivalence makes this determinant nonzero.
    `WithZero.log (Ring.ordFrac R ...)` is the exponent valuation required by the
    node. I read `ordFrac` in `OrderOfVanishing/Basic.lean:324` and the DVR formulas
    in `OrderOfVanishing/Noetherian.lean:155–190`: units have order 1 in the
    multiplicative encoding, and an irreducible uniformizer has `WithZero.exp 1`.
    `WithZero.log_exp`, `log_one`, and `log_mul` in
    `Algebra/GroupWithZero/WithZero.lean:396–413` recover the integer exponent,
    including negative exponents on fractions. Nonzero input excludes the totalized
    value at zero. Verdict: the correct normalized valuation, with no extra choice.

The binders introduce exactly R, K, V, M and then g; H is expressed canonically rather
than quantified as arbitrary data. All universes u, v, w and all variables are explicit.
There is no smallness equality, characteristic assumption, residue-field restriction,
or extra instance restricting the intended class. There is no index set or scheme in
this node; empty-scheme checks are inapplicable.

Edge cases checked independently: V = 0 forces M = g(M) = H = 0; both lengths are 0
and the empty determinant is 1. For g = identity or a lattice-preserving automorphism,
both quotients vanish and the determinant is a unit. For rank one and g multiplication
by t, the lengths are 1 and 0, giving +1; for t⁻¹ they are 0 and 1, giving −1. In
rank two, diag(t²,t⁻³) gives lengths 2 and 3, hence −1. Thus mixed signs are covered,
not just nested images. Zero submodules with nonzero V are excluded precisely by
hspan, as in the node. Every characteristic and arbitrary independent type universes
are admitted; the DVR's intentional nonfield condition is retained.

Independent searches, with wording different from the worker's:

- `msearch.py Q112 lem-exc-dvr-lattice-distance-determinant leanfinder
  "Relative index of two full modules over valuation ring equals determinant valuation"`
  returned eight hits, principally `AddSubgroup.relIndex_eq_abs_det`, its natural
  absolute-value variants, and `Submodule.natAbs_det_basis_change`. I opened
  `FreeModule/Finite/CardQuotient.lean:28–100`: these compute ℤ-lattice cardinalities
  or rational relative indices, not signed DVR lengths. None is an exact match.
- `msearch.py ... loogle "Ring.ordFrac, Module.length"` returned zero hits.
- `msearch.py ... leansearch "Length of a quotient by a full rank submodule over a
  local principal ideal domain computed by determinant order"` returned eight hits.
  Besides the integer-index formulas, `Submodule.finrank_quotient_eq_sum` is closest.
  I opened `FreeModule/Finite/Quotient.lean:115–135`: it computes a finite rank over
  another scalar ring with extra freeness/finite hypotheses, and neither gives
  module length nor the determinant valuation. No exact match.
- Direct `rg -i` for `colength.*det|det.*colength|relative.*length|length.*det|
  det.*length|lattice.*(index|distance)` across Mathlib LinearAlgebra and RingTheory,
  upstream `WeilConjectures`, and the shared `lean/Sheaf` found no exact theorem.
  The upstream Riemann–Roch comment concerns degree of coherent sheaves. The side
  `DvrNormValuationSum` is a consumer, not a duplicate; I opened its full signature.
  A separate search in `dag/lean_names_upstream.json` for the declaration name,
  colength and length/determinant combinations returned no match.

There are no new definition nodes or dependency modules in this delivery, so H12/H13
introduce no further statements to review. No statement correction is needed; the
source's DVR specialization agrees with the node and the unchanged Lean signature.
Consequently no correction/citer audit is required.

Mismatches found and repaired:

- **H8, stale proof documentation.** The worker's report and old docstring were
  prepared before the current stage-1 split: they describe an empty proof list and
  the general-linear-group proof from Stacks. The actual current node is `split`
  and has nine steps using a common lattice and Smith normal form. I replaced the
  proof portion of the docstring with those nine steps, citing all its dependencies:
  torsion-free freeness and rank zero; unit/power exponents; cyclic quotient lengths;
  construction of N = t^q M; full-rank Smith bases; finite sum lengths; determinant
  of the inclusion matrix; the two coordinate matrices; cancellation of H/N.
  This supersedes the worker report's historical empty-proof/status observations.
- **Required proof imports.** I added non-public imports of
  `Mathlib.LinearAlgebra.FreeModule.PID`,
  `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`,
  `Mathlib.RingTheory.PrincipalIdealDomain`, and
  `WeilConjectures.LinearAlgebra.Matrix.CauchyBinet` for the recorded proof plan.
  I read the freeness instance, `Submodule.exists_smith_normal_form_of_le`,
  `PrincipalIdealRing.isNoetherianRing`, the DVR factorization theorem, and
  `Module.length_eq_add_of_exact` in their Mathlib source files. I fetched the exact
  current Cauchy–Binet source using `scompile.py --source
  WeilConjectures.LinearAlgebra.Matrix.CauchyBinet` and checked that its square
  specialization is the formula used in step 7. No interface repair is needed.
- **H3 verdict:** no mathematical mismatch found. I preserved the entire theorem
  signature and node record. The sandbox node differs from the current shared base
  only in `lean`. The recorded `lean.statement` is verbatim the file signature.

H5/H6/H9: no definitions, no axioms, no file-local notation or instances, and precisely
one theorem with precisely one `sorry`. The module and declaration docstrings retain
their source and exact blueprint identifier. All Lean lines are at most 100 characters.
No variable or universe is unbound. There is no unresolved STATEMENT-DISPUTED issue.

Validation after repair: the required `scompile.py Q112
lem-exc-dvr-lattice-distance-determinant <file>` compiled the sandbox form in 1.5 s and
the library form in 1.6 s, with no errors or warnings. Delivery preflight is recorded
below after running the required dry run.

The required `deliver2.py Q112 lem-exc-dvr-lattice-distance-determinant --no-push`
completed successfully: `OK (dry run): commit b929964b39 passes the preflight and
compiles; nothing pushed`. The wrapper excluded a concurrent `lean_audit` delta,
which is outside this delivery; no such metadata change is requested.
