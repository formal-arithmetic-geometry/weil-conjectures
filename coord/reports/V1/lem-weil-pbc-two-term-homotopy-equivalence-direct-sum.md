## Worker report

The module `Sheaf.Algebra.TwoTermHomotopyEquivalenceDirectSum` states
`Module.prod_linearEquiv_of_twoTermHomotopy`, with a single `sorry` proof. It states the
explicit-data form of Stacks Project, Algebra, Lemma 00S3. No definitions, dependency modules,
new nodes, or statement corrections are needed. Only the item's `lean` field changes.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The commutative ring is `(R : Type u) [CommRing R]`.
- The four modules are `A₁ : Type v₁`, `A₀ : Type v₀`, `B₁ : Type w₁`, `B₀ : Type w₀`,
  with the four `AddCommGroup` and four `Module R` instances. Each carrier has its own
  explicitly bound universe, so there is no size restriction on the module pairs.
- The two differentials are `(dA : A₁ →ₗ[R] A₀)` and `(dB : B₁ →ₗ[R] B₀)`.
  No condition on a second differential is needed for a two-term complex.
- The maps φ in degrees 1 and 0 are `φ₁ : A₁ →ₗ[R] B₁` and `φ₀ : A₀ →ₗ[R] B₀`.
- The maps ψ in degrees 1 and 0 are `ψ₁ : B₁ →ₗ[R] A₁` and `ψ₀ : B₀ →ₗ[R] A₀`.
- The first chain-map equation is `hφ : dB.comp φ₁ = φ₀.comp dA`.
- The second chain-map equation is `hψ : dA.comp ψ₁ = ψ₀.comp dB`.
- The two homotopy maps are `h : A₀ →ₗ[R] A₁` and `h' : B₀ →ₗ[R] B₁`.
- The A-degree-1 equation is `hA₁ : LinearMap.id - ψ₁.comp φ₁ = h.comp dA`.
- The A-degree-0 equation is `hA₀ : LinearMap.id - ψ₀.comp φ₀ = dA.comp h`.
- The B-degree-1 equation is `hB₁ : LinearMap.id - φ₁.comp ψ₁ = h'.comp dB`.
- The B-degree-0 equation is `hB₀ : LinearMap.id - φ₀.comp ψ₀ = dB.comp h'`.
- The conclusion is `Nonempty ((A₁ × B₀) ≃ₗ[R] (B₁ × A₀))`: existence of an R-linear
  isomorphism with precisely the displayed order of summands. The binary direct sum is the
  product with componentwise operations, since every two-component family has finite support.
  `Nonempty` asserts existence without specifying a particular choice of isomorphism.

Dependency: `def-weil-pbc-direct-sum-modules` is a Mathlib leaf; its `mathlib_match` is the
recorded declaration, and no `lean` record is required. I read `DirectSum` and its docstring
in `Mathlib.Algebra.DirectSum.Basic` (finitely supported dependent families), and the module
instance, `DirectSum.lof`, `DirectSum.component`, and `DirectSum.induction_on` in the recorded
Basic/Module source files. The module imports `Mathlib.Algebra.DirectSum.Module`, which supplies
the recorded direct-sum framework and the linear-map/equivalence and product-module structures
used in the statement. Its finite-index comparison `DirectSum.linearEquivFunOnFintype`
identifies a finite direct sum with all component families. For two modules the standard
`Prod.instModule` (`Mathlib.Algebra.Module.Prod`) has precisely componentwise operations.
`ModuleCat.biprodIsoProd` in `Mathlib.Algebra.Category.ModuleCat.Biproducts` additionally verifies
that the binary module biproduct is isomorphic to that ordinary product; I read its signature
and docstring. No separate notion is introduced. This is also the encoding used by the
already landed `Module.schanuel` and `Algebra.Extension.conormalModule_principalLocalization`.

Source checking: the local `literature/stacks-project/algebra.tex` is absent on this machine.
I opened https://stacks.math.columbia.edu/tag/00S3 instead, and checked its statement and four
homotopy equations against the node. The node already corrects the order of the off-diagonal
composition in the source's displayed matrix; its expanded proof checks both matrix products.
The theorem docstring carries all three proof steps: block maps C and D, both triangular
compositions, explicit triangular inverses, and equality of the left/right inverses of C.

Edge cases checked mathematically before writing:

- Any or all modules may be zero. The same equations and product modules remain meaningful;
  no nonzero, projective, free, finite-generation, or finite-rank hypothesis is imposed.
- If both differentials vanish, the four homotopy identities force φ and ψ to be inverse
  in each degree; the stated crosswise sum isomorphism follows.
- Contractible two-term complexes (invertible differentials) and identity equivalences
  satisfy the equations with the appropriate homotopies, including h = h' = 0 for identities.
- The zero ring and every characteristic are permitted. The proof uses addition, subtraction,
  and composition only; no scalar division is assumed.
- Both direct sums have exactly two summands, so the finite-support requirement is automatic.
  There is no variable index set and hence no accidental exclusion of an empty index set.

Searches (all tool calls were made for V1 and this item; logged in `searches.jsonl`):

- `msearch.py leansearch`: "Homotopy equivalent two term complexes of modules imply A1 direct
  sum B0 is linearly isomorphic to B1 direct sum A0". Service unavailable (Internal Server
  Error); no result or no-match verdict is claimed for this unavailable search.
- `msearch.py leanfinder`: "Two term chain homotopy equivalence gives linear equivalence of
  A1 times B0 and B1 times A0". Eight hits: `HomotopyEquiv`,
  `CategoryTheory.ShortComplex.HomotopyEquiv`, homotopy constructors/composition facts,
  and homotopy-cofiber facts. None states the crosswise two-term module isomorphism.
- `msearch.py loogle`: "LinearEquiv, LinearMap.comp". Twelve hits about composing a linear
  equivalence with its inverse and cancellation; none supplies the claimed existence theorem.
- `msearch.py grep`: "sum_two_terms|Schanuel|00S3|homotopy.*prod|prod.*homotopy", first over
  Mathlib and then scoped to `Algebra`. The scoped hits concern homotopy cofibre/fibre
  biproducts, not the direct sums of terms of arbitrary homotopy equivalent two-term complexes.
- `rg` with "sum_two_terms|Schanuel|00S3|homotopy.*prod|prod.*homotopy|two.term.*equiv" over
  `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`: products in homotopy
  categories and references to this node in the conormal proof, plus the project's Schanuel
  lemma for projective presentations, which has different hypotheses. No exact match.
- `rg` with this item's id over `WeilConjectures`: no result.
- `rg` for the proposed declaration-name variants in Mathlib, `WeilConjectures`, `lean/Sheaf`,
  and `dag/lean_names_upstream.json`: no declaration-name collision.

No statement dispute or node fault was found. The second reader must independently review
this file and node; no second-reading section is supplied by this worker.


## Second reading by V1

I independently read the item JSON, its only statement dependency
`def-weil-pbc-direct-sum-modules`, and the delivered Lean file. Verdict: the Lean
says exactly what the node says; no statement or module repair is needed.
Only this second-reading report was added.

Source: the local Stacks checkout is absent. I read the upstream raw
`algebra.tex` at https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex,
label `lemma-sum-two-terms` (Tag 00S3), its entire proof, the beginning of
`section-netherlander`, and the chapter's `section-conventions`; I also opened
https://stacks.math.columbia.edu/tag/00S3. The chapter assumes commutative rings
with identity and explicitly permits the zero ring. The section's discussion of
cotangent complexes does not impose finiteness or projectivity on this lemma,
which introduces arbitrary two-term complexes. The node expands the source's
chosen chain maps and homotopies into explicit data, so their universal binders
in Lean have the correct quantifier order.

My object/hypothesis/conclusion checklist, made from the node and matched to Lean:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Commutative ring R | `(R : Type u) [CommRing R]` | Exact, includes zero ring. |
| Four R-modules A1, A0, B1, B0 | Four `Type` binders, four `AddCommGroup` and four `Module R` instances | Exact; no finite, free, projective or nonzero assumptions. |
| Differentials A1 to A0, B1 to B0 | `dA : A₁ →ₗ[R] A₀`, `dB : B₁ →ₗ[R] B₀` | Exact. Two-term complexes need no further differential equation. |
| Degree-one and degree-zero maps phi | `φ₁ : A₁ →ₗ[R] B₁`, `φ₀ : A₀ →ₗ[R] B₀` | Exact. |
| Degree-one and degree-zero maps psi | `ψ₁ : B₁ →ₗ[R] A₁`, `ψ₀ : B₀ →ₗ[R] A₀` | Exact. |
| Phi commutes with differentials | `hφ : dB.comp φ₁ = φ₀.comp dA` | Exact; `comp` has the ordinary function-composition order. |
| Psi commutes with differentials | `hψ : dA.comp ψ₁ = ψ₀.comp dB` | Exact. |
| A homotopy A0 to A1 | `h : A₀ →ₗ[R] A₁` | Exact, linear. |
| B homotopy B0 to B1 | `h' : B₀ →ₗ[R] B₁` | Exact, linear. |
| A-degree-one identity | `hA₁ : LinearMap.id - ψ₁.comp φ₁ = h.comp dA` | Exact, including sign and order. |
| A-degree-zero identity | `hA₀ : LinearMap.id - ψ₀.comp φ₀ = dA.comp h` | Exact. |
| B-degree-one identity | `hB₁ : LinearMap.id - φ₁.comp ψ₁ = h'.comp dB` | Exact. |
| B-degree-zero identity | `hB₀ : LinearMap.id - φ₀.comp ψ₀ = dB.comp h'` | Exact. |
| A1 direct sum B0 is R-linearly isomorphic to B1 direct sum A0 | `Nonempty ((A₁ × B₀) ≃ₗ[R] (B₁ × A₀))` | Exact existence claim, with correct summand order. |

Dependency and one-definition check: I opened `DirectSum` in
`Mathlib/Algebra/DirectSum/Basic.lean` (lines 35–40), its additive-group instance,
`of`, `sum_support_of`, and `induction_on`; in `DirectSum/Module.lean` I read the
module instance, `lof`, `component`, and `linearEquivFunOnFintype` (lines 147–151).
These implement precisely finite-support families, componentwise operations,
inclusions, projections, and finite summation of the dependency node. For two
summands every family is finitely supported, so the Cartesian product with the
standard `Prod.instModule` (read in `Algebra/Module/Prod.lean`, lines 24–28) is
exactly the binary direct sum. I additionally read the construction and signature
of `ModuleCat.biprodIsoProd` (`Algebra/Category/ModuleCat/Biproducts.lean`, lines
35–71). No private direct-sum definition is present or needed. The imported
`Mathlib.Algebra.DirectSum.Module` supplies the recorded dependency framework.
There are no new definition nodes or dependency modules to review under H12/H13.
The sandbox node differs from the base only in `lean`; there is no statement
correction, so the corrected-statement/citer procedure does not apply.

Edge cases checked independently: all four zero modules; one zero complex
(then the other is contractible and its differential is invertible); both
zero differentials (then phi and psi are inverse in each degree); identity
maps with zero homotopies; the zero ring; characteristic two, where subtraction
still gives the stated identities; arbitrary other characteristics. No division
or nontriviality is used. Each module has its own bound universe `v₁`, `v₀`,
`w₁`, `w₀`, independently of `u`; products live in their maxima, so no module
size is excluded. An empty variable index set, empty scheme, and parameter
`n = 0` do not occur in this statement: its sums always have two specified
summands, which may themselves be zero.

Independent searches, run using msearch.py and rg (msearch calls logged in
`searches.jsonl`):

- LeanFinder: "Stable isomorphism of even and odd terms for chain homotopy
  equivalent complexes of length one". Eight hits, including
  `HomotopyEquiv`, `ShortComplex.HomotopyEquiv`, and alternating-constant complex
  lemmas. Their signatures describe homotopy-equivalence data or special
  alternating complexes, not the crosswise linear isomorphism of this node.
- Loogle: `LinearEquiv, LinearMap.prod`. Two hits: `LinearMap.prodEquiv_apply`
  and `Matrix.toLin_finTwoProd`. Neither states this theorem.
- LeanSearch: "Isomorphic cross sums of modules from inverse chain maps up to
  chain homotopy". Service returned Internal Server Error; recorded unavailable,
  not a no-match result.
- Mathlib grep: `stable.*(isom|equiv)|two.?term|00S3|sum_two_terms`. The broad
  service output had unrelated matches; I followed it with direct rg on
  `Algebra/Homology` and `LinearAlgebra` using `two.?term`, `00S3`,
  `sum_two_terms`, and homotopy near direct-sum/linear-equivalence/product words.
  Hits were homotopy-cofiber term biproducts, not this assertion.
- Independent rg over `WeilConjectures`, repository `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for stable isomorphism, two-term, `00S3`,
  `sum_two_terms`, and `prod_linearEquiv_of_twoTermHomotopy`: no existing exact
  statement or declaration-name collision. Project hits concern free covers,
  truncations, tensor Kunneth, or the conormal lemma's citation of this item.

H5/H6/H8/H9: the delivery has one theorem with a single `sorry`, no definitions,
instances, local notation, hidden hypotheses, or proved auxiliary declarations.
Every universe and variable is explicitly bound. The module and theorem
docstrings give Tag 00S3, its label, and this blueprint id. I checked each of
the three proof steps against the node: C and D have the indicated domains;
both products have identity diagonal; subtracting each off-diagonal term
inverts the triangular product; the displayed left/right-inverse calculation
makes C invertible. In particular the docstring correctly uses `ψ₁ ∘ h'`,
where the source's displayed off-diagonal entry has the ill-typed `h' ∘ ψ₁`.
That source typo was already repaired in the node and is not a new correction.
No mismatch found and no Lean/node edit made. Compilation and delivery checks
are recorded below after running them.

Verification: scompile.py compiled the complete delivered module on the server
in 1.2 seconds, exit code 0, without warnings. I checked the recorded
`lean.statement` byte-for-byte against the theorem signature and checked every
module line is at most 100 characters. The first compile invocation used a
relative path from the read-only repository and failed to locate the sandbox
file; rerunning with its absolute sandbox path succeeded.

Delivery dry run: `deliver2.py V1 lem-weil-pbc-two-term-homotopy-equivalence-direct-sum --no-push` printed
`OK (dry run)`; preflight and server compilation passed.
