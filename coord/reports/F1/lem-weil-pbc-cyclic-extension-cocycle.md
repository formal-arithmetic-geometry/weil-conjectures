## Worker report

The module `Sheaf.Paper.CyclicExtensionCocycle` states the cyclic extension and Koszul one-cycle result from Stacks 05ED/05EE. It binds a commutative ring `A`, module `P`, a finite list `f`, its ideal `J`, a presentation module `M_f`, the map `μ`, kernel `K_f`, the cycle predicate `Z_f`, admissibility, the quotient extension family `E_f`, and an arbitrary short exact extension. Clause (1) is rendered by injectivity of `iota`, surjectivity of `pi`, and equality of kernel and range. Clause (2) includes a chosen lift of `1 mod J`, the recovered cycle and admissibility, and linear equivalences `theta` commuting with the maps. Clause (3) states admissibility after subtracting `f_i m` and supplies the corresponding linear equivalence.

Dependencies used are the Mathlib quotient module (`Submodule.mkQ`, `Submodule.ker_mkQ`), direct-sum/module infrastructure (`DirectSum`), and `CategoryTheory.ShortComplex.ShortExact` as recorded by the dependency nodes `def-weil-pbc-free-module`, `def-weil-pbc-quotient-module`, `def-weil-pbc-direct-sum-modules`, and `def-weil-pbc-exact-sequence`. The declaration is intentionally a statement with `sorry` proof.

Edge cases checked include `t = 0` (the `Fin t` family is empty), zero modules, and arbitrary commutative rings; no positivity assumption beyond the source's finite-generator presentation is introduced in Lean.

Searches: `msearch.py leansearch` for cyclic extension classification (service unavailable); `msearch.py leanfinder` for quotient presentations (hits `Module.Presentation.ofExact` and related general tools, no exact theorem); `msearch.py loogle` for quotient declarations (no hit for the queried namespace); `msearch.py grep` for Koszul/cyclic extension (only local cohomology/Koszul background). Repository grep found no existing project declaration. The Stacks source was checked at tags 05ED and 05EE.

## Earlier second reading (a previous round; superseded)

Pending the independent second reader. The statement was compiled remotely with no warnings.

## Second reading by F1

I independently opened the node, the delivered Lean, all four statement dependency
nodes and their Mathlib declarations. The original worker report above describes
the original draft; the following reading and repairs supersede those claims.
I read Stacks `lemma-naive-Koszul-complex` (05ED), `lemma-explicit-ext` (05EE),
and Homology `section-extensions` (010I), using the local Stacks checkout
`/home/ubuntu/c1-stacks-review/more-algebra.tex` and `homology.tex` because the
repository's literature checkout is absent on this machine. These are the source
places named by the node. The source assumes a commutative ring, finite generators,
and arbitrary modules, with no Noetherian, field, flatness, or characteristic
condition. The node makes the extension description explicit in three clauses;
its five proof steps correctly express that description. The node itself needed
no correction; only its `lean` record changes.

Object, hypothesis and conclusion inventory, matched against the final file:

1. Commutative ring A and arbitrary A-module P: `{A : Type u} [CommRing A]`
   and `{P : Type v} [AddCommGroup P] [Module A P]`. Verdict: exact.
2. Positive finite generator count, generators, and their ideal: `t : ℕ`,
   `ht : 1 ≤ t`, `f : Fin t → A`, `J : Ideal A`,
   `hJ : J = Ideal.span (Set.range f)`. Reindexing 1,...,t by `Fin t`
   changes no mathematics. Verdict: exact; the missing positivity was repaired.
3. Free module F with the specified basis: `F : Type w` with module instances
   and `e : Module.Basis (Fin t) A F`. `Module.Basis.repr` is exactly an
   equivalence with `Fin t →₀ A`; thus F is the node's free module, expressed
   invariantly rather than by a specific representation. Verdict: exact.
   The draft only supplied a family `e`, with no basis property; repaired.
4. Relation submodule W: `W : Submodule A F` and `hW` specify precisely the
   span of `f i • e j - f j • e i`. Verdict: exact, preserved.
5. Presentation module, quotient classes, induced map, and kernel: `F ⧸ W`
   is the actual Mathlib quotient; `W.mkQ (e i)` is its basis class;
   `μ : (F ⧸ W) →ₗ[A] A` and `hμ` give its specified values; the kernel is
   `LinearMap.ker μ`. The basis classes generate the quotient, so these values
   determine μ uniquely, with no additional hypothesis. Verdict: exact.
   The draft's arbitrary `M_f` and surjection lacked `ker qF = W`; replaced
   with the concrete quotient, and the arbitrary kernel parameter removed.
6. Cycle set: local `Z_f := {x | ∀ i j, f i • x j = f j • x i}`.
   Verdict: exactly the node's set, with no independent parameter to identify.
7. Induced map xhat and admissibility: local `admissible x` requires membership
   in `Z_f`, existence of `xhat : (F ⧸ W) →ₗ[A] P` with the specified values,
   and vanishing on `LinearMap.ker μ`. Every cycle induces such a unique map
   because precisely W's generators vanish, and basis classes generate the
   quotient. Therefore existentially expressing xhat's vanishing is exactly
   the node's admissibility, not an added restriction. Verdict: exact.
8. Extension module and inclusion: `W_x x` is the concrete span of `(x i,-f i)`
   in `P × A`; `E_f x := (P × A) ⧸ W_x x`; `iota x` is
   `(W_x x).mkQ.comp (LinearMap.inl A P A)`. These are concrete constructions,
   not arbitrary extension modules or maps. The finite binary direct sum is
   the product module with componentwise operations. Verdict: exact.
9. Clause (1), well-defined projection: the conclusion existentially supplies
   `pi : ∀ x, admissible x → E_f x →ₗ[A] A ⧸ J` and its formula
   `pi x hx ((W_x x).mkQ (p,a)) = Ideal.Quotient.mk J a`.
   A linear map on the quotient with this formula asserts precisely the
   well-defined descent of the projection. Verdict: exact; formerly absent.
10. Clause (1), short exactness: for every admissible x, the conclusion gives
    `Function.Injective (iota x)`, `Function.Surjective (pi x hx)`, and
    `LinearMap.ker (pi x hx) = LinearMap.range (iota x)`.
    The equality includes the complex condition and middle exactness; the
    other two facts give endpoint exactness. Verdict: exact; formerly assumed
    as `short_exact` instead of established.
11. Clause (2), arbitrary extension and chosen lift: the second conjunction
    universally quantifies `E : Type z`, its module instances, linear maps
    `j` and `q`, injectivity, surjectivity, kernel/range equality, and
    `lift : E` with `q lift = Ideal.Quotient.mk J 1`. Verdict: exact.
    The implication/conjunction layout separates these hypotheses from (1)
    and (3), which do not depend on a supplied extension.
12. Clause (2), unique recovered tuple: the conclusion supplies `x`,
    `∀ i, j (x i) = f i • lift`, and
    `∀ y, (∀ i, j (y i) = f i • lift) → y = x`.
    Uniqueness of the entire tuple is exactly coordinatewise uniqueness.
    Verdict: exact; the draft's bare existence of an admissible cycle omitted
    both the relation to the lift and uniqueness.
13. Clause (2), cycle and admissibility: `x ∈ Z_f` and a witness
    `hx : admissible x`. Verdict: exact.
14. Clause (2), induced isomorphism: existential `theta : E_f x ≃ₗ[A] E`,
    formula `theta ((W_x x).mkQ (p,a)) = j p + a • lift`,
    `∀ p, theta (iota x p) = j p`, and
    `∀ y, q (theta y) = pi x hx y`. The representative formula ensures
    this is the node's induced map, not merely some extension isomorphism.
    Verdict: exact; these were assumed in the draft and its conclusion instead
    contained a reflexive equality between proofs.
15. Clause (3), changed tuple: for every admissible x and every m, the local
    `x' := fun i => x i - f i • m` and existential `hx' : admissible x'`
    give precisely the claimed admissibility. Verdict: exact.
16. Clause (3), change isomorphism and commutation: existential
    `change_iso : E_f x ≃ₗ[A] E_f x'`, the representative formula
    sending `(p,a)` to `(p + a • m,a)`, compatibility with `iota`, and
    compatibility with `pi`. Verdict: exact; formerly the isomorphism was
    assumed, and its formula and both compatibility clauses were missing.

Dependency audit / one definition per notion:

- `def-weil-pbc-free-module` records `Module.Free` in
  `Mathlib.LinearAlgebra.FreeModule.Basic`; its `exists_basis` field uses
  `Module.Basis`. I opened that field and `Module.Basis` in
  `Mathlib.LinearAlgebra.Basis.Defs`, whose `repr` is the required free-module
  coordinate equivalence. A specified basis is what this node requires, so
  using the underlying Mathlib basis rather than only an abstract Free
  instance preserves the generators. No private free-module definition.
- `def-weil-pbc-quotient-module`: I opened `Submodule.mkQ`,
  `mkQ_surjective` in Quotient.Defs and `ker_mkQ` in Quotient.Basic.
  The final statement uses these actual quotient types and quotient maps.
- `def-weil-pbc-direct-sum-modules`: I opened `DirectSum`, `lof`, `component`,
  and `DirectSum.addEquivProd` in DirectSum.Basic/Module. The node's P⊕A is
  the finite binary product, with the identical component operations;
  `LinearMap.inl` is the usual first inclusion. This uses Mathlib's existing
  product module, not a new direct-sum definition or altered notion.
- `def-weil-pbc-exact-sequence`: I opened `ShortComplex.ShortExact` and
  the ModuleCat interpretation in `Mathlib.Algebra.Homology.ShortComplex.ModuleCat`:
  `moduleCat_exact_iff_range_eq_ker`, `ShortExact.moduleCat_injective_f`,
  `ShortExact.moduleCat_surjective_g`. The three explicit linear-map conditions
  above are exactly its specialization to modules. They avoid packaging all
  modules into a common universe or requiring a separate proof of the complex
  condition just to state the result. No new exactness predicate is defined.

There are no new nodes, dependency modules, missing notions, private global
copies, or statement corrections in this delivery. The theorem-local lets only
spell out the node's explicit concrete set, spans and quotient constructions
with existing Mathlib operations. No definition contains `sorry`. The only
proof is the named theorem's `sorry`; its docstring now carries the source and
all five proof steps, including the dependency notions each step uses. All
variables/universes are explicitly bound; lines are at most 100 characters.

Edge cases: `t = 0` is excluded by the node's own `t ≥ 1`, now faithfully
rendered, rather than silently strengthening the conclusion to that case.
Zero P, the zero ring, zero generators, and J=0 or J=⊤ are all allowed; no
nonzero or nontrivial instances occur. For all-zero f, admissibility forces
x=0 through ker μ, exactly as it should. The sign in the third clause is
correct: `(x i,-f i)` maps to `(x i-f i • m,-f i)`.
No schemes, empty schemes, or geometric characteristic assumptions occur.
A, P, F, and the arbitrary extension E use independent universes u,v,w,z;
quotients of P×A live in their natural maximum universe. No module is
restricted to P's universe, as several were in the draft.

Independent searches (different wording from the first worker):

- `msearch.py ... leansearch "Short exact sequences of modules 0 to P to E
  to R/I described by quotient of P direct sum R by generators"`: service
  unavailable (Internal Server Error), recorded without a no-match verdict.
- `msearch.py ... leanfinder "A short exact extension of a cyclic quotient
  module is isomorphic to a quotient of P times R by relations"`: eight hits,
  including `Module.Presentation.ofExact`, its variants, `ModuleCat.smulShortComplex`,
  and `Function.Exact.linearEquivOfSurjective`. They are general presentation
  tools or scalar multiplication sequences, not the present three-clause
  extension/cycle correspondence.
- `msearch.py ... loogle "Submodule.mkQ"`: twelve quotient infrastructure
  hits, including mkQ, surjectivity, kernel, and liftQ; these confirm the
  existing quotient notion, not an existing statement of this item.
- `rg` across all Mathlib, the source's WeilConjectures, and repository
  lean/Sheaf for `cyclic.*extension|extension.*cyclic|explicit.ext|Koszul.*cycle`
  found field extensions, semidirect products and unrelated names, not this
  theorem. Further searches for `Koszul`, `ExtensionOf`, `admissible`, and
  the exact declaration name likewise found unrelated geometric Koszul
  sequences/admissible blowups. I opened `Module.Baer.ExtensionOf`: it is
  extension of a partial linear map to an intermediate submodule, not an
  extension of A/J by P. No existing theorem renders this node.

The repaired module compiled cleanly with the required server `scompile.py`
command, with no warnings. Its node's `lean.statement` was refreshed directly
from the signature, verbatim. The node's mathematical statement and dependency
list were preserved.
