## Worker report

The module `Sheaf.RingTheory.PolynomialFormalFiber` states
`Polynomial.formalFiber_isGeometricallyRegular`, with `sorry` and no definitions or other theorems.
The seven proof steps in the declaration docstring follow the node's proof, including the zero
factors in the product decomposition. No statement correction or dependency module was needed.

Hypothesis and clause mapping:

- A prime number p: `(p : ℕ) (hp : p.Prime)`.
- The commutative local domain A: `(A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]`.
  The unnamed maximal ideal m is `IsLocalRing.maximalIdeal A`, so no independent ideal is added.
- Noetherian A: `[IsNoetherianRing A]`.
- m-adic completeness: `[IsAdicComplete (IsLocalRing.maximalIdeal A) A]`, equivalent to
  bijectivity of the canonical completion map by `AdicCompletion.of_bijective_iff`.
- The fraction field K = A_(0) of characteristic p:
  `[CharP (Localization.AtPrime (⊥ : Ideal A)) p]`. In a domain, localization at zero inverts
  precisely the nonzero elements; thus this is the exact fraction field named by the node.
- The one-variable polynomial ring A[x]: `Polynomial A`, with its coefficient embedding
  `Polynomial.C : A →+* Polynomial A`.
- A maximal ideal q: `(q : Ideal (Polynomial A)) [q.IsMaximal]`.
- q contracts to m: `hq : q.comap Polynomial.C = IsLocalRing.maximalIdeal A` (the file gives
  the full type annotation on `Polynomial.C`).
- A prime r contained in q: `(r : Ideal (Polynomial A)) [r.IsPrime] (hrq : r ≤ q)`.
- r is nonzero: `hr : r ≠ ⊥`.
- r contracts to zero in A: `hrA : r.comap Polynomial.C = ⊥`.
- κ(r): `r.ResidueField`, defined as the residue field of `Localization.AtPrime r`.
- The completed local ring at q: the conclusion's `let C := AdicCompletion
  (IsLocalRing.maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)`.
  `Localization.AtPrime.map_eq_maximalIdeal` identifies this ideal with q extended to A[x]_q.
- The fibre C ⊗_(A[x]) κ(r): `r.Fiber C`, Mathlib's `κ(r) ⊗_(A[x]) C`, with its canonical
  κ(r)-algebra structure. The tensor-factor swap `Algebra.TensorProduct.comm` identifies
  the two descriptions over κ(r), acting on the residue-field factor.
- The Noetherian conclusion: `IsNoetherianRing (r.Fiber C)`.
- Geometric regularity over κ(r): `Algebra.IsGeometricallyRegular r.ResidueField (r.Fiber C)`.
  This recorded definition already includes Noetherianity; stating the conjunction explicitly
  matches both clauses without changing its logical strength.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (all ideals finitely generated).
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete`, `AdicCompletion`, and the
  checked characterization `AdicCompletion.of_bijective_iff`.
- `Mathlib.RingTheory.AdicCompletion.Algebra`: canonical ring and algebra structures of completion.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime` and the identification
  of its maximal ideal with the extended prime.
- `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField`.
- `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`: `Ideal.Fiber`.
- `Mathlib.Algebra.Polynomial.Basic`: `Polynomial`, `Polynomial.C`.
- `Sheaf.RingTheory.GRing`: `Algebra.IsGeometricallyRegular`; its full definition quantifies
  over finite purely inseparable field extensions and uses `IsRegularRing`.

The two imports suffice: polynomial basic, and GRing (which transitively imports the other
recorded dependencies). Every variable and universe is explicitly bound.

Edge cases checked before writing: A a field has m = 0 and is complete for that ideal; the
statement still covers this case. For example q = r = (x) is allowed, since containment is
non-strict. r = 0 is explicitly excluded. The zero base ring is correctly excluded by the
source's domain hypothesis; the fibre is not given an additional nontriviality hypothesis.
No perfection or separability assumption is added. The prime p may be any prime, including 2;
p = 0 or 1 cannot satisfy `hp`. No dimension or residue-field finiteness restriction is imposed.
The arbitrary `u` does not restrict the size of A. No statement dispute was found.

Source checked: the local literature path is absent on this machine, so I opened
https://stacks.math.columbia.edu/tag/07PU. The hypotheses and conclusion agree with the node.
The seven-step detailed proof is supplied by the DAG node and is retained in the Lean docstring.

Searches made (2026-10-11):

- `msearch.py ... leanfinder "formal fibres of a polynomial ring over a complete Noetherian
  local domain are geometrically regular"`: eight hits concerning `Algebra.IsSmoothAt`,
  `IsStandardSmooth`, `IsEtaleAt`, and smooth-localization results; no matching theorem.
- `msearch.py ... loogle "IsAdicComplete, Polynomial"`: twelve hits, all concerning
  Weierstrass division/preparation of power series; no formal-fibre statement.
- `msearch.py ... grep 'formal.?fib|geometrically.?regular|another_helper' RingTheory`:
  no Mathlib hits.
- `rg` for the item id, geometric regularity and `another_helper` in the source
  `WeilConjectures`, project `lean/Sheaf`, and `dag/lean_names_upstream.json`: only the
  project's existing GRing definition and its uses, no theorem matching the node.
- `rg` for `another_helper_g_ring|polynomial_formal_fiber_geometrically_regular` in Mathlib,
  upstream and Sheaf: no matches. The chosen declaration name is new.

Validation: `scompile.py M1 lem-weil-pbc-another-helper-g-ring` compiled the module on the
server in 2.2 seconds, exit code 0, without warnings. The final delivery dry run follows.


## Second reading by M1

I independently read the item node, its seven proof steps, the delivered Lean file, all six
statement-dependency nodes, and their recorded declarations. I also read the original Stacks
TeX at https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex,
`lemma-another-helper-G-ring` (Tag 07PU), and the rendered source
https://stacks.math.columbia.edu/tag/07PU. The source introduces the same objects and imposes
no additional standing hypothesis on this lemma. Its subset symbol permits equality, as the
node explicitly records. No statement correction, new definition node or dependency module
is present or necessary.

Object, hypothesis and conclusion inventory, matched item by item:

1. A prime number p: `(p : ℕ) (hp : p.Prime)`. Exact; no fixed prime or characteristic excluded.
2. A commutative local domain A with maximal ideal m: `(A : Type u) [CommRing A]
   [IsDomain A] [IsLocalRing A]`, with `IsLocalRing.maximalIdeal A` for m. Exact;
   this is the uniquely determined maximal ideal, not additional data.
3. A is Noetherian: `[IsNoetherianRing A]`. Exact. I read the recorded Mathlib
   `IsNoetherianRing` abbreviation and `isNoetherianRing_iff_ideal_fg` in
   `Mathlib.RingTheory.Noetherian.Defs`; it means every ideal is finitely generated.
4. A is m-adically complete: `[IsAdicComplete (IsLocalRing.maximalIdeal A) A]`.
   Exact. In `Mathlib.RingTheory.AdicCompletion.Basic`, this class requires Hausdorffness
   and precompleteness; `AdicCompletion.of_bijective_iff` identifies it with the node's
   bijective canonical completion map. No separate completeness assumption is introduced.
5. K = A_(0), of characteristic p: `[CharP (Localization.AtPrime (⊥ : Ideal A)) p]`.
   Exact. I read `Localization.AtPrime` in its recorded Mathlib module: it localizes at
   the prime complement. Since A is a domain, the bottom ideal is prime and its complement
   is precisely the nonzero elements. Thus this is the fraction field, without choosing
   another field or imposing an additional algebra structure.
6. A[x], with the coefficient embedding: `Polynomial A` and
   `(Polynomial.C : A →+* Polynomial A)`. Exact. The recorded Polynomial structure
   wraps the finitely supported additive monoid algebra on ℕ, the specified polynomial ring.
7. q is a maximal ideal of A[x]: `(q : Ideal (Polynomial A)) [q.IsMaximal]`. Exact;
   its primality required for localization is inferred from maximality.
8. q contracts to m: `hq : q.comap Polynomial.C = IsLocalRing.maximalIdeal A`,
   with the explicit map type in the file. Exact; this is contraction, not extension.
9. r is prime in A[x]: `(r : Ideal (Polynomial A)) [r.IsPrime]`. Exact.
10. r lies in q: `hrq : r ≤ q`. Exact non-strict containment; r = q is covered.
11. r is nonzero: `hr : r ≠ ⊥`. Exact, and correctly not replaced by a
    nonzero generator assumption.
12. r contracts to zero: `hrA : r.comap Polynomial.C = ⊥`. Exact.
13. κ(r) = A[x]_r / rA[x]_r: `r.ResidueField`. Exact. I read
    `Ideal.ResidueField` in `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`, and
    `IsLocalRing.ResidueField` in its Defs module; this is the quotient of the prime
    localization by its maximal ideal.
14. C is the maximal-ideal completion of A[x]_q: the conclusion's `let C :=
    AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
    (Localization.AtPrime q)`. Exact. `Localization.AtPrime.map_eq_maximalIdeal`
    identifies the ideal with q extended to the localization. I read the compatible-sequence
    completion construction and the ring/algebra instances in `AdicCompletion.Algebra`.
    Its `algebraMap_apply` is the composite of the localization map and completion map;
    the A[x]-algebra used below is the canonical one, not an arbitrary map.
15. The κ(r)-algebra C ⊗_(A[x]) κ(r): `r.Fiber C`. Exact up to the canonical
    tensor swap. The recorded `Ideal.Fiber` abbreviation is κ(r) ⊗_(A[x]) C;
    its left-factor algebra structure is the intended residue-field action. The dependency
    node explicitly authorizes this tensor order through `Algebra.TensorProduct.comm`.
16. This fibre is Noetherian: `IsNoetherianRing (r.Fiber C)`. Exact.
17. It is geometrically regular over κ(r):
    `Algebra.IsGeometricallyRegular r.ResidueField (r.Fiber C)`. Exact. I read the
    recorded definition in `Sheaf.RingTheory.GRing`: Noetherianity and regularity after
    every finite purely inseparable field extension. `IsRegularRing` in Mathlib's
    `RegularLocalRing.Defs` requires Noetherianity and regularity of every prime
    localization. Repeating Noetherianity in the explicit conjunction changes no strength.
    The finite extension quantifier at `Type (max u v)` loses no case: a finite-dimensional
    extension has a representative at the universe of its base field, and the predicate
    is invariant under the corresponding algebra isomorphism.

Edge cases: A may be a field (m = 0, complete), with q = r = (x), so equality of the
primes must and does remain allowed. The zero base ring is excluded exactly by being a
local domain; the fibre has no extra nontriviality assumption. r = 0 is excluded by the
source. Every prime characteristic, including 2, is allowed; p = 0 or 1 cannot satisfy
`hp`. No perfection, finite residue field, dimension or separability assumption is present.
The completion includes n = 0: its zero quotient imposes no restriction on the inverse
limit. There is no index-set or scheme parameter in this statement; empty product factors
in the proof and zero rings are covered by regularity's prime-localization definition.
The arbitrary universe u is explicitly declared and no free variable is left unbound.

Independent searches (2026-10-11), with words distinct from the worker's:

- LeanFinder: `geometric regularity of completed polynomial local rings at primes
  contracting to zero`; eight results for smooth/étale localizations and the complete-local
  ring criterion, none a formal-fibre theorem.
- Loogle: `AdicCompletion, Ideal.Fiber`; zero results.
- LeanSearch: `The formal fiber of the completion of a polynomial ring over a complete
  local domain is geometrically regular`; unavailable (service Internal Server Error),
  so no verdict is inferred from that attempted search.
- Direct rg for `formal.?fib|geometrically.?regular|formalFiber_isGeometricallyRegular|
  another.helper.G.ring` over upstream WeilConjectures, Mathlib RingTheory, project
  lean/Sheaf and dag/lean_names_upstream.json: only the existing project GRing definitions,
  no theorem matching this item and no collision with the delivered declaration.

Mismatch and repair verdict: none. The module has one theorem with a `sorry` proof, no
hollow definitions or private notions. Both imports serve the statement. Its module and
statement docstrings cite 07PU and the correct blueprint id; the seven numbered proof
steps preserve the node's argument, including the zero factors. Header, namespace and
line widths follow the conventions. I verified the node's `lean.statement` equals the
file signature verbatim. I retained the Lean and node unchanged; only this review report
was added. Compilation and delivery validation are recorded below.

Second-reader validation: `scompile.py` compiled the delivered module on the server in
2.2 seconds with exit code 0 and no warnings. `deliver2.py --no-push` printed
`OK (dry run): commit 813386f38 passes the preflight and compiles; nothing pushed`.
