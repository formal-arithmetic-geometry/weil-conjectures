## Worker report

The module `Sheaf.RepresentationTheory.SL2IntegralOrbitCoefficients` states
`RepresentationTheory.exists_unique_sl2_integral_orbit_coefficients`, with one `sorry`.
It changes no informal statement. It adds the missing definition node
`def-sfb-regular-sl2-representation` and imports its module. There are no dependency
repairs or statement corrections, and no mathematical dispute.

Hypotheses and conclusions, matched against the node:

- The commutative ring is `(B : Type u) [CommRing B]`; `q : ℕ` is precisely the
  nonnegative integer. The module is `(V : Type v) [AddCommGroup V] [Module B V]`
  with `[Module.Free B V] [Module.Finite B V]`. The separate module universe is
  unrestricted. Test algebras are `C : Type u`, the standard common universe with
  the base, so polynomial algebras and localizations used in the proof are included;
  there is no independently smaller test-algebra universe.
- Specified summands are `W : Fin (q+1) → Submodule B V`, `hW : DirectSum.IsInternal W`,
  and the free and finite instances for each `W i`. This is the internal form of the
  node's specified direct sum, with the actual submodule inclusions into `V`.
- The representation is `ρ : RegularSL2Representation B V`. Its `app` is exactly a
  group homomorphism into C-linear automorphisms of `C ⊗[B] V`. Its `naturality`
  uses the actual map `f.toLinearMap.rTensor V`, and `regular` says that all matrix
  entries, in one finite basis, are evaluations of polynomials in the four entries
  of `g`. Evaluation on determinant-one matrices gives exactly regular functions in
  the indicated quotient coordinate ring. Existence of representatives is equivalent
  to existence of the quotient functions; no chosen polynomial data or additional
  constraint is imposed on the action.
- `sl2Upper z` and `sl2Lower z` are Mathlib transvections with positions `(0,1)`
  and `(1,0)`. They are precisely the stated elementary matrices, using zero-based
  indexing. `sl2Weyl` is the specified product, with rows `(0,1),(-1,0)`.
  `sl2Torus t` is the standard root word
  `x₊(t)x₋(-t⁻¹)x₊(t)w⁻¹`; multiplication gives `diag(t,t⁻¹)` over every ring.
- `hweight` states the weight `2*(i.val : ℤ)-(q : ℤ)` as a unit power and its scalar
  action on every `1 ⊗ a`, `a : W i`. C-linearity gives the action on the whole
  scalar-extended summand; this imposes exactly the original weight condition.
- `v : W 0` and `hfixed` give the lowest vector and its invariance under every lower
  root element over every base algebra. No nonzero condition occurs.
- The existential family `a : ∀ i, W i` gives the coefficients in their required
  summands. `a 0 = v` is the constant coefficient assertion. The next conjunction
  is the universal polynomial orbit identity in `Polynomial B ⊗[B] V`.
- The following universal binder `b` states uniqueness among all families satisfying
  the polynomial expansion, without requiring the competitor to satisfy any of
  the additional formulas or to have its constant term specified separately.
- The upper-root formula is reindexed by `k=i+j`: the finite sum keeps precisely
  `i.val ≤ k.val`, with coefficient `choose k (k-i) * z^(k-i)` and vector `a k`.
  Thus its coefficient is `choose (i+j) j` with `0≤j≤q-i`.
- The lower-root formula is reindexed by `k=i-j`: it keeps precisely `k.val ≤ i.val`,
  with coefficient `choose (q-k) (i-k) * z^(i-k)`. Substitution gives
  `choose (q-i+j) j` with `0≤j≤i`. There is no division in either formula.
- The Weyl clause uses `(-1 : C)^i.val` and index `q-i.val`. The index-bound proof
  changes no hypothesis. These clauses quantify over all C and all z separately.
- The coefficient-of-z clause applies Mathlib's actual `Polynomial.lcoeff B 1`,
  tensored with `V`, and then `TensorProduct.lid B V`. It is `(i.val+1) • a_(i+1)`
  under exactly `hi : i.val < q`.
- For arbitrary `B → D`, the next clause characterizes all polynomial orbit
  coefficients `c : Fin(q+1) → D ⊗[B] V` by an iff: the scalar-extended polynomial
  orbit expansion holds exactly when `c i = 1 ⊗ a i`. The expansion uses
  `cancelBaseChange B D (Polynomial D) (Polynomial D) V`, not an arbitrary
  comparison. The following equality spells out that orbit expansion explicitly.
  Together with the three all-C identities and `ρ.naturality`, this states that
  the coefficients and identities commute with arbitrary base change.
- For `B → D → E` the final clause uses Mathlib's canonical
  `TensorProduct.AlgebraTensorModule.cancelBaseChange B D E E V` and explicitly
  sends `e ⊗ (d ⊗ a i)` to `(d • e) ⊗ a i`. This is the successive-base-change
  comparison in the node. It assumes only the scalar-tower compatibility, not
  injectivity or flatness of any structure map.

Dependency declarations used, with their recorded modules read in full at the
relevant signatures and docstrings:

- `def-weil-pbc-free-module`: `Module.Free` in
  `Mathlib.LinearAlgebra.FreeModule.Basic`; finiteness is Mathlib `Module.Finite`.
- `def-weil-pbc-direct-sum-modules`: `DirectSum`, its module instance, `DirectSum.lof`,
  and `DirectSum.component` in `Mathlib.Algebra.DirectSum.Basic` / `.Module`.
  The statement uses the same module's `DirectSum.IsInternal` specialization to
  specified submodules, rather than introducing another direct-sum construction.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, `TensorProduct.lift` and `ext'` in
  `.Basic`, `LinearMap.rTensor` in `.Map`. Scalar-extended bases are
  `Module.Basis.baseChange` from `.Basis`. Successive base change uses `.Tower`.
- The new node imports `Matrix.SpecialLinearGroup` and its `transvection` / `map`
  from `Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup`, with `Matrix.det` from
  `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`. It uses `MvPolynomial` and
  `MvPolynomial.eval₂` from `Mathlib.Algebra.MvPolynomial.Basic` / `.Eval`, and
  the actual `AlgHom` from `Mathlib.Algebra.Algebra.Hom`.
- Proof dependency `lem-pur-commutative-ring-binomial-expansion` has the Mathlib
  match `add_pow` in `Mathlib.Data.Nat.Choose.Sum`. This is a plain proof import.
  The other proof dependencies are already public statement imports.

Edge cases checked mathematically before writing: `q=0` has one index and trivial
weights; both root formulas have their single constant term, the Weyl sign is +1,
and the degree-one clause has no valid index. The zero ring and zero module are
permitted, including a basis of length zero. Individual zero summands and `v=0`
are permitted; no vectors need to span or be primitive. For `q=1` on the standard
module, the lowest vector is `e₂`, the upper coefficient is `e₁`, and the specified
Weyl element takes `e₂` to `e₁` and `e₁` to `-e₂`, verifying the signs. For `q=2`
on binary quadratics the middle coefficient is `2 e₁e₂`, which can vanish in
characteristic two; the formulas require no cancellation, and cover this case.
No distinctness of integer weights as elements of B is assumed: the proof compares
Laurent monomials over the universal torus, not ring-valued integer eigenvalues.

Searches made:

- `msearch.py leanfinder`, query “Polynomial orbit coefficients of a lowest weight
  SL2 vector over a commutative ring satisfy binomial root actions and Weyl reversal”:
  eight Lie-module/root-system hits, including `IsSl2Triple.HasPrimitiveVectorWith`;
  none states a group representation result over arbitrary rings.
- `msearch.py loogle`, `Matrix.SpecialLinearGroup, Representation`: zero hits.
- `msearch.py grep`, `lowest.*weight|orbit.*coeff|regular.*representation`,
  subdirectory `RepresentationTheory`: seventeen regular-representation references,
  all regular actions of abstract groups, not regular functions on SL₂.
- `msearch.py leansearch`, “natural representations of SL2 over a commutative ring
  with regular matrix coefficients”: eight matrix-group/standard-action hits.
- `msearch.py leanfinder`, “a natural family of linear SL2 representations over all
  commutative base algebras with regular polynomial matrix entries”: eight
  matrix-group/upper-half-plane action hits, no matching notion.
- `msearch.py grep`, `RegularSL2|SL2Representation|regular.*matrix.*entries`,
  subdirectory `RepresentationTheory`: zero hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for `SL2`, `SpecialLinearGroup`,
  regular SL₂ and polynomial representations found the Lie-module polynomial
  model and the field-only `SL2Hom` of `RankOneRootInterfaces`. The latter maps
  into points of a group scheme and does not encode actions on arbitrary
  scalar-extended finite free modules. Neither is a duplicate of this definition.
- Exact-name searches in Mathlib, both project roots, and
  `dag/lean_names_upstream.json` found no declaration clashes. The prescribed
  item-id grep of `lean/WeilConjectures` found no attachment.
- `tools/blueprint_refs.py search 'SL2 representation'` found zero blueprint
  nodes. Searches of definition nodes for regular/natural SL₂ found only the
  different field-only rank-one interface. No existing node carries this notion.

Source read: the actual local Milne PDF, printed pp.466–467 (PDF pp.478–479),
including the polynomial discussion before Proposition 22.14 and Lemma 22.15.
The source node explicitly marks the binomial identities over rings as an agent
supplement, not a quotation of Milne's field statements. The theorem docstring
preserves all ten proof steps, including the denominator-injectivity argument.

## New nodes

`def-sfb-regular-sl2-representation` defines precisely the natural regular action
and the root, Weyl and torus conventions needed by this item. Its module is
`Sheaf.RepresentationTheory.RegularSL2Representation`. The structure has actual
families of group homomorphisms and proof fields for naturality and polynomial
regularity. Its four matrix helpers have explicit Mathlib transvection data; no
construction uses `sorry` or an existence choice. Source: the action convention
of this item and Milne p.466's polynomial-coordinate description. The three
search kinds and DAG/project searches above are stored in the node's
`mathlib_searches` as well. No existing arbitrary-ring natural linear SL₂ action
interface was found. The item gains only this definition in `stmt_deps`.

Validation: both delivered modules compile through `scompile.py` in dependency
order, including the sandbox and library-name checks, with no errors or unexpected
warnings. The first theorem compile exposed an ambiguous `Polynomial.X` scalar;
explicit `(Polynomial.X : Polynomial B)` / `Polynomial D` annotations repaired
that elaboration issue without changing the statement. The declaration signatures
in both node records are copied verbatim from the delivered files. The only
postponed proof is the item's named theorem, with the full ten-step proof plan.

## Second reading by Q50

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
