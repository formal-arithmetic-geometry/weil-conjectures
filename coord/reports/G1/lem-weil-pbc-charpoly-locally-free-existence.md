## Worker report

The module states `Algebra.charpoly_locallyFree_exists_unique`. It binds a commutative ring `A`, an `A`-module `M`, rank `n`, a finite standard-open family `f`, the unit-ideal hypothesis `Ideal.span (Set.range f) = ⊤`, local bases of `LocalizedModule.Away (f i) M`, and an endomorphism `φ`. Its conclusion is existence and uniqueness of a polynomial `χ : Polynomial A`. For every commutative target ring and ring map, `RingHom.toAlgebra` supplies the base-change algebra structure; every basis of `A' ⊗[A] M` of cardinality `n` gives the mapped polynomial as the matrix characteristic polynomial. The displayed expansion uses `X ^ n` plus coefficients indexed by `Fin n`, and the final implication gives the usual matrix characteristic polynomial when `M` is free.

The localization dependency is rendered by `LocalizedModule.Away`; polynomial rings by `Polynomial`; base change is represented by the scoped tensor product `A' ⊗[A] M`; the free-module characteristic polynomial is `Matrix.charpoly` of `LinearMap.toMatrix`. The dependency records are Mathlib declarations: `LocalizedModule.Away`, `Localization.Away`, `Polynomial`, and `Matrix.charpoly`.

Edge cases checked: `n = 0` makes `Fin n` empty and the expansion reduces to `1`; `r = 0` is allowed syntactically (the unit-ideal hypothesis then controls consistency); zero modules and zero rings are not excluded by the binders. Arbitrary universes are covered by explicit `Type*` binders.

Searches: the node's recorded LeanSearch/LeanFinder/Loogle/grep searches found only free-module characteristic polynomials in Mathlib. Additional repository searches found no existing locally-free characteristic-polynomial declaration.

No statement correction or `STATEMENT-DISPUTED` note was needed.

## Earlier second reading (a previous round; superseded)

The file and node were read together. The ring, module, rank, covering elements, unit-ideal condition, local freeness witnesses, endomorphism, arbitrary ring-map base changes, characteristic-polynomial clause, monic expansion, uniqueness, and free case all have corresponding Lean binders or conjuncts. The tensor product is written in Mathlib's left-module order `A' ⊗[A] M`, which is canonically the stated scalar extension. No mismatch was found.


## Second reading by G1

I independently read the complete node, its seven proof steps, all five statement-dependency
nodes and their recorded Mathlib declarations. There are no new nodes, dependency modules,
or stage-2 statement corrections in this delivery. The TeX statement remains unchanged.
The locally free characteristic-polynomial construction is absent from the checked libraries.

Source reading: this clone has no Stacks .tex files, so I opened the official Stacks sources:
[more-algebra.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex),
label `lemma-characterize-henselian-pair`, proof (3)⇒(1), and
[algebra.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex),
label `lemma-standard-covering` (Tags 09XI and 00EJ). Current line numbers differ from the
node's stored line numbers. The former explicitly constructs characteristic polynomials on
finite locally free summands by gluing free matrix characteristic polynomials; the latter
provides exactness of the standard localization cover. The henselian pair is the surrounding
application, not a hypothesis of this general construction. No Noetherian, field,
nontriviality, or characteristic hypothesis is required for this extracted lemma.

Object/hypothesis/conclusion inventory, matched against the final Lean:

- Commutative ring A: `{A : Type u} [CommRing A]`. Exact; includes the zero ring.
- A-module M: `{M : Type v} [AddCommGroup M] [Module A M]`. Exact; independent universe,
  and no global freeness, projectivity or finiteness instance added.
- Nonnegative integer n and finite list of length r: `{n r : ℕ} (f : Fin r → A)`.
  Exact; both zero values are allowed, and indexing starts at zero without changing the list.
- Unit-ideal generation: `hgen : Ideal.span (Set.range f) = ⊤`. Exact.
- Rank-n free localization at each f_i: `hfree : ∀ i : Fin r, ∃ e : Module.Basis (Fin n)
  (Localization.Away (f i)) (LocalizedModule.Away (f i) M), True`. Exact; existence of a
  basis, not a basis chosen globally as extra data. The terminal True adds no hypothesis.
  `LocalizedModule.Away` is localization at the powers of f_i, and its scalar action is the
  recorded `Localization.Away` action (`moduleOfIsLocalization` in LocalizedModule.Basic).
- A-linear endomorphism: `(φ : M →ₗ[A] M)`. Exact.
- Polynomial over A: `∃ χ : Polynomial A`. Exact; Polynomial wraps finitely supported
  natural-number coefficients with convolution multiplication.
- Every commutative target ring and every ring map: `∀ (A' : Type (max u w)) [CommRing A']
  (ρ : A →+* A')`, with `RingHom.toAlgebra ρ`. Exact as a universe-polymorphic construction;
  no injectivity, flatness, locality, or finiteness imposed on ρ.
- Only scalar extensions free of rank n, and computed in any basis: `∀ e : Module.Basis
  (Fin n) A' (A' ⊗[A] M)`. This is vacuous when there is no such basis, as required.
  The tensor factor order is the dependency node's recorded Mathlib representation; tensor
  symmetry identifies it with M ⊗_A A'. The opened `LinearMap.baseChange` signature and
  `baseChange_tmul` send a ⊗ m to a ⊗ φ(m), exactly the required map.
- Mapped polynomial equals the determinant polynomial: `χ.map ρ = (LinearMap.toMatrix e e
  (φ.baseChange A')).charpoly`. Exact. I opened `toMatrix` and `Matrix.charpoly`;
  `charmatrix` is scalar X minus the matrix mapped through C, and charpoly is its determinant.
- Exactly one polynomial satisfying that property: the local predicate P contains only
  the preceding base-change condition; `(P χ ∧ ∀ χ' : Polynomial A, P χ' → χ' = χ)`.
  Exact, and competitors need not separately satisfy the expansion or free-case conjuncts.
- Monic expansion: `∃ c : Fin n → A, χ = Polynomial.X ^ n + ∑ k : Fin n,
  Polynomial.C (c k) * Polynomial.X ^ (k : ℕ)`. Exact, with precisely the coefficients
  below n; over the zero ring this equality retains its intended meaning.
- Free case: `Nonempty (Module.Basis (Fin n) A M) → ∀ e : Module.Basis (Fin n) A M,
  χ = (LinearMap.toMatrix e e φ).charpoly`. Exact in every rank-n basis.

Edge cases: n = 0 has an empty coefficient sum and the 0-by-0 determinant is 1; no positive
rank assumption occurs. For r = 0, hgen forces the zero ring, which is allowed; all modules
and polynomials over it are zero objects, so uniqueness remains consistent. Zero modules,
zero endomorphisms, zero rings and arbitrary characteristics are covered. Empty schemes are
not objects of this module lemma; the empty affine spectrum corresponds to the allowed zero
ring. A and M have independent explicit universes. The original independently quantified
`A' : Type*` could live below A and fail to include the localization rings needed for
uniqueness. I changed it to `Type (max u w)`, which contains those rings (using ULift if
necessary). The arbitrary w covers targets of any larger universe; smaller targets can be
lifted with their ring maps, bases and polynomial equations. No base or module is confined
to Type 0, and no variable/universe is left auto-implicit.

Independent searches, using different descriptions from the worker:

- msearch leansearch: "characteristic polynomial for constant rank finite projective modules
  over rings". Service returned Internal Server Error / UNAVAILABLE; no verdict inferred.
- msearch loogle: `"charpoly"`. Returned Matrix.charpoly and its elementary matrix results,
  including map/reindex/isEmpty, not the locally free construction.
- msearch leanfinder: "determinant polynomial of endomorphism on locally free modules over
  commutative rings". Returned LinearMap determinant and free charpoly results; I opened
  Charpoly.Basic and confirmed `[Module.Free R M] [Module.Finite R M]` are required.
- rg in Mathlib Charpoly and the source WeilConjectures Charpoly modules for `locally.free`,
  `locallyFree` and `projective`: no matching construction. rg for charpoly/characteristic
  polynomial across repository lean/Sheaf and source WeilConjectures found free matrix,
  direct-sum and eigenvalue statements, not this general module statement. Name search in
  dag/lean_names_upstream.json, source WeilConjectures and lean/Sheaf found no existing
  `charpoly_locallyFree_exists_unique`. All five existing dependency notions are used;
  no private replacement definition or missing dependency module is needed.

Mismatches and repairs: moved uniqueness outside the additional expansion/free-case conditions
so it characterizes the base-change property alone; related the target universe to the base
universe to include localization tests; replaced the three-sentence proof synopsis with all
seven node proof steps and their dependency names; added the standard copyright header;
imported TensorProduct.Tower directly for the baseChange declaration used. No mathematical
node correction was necessary. The theorem remains a single named sorry, with no proved
lemma or hollow definition. The local P is only a let abbreviation of the displayed property.
All imports serve declarations used in the statement. The node's lean.statement was updated
verbatim from the repaired signature. The prescribed scompile command compiled the final
70-line module cleanly (1.3 seconds), with no warnings or errors.
