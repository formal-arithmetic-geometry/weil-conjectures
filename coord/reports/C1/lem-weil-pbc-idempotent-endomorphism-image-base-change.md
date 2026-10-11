## Worker report

The module `Sheaf.LinearAlgebra.IdempotentImageBaseChange` states
`LinearMap.idempotent_image_baseChange`, with `sorry` and no new definitions.
The node is unchanged except for its `lean` record. No statement correction or dispute.

Hypotheses and clauses, individually:

- The arbitrary commutative ring is `{R : Type u} [CommRing R]`; rank `n ≥ 0`
  is `(n : ℕ)`. The finite free module is `Fin n → R`, the standard coordinate model
  of `R^{⊕ n}` (finite direct sums equal finite products).
- The arbitrary R-linear endomorphism is `p : (Fin n → R) →ₗ[R] (Fin n → R)`.
  Its idempotence is precisely `hp : p.comp p = p`.
- The standard-basis matrix X is `LinearMap.toMatrix' p`: its (i,j) entry is
  `p (Pi.single j 1) i`, by the full definition in Matrix.ToLin.
- Clause (i), internal direct sum of the two images, is
  `IsCompl p.range (LinearMap.id - p).range`. For submodules `IsCompl` says the
  intersection is bottom and the sum is top, exactly the internal direct sum assertion.
- The stated identification of the second summand with the kernel is
  `(LinearMap.id - p).range = p.ker`.
- Finite generation and projectivity are respectively `Module.Finite R p.range`
  and `Module.Projective R p.range`. No freeness of the image is asserted.
- Clause (ii), arbitrary ring map, is `{S : Type v} [CommRing S] (ρ : R →+* S)`.
  `letI : Algebra R S := ρ.toAlgebra` supplies exactly its scalar structure,
  without adding an algebra hypothesis unrelated to ρ.
- The S-linear endomorphism with entrywise matrix ρ(X) is the let-bound
  `pS := Matrix.toLin' ((LinearMap.toMatrix' p).map ρ)`.
- Its idempotence is `pS.comp pS = pS`.
- The canonical S-linear tensor map is specified as an existential `f`, together with
  `∀ (s : S) (x : p.range), f (s ⊗ₜ[R] x) = fun i ↦ s * ρ (x.val i)`.
  Pure tensors generate the tensor product, so this formula determines f uniquely;
  it cannot select an unrelated embedding. The tensor factors are written in Mathlib's
  scalar-extension convention `S ⊗[R] p.range`, which has the standard S-action on
  its left factor. The canonical tensor commutor identifies this with the node's
  `p.range ⊗[R] S`, and carries `x ⊗ s` to `s ⊗ x`, so the formula is precisely
  the node's `v ⊗ s ↦ s · ρ(v)`, with its S-module structure transported accordingly.
- Injectivity is `Function.Injective f`; image equality is `f.range = pS.range`.
- The resulting S-module identification is the existential linear equivalence
  `e : S ⊗[R] p.range ≃ₗ[S] pS.range`. The equation
  `pS.range.subtype.comp e.toLinearMap = f` explicitly requires that its map
  followed by inclusion be the same canonical map, not an arbitrary isomorphism.

Dependencies: `stmt_deps` is empty, so no recorded dependency declarations are needed.
The imports use Mathlib's existing `LinearMap.toMatrix'` and `Matrix.toLin'`
(`Mathlib.LinearAlgebra.Matrix.ToLin`), `Module.Projective`
(`Mathlib.Algebra.Module.Projective`, also bringing in tensor products), and
`Module.Finite` (`Mathlib.RingTheory.Finiteness.Basic`). Submodule range, kernel,
complementarity, tensor product, and linear equivalence are Mathlib notions throughout.
The proof docstring records all three node steps and the proof-only dependency
`lem-weil-pbc-module-base-change-universal-property`.

Source read: the local Stacks TeX is absent on this machine; the full statement and proof
of https://stacks.math.columbia.edu/tag/07M5 were opened. Its final projector-image
argument is the one specified by the node. No additional restriction such as flatness
is needed in this split-summand calculation.

Edge cases checked mathematically before writing: rank zero gives zero images and zero
tensor modules, with complementary bottom submodules since top equals bottom. The zero
ring is allowed (no Nontrivial hypotheses). For p = 0 the first image vanishes; for p = 1
it is the whole module. Maps to the zero ring and non-flat quotients remain allowed:
the inclusion is split before tensoring, which preserves its left inverse for every S.
Independent universes u and v allow any source and target ring sizes. Every variable and
universe is explicitly bound.

Searches (all through `/home/ubuntu/weil-launcher/msearch.py`, except the noted rg):

- LeanFinder: `The image of an idempotent endomorphism of a finite free module is finite
  projective and its image commutes with arbitrary base change`. Eight hits, including
  `LinearMap.isProj_range_iff_isIdempotentElem` and
  `LinearMap.IsIdempotentElem.isProj_range`; none states the complete node.
- Loogle: `LinearMap.baseChange, LinearMap.range`. No hits.
- Mathlib grep: `range_baseChange|baseChange_range|liftBaseChange|toLin.*map`
  under `LinearAlgebra`. Twenty-five hits, mostly unrelated bilinear-map and matrix
  results; no complete idempotent-image base-change statement.
- LeanSearch: `image of idempotent linear map commutes with tensor base change`.
  Unavailable: Internal Server Error. No verdict inferred from the unavailable service.
- rg over `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  `idempotent.*base|range_baseChange|baseChange_range|lem-weil-pbc-idempotent-endomorphism-image-base-change`:
  only unrelated blowup, scheme-étale range, and clopen idempotent-base-change results.
  No existing statement. The node-id search found no upstream declaration.
- rg for `idempotent_image_baseChange` in Mathlib, WeilConjectures, lean/Sheaf,
  and the upstream names index found no name collision.

Server validation: `scompile.py C1 lem-weil-pbc-idempotent-endomorphism-image-base-change
<module>` exited 0, compiled in 1.3 seconds, with no warnings or errors.

## Second reading by C1

I read the node and the complete declaration independently. The correspondence is:

- The node's commutative ring `R`, rank `n ≥ 0`, and endomorphism `p` are rendered by
  `{R : Type u} [CommRing R]`, `(n : ℕ)`, and
  `p : (Fin n → R) →ₗ[R] (Fin n → R)`.
- Idempotence is exactly `hp : p.comp p = p`; the matrix `X` is rendered by
  `LinearMap.toMatrix' p`, and the base changed map is the let-bound
  `pS := Matrix.toLin' ((LinearMap.toMatrix' p).map ρ)`.
- Clause (i) is rendered verbatim by `IsCompl p.range (LinearMap.id - p).range`,
  `(LinearMap.id - p).range = p.ker`, `Module.Finite R p.range`, and
  `Module.Projective R p.range`.
- Clause (ii)'s arbitrary ring map is `(S : Type v) [CommRing S]
  (ρ : R →+* S)` with `letI : Algebra R S := ρ.toAlgebra`; no flatness,
  finiteness, nonzero, or characteristic hypothesis is added. The idempotence
  clause is `pS.comp pS = pS`.
- The canonical map is an existential `S ⊗[R] p.range →ₗ[S] (Fin n → S)`
  with the pure-tensor formula `f (s ⊗ₜ[R] x) = fun i ↦ s * ρ (x.val i)`, followed
  by `Function.Injective f` and `f.range = pS.range`. The final existential linear
  equivalence and compatibility equation are exactly the node's last clause.
  Mathlib supplies the S-linear scalar-extension convention as `S ⊗[R] p.range`;
  its canonical tensor commutor is the node's displayed `p.range ⊗[R] S` map, so
  this is the same base-change object and formula rather than an extra assumption.

Edge cases checked: `n = 0`, the zero ring, `p = 0`, `p = 1`, maps to the zero
ring, non-flat ring maps, and independent universes `u` and `v` are all admitted.
No variable or universe is implicit or unbound.

I searched Mathlib, `WeilConjectures`, `lean/Sheaf`, and the upstream-name index with
`rg`, and ran LeanFinder, Loogle, and the recorded LeanSearch query for projector
image/base-change statements. They found only partial tensor/range lemmas and no
statement of this node; `LinearMap.idempotent_image_baseChange` is new.

No mismatch with the node was found after checking every hypothesis and conclusion
clause. The temporary direct `p.range ⊗[R] S` spelling was rejected by Mathlib because
that tensor order has no inferred `Module S` instance; the retained `S ⊗[R] p.range`
spelling is the standard scalar-extension representation documented in the declaration
and is canonically commuted to the node's order.
