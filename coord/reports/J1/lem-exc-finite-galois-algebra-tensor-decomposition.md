## Worker report

The module states `AlgebraicGeometry.finiteGaloisTensorCoproduct` with a `sorry`
proof. It gives an isomorphism from the coproduct of copies of `Spec E` to the
affine fibre product and fixes both projection maps on every component.

- `L E : Type u`, `[Field L]`, `[Field E]`, `[Algebra L E]` render the field
  extension `E/L` and its structure morphism.
- `[FiniteDimensional L E] [IsGalois L E]` render finite Galois. Mathlib's
  `IsGalois` means separable and normal, with separability algebraic.
- `E ≃ₐ[L] E` is `Q = Aut_L(E)`; its finiteness follows from the finite
  dimensionality hypothesis. `φ : (E ⊗[L] E) ≃ₐ[L] ((E ≃ₐ[L] E) → E)` is
  the supplied tensor-product decomposition. `hφ` states its value on every
  pure tensor and every `q` is `a * q b`.
- The pullback of the two maps `Spec.map (CommRingCat.ofHom (algebraMap L E))`
  is `W = Spec E ×_(Spec L) Spec E`. The `∃ e : (∐ ... ) ≅ pullback ...`
  clause gives the asserted isomorphism with the coproduct indexed by `Q`.
- The first conjunct says each coproduct injection followed by `e.hom` and
  `pullback.fst` equals the identity on `Spec E`. It specifies that the
  isomorphism is over `Spec E` via the first projection.
- The second conjunct says the same component followed by `pullback.snd`
  equals `Spec.map` of `q.toRingEquiv.toRingHom`, hence is `Spec q`.

Statement dependencies used from Mathlib: `Algebra` in
`Mathlib.Algebra.Algebra.Defs`; `Algebra.IsSeparable` in
`Mathlib.FieldTheory.Separable` (through `IsGalois` in
`Mathlib.FieldTheory.Galois.Basic`); `AlgebraicGeometry.Spec` and `Spec.map`
in `Mathlib.AlgebraicGeometry.Scheme`; `CategoryTheory.Limits.pullback`,
`pullback.fst`, and `pullback.snd` in
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`;
`Algebra.TensorProduct.includeLeft`, `includeRight` in
`Mathlib.RingTheory.TensorProduct.Basic`; and
`AlgebraicGeometry.pullbackSpecIso` in `Mathlib.AlgebraicGeometry.Pullbacks`.
For the proof, `AlgebraicGeometry.sigmaSpec` and its finite-index `IsIso`
instance in `Mathlib.AlgebraicGeometry.Limits` express the finite-product
spectrum decomposition. Every `stmt_deps` record was checked against its
Mathlib declaration or signature.

Edge cases: `E = L` gives a singleton automorphism group and one coproduct
component; the statement makes no characteristic restriction. A field is
nonzero, so the zero-ring and empty-spectrum cases do not arise. `Q` cannot
be empty because it contains the identity automorphism.

Searches: `leanfinder` with "affine fibre product Spec E over Spec L is
disjoint union of Spec E indexed by Galois automorphisms with projection
maps" found `pullbackSpecIso` but no exact theorem. `loogle` with
`AlgebraicGeometry.pullbackSpecIso,AlgebraicGeometry.Spec,CategoryTheory.Limits.coproduct`
found no match (the final identifier was unknown). `msearch.py grep` with
`coproduct.*Scheme|HasCoproducts.*Scheme|Sigma.*Scheme` in
`AlgebraicGeometry` found the generic finite coproduct construction in
`Mathlib.AlgebraicGeometry.Limits`. `rg` for Galois/tensor/coproduct in
Mathlib and the source repository found no exact declaration. `rg` for
`lem-exc-finite-galois-algebra-tensor-decomposition` in the source Lean
and the project's `lean/Sheaf` tree found no declaration.

The local `literature/stacks-project/pione.tex` was absent on this machine;
I checked the official Stacks Project Tag 03SF web page, which gives the
finite étale Galois-cover context. The node's proof also cites Tags 01I4
and 00ED for the affine pullback and finite-product spectrum calculations.

## Second reading by J1

I read the node statement, its six statement-dependency records and the Lean
module independently. The cited local `pione.tex` is absent, so I checked Stacks
Tags 03SF, 01I4 and 00ED on the official site. Tag 03SF supplies the finite
etale Galois-cover context; Tags 01I4 and 00ED give the affine fibre-product
and product-spectrum facts used by the node's proof.

- The fields `L` and `E` and extension `E/L` are `(L E : Type u) [Field L]
  [Field E] [Algebra L E]`. This is the field-extension notion recorded by
  `def-pc-field-extension`, with structure map `algebraMap L E`.
- Finite Galois is `[FiniteDimensional L E] [IsGalois L E]`. Mathlib's
  `IsGalois` is separable algebraic plus normal (checked in
  `FieldTheory/Galois/Basic.lean`); `FiniteDimensional` supplies finiteness.
  There is no extra characteristic assumption.
- `Q = Aut_L(E)` is `E ≃ₐ[L] E`, the full group of algebra automorphisms,
  both in the product codomain and as the coproduct index. No subgroup or
  alternative set of embeddings is substituted.
- The supplied `L`-algebra isomorphism is
  `(φ : (E ⊗[L] E) ≃ₐ[L] ((E ≃ₐ[L] E) → E))`.
  `(hφ : ∀ (a b : E) (q : E ≃ₐ[L] E),
  φ (a ⊗ₜ[L] b) q = a * q b)` fixes its canonical value on every pure
  tensor and every automorphism. This is exactly the node's supplied `phi`,
  not an additional existence assumption.
- `π : Spec E ⟶ Spec L` is
  `Spec.map (CommRingCat.ofHom (algebraMap L E))`. Both arguments of
  `pullback` are this map, so the resulting object is the node's `W`.
  These are the `Spec` and `pullback` declarations recorded by
  `def-weil-affine-spectrum` and `def-pc-fibre-product`.
- `∃ e : (∐ fun _ : E ≃ₐ[L] E => Spec (.of E)) ≅ pullback ...`
  is the asserted scheme isomorphism from the coproduct of the `Q` copies
  to `W`. Its orientation is the one required by the two component formulas.
- The first conjunct says, for every `q`, `Sigma.ι ... q ≫ e.hom ≫
  pullback.fst _ _ = 𝟙 (Spec (.of E))`. Thus the isomorphism is over
  `Spec E` through the first projection, and the first component map is
  the identity. The second conjunct uses `pullback.snd` and sets the same
  composite equal to `Spec.map (CommRingCat.ofHom
  q.toRingEquiv.toRingHom)`, precisely `Spec q`. Both conclusions have the
  node's universal quantifier over `q`; no projection label is omitted.

Edge cases: `Q` contains the identity, so the index set is never empty.
When `E = L`, the group is trivial and the statement has one component.
Fields exclude the zero ring, so `Spec E` is not an empty scheme. No natural
number or characteristic restriction occurs. `Type u` is an arbitrary
universe, and every universe and variable is explicitly bound. The product
and coproduct use the same index type, with no small finite enumeration chosen.

Independent searches used `msearch.py` LeanFinder query "Galois extension
affine spectrum self fiber product disjoint union automorphisms projection
maps" (generic pullback results, no exact theorem), Loogle query
`AlgebraicGeometry.pullbackSpecIso, AlgebraicGeometry.sigmaSpec` (zero hits),
and grep query `finiteGaloisTensorCoproduct|Galois.*sigmaSpec|sigmaSpec.*Galois`
(zero hits). I also searched the project's `lean/Sheaf`, the source
`WeilConjectures`, and Mathlib by `Galois` with `coproduct` or `pullback`,
and by `sigmaSpec` with `tensor` or `IsGalois`; no exact statement exists.
Mathlib supplies the generic `pullbackSpecIso` and `sigmaSpec`, which are
proof tools rather than duplicates of this conclusion.

Verdict: the Lean signature matches every object, hypothesis, and conclusion
clause of the node. No mismatch was found, and the module and node record
needed no change. The theorem has only a `sorry` proof, its source and
blueprint appear in both docstrings, and `scompile.py` compiled it cleanly.
