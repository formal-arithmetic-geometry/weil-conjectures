## Worker report

The module `Sheaf.RingTheory.ModelFibreRegularityDescent` states
`Algebra.model_fibre_regularity_descent`, with its sole proof `sorry`. There are no
new definitions, auxiliary theorems, dependency repairs, or statement corrections.
The node copy changes only `lean`. I read Stacks `more-morphisms.tex`,
`lemma-slice-given-element` (Tag 056Y), including the second paragraph's flat local
comparison and descent of the specified nonzerodivisor. The module docstring
contains the seven-step proof of this DAG node, with its dependency ids.

The statement uses the recorded Mathlib fibre convention, namely
`p.Fiber B = p.ResidueField ⊗[A] B`. Thus it reverses both displayed tensor-factor
orders from the prose via tensor symmetry, without changing any ring or map.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Four commutative rings, of arbitrary sizes | `A₀ : Type u₀`, `A : Type u`, `B₀ : Type v₀`, `B : Type v`, with four `CommRing` instances; four explicitly declared independent universes |
| Ring homomorphism `A₀ → A`, model algebra `B₀/A₀`, algebra `B/A` | `[Algebra A₀ A] [Algebra A₀ B₀] [Algebra A B]`; the corresponding `algebraMap`s are the ring homomorphisms |
| Given base-change isomorphism | `e : A ⊗[A₀] B₀ ≃ₐ[A] B` |
| Prime `q` and contraction `p` | `(q : Ideal B) [q.IsPrime]`, `(p : Ideal A) [p.IsPrime]`, and `hp : p = q.comap (algebraMap A B)` |
| Model map `b₀ ↦ e(1 ⊗ b₀)` and its contracted prime `q₀` | `e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom`; `hq₀` sets `q₀` equal to the contraction of `q` under exactly that map |
| Common contraction `p₀` | `hp₀ : p₀ = p.comap (algebraMap A₀ A)`; the first conclusion also states `p₀ = q₀.comap (algebraMap A₀ B₀)` |
| Residue fields and fibres | `p₀.ResidueField`, `p.ResidueField`, `p₀.Fiber B₀`, `p.Fiber B` use the recorded declarations directly |
| Canonical residue-field extension | `[Algebra p₀.ResidueField p.ResidueField]`, with `hk` identifying its algebra map with `Ideal.ResidueField.map p₀ p (algebraMap A₀ A) hp₀` |
| Canonical `k`-algebra isomorphism of the base-changed model fibre and the fibre | `∃ Φ : p.ResidueField ⊗[p₀.ResidueField] (p₀.Fiber B₀) ≃ₐ[p.ResidueField] p.Fiber B`; its following equation fixes the value on EVERY `c ⊗ (c₀ ⊗ b₀)` to `(c * u(c₀)) ⊗ e(1 ⊗ b₀)` |
| Fibre prime corresponding to `q` | `∃ (r : Ideal (p.Fiber B)) (_ : r.IsPrime)`, with `r.comap Algebra.TensorProduct.includeRight.toRingHom = q` |
| Its contraction to the model fibre | `∃ (r₀ : Ideal (p₀.Fiber B₀)) (_ : r₀.IsPrime)`, with `r₀ = r.comap (Φ.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)`; it also states that the contraction to `B₀` is `q₀` |
| Induced local homomorphism `C₀ → C` | `∃ ψ : Algebra (Localization.AtPrime r₀) (Localization.AtPrime r)`, with `IsLocalHom ψ.algebraMap`; the equation for every model-fibre element `z` identifies it with the localization of `z ↦ Φ(1 ⊗ z)` |
| Faithful flatness of that particular map | `Module.FaithfullyFlat (Localization.AtPrime r₀) (Localization.AtPrime r)` uses the locally bound algebra structure `ψ`, in the project convention |
| Canonical quotient identifications | `ε₀` and `ε` are ring equivalences from `B₀_q₀ / p₀ B₀_q₀` and `B_q / p B_q` to `Localization.AtPrime r₀` and `Localization.AtPrime r`; the extended ideals are exactly `(p₀.map (algebraMap A₀ B₀)).map (algebraMap B₀ _)` and its un-subscripted analogue |
| Naturality of these identifications | The equations for every `b₀` and `b` identify their images with `1 ⊗ b₀` and `1 ⊗ b` in the respective fibre localizations; a third equation explicitly states commutation from `B₀` through `ψ` and through `e` |
| Specified element with `a = e(1 ⊗ a₀) ∈ q` | `∀ a₀ : B₀, e (1 ⊗ₜ[A₀] a₀) ∈ q → ...`; `a` is written as its defining expression, never introduced as an independent element |
| Multiplication by its image in `C` is injective | `Function.Injective (fun x : Localization.AtPrime r ↦ algebraMap (p.Fiber B) (Localization.AtPrime r) (1 ⊗ₜ[A] e (1 ⊗ₜ[A₀] a₀)) * x)` |
| Regular singleton in `C₀` | `RingTheory.Sequence.IsRegular (Localization.AtPrime r₀) ([algebraMap (p₀.Fiber B₀) (Localization.AtPrime r₀) (1 ⊗ₜ[A₀] a₀)])` |
| Image belongs to the maximal ideal | Membership of the same image in `IsLocalRing.maximalIdeal (Localization.AtPrime r₀)` |
| It is a nonzerodivisor | Explicit `Function.Injective` for multiplication by this image on `Localization.AtPrime r₀` |
| Its quotient is nonzero | `Nontrivial (Localization.AtPrime r₀ ⧸ Ideal.span {the same image})` |

The contraction equations are a way of naming the contractions, rather than extra
geometric assumptions. Similarly `hk` is a fully explicit way to put the canonical
residue-field scalar structure in the type of the tensor product. For every input
in the prose, `Ideal.ResidueField.map ... hp₀` exists and its `.toAlgebra` supplies
this instance and `hk` by reflexivity. Thus this binder does not demand separability,
flatness, or any additional property of the given base change. It rules out using
an unrelated field embedding. Both quotient identifications and the local map are
characterized on the original elements, which uniquely determines the maps on all
fractions. In particular these are not arbitrary isomorphisms, arbitrary ring maps,
or mere `Nonempty` witnesses.

Dependency declarations read and reused:

- `def-weil-pbc-module-tensor-product`: `TensorProduct` and `TensorProduct.mk`
  (`Mathlib.LinearAlgebra.TensorProduct.Defs`); read also `TensorProduct.lift`,
  `TensorProduct.ext'` (`Basic`) and `LinearMap.rTensor` (`Map`) from its recorded
  Mathlib match. Tensor algebra and the two inclusions come from
  `Mathlib.RingTheory.TensorProduct.Basic`.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`
  (`Mathlib.RingTheory.Localization.AtPrime.Basic`), `Ideal.ResidueField` and
  `Ideal.ResidueField.map` (`Mathlib.RingTheory.LocalRing.ResidueField.Ideal`),
  and `Ideal.Fiber` (`Mathlib.RingTheory.LocalRing.ResidueField.Fiber`).
- `def-weil-pbc-faithfully-flat-ring-map`: `Module.FaithfullyFlat`
  (`Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`). Its recorded ring-map
  specialization `RingHom.FaithfullyFlat` was also read; the delivered statement
  follows STATE's algebra/module convention instead of a bare ring-map predicate.
- `def-weil-pbc-regular-sequence`: `RingTheory.Sequence.IsRegular`
  (`Mathlib.RingTheory.Regular.RegularSequence`), which includes weak regularity
  and the nonzero-quotient condition. It is used for the singleton with the ring
  itself as module.
- Proof dependency `lem-weil-pbc-fibre-ring-localization-quotient`:
  `Ideal.Fiber.algEquivAux₁` and `Ideal.Fiber.algEquivQuotient`
  (`Mathlib.RingTheory.LocalRing.ResidueField.Fiber`), read in full.
- Proof dependency `lem-weil-pbc-field-extension-base-change-faithfully-flat`:
  the tensor-product instance for `Module.FaithfullyFlat`
  (`Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`).
- Proof dependency `lem-weil-pbc-flat-local-ring-maps`:
  `RingHom.Flat.localRingHom` (`Mathlib.RingTheory.RingHom.Flat`) and
  `Localization.localRingHom`, its fraction equation and its `IsLocalHom` instance
  (`Mathlib.RingTheory.Localization.AtPrime.Basic`).
- Proof dependencies `lem-weil-pbc-flat-local-hom-faithfully-flat` and
  `lem-weil-pbc-faithfully-flat-universally-injective`:
  `Module.FaithfullyFlat.of_flat_of_isLocalHom` and
  `Module.FaithfullyFlat.tensorProduct_mk_injective`
  (`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`).
- Proof dependency `lem-weil-pbc-fibre-ring-local-ring-natural-iso`:
  `Ideal.Fiber.localRingHom_surjective_ker_quotientEquiv`
  (`WeilConjectures.RingTheory.FibreLocalRingNaturalIso`), including its full
  signature, docstring, and construction. This is imported privately as a proof
  dependency, not redeclared.

All statement dependencies are public imports (including their owning transitive
Mathlib imports); the additional proof-dependency modules are plain imports.
There is no unused project-specific import and no duplicate Sheaf twin import.
The example `Sheaf.CategoryTheory.CompactObject` is now withdrawn; its node records
the live `WeilConjectures.CategoryTheory.CompactObject`, which I also read for the
module-mode header and declaration conventions.

Edge cases checked mathematically before finalizing:

- The zero ring cannot support the specified prime `q`; this excludes no valid
  input. Existence of `q` forces all the relevant localized fibre rings to be
  nontrivial.
- No assumption on flatness of `A₀ → A` is used: for example the base change
  `Z → F_p`, `B₀ = Z[T]`, and `q = (T)` yields both fibre local rings
  `F_p[T]_(T)`. The singleton `T` satisfies the asserted conclusions.
- For the identity base change the fibre comparison is the canonical identity
  under the tensor unit equivalence; the statement includes this case.
- Arbitrary transcendental or inseparable residue-field extensions are admitted;
  any extension of fields is faithfully flat and the subsequent local map is
  flat local. No characteristic or separability binder occurs.
- A field fibre stalk has maximal ideal zero, so an element in it cannot at once
  satisfy the injectivity premise. A unit cannot belong to `q`. The final
  implication is correctly vacuous in these cases, while all comparison clauses
  still hold independently of the chosen element.
- If the chosen element is zero, or a nilpotent such as `ε` in
  `k[ε]/(ε²)`, its multiplication is not injective on the nonzero local ring.
  The regular-singleton conclusion is therefore not falsely asserted.
- No Noetherian or finite-presentation condition enters descent: injectivity of
  the faithfully flat map reflects the zero product, and containment in the
  maximal ideal supplies the nonzero quotient.
- All four ring universes remain independent; tensor products and prime
  localizations live in the corresponding maxima. There is no universe equality,
  small test-object quantifier, or file-local notation in the signature.

Searches actually run through `msearch.py Q63 lem-trf-model-fibre-regularity-descent`:

1. `leanfinder`, query `Base change algebra fibre local rings are related by a
   canonical faithfully flat local map, and regular singletons descend`: eight
   hits, including `Algebra.HasGoingDown.of_flat`, `Algebra.QuasiFiniteAt.baseChange`,
   and stable-base-change results for smooth maps. No full statement or canonical
   fibre-stalk comparison with the designated element.
2. `loogle`, query `"Fiber", "localRingHom"`: zero hits.
3. `grep`, query `fiber.*faithfullyFlat|faithfullyFlat.*fiber|localRingHom`,
   subdirectory `RingTheory`: 25 hits, including the generic
   `Localization.localRingHom` and local-property infrastructure. These provide
   constituents already used through the recorded nodes, not this theorem.
4. `leansearch`, query `A canonical isomorphism of fibre rings under base change
   induces a faithfully flat map of fibre local rings and descends a regular
   element`: eight hits, including regular-sequence ASCENT
   (`RingTheory.Sequence.IsRegular.of_faithfullyFlat_of_isBaseChange`,
   `.of_faithfullyFlat`), `IsSMulRegular.of_flat_of_isBaseChange`, and faithful-flat
   base-change stability. None identifies these two fibre local rings and
   descends this specified singleton.
5. `rg -n` over `lean/WeilConjectures` and `lean/Sheaf`, query
   `model[Ff]ibre|model_fibre|lem-trf-model-fibre-regularity-descent|Fiber.*baseChange|fiber.*baseChange`:
   unrelated geometric fibre/cohomology base change and model dimension results;
   no duplicate. A second focused `rg` for model/fibre regularity also searched
   `dag/lean_names_upstream.json` and both ring-theory trees, with no duplicate.
6. `grep -rn 'lem-trf-model-fibre-regularity-descent' lean/WeilConjectures`: no hits.
   Exact-name `rg` for `model_fibre_regularity_descent` across Mathlib, both live
   source roots and `dag/lean_names_upstream.json`: no hits before writing.

Validation uses only the prescribed `scompile.py` and `deliver2.py --no-push`.
Initial compiler feedback identified a reserved Unicode binder (`λ`), ambiguity
between the singleton list and index notation, and one line over 100 characters;
all were repaired in the sandbox. No changes to the mathematical statement were
needed. The final dry-run result is recorded by the delivery wrapper.

No STATEMENT-DISPUTED flag or node fault was found. Per the dispatcher's current
instructions I deliver directly; the maintainer supplies the independent review.

## Second reading by Q63

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
