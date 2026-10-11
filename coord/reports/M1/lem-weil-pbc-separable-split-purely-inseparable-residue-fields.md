## Worker report

The module `Sheaf.FieldTheory.SeparableSplitPurelyInseparableResidueFields` states
`Algebra.exists_separable_split_purelyInseparable_prime_quotients`. Its sole proof is
`by sorry`; there are no new definitions, auxiliary proofs, or axioms. Only the item's
`lean` field changes. No dependency module, new node, or statement correction is needed.

Hypothesis and conclusion correspondence:

- The field k is `(k : Type u) [Field k]`.
- The finite list K_1,...,K_n is `(n : ℕ) (K : Fin n → Type v)`;
  zero-based `Fin n` merely reindexes the n fields.
- Each K_i is a field extension through `[∀ i : Fin n, Field (K i)]` and
  `[∀ i : Fin n, Algebra k (K i)]`; the extension map is `algebraMap k (K i)`.
- Each K_i/k is finite through `[∀ i : Fin n, Module.Finite k (K i)]`.
  Over a field, finite generation as a module is exactly finite dimensionality.
- The extension L/k is the existential field `(L : Type (max u v)) (_ : Field L)`
  with its specified algebra structure `(_ : Algebra k L)`.
- Finiteness is `Module.Finite k L`; separable algebraicity is
  `Algebra.IsSeparable k L`. Algebraicity is already implied by this Mathlib predicate.
- The parenthetical choice of a finite Galois L is rendered by `IsGalois k L`,
  together with the already stated finiteness. The relative separable subfields are
  `separableClosure k (K i)`, and their k-embeddings into L are
  `∀ i : Fin n, Nonempty (separableClosure k (K i) →ₐ[k] L)`.
  Algebra homomorphisms from these fields are automatically injective. This witness
  property is explicitly asserted in the node's parenthesis and its source, rather than
  an extra hypothesis on the input fields.
- The conclusion for every i is the outer `∀ i : Fin n`.
- Clause (a) is `Finite (PrimeSpectrum (L ⊗[k] K i))`: prime-spectrum points are
  precisely prime ideals, so this says there are only finitely many such ideals.
- Clause (b) quantifies over `p : Ideal (L ⊗[k] K i)` with hypothesis `p.IsPrime`.
  The quotient is the actual ring `(L ⊗[k] K i) ⧸ p`, not an arbitrary residue field
  carrier. `IsField` asserts that its existing ring structure is a field; it includes
  nontriviality and invertibility of each nonzero element.
- Its finiteness and pure inseparability over L are respectively
  `Module.Finite L ((L ⊗[k] K i) ⧸ p)` and
  `IsPurelyInseparable L ((L ⊗[k] K i) ⧸ p)`.
  The tensor product's default L-algebra is `Algebra.TensorProduct.leftAlgebra`:
  `algebraMap L (L ⊗[k] K i)` sends l to l tensor 1. The quotient inherits this
  algebra structure through the quotient map. Thus this is precisely the specified
  extension map, without a freely chosen algebra structure on the quotient.

Recorded dependency declarations read and used:

- `def-pc-field-extension`: `Algebra` in `Mathlib.Algebra.Algebra.Defs`, specifying
  the ring homomorphism and compatible scalar action. Used for each input extension
  and the output extension.
- `def-weil-pbc-separable-algebraic-extension`: its Mathlib match
  `Algebra.IsSeparable` in `Mathlib.FieldTheory.Separable`, whose docstring and
  signature say every minimal polynomial is separable, implying algebraicity.
  This node has status mathlib and needs no separate lean record.
- `def-weil-pbc-finite-purely-inseparable-extension`: `IsPurelyInseparable` in
  `Mathlib.FieldTheory.PurelyInseparable.Basic` and `Module.Finite` in
  `Mathlib.RingTheory.Finiteness.Defs`. Mathlib permits the purely inseparable
  predicate on commutative rings, so it can be stated on the actual quotient ring
  alongside `IsField`, without selecting an inverse operation in the signature.

The parenthetical clause also uses the already existing Mathlib notions `IsGalois`
(`Mathlib.FieldTheory.Galois.Basic`, Tag 09I0) and `separableClosure`
(`Mathlib.FieldTheory.SeparableClosure`, Tag 09HC), the latter already carried by
`def-weil-pbc-relative-separable-closure` among this item's proof dependencies.
The canonical tensor and quotient rings, `PrimeSpectrum`, and `IsField` are Mathlib
notions. Their modules and definitions were read; no notion is privately duplicated.

Source check: this clone does not contain `literature/stacks-project/more-morphisms.tex`.
Read the source proof at https://stacks.math.columbia.edu/tag/02LM instead. It chooses
finite Galois L receiving the separable subfields, identifies the relevant points with
primes of the tensor products, and asserts the resulting residue extensions are finite
purely inseparable. The declaration docstring carries all five steps of this node's
proof, including the linear-algebra finiteness argument, the split-minimal-polynomial
argument, and the characteristic-zero and positive-characteristic arguments.

Edge cases checked mathematically before writing:

- n = 0: `Fin 0` is empty; all family and prime conclusions are vacuous, and k/k is
  finite separable Galois. Transport k to `Type (max u v)` if necessary.
- K_i = k: the tensor product is L and its only prime quotient is L modulo the zero ideal,
  giving the identity purely inseparable extension of degree one.
- Characteristic zero: pure inseparability forces the quotient extension map to be
  surjective, as required. Positive characteristic allows nontrivial purely inseparable
  residue extensions and nonreduced tensor products; reducedness is not assumed.
- The top ideal is excluded by `p.IsPrime`; the zero ring is not asserted to be a field.
- Universes u and v are explicit and independent, and the existential L lies in their
  maximum. A finite algebraic extension can be realized there; no input universe or
  family size is excluded. No auto-bound variables or statement lets are used.

Searches for an existing statement (2026-10-11):

- msearch.py, Lean Finder: "finite family of finite field extensions admits finite
  separable Galois extension such that all prime quotients of tensor products are finite
  purely inseparable". Eight hits concern finite fields, finite Galois intermediate
  fields and splitting fields; none states this result for general fields and prime
  quotients of all tensors in a finite family.
- msearch.py, Loogle: `IsPurelyInseparable, TensorProduct`. Four hits:
  `IsPurelyInseparable.exists_pow_mem_range_tensorProduct`, its expChar variant,
  `PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable`, and its tensor-map variant.
  They assume an already purely inseparable extension; none chooses the common finite
  separable splitting extension required here.
- msearch.py, Mathlib grep:
  `IsPurelyInseparable.*TensorProduct|TensorProduct.*IsPurelyInseparable`. Four hits
  in PurelyInseparable/Basic and Spectrum/Prime/Homeomorph, the same ingredients.
- msearch.py, LeanSearch: "finite separable extension splitting tensor products into
  purely inseparable residue fields". Service unavailable: Internal Server Error;
  no search verdict is inferred from the unavailable service.
- rg over the source `WeilConjectures` and project `lean/Sheaf` for
  `separable-split-purely|IsPurelyInseparable.*TensorProduct|TensorProduct.*IsPurelyInseparable`:
  the project has references in the proof docstrings of GenericSeparableAlgebraSplitting
  and EtaleLocalFiniteMultiplePoints, plus an unrelated GRing condition; no existing
  declaration of this statement. Direct source search for the item's id found no match.
- Exact-name search for `exists_separable_split_purelyInseparable_prime_quotients` in
  Mathlib, the source project, project Lean, and `dag/lean_names_upstream.json` found
  no collision. Read the related project module FiniteGaloisReceivingSeparableExtensions;
  it supplies only the common Galois extension, not the tensor prime-quotient conclusion.

No STATEMENT-DISPUTED issue or node fault was found. The final module compiled on the
server in 1.5 seconds, with exit code 0 and no errors or warnings.


## Second reading by M1

Independent reading of the sandbox node and Lean file, all three statement dependency
nodes and their recorded Mathlib declarations, and the relative-separable-closure node.
There are no new definition nodes, dependency modules, or statement corrections.

Source: read the Stacks TeX directly at
https://raw.githubusercontent.com/stacks/stacks-project/master/more-morphisms.tex,
label `lemma-etale-makes-quasi-finite-finite-multiple-points-var` (Tag 02LM),
and the corresponding [Stacks page](https://stacks.math.columbia.edu/tag/02LM).
The locally-of-finite-type and isolated-fibre-point assumptions serve to establish
finiteness of the input residue extensions. The extracted field lemma takes that
finiteness directly; no additional geometric assumption survives the extraction.
The source chooses a common finite Galois extension receiving the separable parts,
then obtains finitely many tensor primes and finite purely inseparable residues.
A prime quotient of a finite algebra over a field is itself a field, so the node's
quotient formulation agrees with the source's residue-field formulation.

Objects, hypotheses, and conclusion clauses, item by item:

1. Base field k: `(k : Type u) [Field k]`. Verdict: exact; no characteristic,
   perfectness, or algebraic-closedness assumption.
2. Finite family K_1,...,K_n: `(n : ℕ) (K : Fin n → Type v)`. Verdict: exact
   reindexing, including the empty family.
3. Each K_i is a field: `[∀ i : Fin n, Field (K i)]`. Verdict: exact.
4. Each specified extension K_i/k: `[∀ i : Fin n, Algebra k (K i)]`.
   Read `Algebra` in Mathlib/Algebra/Algebra/Defs.lean:95, including its ring map.
   Together with the field structures this is precisely def-pc-field-extension.
   Verdict: exact, with no independently chosen or unconstrained embedding.
5. Each extension is finite: `[∀ i : Fin n, Module.Finite k (K i)]`.
   Read Module.Finite in RingTheory/Finiteness/Defs.lean:117; it says finite module
   generation, equivalent to finite vector-space dimension over k. Verdict: exact.
6. One common witness L/k, chosen before i and the prime: existential
   `(L : Type (max u v)) (_ : Field L) (_ : Algebra k L)`.
   Verdict: exact objects and quantifier order. The algebra structure is part of
   the extension, not an extra hypothesis on the inputs.
7. Witness finite and separable algebraic: `Module.Finite k L ∧
   Algebra.IsSeparable k L`. Read the separable class at Separable.lean:549 and
   its algebraicity instance at :570, against the recorded dependency's full
   statement. Verdict: exact; algebraicity is included in Mathlib separability.
8. Parenthetical stronger choice: `IsGalois k L` and
   `∀ i : Fin n, Nonempty (separableClosure k (K i) →ₐ[k] L)`.
   Read IsGalois at Galois/Basic.lean:57 (separable and normal) and
   separableClosure at SeparableClosure.lean:83 (the relative intermediate field
   of separable elements), against def-weil-pbc-relative-separable-closure.
   The latter is the relative closure, not an abstract separably closed field.
   Field algebra homomorphisms are injective, so these are the required embeddings.
   Verdict: exact rendition of the node's parenthetical clause and source choice.
9. Clause (a), for every i: `∀ i : Fin n, Finite (PrimeSpectrum (L ⊗[k] K i))`.
   Read PrimeSpectrum at Spectrum/Prime/Defs.lean:34: its data are an ideal and
   a proof of primality. Verdict: exactly finitely many prime ideals, with no
   stronger cardinality or reducedness assertion.
10. Clause (b), for every prime: `∀ (p : Ideal (L ⊗[k] K i)), p.IsPrime → ...`.
    Verdict: exact domain of quantification; maximality is a consequence, not
    an added hypothesis.
11. Actual quotient is a field: `IsField ((L ⊗[k] K i) ⧸ p)`.
    Read IsField at Algebra/Field/IsField.lean:33: nontriviality, commutativity,
    and inverses for nonzero elements. Verdict: exactly the canonical quotient
    ring is a field, without replacing it by an arbitrary field carrier.
12. Specified map from L: the default tensor left algebra at
    RingTheory/TensorProduct/Basic.lean:281 has algebraMap given by includeLeft;
    Quotient.algebra at Ideal/Quotient/Operations.lean:354 composes this with
    Ideal.Quotient.mk. Verdict: exactly l maps to (l tensor 1) modulo p.
13. Quotient finite over L: `Module.Finite L ((L ⊗[k] K i) ⧸ p)`.
    Verdict: exact finiteness using that same canonical scalar action.
14. Quotient purely inseparable over L:
    `IsPurelyInseparable L ((L ⊗[k] K i) ⧸ p)`.
    Read the class at PurelyInseparable/Basic.lean:107 and its power criterion
    at :211 (valid already for a domain). Alongside IsField this is precisely
    def-weil-pbc-finite-purely-inseparable-extension. Verdict: exact in all
    characteristics; no chosen Field instance changes the quotient's operations.

Edge cases: n = 0 is admitted, with a universe lift of k as the witness; no Nonempty
family assumption is present. K_i = k gives L and its zero prime quotient. Characteristic
zero gives the identity extension at each quotient; positive characteristic permits
nontrivial purely inseparable extensions and nilpotents in the tensor ring. A prime is
proper, excluding the top ideal and zero quotient ring. Zero input fields are excluded
by Field, as in the node; no schemes or zero objects are introduced. Independent u,v
are bound explicitly, and max u v accommodates a lift of the base and a common finite
extension. All existential structures scope over every subsequent clause. No extra
Noetherian, finite-set-carrier, or universe hypothesis occurs.

Independent searches, using terms different from the first worker's:

- msearch Loogle: `"separableClosure", "TensorProduct"`: zero hits.
- msearch Lean Finder: "There exists a normal finite extension making prime ideal
  quotients of base changed finite field extensions radicial": eight hits, including
  Ideal.Quotient.normal, quasi-finite residue finiteness, and ramification/Frobenius
  lemmas. None chooses the common splitting field with this conclusion.
- msearch Mathlib grep:
  `separableClosure.*TensorProduct|TensorProduct.*separableClosure|exists.*purelyInseparable`:
  IsPurelyInseparable.exists_pow_mem_range_tensorProduct only. It assumes the input
  extension is already purely inseparable, so is not this existence statement.
- msearch LeanSearch: "finite normal extension of a base field whose tensor product
  prime quotients are radicial": unavailable (Internal Server Error). No conclusion
  is inferred from this failed service.
- Independent rg on the full source WeilConjectures and project lean/Sheaf using
  `purely.?inseparable`, `radicial`, `separable.*split`, `split.*separable`,
  `IsPurelyInseparable`, and `separableClosure`: related descent, splitting and tower
  results only. Opened source Mathlib/RingTheory/Etale/FiniteSplitting.lean: its
  of_comp_eq helper and exists_etale_isIdempotentElem_forall_eq have different objects
  and conclusions. Opened project FiniteGaloisReceivingSeparableExtensions.lean:
  its signature supplies the common normal separable field and embeddings, with
  no tensor prime conclusion. GenericSeparableAlgebraSplitting.lean concerns a finite
  algebra's reduction and uses this node. No duplicate declaration was found.

H5/H6/H8/H9 checks: there is no definition with postponed data, no theorem proved,
and no private copy of a dependency. The sole theorem has `by sorry`. Its docstring
names the source and blueprint and follows all five node proof steps, including the
finite-module argument, split minimal polynomials, and Frobenius argument. Namespace,
explicit universes, imports, and line widths conform. The node's lean.statement was
compared as literal text with the complete file signature through the conclusion:
identical. No variables are auto-bound.

Mismatches found: none. Changed only this report by appending the independent reading;
left the correct Lean and node unchanged. Compilation using scompile.py from the
sandbox completed on the server in 1.5 seconds, exit code 0, without warnings.
