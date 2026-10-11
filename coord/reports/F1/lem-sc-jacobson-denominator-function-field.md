## Worker report

The module states `RingTheory.exists_inv_mem_jacobson_of_tensor_surjective`, the Stage-2
statement of Stacks Tag 09N5. `A` is a commutative domain with fraction field `K`, represented
by `[CommRing A] [IsDomain A] [Algebra A K] [IsFractionRing A K]`. The finite family of rings
is `B : ι → Type w` with `[Finite ι]`; each `B i` is a commutative domain, Noetherian, and
semilocal, rendered by `[Finite (MaximalSpectrum (B i))]`, has `ringKrullDim (B i) = 1`, and
has `K` as fraction field through `[Algebra (B i) K] [IsFractionRing (B i) K]`. The canonical
map `A ⊗[ℤ] B i → K` is rendered by `Algebra.TensorProduct.productMap` on the scalar-tower
algebra maps and is assumed surjective in `hsurj`. The conclusion gives a nonzero `f : A`
and, for every `i`, an element `b : B i` in `Ideal.jacobson (⊥ : Ideal (B i))` whose image in
`K` equals `(algebraMap A K f)⁻¹`; this is exactly that `f⁻¹` belongs to each Jacobson radical.
The proof is `sorry`, as required at stage 2. The finite index type uses `[Finite ι]` so the
hypothesis is used by the statement without a linter warning.

Dependencies used are the Mathlib declarations `IsNoetherianRing` (`Mathlib.RingTheory.Noetherian.Defs`),
`ringKrullDim` (`Mathlib.RingTheory.KrullDimension.Basic`), `Ideal.jacobson`
(`Mathlib.RingTheory.Jacobson.Ideal`), `IsFractionRing` (`Mathlib.RingTheory.Localization.FractionRing`),
`MaximalSpectrum` (`Mathlib.RingTheory.Spectrum.Maximal.Basic`), and
`Algebra.TensorProduct.productMap` / `IsScalarTower.toAlgHom` (`Mathlib.RingTheory.TensorProduct.Maps`).

Edge cases checked: `ι` may be empty (the universal conclusion is then vacuous); a singleton
family is permitted; `A` and each `B i` are required domains as in the source; dimension is
exactly one; and no characteristic or countability restriction is introduced. The inverse is
expressed in `K` and related to a radical element by an equality, so no coercion or type mismatch
silently changes the conclusion.

Searches made: `msearch.py leanfinder` for a common denominator/Jacobson-radical theorem (only
generic Jacobson and valuation results; no exact match); `msearch.py loogle` for
`Ideal.jacobson, Algebra.TensorProduct.productMap` (no exact combined hit); `msearch.py grep`
for Jacobson/semilocal denominator declarations (generic declarations only); `rg` over
`WeilConjectures` and `lean/Sheaf` (no existing statement). The Stacks source was checked at
Tag 09N5, Lemma 33.37.8.

## Earlier second reading (a previous round; superseded)

Pending the independent second reader.

## Second reading by F1

Independent source reading: `/home/ubuntu/c1-stacks-review/tags/tags` maps 09N5 to
`varieties-lemma-create-globally-generated`; I read the statement and complete proof in
`/home/ubuntu/c1-stacks-review/varieties.tex`, lines 7536–7590. The repository's literature
checkout is absent on this machine; this available Stacks checkout supplies the named source.
The source introduces its rings and fraction field in the lemma itself, without a standing
base-field, characteristic, Noetherian assumption on A, or geometric hypothesis. Its proof
explicitly seeks a nonzero element, as does the node.

Object/hypothesis/conclusion inventory, matched against the delivered signature:

- Commutative domain A: `{A : Type u} [CommRing A] [IsDomain A]`. Exact; no Noetherian,
  local, or finite-type assumption on A.
- Fraction field K of A: `{K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]`.
  Exact. I opened FractionRing.lean:53 and :137: this is localization at non-zero-divisors
  and its algebra map is injective, so it supplies the stipulated inclusion of A into K.
- Finite family B_1,...,B_r: `{ι : Type w} [Finite ι] (B : ι → Type t)`. Exact; no enumeration
  is required. All four universe parameters are now independently bound.
- Subrings B_i of K that are domains with fraction field K: `[∀ i, CommRing (B i)]`,
  `[∀ i, IsDomain (B i)]`, `[∀ i, Algebra (B i) K]`, `[∀ i, IsFractionRing (B i) K]`.
  Exact up to canonical identification with each algebra map's image in K. Injectivity of
  these localization maps ensures these are subrings, not arbitrary non-injective maps.
- Noetherian B_i: `[∀ i, IsNoetherianRing (B i)]`. Exact. Opened dependency node
  def-weil-pbc-noetherian-ring and its recorded Noetherian/Defs.lean:196 declaration:
  Noetherian as a self-module means every ideal is finitely generated.
- Dimension exactly one: `hdim : ∀ i, ringKrullDim (B i) = 1`. Exact. Opened dependency
  node def-weil-pbc-krull-dimension-ring and KrullDimension/Basic.lean:30: the dimension
  is the strict-chain dimension of PrimeSpectrum, valued in WithBot ℕ∞.
- Semilocal B_i: `[∀ i, Finite (MaximalSpectrum (B i))]`. Exact. Opened
  Spectrum/Maximal/Basic.lean, including equivSubtype: these points are precisely maximal
  ideals. LocalProperties/Semilocal.lean uses this same finite-spectrum convention.
- Each canonical A tensor B_i -> K is surjective: `hsurj : ∀ i, Function.Surjective
  (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom ℤ A K)
  (IsScalarTower.toAlgHom ℤ (B i) K))`. Exact. Opened TensorProduct/Maps.lean:810–818:
  productMap sends a pure tensor to the product of the two algebra-map images.
  Tensoring over ℤ is the tensor product of rings used by the source. Integer scalar
  towers are canonical; they introduce no compatibility assumption between A and B_i.
- One common nonzero element: `∃ f : A, f ≠ 0 ∧ ∀ i, ...`. Exact; the existential
  precedes the universal quantifier on i.
- Its inverse belongs to every Jacobson radical: `∃ b : B i,
  b ∈ (Ideal.jacobson (⊥ : Ideal (B i)) : Set (B i)) ∧
  algebraMap (B i) K b = (algebraMap A K f)⁻¹`. Exact: existence of a preimage b expresses
  membership of the field inverse in the embedded subring's radical. I opened
  Jacobson/Ideal.lean:65: jacobson of bottom intersects all maximal ideals. No localization
  radical or radical of a different ideal is substituted.

Edge cases: the empty finite family is admitted and f=1 satisfies the conclusion; a singleton
is admitted; arbitrary characteristics and finite fields are not excluded by any new binder.
Zero rings are excluded exactly by the source's domain/field hypotheses. A field cannot be a
B_i because dimension is exactly one, as required. No scheme or natural-number parameter
occurs. No universe is unbound, and A, K, the index type, and the B_i carriers can now have
different universes.

Independent searches (actual msearch.py calls, recorded in searches.jsonl): LeanFinder query
"A finite collection of one dimensional local domains with common quotient field admits an
element whose reciprocal lies in all maximal ideals" returned generic maximal-ideal inverse,
Dedekind denominator, DVR and valuation-subring results, none with the finite-family tensor
hypothesis and common reciprocal conclusion. Loogle `Ideal.jacobson, IsFractionRing` returned
zero hits. Mathlib grep `reciprocal|common.*denominator|semilocal|semi.local` in RingTheory
returned semilocal local-property results and Localization/Integer common-denominator lemmas,
not this theorem. Independent rg searches for 09N5, the proposed declaration name,
common denominators, Jacobson/tensor/fraction combinations and semilocal spellings across
WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json found no duplicate. The landed
ExistsNegativeValuationOfTensorSurjective module was opened: it treats a single DVR and only
supplies the base case, not this statement. Existing Mathlib notions are used throughout;
there is no new definition node or dependency module to audit, and no private definition.

Mismatches repaired: A and K formerly shared `Type u`; separated them and the family/index
universes to avoid an unnecessary universe restriction. The old docstring only listed the
proof reductions; expanded it to the node's three steps, including the conductor exponents,
lying-over descent, finite localization reduction, valuation base case and power/sum
induction, and the empty-family case. No mathematical hypothesis or conclusion was changed;
no node statement correction or citer audit is needed. The node's lean.statement is now the
literal multiline signature from the module. Every theorem proof remains `by sorry`; there
are no definitions or auxiliary proofs. All imports supply notions appearing in the signature.
The source and blueprint markers remain on both docstrings, and lines fit the 100-character
limit. Server scompile.py completed cleanly, exit code 0, without warnings.
