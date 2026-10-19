## Worker report

The module `Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer` states
`Padic.coefficientExtension_localization_uniformizer`, with its entire proof `sorry`.
No definitions or dependency modules are added, and no natural-language statement changes.

Hypotheses and clauses, in order:

- The prime ℓ is `l : ℕ` with `[Fact l.Prime]`. The finite extension is `E : Type u`
  with `[Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
- The integer ring and chosen uniformizer are the recorded
  `Padic.coefficientExtensionIntegers l E` and
  `Padic.coefficientExtensionUniformizer l E`. Their subtype algebra on E is precisely
  the inclusion of the ring of integers in E.
- E being that localization is
  `IsLocalization.Away (coefficientExtensionUniformizer l E) E`.
- The induced map being an isomorphism is the existential algebra equivalence
  `φ : Localization.Away (coefficientExtensionUniformizer l E) ≃ₐ[
  coefficientExtensionIntegers l E] E`. Being an algebra equivalence makes it fix the
  included integers. The following universally quantified equation on `x` and `n : ℕ`
  specifies its value on `IsLocalization.mk'` of x and π^n as `(x : E) * (π : E)⁻¹ ^ n`.
  Thus it is exactly the induced fraction map, rather than an unspecified field isomorphism.
- Every integer-ring module is quantified as `M : Type v`, `[AddCommGroup M]`, and
  `[Module (coefficientExtensionIntegers l E) M]`, with independent universe v and
  no finiteness, flatness, or nonzero assumption.
- The tensor objects are exactly `M ⊗[coefficientExtensionIntegers l E] Localization.Away π`
  and `M ⊗[coefficientExtensionIntegers l E] E` in the stated order.
- `s` and `t` are existential `Module E` structures on these two tensor products.
  The first action equation says `s` acts on pure tensors by
  `e • (m ⊗ a) = m ⊗ (φ.symm e * a)`; this is the required transported E-action.
  The second says `t` acts by `e • (m ⊗ a) = m ⊗ (e * a)`, the usual E-action
  on the right factor. Additivity and generation by pure tensors determine both
  actions on the whole tensor product, so these are not arbitrary auxiliary structures.
- `F` is an additive equivalence between the displayed tensors, its equation on pure
  tensors is `F (m ⊗ a) = m ⊗ φ a`, and the last equation for all e and z says
  `F (s.toSMul.smul e z) = t.toSMul.smul e (F z)`. An additive equivalence preserving
  scalar multiplication is precisely an E-linear equivalence. This expresses the
  claimed E-module isomorphism without introducing a separate definition of transport,
  local notation, local instances, or hidden `let` binders in the statement.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtension`:
  `Padic.coefficientExtensionIntegers`, `Padic.coefficientExtensionUniformizer`, and
  their full signatures and docstrings; the former is the subring of spectral absolute
  value at most one and the latter is its chosen maximal-ideal generator.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away` (read from its
  recorded declaration); imported through `Mathlib.RingTheory.Localization.Away.Basic`,
  which supplies its ring structure and `IsLocalization.Away`, also read in full.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`, `TensorProduct.mk`;
  `Mathlib.LinearAlgebra.TensorProduct.Basic`: `TensorProduct.lift`, `ext'`;
  `Mathlib.LinearAlgebra.TensorProduct.Map`: `LinearMap.rTensor` and its pure-tensor
  equation. These are the tensor dependency's recorded Mathlib matches, and no copy
  of the tensor product is made. The delivered signature uses `TensorProduct` and
  pure tensors, so the Basic import supplies what it needs.
- Proof dependency `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`,
  `Padic.extension_integers_dvr`: read its full statement and proof docstring. This module
  is already publicly imported by CoefficientExtension; no redundant import is added.

The blueprint source `def-weil-rationalization-karoubi.md` was read, including the
Hom tensor E formula and its special case E = ℚ_ℓ. Stacks algebra.tex was read at
00CO (fractions, ring operations, and canonical map) and 00CX (tensor universal property).
The delivered theorem docstring records all three proof steps of the node: fraction
map and injectivity, surjectivity via integer-power factorization, and mutually inverse
balanced tensor maps with transported scalar action.

Edge cases checked: x = 0 and n = 0 are allowed in the fraction formula; π is nonzero
by the coefficient extension dependency, without adding a hypothesis. No prime is
excluded, including 2. E = ℚ_ℓ is included. M = 0, modules with torsion (whose field
scalar extension can vanish), infinite modules and modules in an independent universe
are all included; there is no faithful, finite, or flat module hypothesis. The two
module actions are specified on generators and preserve the existing additive groups.

Searches for an existing full statement (all via msearch.py with this group/item):

- LeanFinder: “The fraction field of a discrete valuation ring is the localization away
  from a uniformizer, and tensor products agree”. Eight hits: fraction-ring localization
  at a prime, valuation-subring localization, and localization towers, including
  `IsFractionRing.isFractionRing_of_isDomain_of_isLocalization`. No hit states this
  coefficient extension identification with its tensor and transported-action clause.
- Loogle: `IsLocalization.Away, IsFractionRing`: zero hits.
- Mathlib grep: `isLocalization_away|isLocalizationAway|[Aa]way.*[Ff]raction`: 25 hits,
  principally spectrum criteria, etale maps, cotangent modules, and geometric
  localizations. No full match.
- LeanSearch: “The fraction field of a discrete valuation ring is its localization at
  a uniformizer”: service unavailable, Internal Server Error. No verdict inferred.
- Direct rg in WeilConjectures and project lean/Sheaf for
  `localization.*uniformizer|integers.*localization|lem-weil-l-adic-integers-localization-uniformizer`:
  only unrelated integer approximation/localization comments in the project, no upstream
  node-tag or full-statement match.
- Direct rg in Mathlib, WeilConjectures, project lean/Sheaf and the upstream-name index
  for the proposed declaration name found no collision. Tensor-product and localization
  source searches provided the existing notions used above.

Server validation: scompile.py compiles the delivered file cleanly, 1.5 seconds, nice 19,
two threads, within the 60-second per-file limit. Earlier attempts corrected a denominator
membership name and added an explicit submonoid type annotation. No local compiler ran.
No statement dispute or dependency fault was found.

## Second reading by NF

I independently read the sandbox node and signature, the three statement-dependency
nodes, their actual declarations, and the DVR proof-dependency declaration. No
mathematical mismatch was found; no Lean or node change was needed. This delivery
has no new definition nodes, dependency modules, or statement correction.

The node's objects, hypotheses, and conclusions matched against Lean:

1. A prime ℓ and finite field extension E/ℚ_ℓ: `(l : ℕ) [Fact l.Prime]`
   and `(E : Type u) [Field E] [Algebra ℚ_[l] E]
   [FiniteDimensional ℚ_[l] E]`. These are exactly the hypotheses, with no
   separate topology, completeness, DVR, or residue-field instance required. PASS.
2. Its valuation ring and chosen uniformizer: `coefficientExtensionIntegers l E`
   and `coefficientExtensionUniformizer l E`. I opened CoefficientExtension.lean:
   the former selects the subring characterized by the spectral absolute value ≤ 1;
   the latter selects a generator of the same witness's maximal ideal. I traced
   these to `extension_integers_dvr`, whose membership equations determine the
   subring and ideal uniquely. The chosen uniformizer is legitimate chosen data,
   not an additional hypothesis or a new definition in this delivery. PASS.
3. The inclusion makes E the localization away from that element:
   `IsLocalization.Away (coefficientExtensionUniformizer l E) E` uses the existing
   subring-inclusion algebra on E. I opened the Mathlib abbreviation: it is
   `IsLocalization (Submonoid.powers x) S`. Thus the intended structure map,
   rather than an unspecified map into E, is being localized. PASS.
4. The induced ring map is an isomorphism: the existential `φ` has type
   `Localization.Away π ≃ₐ[coefficientExtensionIntegers l E] E`. Its algebra-map
   compatibility fixes the inclusion, and its following equation specifies
   `φ(x/π^n) = (x : E) * (π : E)⁻¹ ^ n` for every x and natural n. The explicitly
   typed denominator is a member of `Submonoid.powers π`, including n = 0.
   Algebra equivalence states the induced ring isomorphism in this setting. PASS.
5. For every integer-ring module M: `∀ (M : Type v) [AddCommGroup M]
   [Module (coefficientExtensionIntegers l E) M]`. Its independent universe v
   covers arbitrary sizes; there is no extra finite, flat, or faithful condition. PASS.
6. The two tensors are in the required order: `M ⊗[O] Localization.Away π` and
   `M ⊗[O] E`, using exactly Mathlib `TensorProduct`. I opened its quotient
   construction, bilinear `mk`, and the `lift` and `ext'` signatures. No tensor
   product notion is copied. PASS.
7. The left tensor's E-action is transported through φ: the existential `s`
   is a `Module E` on its existing additive group, and its equation is
   `s.toSMul.smul e (m ⊗ₜ a) = m ⊗ₜ (φ.symm e * a)`. The right structure t
   similarly acts by multiplication by e in E. These are determined on all
   tensors because tensors are additively generated by pure tensors and module
   actions distribute over addition. In particular the existential structures
   cannot evade the transported-action requirement. PASS.
8. The tensors are isomorphic as E-modules: `F` is an additive equivalence,
   satisfies `F (m ⊗ₜ a) = m ⊗ₜ φ a`, and commutes with the s and t scalar
   actions for every e and every tensor z. Additive equivalence plus precisely
   this scalar compatibility is an E-linear equivalence. The pure-tensor formula
   specifies the canonical map given by the node's proof. The single φ precedes
   the universal M, so all modules use the same ring isomorphism. PASS.

Sources checked: the master blueprint's `def-weil-rationalization-karoubi.md`
introduces ℓ ≠ p, Y, and categorical data for its geometric application; this
auxiliary ring/module lemma introduces no characteristic p or scheme, so those
application hypotheses do not belong in it. Its Hom tensor E formula is exactly
what this lemma justifies. I read Stacks algebra.tex at `definition-localization`
(00CO), its preceding fraction construction and following universal property,
and at `lemma-tensor-product` (00CX), including its construction and pure-tensor
generation. The chapter conventions explicitly make rings commutative with 1.
There is no additional Noetherian or finiteness hypothesis there.

Edge cases: n = 0 gives denominator 1 and the inclusion; x = 0 is included.
Every prime, including 2, is allowed; E = ℚ_ℓ is allowed. The zero field is
properly excluded by Field, while the zero module, torsion modules, and infinite
modules are included. In particular both tensors may vanish. Universes u and v
are explicitly bound and unrestricted. No scheme or index set occurs, so empty
schemes and empty index sets impose no missing case.

Independent searches, using different wording from the worker:

- LeanFinder through msearch.py: “Inverting a prime element in a discrete
  valuation ring yields an algebra equivalence to its fraction field and preserves
  scalar extension of modules”. Eight results, including `FractionRing.algEquiv`
  and `IsFractionRing.algEquiv`; these concern fraction rings and do not supply
  this statement about the chosen coefficient uniformizer and transported tensors.
- Loogle through msearch.py: `IsDiscreteValuationRing, Localization.Away`:
  zero results.
- LeanSearch through msearch.py: “Tensor extension of scalars from the integers
  of a finite p-adic field after inverting a uniformizer equals tensor with the
  field”: unavailable, Internal Server Error; no mathematical verdict inferred.
- Direct rg across Mathlib, upstream WeilConjectures, project lean/Sheaf and
  dag/lean_names_upstream.json for `uniformizer.*localiz|localiz.*uniformizer|
  invert.*uniformizer|uniformizer.*invert` and the proposed declaration name.
  Two project files have private generic `fractionRing_away_uniformizer` lemmas;
  I opened SmoothTraitAffineGenericOpen.lean and read its signature and proof.
  It proves only the first localization clause for a generic DVR, with no
  coefficient data, explicit fraction isomorphism or tensor/action clause, and
  is private. Other matches are comments and uses, not this full statement.
  No declaration-name collision or full duplicate was found.

H5–H9: this file contains no new data definition, exactly one theorem with
`sorry`, no proof or private/local declaration, and no unbound binder. Module
and theorem docstrings identify the source and this blueprint node; the theorem
carries all three proof steps, including cross multiplication, the nonzero-field
integer-power decomposition, and the balanced mutually inverse tensor maps.
Imports provide the recorded notions and the DVR proof dependency transitively.
The node's lean.statement was checked verbatim against the complete signature.

Validation: the first wrapper invocation used a relative path from the read-only
repository and failed to find the sandbox file; I reran with its absolute sandbox
path. The required scompile.py server compile passed cleanly in 1.5 seconds,
nice 19, two threads, 60-second limit; no local compiler ran. The only change
from this second reading is this appended independent review.
