## Worker report

The module `Sheaf.RingTheory.PrimeLocalizedModuleBaseChange` states
`LocalizedModule.prime_localized_module_base_change`, with its complete conclusion in the
transparent proposition `LocalizedModule.primeLocalizedModuleBaseChange`. The proposition
only assembles existing Mathlib objects and canonical maps. Its data contains no `sorry`;
the theorem is the single postponed proof, with all five DAG proof steps in its docstring.
The item statement, statement dependencies and proof plan are unchanged.

Hypothesis and clause correspondence (read against the node and Stacks Algebra 00SI/00SJ):

- Commutative rings and arbitrary ring homomorphism: `{A : Type u} {B : Type v}`,
  `[CommRing A] [CommRing B]`, and `(f : A →+* B)`; `f.toAlgebra` installs exactly that map.
  The independent universes `u`, `v`, `w` admit arbitrary sizes of rings and modules.
- Arbitrary A-module: `(M : Type w) [AddCommGroup M] [Module A M]`.
  No flatness, finite generation, finite presentation or injectivity hypothesis occurs.
- `N = M ⊗[A] B`, with B acting on its B factor: represented by `B ⊗[A] M`, using
  Mathlib's scalar-left convention. Tensor symmetry identifies `b ⊗ m` with the node's
  `m ⊗ b`; the standard `TensorProduct.leftModule` acts on B, hence on the second
  factor in the node's notation. This is a change of tensor notation, not of module.
- Prime q and contracted p: `(q : Ideal B) [q.IsPrime]` and `p := q.comap f`.
  Primality of p is Mathlib's existing comap-prime instance, not an added hypothesis.
- `Ap`, `Bq`, `Mp`, `Nq` are `Localization.AtPrime p`, `Localization.AtPrime q`,
  `LocalizedModule p.primeCompl M`, and `LocalizedModule q.primeCompl (B ⊗[A] M)`.
  Fractions are the recorded `Localization.mk` and `LocalizedModule.mk`.
- The induced local map is exactly `Localization.localRingHom p q f rfl`.
  The first conjunct is the inverse-image equality for the maximal ideals. Its
  existing Mathlib locality theorem supplies the instance needed to form the
  canonical residue-field scalar action inside the proposition; it is no premise.
- Residue fields are `p.ResidueField` and `q.ResidueField`, the recorded quotient of
  the prime localization; Mathlib's `IsFractionRing (A ⧸ p) p.ResidueField` instance
  identifies it with the node's fraction-field description. The second conjunct
  identifies the scalar map with `Ideal.ResidueField.map p q f rfl`; that declaration
  is, by definition, the residue map of `Localization.localRingHom`.
- Φ is the existential `Nq ≃ₗ[Bq] Bq ⊗[Ap] Mp`; the first universally quantified
  equation is precisely `(m ⊗ b)/t ↦ (m/1) ⊗ (b/t)` after commuting factors.
- Ψ is the existential κ(q)-linear equivalence from
  `q.ResidueField ⊗[p.ResidueField] (p.ResidueField ⊗[Ap] Mp)` to
  `q.ResidueField ⊗[Bq] Nq`. Commuting each scalar factor gives exactly the two
  tensor expressions in the node.
- The second universally quantified equation covers every `m`, every denominator
  `s : p.primeCompl`, every `a : p.ResidueField`, and every `b : q.ResidueField`.
  Its scalar is `Ideal.ResidueField.map p q f rfl a * b /
  algebraMap B q.ResidueField (f s)`, exactly bar-f(a)b divided by the residue of
  f(s), and its module factor is `LocalizedModule.mk ((1 : B) ⊗ₜ[A] m) 1`.
- The final equality says Ψ equals α followed by β inverse followed by scalar
  extension of Φ inverse, with α and β the two specified
  `TensorProduct.AlgebraTensorModule.cancelBaseChange` equivalences. These are
  the canonical tensor-associativity and unit comparisons, not arbitrary maps.
  The native scalar towers on residue fields ensure both middle objects have
  the same Ap action. The Φ and Ψ formulas determine the comparisons on generators.

Dependency declarations read and used:

- `def-weil-pbc-module-tensor-product`: `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, with its pure tensor and linear structure.
- `def-weil-pbc-module-localization`: `LocalizedModule`, `LocalizedModule.mk` in
  `Mathlib.Algebra.Module.LocalizedModule.Basic`.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime` in
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, and `Ideal.ResidueField` in
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal` (which publicly imports that module).
- The proof dependencies are all Mathlib leaves, available through the two public imports:
  `IsLocalization.lift`, `IsLocalization.ringHom_ext` in Localization.Defs;
  `IsLocalizedModule.rTensor`, `IsLocalizedModule.map_lTensor` in Localization.BaseChange;
  `TensorProduct.AlgebraTensorModule.cancelBaseChange` in LinearAlgebra.TensorProduct.Tower.
  Also read `LocalizedModule.equivTensorProduct` and its fraction formula in BaseChange.
  No project dependency has an unusable record and no definition needs a replacement.

Edge cases checked mathematically before writing:

- M = 0: both localized and fibre modules are zero; the formulas hold.
- Identity f: p = q, and the maps reduce to the standard localization/tensor-unit maps.
- Noninjective and nonflat f, e.g. Z → F_p, and torsion M = Z/p: all comparisons
  are universal-property identities; no argument cancels a scalar acting on M.
- Arbitrary field extension with p = q = 0: the claim is tensor base-change transitivity.
- The zero target ring has no prime q; the stated prime hypothesis correctly excludes it.
  The zero source ring cannot have a unital map to a ring admitting a prime.
- For every permitted denominator s, f(s) lies outside q, so its residue is nonzero.
  Numerators may vanish in either module or either residue field.

Searches (2026-10-24):

- `msearch.py ... leanfinder "Prime localization of a scalar extended module and residue
  fibre comparison with pure tensor formulas"`: eight hits, including
  `Ideal.ResidueField.exists_smul_eq_tmul_one`, `Module.mem_freeLocus_iff_tensor`,
  and prime-spectrum fibre equivalences. None states the paired module comparisons.
- `msearch.py ... loogle "LocalizedModule, TensorProduct"`: four hits:
  `LocalizedModule.equivTensorProduct` and its three evaluation lemmas. These give
  localization-as-tensor, not both prime comparisons or their compatibility.
- `msearch.py ... leansearch "localization tensor product module base change residue
  fields"`: eight hits including `IsLocalizedModule.rTensor`,
  `IsLocalization.tensorProduct_isLocalizedModule`, and tensor localizations.
  They are the constituent Mathlib facts, not the full statement.
- `msearch.py ... grep "residueFieldMap|localRingHom|cancelBaseChange" RingTheory`:
  25 hits, including `Localization.localRingHom`, its evaluation lemmas, and uses
  of `cancelBaseChange`; reused these canonical constructions.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, Mathlib and
  `dag/lean_names_upstream.json` for the proposed names and the item id: no match.
  Broader searches for residue-field scalar maps found `LciFibreTensorTransition`;
  its flat finitely presented algebra-fibre theorem is not this arbitrary-module lemma.
  Direct source reading also found the canonical residue-field algebra in
  `IsLocalRing.ResidueField` and `Ideal.ResidueField.map`.

No statement correction, new node, dependency repair, or disputed statement is needed.

## Second reading by Q11

This is the author's second pass; the maintainer supplies the independent delivery review.
Reopened the item JSON and the complete Lean file and matched every hypothesis and all
four substantive conclusions above. In particular, checked the direction of Φ and Ψ,
the B-factor action after symmetry, both denominator placements, and the order
α; β inverse; base change of Φ inverse. The residue-field scalar map is constructed
from the exact localized f, and the explicit equality with `Ideal.ResidueField.map`
prevents an arbitrary field action. The proof-only typeclass instance is taken from
Mathlib's existing locality theorem and is not an extra mathematical assumption.
The first compiler run found that `LinearEquiv.baseChange` takes all four type
arguments explicitly, unlike `LinearMap.baseChange`; supplied Bq, κ(q), and the
two modules without altering the mathematical statement.
The transparent assertion contains the canonical setup; no theorem-level `let`
binder, free variable, arbitrary comparison, or new axiom occurs. No mismatch found.
