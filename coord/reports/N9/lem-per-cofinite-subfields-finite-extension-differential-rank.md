## Worker report

The module `Sheaf.FieldTheory.CofiniteSubfieldsDifferentialRank` states
`FieldTheory.exists_cofinite_subfield_differential_finrank_eq`, with a single `sorry`.
No definition, new node, dependency repair, or statement correction is needed.

Source checked directly: ILO, Travaux de Gabber, Exposé IV, Proposition 1.2.4,
printed p.49 (PDF p.55), including the preceding stabilization lemmas on printed p.48.
The node matches the source, with the necessary explicit nonempty indexing convention.

Hypothesis and conclusion correspondence:

- Prime p: `(p : ℕ) [Fact p.Prime]`.
- Field K of characteristic p: `(K : Type u) [Field K] [CharP K p]`.
- Finite field extension L/K: `(L : Type v) [Field L] [Algebra K L]
  [Module.Finite K L]`. The ring homomorphism is `algebraMap K L`, automatically
  injective for fields. Characteristic p for L follows from this field embedding;
  it is not a separate restriction.
- Nonempty family of subfields of K: `{I : Type w} [Nonempty I]
  (F : I → Subfield K)`. All three universes are explicitly declared and independent.
- Every K_alpha is cofinite: `hcofinite : ∀ a : I, Module.Finite (F a) K`.
  This is finite vector-space dimension, not finiteness of the underlying field.
- Intersection equals exactly the pth powers: `hinter : (⋂ a : I, (F a : Set K)) =
  Set.range (fun x : K ↦ x ^ p)`. This uses the actual power image, not a new
  definition or an assumed identification with a field closure.
- Downward directedness: `hdirected : ∀ a b : I, ∃ c : I, F c ≤ F a ⊓ F b`.
- The chosen stage belongs to the original indexing set: `∃ b : I`.
- Every subfield K' below this stage, without requiring it to contain K^p:
  `∀ K' : Subfield K, K' ≤ F b → Module.Finite K' K → ...`.
- The equality of differential dimensions is
  `Module.finrank L (KaehlerDifferential K' L) =
  Module.finrank K (KaehlerDifferential K' K)`.
  Mathlib supplies the canonical K'-algebra structures by subfield inclusion and
  composition with `algebraMap K L`; no arbitrary embedding is quantified over.
  The two differential modules have finite dimension: K/K' and L/K' are finite
  field extensions and hence finite type, so natural-number finrank renders the
  source's dimension faithfully. No finite-dimension clause is added to the conclusion.

Statement dependencies read with their full recorded signatures and docstrings:

- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra`.
- `def-weil-finitely-generated-module`: `Mathlib.RingTheory.Finiteness.Defs`,
  `Module.Finite` (finite-dimensional vector spaces over fields).
- `def-weil-pbc-kahler-differentials`: `Mathlib.RingTheory.Kaehler.Basic`,
  `KaehlerDifferential`, `KaehlerDifferential.D`, and
  `KaehlerDifferential.linearMapEquivDerivation`.

Proof dependencies are imported without `public`. Their usable declarations were read:

- `Mathlib.LinearAlgebra.Basis.VectorSpace`: `Module.Free.of_divisionRing`.
- `WeilConjectures.FieldTheory.IntersectionSubfieldsSubspace`:
  `IntermediateField.exists_ne_zero_mem_base_iff_forall_mem_intermediateField`.
- `WeilConjectures.FieldTheory.FrobeniusBasisCompositum`:
  `FieldTheory.frobenius_basis_compositum` (spanning for arbitrary finite bases;
  independence is deliberately not asserted there).
- `Mathlib.LinearAlgebra.Dimension.Free`: `Module.finrank_mul_finrank`;
  `Mathlib.RingTheory.Finiteness.Basic`: `Module.Finite.trans` for tower finiteness.
- `WeilConjectures.FieldTheory.PBasisExtension`: `FieldTheory.exists_pBasis_extension`.
- `WeilConjectures.FieldTheory.PBasisDifferentialsBasis`:
  `KaehlerDifferential.exists_basis_differentials_of_pBasis`.

The four upstream modules absent from the older local checkout were read using
`scompile.py --source`, so their published interfaces, not stale paths, were checked.
The theorem docstring records all six steps of the node proof, including derivations
annihilating the composita E=K'K^p and F=K'L^p and cancellation of the positive [L:K].

Edge cases checked:

- Empty I must be excluded since the conclusion chooses b; `[Nonempty I]` does this.
- Singleton families over perfect K are allowed. Finite extensions of a perfect
  field are separable, and all the relative differential dimensions agree.
- L=K gives the identical dimensions, without an unnecessary proper-extension hypothesis.
- p=2 is included; p=0 and p=1 are excluded exactly by primality.
- No finite p-rank of K, separability of L/K, or countability of I is assumed.
- K' need not contain K^p. For K=F_p(t), L=K(t^(1/p)), the stage F_p(t^p)
  works; K'=F_p(t^(p^2)) is allowed and both differential dimensions are one.
  Requiring K^p ≤ K' would incorrectly discard this case.
- The universes of K and L may differ; equality compares natural dimensions and
  needs no equality of carrier universes. The index universe also remains arbitrary.

Searches for an existing exact statement:

- `msearch.py leanfinder`, query “For a finite field extension in characteristic p
  the dimensions of Kahler differentials agree over sufficiently small cofinite
  subfields with intersection the pth powers”: 8 hits. They concern smooth
  presentations, purely inseparable degrees, finite fields, and characteristic-zero
  differential fields; none asserts stabilization for this family of subfields.
- `msearch.py loogle`, query `KaehlerDifferential, Module.finrank`: 0 hits.
- `msearch.py grep`, query
  `KaehlerDifferential.*finrank|finrank.*KaehlerDifferential|cofinite.*[Ss]ubfield`:
  0 Mathlib hits.
- Direct `rg` of that expression plus the node id in `WeilConjectures`, `lean/Sheaf`,
  and `dag/lean_names_upstream.json`: no upstream match; side-library hits concern
  separating transcendence bases, Cartier equality, or local differential ranks,
  not a directed family of cofinite subfields. Read the separating-basis module;
  its finite-generation and separability assumptions give a different theorem.
- Direct `rg` for the proposed full declaration name and module name in Mathlib,
  upstream, side library and the upstream-name registry: no collisions.

Validation: prescribed `scompile.py N9 <item> <module>` compiled both sandbox and
library-path forms cleanly (1.6 s and 1.4 s); only the permitted postponed proof remains.
There are no disputed statements or node faults.

Additional search: `msearch.py leansearch`, query “Matsumura stabilization of dimensions
of relative Kahler differentials over a decreasing family of cofinite subfields in
characteristic p”: 8 hits on functorial differential maps, smooth-presentation ranks,
localization, polynomial differentials, and formally etale vanishing; none matches.

Delivery validation: `deliver2.py N9 <item> --no-push` returned OK: the packet passes
server preflight and per-file compilation. The delivery contains only this module,
the item's node with only its `lean` field changed, and this report.

## Second reading by N9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
