## Worker report

`Sheaf.RingTheory.CofinitePBasisCompletedGenericRank` states
`RingTheory.cofinitePBasisCompletedGenericRank`. Its only proof is `sorry`.
No definition, helper theorem, new node or dependency repair is needed. The
item's only changed field is `lean`. The prior module was deleted as dead,
as recorded in `lean_removed`; searches confirm the declaration is currently
absent. The old Q85 report was read as history, then the source, dependency
interfaces and present statement were checked afresh.

Source read: the local ILO Travaux de Gabber PDF, Exposé IV, printed pp.48–51
(PDF pp.54–57), Proposition 1.2.4 and 2.1.3–2.1.6, especially (2.a) and (2.b).
The statement is precisely (2.b) for a domain. The source's sentence immediately
before (2.b) reverses the two power-series subscripts; the accepted node proof
already corrects this. No correction to the node statement is needed.

Hypothesis and clause correspondence:

- Complete Noetherian local domain `(A,m)`: `(A : Type u)` with `[CommRing A]`,
  `[IsDomain A]`, `[IsLocalRing A]`, `[IsNoetherianRing A]`, and
  `[IsAdicComplete (IsLocalRing.maximalIdeal A) A]`. The maximal ideal used
  everywhere is the canonical maximal ideal of this local ring.
- Positive characteristic: `(p : ℕ) [Fact p.Prime] [CharP A p]`. A domain's
  positive characteristic is prime, so primality adds no mathematical restriction.
- Finite dimension `d ≥ 1`: `(d : ℕ) (hd : 1 ≤ d)` and
  `(hdim : ringKrullDim A = d)`, where the natural is coerced to `WithBot ℕ∞`.
- Fixed coefficient subfield: `(k : Type v) [Field k] [Algebra k A]` and
  `hres : Function.Bijective ((IsLocalRing.residue A).comp (algebraMap k A))`.
  The map from a field to the nonzero ring A is injective, so its image is the
  specified coefficient subfield; hres is exactly the residue isomorphism.
  `[CharP k p]` records the necessarily inherited characteristic.
- Supplied p-basis: `(E : Type w) (β : E → k)` and hpb give a `Module.Basis`
  indexed by `{a : E →₀ ℕ // ∀ i : E, a i < p}`, whose value at a is precisely
  `(a : E →₀ ℕ).prod (fun i e ↦ β i ^ e)`. This includes every bounded,
  finitely supported monomial and the empty monomial 1. Its scalar field is
  `Subfield.closure (Set.range (fun x : k ↦ x ^ p))`. Frobenius is a field
  homomorphism in characteristic p, so its image is already a subfield; this
  closure is exactly k^p, also the intermediate field used by the recorded
  p-basis proof dependencies. No second p-basis definition is introduced.
- Every finite J and its cofinite subfield: `F : Finset E → Subfield k` and hF
  characterize F J by equality with the closure of p-th powers together with
  `{x : k | ∃ i : E, i ∉ J ∧ β i = x}`. Thus the family is exactly F_J.
- The scalar structures `[∀ J : Finset E, Algebra (F J) A]` are specified by
  `hcomp : ∀ J x, algebraMap (F J) A x = algebraMap k A (x : k)`.
  This is the composite of the coefficient embedding and subfield inclusion,
  not an arbitrary action. For every F these structures exist as
  `((algebraMap k A).comp (F J).subtype).toAlgebra`, and hcomp fixes their
  algebra maps uniquely. It imposes no further mathematical hypothesis.
- `L = Frac(A)`: `(L : Type z) [Field L] [Algebra A L] [IsFractionRing A L]`.
  This permits any model of the canonical fraction field.
- `M_J = lim_n Ω/(m^n Ω)` is the explicit Mathlib expression
  `AdicCompletion (IsLocalRing.maximalIdeal A) (KaehlerDifferential (F J) A)`.
  AdicCompletion's definition is exactly the compatible families in quotients
  by `(m^n • ⊤)`. Neither finite generation nor completeness of Ω is assumed.
- Finite exceptional J0 and every finite superset J:
  `∃ J0 : Finset E, ∀ J : Finset E, J0 ⊆ J → ...`. In particular J0 itself
  is included. The conclusion is
  `Module.rank L (L ⊗[A] AdicCompletion ... (KaehlerDifferential (F J) A))
  = (d + J.card : ℕ)`.
  Scalar extension is written with L on the left so the L-module structure is
  canonical; tensor symmetry identifies it with M_J ⊗_A L in the node.
  Cardinal-valued Module.rank asserts actual finite dimension, avoiding
  Module.finrank's zero value for infinite-dimensional spaces.

Statement dependencies, signatures and docstrings read:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, the Noetherian self-module condition, equivalently all
  ideals finitely generated (lines 193–205).
- `def-weil-pbc-adically-complete-ring`:
  `Mathlib.RingTheory.AdicCompletion.Basic`, `IsAdicComplete` (lines 45–56),
  `AdicCompletion` (lines 164–174), `AdicCompletion.of` (lines 363–367), and
  `AdicCompletion.of_bijective_iff` (line 647). These give precisely completeness
  and the inverse-limit module, including separatedness.
- `def-weil-pbc-krull-dimension-ring`:
  `Mathlib.RingTheory.KrullDimension.Basic`, `ringKrullDim` (lines 27–31),
  the Krull dimension of the prime spectrum.
- `def-weil-pbc-kahler-differentials`: `Mathlib.RingTheory.Kaehler.Basic`,
  `KaehlerDifferential` (lines 145–154), `KaehlerDifferential.D`
  (lines 201–205) and `KaehlerDifferential.linearMapEquivDerivation`
  (lines 327–335). These give the differential module and its universal property.

All four are public imports; no dependency definition is copied.
Additional public Mathlib imports supply residue fields, fraction fields, subfield
closure and cardinal dimension. The available proof-dependency modules are plain
imports: Mathlib's `RingTheory.Ideal.KrullsHeightTheorem` for
`Ideal.exists_finset_card_eq_height_of_isNoetherianRing`, and
`RingTheory.Etale.Kaehler` for `KaehlerDifferential.isLocalizedModule_map`;
`WeilConjectures.RingTheory.PowerSeriesRingSubfields` for
`RingTheory.iInter_frobenius_subfields_mvPolynomial_mvPowerSeries`;
`WeilConjectures.RingTheory.PBasisComplementMonomialBasis` for
`RingTheory.pBasisComplementMonomialBasis`; and
`WeilConjectures.FieldTheory.PBasisDifferentialsBasis` for
`KaehlerDifferential.exists_basis_differentials_of_pBasis`.
Their full signatures and proof docstrings were read in the current source.
The three proof-only nodes `lem-per-parameter-ideal-formal-normalization`,
`lem-per-cofinite-subfields-finite-extension-differential-rank`, and
`lem-per-pth-power-series-completed-differential-comparison` currently have no
Lean records or mathlib matches. They are named in the six-step proof docstring;
there are no recorded modules to import. They are unnecessary to type the item
and require no dependency module in this statement-only delivery.

Edge cases checked before writing:

- E may be empty, corresponding to a perfect coefficient field. Then J and J0
  can only be empty and the asserted rank is d.
- E may be infinite; only J and J0 are finite. Every monomial still has finite
  support, and no Fintype or finite-p-basis hypothesis appears.
- For A = k[[t]], the rank is 1 + |J|, including J empty.
- J0 cannot generally be forced empty. For k = F_p(s) and
  A = k[[x,y]]/(y^p - s*x^p), A is a complete local domain of dimension 1;
  over k the completed differential rank is 2, so J empty fails. For J = {s},
  the relation becomes x^p ds = 0 and ds vanishes generically, leaving rank
  2 = d + |J|. The statement permits the needed nonempty J0.
- d = 0 is excluded exactly as in the node; p = 0 and p = 1 are excluded by
  positive prime characteristic. The zero ring is excluded by IsDomain.
- u, v, w, z are explicit independent universes for A, k, E, L. No universe
  equality, smoothness, regularity or finite-type assumption was added.

Searches run in this session (the wrapper retains searches.jsonl):

- `msearch.py leanfinder`: “A complete Noetherian local domain with coefficient
  field in positive characteristic has completed differential generic rank
  dimension plus the size of a sufficiently large finite removed p-basis subset”.
  Eight hits, including standard-smooth differential rank formulas and Krull
  dimension/cotangent-space results; none is this stabilization theorem.
- `msearch.py loogle`: `AdicCompletion, KaehlerDifferential`: zero hits.
- `msearch.py grep`: `cofinite.*[Pp][Bb]asis|completed.*[Gg]eneric.*[Rr]ank`:
  zero hits.
- `msearch.py leansearch`: “completed Kähler differentials generic rank after
  removing a finite subset of a coefficient field p-basis”: eight differential,
  standard-smooth and polynomial hits; no completion stabilization result.
- Direct rg in lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json
  for `cofinitePBasisCompletedGenericRank|CofinitePBasisCompletedGenericRank`
  and variants `cofinite.*[Pp][Bb]asis|completed.*generic.*rank`: no present
  declaration. The item-id search in lean/WeilConjectures likewise found none.
- Searches for AdicCompletion and p-basis uses in the project's RingTheory and
  FieldTheory modules found existing completion and p-basis constructions, but
  no copy of this theorem. Those existing Mathlib constructions are used here.

Validation: prescribed scompile.py compiled the final module in sandbox and
library-name modes, both in 1.3 seconds, without errors or warnings. Every
binder and universe is explicit, and every line is at most 100 characters.
The only postponed theorem is the named item, with all six accepted proof
steps in its docstring. No STATEMENT-DISPUTED issue or node correction remains.

## Second reading by Q157

I made a separate reading pass with the current node and final Lean module open.
The dispatcher prohibits starting another agent, so this is a self-check; the
maintainer's independent delivery review remains independent of the author.
Each binder was matched to domain, local, Noetherian, complete, positive
characteristic, finite positive dimension, the fixed coefficient field and its
residue isomorphism, and the complete bounded-monomial p-basis. The exact subfield
family and its fixed composite algebra maps were checked, followed by the
fraction-field and inverse-limit differential expressions. Finally, the finite
exceptional set, all its finite supersets and the d + cardinality equality were
compared directly. No hypothesis or conclusion mismatch was found and no
statement correction was made. Cardinal rank preserves the finite-dimensional
claim, empty E remains possible, and hcomp prevents an arbitrary scalar action.
The only item delta is its Lean binding, and there are no new or repaired nodes.
