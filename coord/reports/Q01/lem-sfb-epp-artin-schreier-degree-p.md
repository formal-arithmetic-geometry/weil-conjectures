## Worker report

The module `Sheaf.RingTheory.EppArtinSchreierDegreeP` states
`IsDiscreteValuationRing.exists_epp_artin_schreier_degree_p`, with only `sorry` as
its proof. The item statement and all dependency fields are unchanged. There are
no new definitions, new nodes, dependency repairs or statement corrections.

Source read: `literature/stacks-project/more-algebra.tex`, the complete statement
and proof of Tag 09F1, `lemma-characteristic-p-case`, and the preceding valuation
tests. The node intentionally takes only the finite separable conclusion: the
source's nonempty-J construction itself produces a separable extension, and the
node does not request the stronger Galois wording. The ten-step accepted DAG
proof, including the corrected telescoping sign, is in the theorem docstring.
The named example module has been withdrawn; its node now records upstream
`WeilConjectures.CategoryTheory.CompactObject`, which was read for conventions.

Hypotheses and clauses, in order:

- Prime p: `p : ℕ` and `hp : p.Prime`.
- Complete DVRs A, B, C: each has `CommRing`, `IsDomain`,
  `IsDiscreteValuationRing`, and `IsAdicComplete (IsLocalRing.maximalIdeal _) _`.
- Injective local maps: `Algebra A B`, `Algebra B C`, both `IsLocalHom`
  instances, and the explicit `hinjAB` and `hinjBC`. `Algebra A C` and
  `IsScalarTower A B C` encode their composite.
- Fraction fields K, L, M: `Field` and `IsFractionRing` over A, B, C,
  respectively. The K/L/M algebras and scalar towers express the stated field
  inclusions and their compatibility with the ring inclusions. The extra
  A-to-L, B-to-M and A-to-M structures only record the same composites.
- M/L finite: `Module.Finite L M`; its degree is `hdegree : Module.finrank L M = p`.
- Bottom ramification index one: `hindex`, mapping A's maximal ideal to B's.
- Residue characteristic and fraction characteristic: the two `CharP` instances.
- Galois means normal and separable: `IsGalois L M` has exactly these two fields.
- Perfect-core equality inside k_B: `hcore` equates the range of the canonical
  residue map with the set of b admitting a p^n-th root for every natural n.
  Its n=0 clause is automatic and matches the node's n≥0 indexing.
- The required K₁/K: the existential field and algebra structures, a compatible
  A-algebra structure, `Module.Finite K K₁`, and `Algebra.IsSeparable K K₁`.
  Its universe is the maximum of all input universes; finite extensions can
  always be represented there and no test-field quantifier is restricted.
- Totally ramified: `hDVR` makes the actual `integralClosure A K₁` a DVR;
  `hlocal` supplies its canonical local map from A; bijectivity of the induced
  residue-field map says the residue field is unchanged. The following ideal
  equality gives ramification index `Module.finrank K K₁`. These conditions
  express exactly the inline definition of total ramification. Explicit instance
  arguments tie both residue and maximal-ideal expressions to this same DVR.
- Upper normalization: `eppUpperClosure C K M K₁` is literally the integral
  closure of C in `(M ⊗[K] K₁) ⧸ nilradical (M ⊗[K] K₁)`.
- Canonical map: `eppNormalizationMap A C K M K₁` restricts the map
  x ↦ 1 tensor x followed by reduction, so contracts ideals along the actual
  normalization map, rather than along a map supplied as an assumption.
- Every maximal q: the universal binder and `q.IsMaximal` include all branches.
  The first conjunct asserts maximality of its contraction n in the lower closure.
  The next asserts that the lower localization at n is a DVR. The following
  existential asserts both domain and DVR structure for the upper localization
  at q; no global domain assertion is imposed on a product normalization.
- Finally `Ideal.map` along normalization followed by localization extends n to
  the upper localized ring, and equals the extension of q there. This is exactly
  n S'_q = q S'_q, with no residue-separability or further-base-change conclusion.

Dependency declarations read and used:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`
  (lines 56–60); excludes fields, and includes locality and principal ideals.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete` (lines 45–56),
  including both Hausdorffness and precompleteness.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra` (line 95).
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`
  (line 216), whose carrier is `IsIntegral`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct` (line 81).
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`
  (line 57), the localization away from the specified prime.
- `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable` (line 549), whose
  algebraicity is built in through separability of the minimal polynomial.
- `Mathlib.FieldTheory.Galois.Basic`: `IsGalois` (line 57).
- `Mathlib.RingTheory.LocalRing.ResidueField.Basic`: `IsLocalRing.ResidueField.map`
  (line 96), induced by the actual local ring map.
- `Sheaf.RingTheory.EppEssentiallyFiniteTypeTraits`: existing real constructions
  `IsDiscreteValuationRing.eppReducedTensor`, `.eppUpperClosure`, and
  `.eppNormalizationMap` (lines 45, 52, 62). Their complete definitions were read.
  Only these general constructions are used; the essentially-finite-type
  existence theorem and its hypothesis are not used. No new dependency on that
  downstream theorem is added to the DAG, and none of its proof is assumed.
- Proof-only import `Sheaf.RingTheory.CompleteDVRFiniteNormalization`:
  `IsDiscreteValuationRing.complete_finite_normalization`; full statement and
  proof docstring read. The other statement/proof dependency nodes were read;
  the Artin–Schreier presentation, valuation tests, truncated coefficients,
  totally ramified base change, and approximate uniformizer-root nodes currently
  have no recorded modules, so no imports are invented for them.

Edge cases checked: p=0 or 1 is excluded by primality; p=2 is included. Fields
are excluded only for the three given DVRs, as the node requires. Upper residue
fields need not be perfect, finite or algebraic. The integral Artin–Schreier case
allows K₁=K and ramification index one. A split generic tensor is allowed and
all its maximal branches are tested. Nilpotents are removed by the actual
nilradical quotient, not by an assumed reducedness hypothesis. The lower
localization condition is explicitly retained even though complete finite
normalization will later imply it. No new statement fault was found.

Searches actually run (2026-10-24):

- `msearch.py ... leanfinder`: “Artin Schreier Galois degree p extension of
  complete discrete valuation rings admits a finite separable totally ramified
  coefficient extension eliminating ramification”: 8 hits, including
  `Ideal.ramificationIdxIn_mul_ramificationIdxIn`,
  `Ideal.inertiaDegIn_ne_zero`, and unramified-at-prime results; none states this
  coefficient-extension theorem or its perfect-core hypothesis.
- `msearch.py ... loogle`: `IsDiscreteValuationRing, IsGalois, IsAdicComplete`:
  0 hits.
- `msearch.py ... grep`: `WeakSolution|weakSolution|TotallyRamified|totallyRamified|IsGalois`
  under RingTheory: 25 hits on general Galois, trace and ramification APIs, no
  matching coefficient-extension statement.
- `msearch.py ... grep`: `Epp|epp|ArtinSchreier` under FieldTheory: 0 hits.
- `rg` in both project source trees for weak solution, total ramification,
  perfect core, Epp and Artin–Schreier: found the general Epp constructions used
  here, henselian DVR ramification results, and reciprocal-polynomial
  Artin–Schreier field constructions, but no exact match.
- Literal item-id search in `lean/WeilConjectures`: no match.

Validation: `scompile.py` compiled this file separately as a sandbox and as its
library module against the published live build; both completed with no errors
or non-sorry warnings. Delivery preflight and its fresh per-file compile are run
by `deliver2.py`.

## Second reading by Q01

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fix (cc second reader, 2026-10-24)

The delivered module public-imported `Sheaf.RingTheory.EppEssentiallyFiniteTypeTraits`, the module of
`lem-sfb-epp-essentially-finite-type-traits`. Its proof_deps reach this item through
lem-sfb-epp-weak-perfect-residue → lem-sfb-epp-finite-coefficient-triple → this item. At stage 3 that
citer could then never import this theorem (import cycle). The fix drops the import and writes the
objects inline from Mathlib. S' = `integralClosure C ((M ⊗[K] K₁) ⧸ nilradical (M ⊗[K] K₁))`, which
is definitionally the citer's `eppUpperClosure C K M K₁`. The map R' → S' is a universally quantified
φ pinned by `φ x = mk (1 ⊗ₜ x)`. This φ is unique because S' is a subring, and the citer's
`eppNormalizationMap A C K M K₁` satisfies the pin by `rfl`, which a check file compiled in the same
call confirms. All hypotheses, the totally-ramified clauses and the four weak-solution conjuncts are
otherwise unchanged. Compiled clean with nt_compile.py (4.9 s). The lean record's statement is
updated to match. Nothing in stmt_deps changes. No lake build. No repository was modified.
