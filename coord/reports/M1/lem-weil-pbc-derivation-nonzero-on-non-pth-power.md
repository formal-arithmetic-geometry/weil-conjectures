## Worker report

The module `Sheaf.RingTheory.Derivation.DetectNonPthPower` states
`Derivation.exists_apply_ne_zero_of_not_pth_power`, with its proof `sorry`.
No definitions, additional nodes, dependency modules, or statement corrections were needed.

Clause-by-clause correspondence:

- Prime number p: `(p : ℕ) [Fact p.Prime]`.
- Integral domain B: `(B : Type u) [CommRing B] [IsDomain B]`.
- p = 0 in B: `[CharP B p]`. In a nonzero integral domain with p prime,
  this is equivalent to the node's p = 0: the characteristic divides p and cannot be 1.
- Fraction field M of B: `(M : Type v) [Field M] [Algebra B M]
  [IsFractionRing B M]`. The embedding used in the power condition is `algebraMap B M`.
  `IsFractionRing` is localization at nonzerodivisors, which in a domain are exactly
  the nonzero elements, i.e. localization at the zero prime. This is the fraction-field
  specialization of def-weil-pbc-localization-at-prime, not a new notion.
- Noetherian local base (R₀, m₀): `(R₀ : Type w) [CommRing R₀]
  [IsNoetherianRing R₀] [IsLocalRing R₀]`, with m₀ = `IsLocalRing.maximalIdeal R₀`.
- m₀-adically complete: `[IsAdicComplete (IsLocalRing.maximalIdeal R₀) R₀]`.
  This includes separatedness, not just existence of limits.
- Finite type ring map R₀ → B: `[Algebra R₀ B] [Algebra.FiniteType R₀ B]`.
  An algebra structure on commutative rings is precisely such a ring map. The theorem
  is universally quantified over any witness R₀ and its map; this renders the node's
  assumption that such a witness exists without imposing injectivity or locality on the map.
- f in B: `(f : B)`.
- f not a pth power in M: `(hf : ¬ ∃ x : M, x ^ p = algebraMap B M f)`.
- Existence of an additive derivation B → B satisfying the stated Leibniz rule and
  nonzero on f: `∃ D : Derivation ℤ B B, D f ≠ 0`.
  Integer linearity is equivalent to additivity for maps of additive groups;
  the extra field D(1) = 0 follows from the Leibniz rule by cancellation in B.
  Thus this is exactly an absolute derivation; it does not assert R₀-linearity.

Dependency declarations read and used:

- def-weil-pbc-noetherian-ring: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, the self-module Noetherian condition, equivalently all ideals FG.
- def-weil-pbc-adically-complete-ring: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `IsAdicComplete`. Its signature extends `IsHausdorff` and `IsPrecomplete`;
  its self-module specialization is the dependency's complete ring notion.
- def-weil-pbc-finite-type-algebra (Mathlib leaf): `Mathlib.RingTheory.FiniteType`,
  `Algebra.FiniteType`, whose field says the top subalgebra is finitely generated.
- def-weil-pbc-localization-at-prime (Mathlib leaf): recorded `Localization.AtPrime`,
  `Ideal.ResidueField`, and `Ideal.Fiber` signatures/docstrings read in the AtPrime,
  ResidueField/Ideal, and ResidueField/Fiber source files. Only the fraction-field case
  is needed, rendered by `IsFractionRing` from
  `Mathlib.RingTheory.Localization.FractionRing`: localization at `nonZeroDivisors B`.
- Conclusion uses `Derivation` from `Mathlib.RingTheory.Derivation.Basic`; its full
  structure signature/docstring was read. `Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic`
  supplies the maximal ideal of the local base.

Source check: the repository's `literature/stacks-project/more-algebra.tex` is absent
on this machine, so read the complete statement and proof at
https://stacks.math.columbia.edu/tag/07PH instead. The statement agrees with the node.
The declaration docstring carries all six node proof steps and their supporting node IDs.

Edge cases checked: p = 0 and p = 1 are excluded by primality, as in the source;
B = the zero ring is excluded by IsDomain; f = 0 and any pth power do not satisfy hf;
if M is perfect there is no f satisfying hf. The base map may have kernel, and R₀
need not have characteristic p (the proof first passes to its image). Fields are allowed
as complete local bases, with zero maximal ideal. No positive Krull dimension or nonempty
set of algebra generators is imposed. Separate explicit universes u, v, w allow arbitrary
sizes for B, M, and R₀. All variables are bound and autoImplicit is disabled.

Searches for an existing statement:

- msearch.py leanfinder: "A derivation detects a non pth power in a finite type domain
  over a complete Noetherian local ring of characteristic p". Eight hits, all perfect
  rings/closures/perfections; none states the detection theorem.
- msearch.py loogle: `Derivation, CharP`. Zero hits.
- msearch.py grep: `exists.*derivation|derivation.*exists` in `RingTheory/Derivation`.
  Zero hits.
- msearch.py leansearch: "A characteristic p domain finite type over a complete local
  ring admits a derivation nonzero on any element not a pth power". Service unavailable
  (Internal Server Error); no verdict assigned. The other search methods succeeded.
- rg of `derivation|Derivation` in source RingTheory and project lean/Sheaf/RingTheory:
  localization extension and Hopf-algebra Cartier results; no matching theorem.
- rg of `derivation.*(pth|nonzero|power)|Derivation.*CharP` in all source WeilConjectures
  and project lean/Sheaf: a result that derivations kill pth powers, but no converse
  detection result with these hypotheses.
- rg of the item's exact ID in source WeilConjectures: no hits.
- rg of the proposed name / non-pth-power names in dag/lean_names_upstream.json,
  project lean/Sheaf and source WeilConjectures: no conflict; grep of `Derivation|07PH`
  in dag/lean_names_upstream.json also found no existing detection statement.

Validation: server scompile.py completed with exit code 0 in 1.3 s, without warnings.
No statement disputes or node faults found. The independent second reader must still
review this module; no second-reading section has been written by this worker.

## Second reading by M1

Independently opened the sandbox node and module, all four statement-dependency nodes,
and the Mathlib declarations below. Read the actual Stacks TeX at
https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex,
from `lemma-find-D` through its proof, and the introduction of the section
`section-regularity-derivations`; also checked the rendered tag
https://stacks.math.columbia.edu/tag/07PH. The local literature checkout lacks that
TeX file. The section introduces ordinary ring maps and absolute derivations;
there is no additional standing field, finiteness, or linearity hypothesis.
The node agrees with the source. No statement correction is needed.

The following is my object/hypothesis/conclusion inventory, matched against the Lean:

- Prime integer p: `(p : ℕ) [Fact p.Prime]`. Exact; the natural-number convention
  expresses precisely a positive prime.
- Commutative integral domain B: `(B : Type u) [CommRing B] [IsDomain B]`.
  Exact, including nontriviality; the source's rings are commutative.
- p vanishes in B: `[CharP B p]`. Exact under the preceding assumptions:
  if p vanishes, the characteristic of this nonzero domain divides the prime p
  and hence is p. Conversely characteristic p makes p vanish. No extra restriction.
- Fraction field M and the inclusion of B: `(M : Type v) [Field M]
  [Algebra B M] [IsFractionRing B M]`, using `algebraMap B M`. Exact.
  Read `IsFractionRing` in `Localization/FractionRing.lean:53`: it is
  `IsLocalization (nonZeroDivisors B) M`. Read the dependency's
  `Localization.AtPrime` in `Localization/AtPrime/Basic.lean:57`, localization at
  `P.primeCompl`. For the zero prime of a domain that complement and the
  nonzerodivisors are both precisely the nonzero elements. Thus this is the same
  fraction-field notion, with an arbitrary model rather than a private copy.
  Also opened `Ideal.ResidueField` and `Ideal.Fiber` in the recorded residue-field
  files; the node's residue-field and fibre clauses are not used by this item.
- Existence of a Noetherian local base `(R₀, m₀)`: `(R₀ : Type w) [CommRing R₀]
  [IsNoetherianRing R₀] [IsLocalRing R₀]`. Exact. The named maximal ideal is
  `IsLocalRing.maximalIdeal R₀`; uniqueness of the maximal ideal removes any need
  for an independent ideal binder. Read `IsNoetherianRing` in
  `Noetherian/Defs.lean:196` and its ideal-FG equivalence: this is exactly the
  dependency node's notion, not finite dimensionality or finite type.
- Completeness at that maximal ideal:
  `[IsAdicComplete (IsLocalRing.maximalIdeal R₀) R₀]`. Exact. Opened the class
  in `AdicCompletion/Basic.lean:56` and `AdicCompletion.of_bijective_iff:647`:
  this asserts both Hausdorffness and precompleteness, equivalently bijectivity
  of the canonical map to the inverse limit, as the dependency requires.
- A finite type ring map R₀ → B: `[Algebra R₀ B] [Algebra.FiniteType R₀ B]`.
  Exact. Read `Algebra.FiniteType` in `FiniteType.lean:39`: the top subalgebra
  is finitely generated. For commutative rings an algebra supplies the ring map;
  neither injectivity nor a local map is required. Quantification over a witness
  R₀ and its map is equivalent to using the node's existential premise, since
  the conclusion does not mention that witness. The order of f and the base
  witness does not change the assertion because their hypotheses are independent.
- Element f of B: `(f : B)`. Exact.
- f is not a pth power in M:
  `(hf : ¬ ∃ x : M, x ^ p = algebraMap B M f)`. Exact, including roots outside B.
- Existence of an additive map D : B → B with the Leibniz rule:
  `∃ D : Derivation ℤ B B, ...`. Exact. Read the full structure signature and
  fields in `Derivation/Basic.lean:45`. Integer linearity is precisely additivity
  on additive groups; the scalar action of B on itself is multiplication.
  The additional `map_one_eq_zero'` is forced by the Leibniz rule and additive
  cancellation. This is absolute differentiation, not R₀-linear differentiation.
- Nonzero value on the specified element: `D f ≠ 0`. Exact, under the same
  existential quantifier; no assertion that every derivation detects f.

Edge cases: zero B is excluded by the source's domain assumption; p = 0 or 1
is excluded by primality. Zero f, or any pth power, fails hf. For a perfect
fraction field the premise is empty, as intended. B may be a field, R₀ may
be a field with zero maximal ideal, and the base map may have kernel.
No characteristic assumption is imposed on R₀ itself, and no positive dimension,
nonempty generator list, or nonempty index set is required. Separate bound
universes u, v, w cover arbitrary sizes for all three rings. There are no scheme
or index-set variables in this statement; the proof's zero-variable power-series
and polynomial cases impose no restriction on its signature.

Independent duplicate searches (using different wording from the first reader):

- msearch loogle `Derivation, "ne_zero"`: zero hits.
- msearch leanfinder `Absolute derivations separate elements outside the image of
  Frobenius in domains essentially finite type over complete local rings`: eight
  hits, concerning differential field extensions, arithmetic Frobenius, Witt
  vectors, or formal étaleness; none has this statement.
- msearch leansearch `There exists an additive derivation of a domain nonzero on
  an element not a power in its fraction field`: unavailable, Internal Server
  Error, recorded without a mathematical verdict.
- rg over Mathlib RingTheory, source WeilConjectures, project lean/Sheaf, and
  dag/lean_names_upstream.json for `frobenius.*derivation`,
  `derivation.*frobenius`, `derivation.*complete`, the proposed declaration and
  `07PH`: only the source's theorem that derivations kill Frobenius powers.
- rg for `derivation.*(detect|separat|non.?pth|complete.local)`,
  `exists.*derivation`, and `derivation.*exists` in Mathlib's derivation directory,
  the source, and project: Cartier/bialgebra existence statements only. Opened
  `AlgHom.isPrime_iInf_pow_ker_of_forall_exists_derivation` and
  `Bialgebra.exists_derivation_of_cotangent`; their extra bialgebra/cotangent
  data and different conclusions do not give this node. No duplicate found.

No new nodes or dependency modules are in this delivery, and none is needed.
No mismatch found and no Lean or node edit made. The theorem is still the sole
`sorry`; there is no definition, hollow data, or proved auxiliary statement.
The docstring includes the correct source and blueprint ID and covers all six
node proof steps (its first paragraph combines node steps 1–2, and its next two
cover node steps 3–4). All supporting node IDs occur, including the differential,
p-basis, intersection, dual-separation, and denominator-clearing arguments.
The namespace, imports, line widths, explicitly bound universes, and signature
record were checked. The node's `lean.statement` is verbatim the file signature.
The only change by this second reading is this independent review report.
