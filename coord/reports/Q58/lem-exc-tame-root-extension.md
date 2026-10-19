## Worker report

The delivery states the unchanged node as
`IsDiscreteValuationRing.tame_root_extension` in
`lean/Sheaf/FieldTheory/TameRootExtension.lean`. Its sole proof is `sorry`; it adds no
other theorem, definition, dependency node, or statement correction. The previous
handoff contained no module, report, or item node copy; all three are now present.

Hypothesis-by-hypothesis correspondence:

- A henselian discrete valuation ring is `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [HenselianLocalRing R]`. The recorded DVR definition
  excludes fields and the zero ring.
- Its fraction field is `(F : Type v) [Field F] [Algebra R F] [IsFractionRing R F]`.
- Its algebraically closed residue field is the canonical
  `IsLocalRing.ResidueField R`, with `[IsAlgClosed (IsLocalRing.ResidueField R)]`.
  Thus the letter `k` in the node introduces no additional independent field.
- Positive residue characteristic is `(p : ℕ) (hp : 0 < p)` and
  `[CharP (IsLocalRing.ResidueField R) p]`. This does not assume `CharP R p`, so
  mixed-characteristic DVRs are retained. Positive characteristic of a field is
  prime, making `hmp : ¬ p ∣ m` equivalent to coprimality with `p`.
- The uniformizer is `(π : R)` with
  `hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}`, exactly its recorded meaning.
- The fixed separable closure is `(Fsep : Type w) [Field Fsep] [Algebra F Fsep]
  [IsSepClosure F Fsep]`. The `Algebra R Fsep` and `IsScalarTower R F Fsep`
  binders express the compatible composite embedding of `R`; they are structural
  data for the given tower and impose no extra mathematical condition.
- Positive exponent prime to the residue characteristic is
  `(m : ℕ) (hm : 0 < m) (hmp : ¬ p ∣ m)`.

Clause-by-clause correspondence:

- Every root of `X^m - 1` in the fixed closure belongs to `R`:
  `∀ ζ : Fsep, ζ ^ m = 1 → ∃ r : R, algebraMap R Fsep r = ζ`.
- The conditional root hypothesis is
  `∀ α : Fsep, α ^ m = algebraMap R Fsep π → ...`.
- The splitting field inside this same closure is an existential
  `L : IntermediateField F Fsep` satisfying
  `IsSplittingField F L (X ^ m - C (algebraMap R F π))`. A splitting intermediate
  field is uniquely determined there by the polynomial's roots; no arbitrary
  extension or embedding replaces it.
- It equals `F(α)`: `L = IntermediateField.adjoin F {α}`.
- It is cyclic Galois: `IsGalois F L ∧ IsCyclic (Gal(L / F))`.
- Its degree is `m`: `Module.finrank F L = m`. Finiteness is already implied by
  the splitting-field clause.
- Its normalization is the existing Mathlib `integralClosure R L`. The last
  clause supplies `q : Ideal (integralClosure R L)`, asserts `q.IsMaximal`, and
  explicitly asserts `∀ q', q'.IsMaximal → q' = q`. Thus uniqueness concerns
  **all** maximal ideals, independently of the ramification equation.
- The index at that unique maximal ideal is `q.ramificationIdx R = m`, using
  Mathlib's ramification index defined by the local quotient length. For the DVR
  normalization of Tag 09EV it is the exponent in Tag 09E4's
  `m_R B = m_B^e`. The integral extension forces `q` to contract to `m_R`.

Dependency declarations and source signatures read:

- `def-weil-pbc-henselian-terminology`: the recorded module is
  `WeilConjectures.Mathlib.RingTheory.Henselian`. The theorem uses the recorded
  `HenselianLocalRing R` class (defined in `Mathlib.RingTheory.Henselian`); the
  module also provides the recorded `IsStrictlyHenselianLocalRing` class and its
  equivalence with henselian plus separably closed residue field for Step 1.
- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing R` in
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, including its full class and
  `irreducible_iff_uniformizer` signature and docstring.
- `def-weil-algebraic-closure`: `IsAlgClosed` in
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, as the node's Mathlib match specifies
  for an algebraically closed field. The defining splitting condition is
  equivalent to the node's nonconstant-polynomial-root condition.
- `def-weil-pbc-integral-closure`: `integralClosure` in
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, with carrier
  `{r | IsIntegral R r}`, used directly on the canonical algebra `R → L`.
- `def-pd-separable-closure`: the recorded module
  `WeilConjectures.Mathlib.FieldTheory.IsSepClosed` explains that the closure
  itself is `IsSepClosure`; its recorded
  `IsSepClosure.exists_intermediateField_mem` gives the finite separable
  subextension description. The statement uses that existing `IsSepClosure`
  class, whose two fields are separable closedness and separability (including
  algebraicity).

The module publicly imports the statement interfaces and imports the stated
proof dependencies `Sheaf.AlgebraicGeometry.Morphisms.StrictLocalRootsOfUnity`
and `Sheaf.AlgebraicGeometry.Morphisms.DvrUniformizerRootAlgebra` without public
visibility. The generic Kummer, monic quotient, and PID normality ingredients use
Mathlib's existing `KummerExtension`, `AdjoinRoot`, and `Polynomial.RationalRoot`
interfaces. The theorem docstring gives all six node proof steps and names the
corresponding nodes. Source text checked: pione.tex, Tag 0BUB final paragraph;
more-algebra.tex, Tags 09EV and 09E4; and the current main-20261015 blueprint's
`lem-exc-dvr-galois.proof.md`, paragraph two.

Edge cases: `m = 1` is included and gives the trivial cyclic Galois group and
index and degree one. `m = 0` and characteristic zero are excluded exactly as in
the node. Positive characteristic of the residue field automatically excludes
`p = 1`. Mixed characteristic is included. A uniformizer is nonzero because a
DVR has nonzero maximal ideal. The three independent universes `u v w` put no
size equality on the ring, its fraction field, or the separable closure. No
local notation or private definition occurs. The coefficient, root, splitting
field and normalization use the same tower throughout.

Searches executed for this work:

- `msearch.py ... leanfinder` with query "Over a henselian discrete valuation
  ring with algebraically closed residue field, adjoining an nth root of a
  uniformizer prime to the residue characteristic is cyclic Galois of degree and
  ramification index n": eight hits, including
  `isCyclic_of_isSplittingField_X_pow_sub_C`, `isCyclic_tfae`, and generic
  ramification/Galois comparisons. None supplies the henselian lifting,
  uniformizer irreducibility, and ramification clauses together.
- `msearch.py ... leansearch` with query "A henselian discrete valuation ring
  with algebraically closed residue field contains all roots of unity of order
  prime to the residue characteristic and a uniformizer root extension is cyclic
  and totally ramified": eight hits on henselian classes and valuation
  uniformizers, no exact theorem.
- `msearch.py ... loogle 'IsDiscreteValuationRing, IsGalois'`: zero hits.
- `msearch.py ... grep 'uniformizer|eisenstein|ramificationIdx.*root' FieldTheory`:
  two hits, both rational-function valuations, no exact match.
- `rg` over the upstream `WeilConjectures/` sources for the item ID and
  `tame_root_extension`/root-uniformizer names: no whole-statement declaration.
- `rg` over project `lean/Sheaf` and `dag/lean_names_upstream.json` for the same
  names: the consumer's docstring and root-algebra/Abhyankar lemmas occur, but no
  duplicate declaration. The two recorded root-algebra proof modules give the
  generic ingredients, not this whole theorem.

Validation: the final module compiles cleanly via the prescribed `scompile.py`
wrapper, with no warnings. The node copy changes only `lean`, records the exact
signature without the proof assignment, and uses the UTC date from the machine.
No `STATEMENT-DISPUTED` or node fault applies.

## Second reading by Q58

I independently opened the repository node, the delivered node and Lean module,
every statement dependency's node and declaration, and the source passages. The
node is unchanged except for `lean`; there is no `statement_change`, new node,
or dependency module to review. No semantic or convention mismatch was found,
so I left the Lean and node record unchanged.

The source reading covered pione.tex, Tag 0BUB, the entire lemma and final proof
paragraph; algebra.tex, Tag 04GG, its local-ring setup and simple-root lifting
conditions; more-algebra.tex, Tag 09E4 (definition of an extension of DVRs and its
index), Tag 09E8 (finite separable normalization and uniqueness in the henselian
case), and Tag 09EV (the root algebra and its normalization). I also read paragraph
two of main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/
lem-exc-dvr-galois.proof.md. The source's general decomposition lemma does not
assume henselianity or algebraically closed residue field; those are exactly the
specialization explicitly made by this node and the blueprint. No completeness
or excellence hypothesis is needed for this root-extension assertion: the
standard root algebra is already the normalization. The finite separable
normalization discussion in 09E8 also applies to a DVR without excellence.

My object/hypothesis/clause inventory, matched against the Lean:

| Node item | Lean rendering and verdict |
| --- | --- |
| A commutative henselian DVR `R` | `(R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]`; exact. The DVR class extends local PID and requires nonzero maximal ideal. Henselianity is Mathlib's simple-root-lifting class, as the recorded dependency specifies. |
| Its fraction field `F` | `(F : Type v) [Field F] [Algebra R F] [IsFractionRing R F]`; exact, allowing any chosen fraction field. |
| Algebraically closed residue field `k` | `[IsAlgClosed (IsLocalRing.ResidueField R)]`; exact. Here `k` names the canonical residue field, rather than unrelated additional field data. I opened `IsAlgClosed`: every polynomial splits, equivalent to every nonconstant polynomial having a root. |
| Residue characteristic `p > 0` | `(p : ℕ) (hp : 0 < p)` and `[CharP (IsLocalRing.ResidueField R) p]`; exact. There is no characteristic assumption on `R` or `F`. |
| Uniformizer `π` | `(π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})`; exact. I checked `irreducible_iff_uniformizer` in the recorded DVR module. |
| A fixed separable closure of `F` | `(Fsep : Type w) [Field Fsep] [Algebra F Fsep] [IsSepClosure F Fsep]`; exact. I opened `IsSepClosure`, whose fields are separable closedness and separability, and the recorded upstream `IsSepClosure.exists_intermediateField_mem`. Algebraicity is included in separability. |
| The embedding of `R` into that closure | `[Algebra R Fsep] [IsScalarTower R F Fsep]`; exact compatible composite embedding. The composite always supplies these structures, so these binders do not restrict the extension mathematically. |
| Each positive integer `m` prime to `p` | `(m : ℕ) (hm : 0 < m) (hmp : ¬p ∣ m)`; exact, since positive characteristic of a field is prime. |
| All roots of `X^m - 1` belong to `R` | `∀ ζ : Fsep, ζ ^ m = 1 → ∃ r : R, algebraMap R Fsep r = ζ`; exact membership in the embedded ring, for every root in the fixed closure. |
| Every chosen root `α` of `π` | `∀ α : Fsep, α ^ m = algebraMap R Fsep π → ...`; exact conditional quantifier, using the same closure and embedding. |
| Its splitting field `L` inside that closure | `∃ L : IntermediateField F Fsep, IsSplittingField F L (X ^ m - C (algebraMap R F π)) ∧ ...`; exact. I opened `Polynomial.IsSplittingField`: it asserts splitting and generation by the root set. In a fixed ambient field its image is the unique splitting subfield, so the existential does not allow a larger unrelated extension. |
| `L = F(α)` | `L = IntermediateField.adjoin F {α}`; exact equality of subfields of the same closure. |
| Cyclic Galois | `IsGalois F L ∧ IsCyclic (Gal(L / F))`; exact, with the ordinary full field automorphism group. |
| Degree `m` | `Module.finrank F L = m`; exact. The splitting-field predicate already entails finiteness, so `finrank` cannot conceal an infinite-degree case. |
| Integral closure of `R` in `L` | `integralClosure R L`; exact existing dependency. I read its carrier `{r | IsIntegral R r}` and its canonical subalgebra structure, not a private replacement. |
| Unique maximal ideal of that closure | `∃ q : Ideal (integralClosure R L), q.IsMaximal ∧ (∀ q', q'.IsMaximal → q' = q) ∧ ...`; exact global uniqueness, not uniqueness only among ideals with index `m`. |
| Ramification index there is `m` | `q.ramificationIdx R = m`; exact. I read the definition as the length of `B_q / (q ∩ R)B_q` over `B_q`. Integrality makes the contraction the unique maximal ideal of `R`. In the normalized DVR this length equals the exponent in `m_R B_q = m_(B_q)^e`, precisely Tag 09E4. I checked the comparison `Ideal.ramificationIdx'_eq_ramificationIdx'`, which reduces the index to the DVR quotient length. |

The quantifier order is right: the ring, its fields, characteristic, uniformizer,
and exponent are fixed before the conjunction; the root-of-unity clause is
independent of `α`; each `α` satisfying the equation gets the splitting-field and
normalization conclusions. No unrelated finite-extension, Noetherian, separability,
or algebraic-closure hypothesis has been added. Nonzero `π` follows from the DVR
class and its maximal-ideal equation, rather than being assumed separately.

I read the proof-dependency signatures too: `strict_local_roots_of_unity` gives
cardinality, cyclicity, and the unit difference; `dvr_uniformizer_root_algebra`
gives the domain, DVR and generated maximal ideal for every positive exponent.
`AdjoinRoot.powerBasis'` gives the stated powers basis for monic polynomials.
The four Kummer declarations recorded on
`lem-exc-kummer-binomial-splitting-field` give exactly the generation, Galois,
cyclicity and degree ingredients, assuming primitive roots and irreducibility.
`PrincipalIdealRing.isNoetherianRing` and
`UniqueFactorizationMonoid.instIsIntegrallyClosed` supply the PID properties.
The imports include the recorded statement interfaces and the stated proof
ingredients, with the latter non-public. The theorem docstring follows all six
node proof steps, including denominator clearing and the two inclusions proving
that the standard root algebra is the normalization. All source and blueprint
docstrings are present. There is one theorem with `sorry`, no definitions, no
proved helper, no private/local notation, and no unbound universe or variable.

Edge cases checked independently: `m = 1` remains included (trivial Galois group,
degree and index one), while `m = 0` is excluded exactly by positivity. `p = 0`
is excluded by the node; `p = 1` is impossible for the residue field. Equal and
mixed characteristic are both admitted. Zero rings, fields as DVRs, and `π = 0`
are excluded by the DVR hypotheses, not by hidden additional assumptions. There
is no index family, scheme or zero-module parameter here. Independent universes
`u v w` allow the ring, fraction field and separable closure at different sizes;
no equality or artificial small-universe test is imposed.

Independent searches, using queries different from the worker's:

- LeanFinder via `msearch.py`: "A tame Kummer extension of the fraction field of
  a strictly henselian DVR obtained by extracting a root of a parameter has
  degree equal to ramification index and cyclic automorphism group". Eight hits,
  including `isCyclic_tfae`, `isCyclic_of_isSplittingField_X_pow_sub_C`,
  `autEquivZmod`, and `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing`.
  They give separate field-theoretic or ramification ingredients; none states
  the whole lifting/root/normalization result. I opened the relevant Kummer
  declarations and their common hypotheses.
- Loogle via `msearch.py`: `IsDiscreteValuationRing, Polynomial.IsSplittingField`;
  zero hits. An initial unqualified `IsSplittingField` query was rejected as an
  unknown identifier and was corrected to this qualified query.
- LeanSearch via `msearch.py`: "Extracting an invertible-order root of a parameter
  of a henselian discrete valuation ring gives a totally ramified cyclic field
  extension when the residue field is algebraically closed". Eight hits on
  `HenselianLocalRing.TFAE`, henselian constructors, `isCyclic_tfae`, and
  cyclotomic extensions; no whole-statement match.
- `rg` on upstream `WeilConjectures/`, project `lean/Sheaf`, and Mathlib
  `FieldTheory/` and `RingTheory/RamificationInertia/` for
  `tame.*root|root.*tame|uniformizer.*(cyclic|galois)|ramification.*kummer|kummer.*ramification|parameter.*root`.
  The project hits concern tensor factors, root normalization, Abhyankar
  cancellation, and the tame sequence's citation of this item. I opened
  `DvrGaloisRootFactorUniformizer.lean`: it concerns a generic tensor factor and
  an index-one conclusion after a further extension, not this theorem. I also
  opened `HenselianDVRTameSequence.lean`, which cites the present item in its
  proof and states a profinite exact sequence. Neither duplicates this item.
- A further `rg` for `tame_root_extension`, the item ID, uniformizer/root pairs,
  and henselian/Kummer pairs in upstream names and Mathlib found no existing
  full declaration. Thus `existing: false` is justified; all underlying notions
  remain the existing recorded definitions.

Validation: I reran the required `scompile.py` from the item sandbox on
`lean/Sheaf/FieldTheory/TameRootExtension.lean`; both the sandbox and library-path
checks succeeded with no errors or warnings. I independently compared the
extracted theorem signature against `lean.statement`: verbatim equal. All Lean
lines are at most 100 characters. The second reading changes only this report;
there is no statement correction or unresolved dispute.
