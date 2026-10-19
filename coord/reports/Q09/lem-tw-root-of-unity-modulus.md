## Worker report

The new module `Sheaf.Paper.RootOfUnityModulus` states
`AlgebraicGeometry.WeilGroup.rootOfUnity_modulus_and_isOfWeight_zero`, with its whole
proof postponed by `sorry`. There are no new definitions, auxiliary theorems, new nodes,
dependency repairs, or statement corrections. Only the item's `lean` field changes.

I read the full item, its sole statement dependency `def-tw-eigenvalue`, and the exact
Mathlib proof dependency `lem-tw-complex-norm-root-of-unity`. I read both blueprint
snapshots' lemma and proof, which agree. There is no repair-note file for this item.
The current `LinearAlgebra` module is absent from the older source checkout; I obtained
its actual live source through `scompile.py --source
WeilConjectures.EtaleCohomology.Purity.RealSheaves.LinearAlgebra` and read the full
`IsOfWeight` signature, body and docstring.

Clause-by-clause correspondence:

- The ambient prime-power base and distinct coefficient prime in `def-tw-eigenvalue`
  are `(p l r : ℕ) [Fact p.Prime] [Fact l.Prime] (_hr : 1 ≤ r)
  (_hlp : l ≠ p)`, with `q` written as `p ^ r`. A positive integral exponent is
  represented by a positive natural number, covering every exponent in the convention.
  These are the coefficient and base parameters already assumed by that definition.
- The fixed field isomorphism defining the absolute value is
  `(ι : PadicAlgCl l ≃+* ℂ)`. This has no continuity assumption.
- The specified nonzero scalar in the algebraic closure is
  `(ζ : (PadicAlgCl l)ˣ)`, using Mathlib's fixed algebraic closure of the ell-adic field.
- Being a root of unity is exactly
  `(hζ : ∃ n : ℕ, 1 ≤ n ∧ ζ ^ n = 1)`, with the equality in the unit group.
  Unit coercion preserves powers and one, so this is the stated scalar power equality.
- Absolute value one is the first conjunct `‖ι (ζ : PadicAlgCl l)‖ = 1`.
  The revised eigenvalue definition explicitly defines absolute value this way.
- Weight zero is the second conjunct
  `IsOfWeight ι.toRingHom (p ^ r) 0 (ζ : PadicAlgCl l)`. This uses the recorded
  dependency, whose body is `‖ι α‖ = (q : ℝ) ^ (w / 2)`. Its real weight parameter
  specializes to the integer zero in the node, without changing the weight convention.
- The final clause is `∀ κ : PadicAlgCl l ≃+* ℂ,
  ‖κ (ζ : PadicAlgCl l)‖ = 1`. The independently quantified isomorphism covers every
  isomorphism, including the initially fixed one.

The lemma concerns scalars, not an eigenvalue of a chosen operator. Accordingly it has
no scheme, cohomology group, Frobenius operator or eigenvector premise: those objects
occur in the eigenvalue portion of the dependency, while its absolute-value and weight
portions apply to scalars. No assertion of being an eigenvalue is silently imposed.

Dependency declarations used:

- `WeilConjectures.EtaleCohomology.Purity.RealSheaves.LinearAlgebra` (public import):
  `AlgebraicGeometry.WeilGroup.IsOfWeight`, read from the live source. This is the
  published declaration realizing the weight clause of `def-tw-eigenvalue`; the snapshot
  dependency has no `lean` record. No replacement definition is introduced.
- `Mathlib.Analysis.Complex.Basic` (proof import):
  `Complex.norm_eq_one_of_pow_eq_one {ζ : ℂ} {n : ℕ}
  (h : ζ ^ n = 1) (hn : n ≠ 0) : ‖ζ‖ = 1`, read at lines 101–102 of the pinned
  Mathlib source. This exactly matches `lem-tw-complex-norm-root-of-unity`.
- `PadicAlgCl` is Mathlib's `AlgebraicClosure ℚ_[l]`, as read in
  `Mathlib.NumberTheory.Padics.Complex`; it is available through the public import.

The declaration docstring gives the complete node proof: choose a positive exponent,
map its power equality through the isomorphism, use the complex-norm lemma with the
nonzero exponent, identify the absolute-value clause, specialize the real-power
weight equality to zero, and repeat for an arbitrary other isomorphism.

Edge cases checked mathematically before writing: `ζ = 1` allows exponent one; `ζ = -1`
allows exponent two; higher roots have the same argument with no primitivity assumption.
The exponent zero is excluded, since otherwise every unit would satisfy the power
premise. The scalar zero is excluded by the unit type. For every allowed base `p ^ r`,
the weight-zero real power is one. No continuity or compatibility with the ell-adic norm
is required of either isomorphism. The coefficient field and ℂ are the same concrete
fields as in the source, so there is no independent universe restriction. Norms are
always taken after mapping to ℂ, avoiding the incorrect ell-adic interpretation.

Searches performed for this delivery:

- `msearch.py ... leanfinder`, query "Every root of unity in the algebraic closure of
  the ell-adic numbers has absolute value one under every isomorphism to the complex
  numbers and weight zero": eight hits, including `PadicComplex.norm_extends`,
  `NumberField.Embeddings.pow_eq_one_of_norm_eq_one` and unrelated cyclotomic and
  Mahler-measure results; no exact three-clause theorem.
- `msearch.py ... leansearch`, query "root of unity has complex absolute value one and
  Frobenius weight zero": eight hits, including the exact complex norm lemma and
  primitive-root and roots-of-unity variants; none includes the weight convention and
  both field-isomorphism clauses.
- `msearch.py ... loogle`, query
  "Complex.norm_eq_one_of_pow_eq_one, IsOfWeight": zero hits, unknown identifier
  `IsOfWeight`. This service does not index the project definition; not evidence of
  its absence. The live source above supplies it.
- `msearch.py ... grep`, query
  "norm_eq_one_of_pow_eq_one|root_of_unity.*weight": six Mathlib hits, including the
  complex norm theorem and uses in number fields and roots-of-unity files.
- Direct `rg` for `lem-tw-root-of-unity-modulus`, norm/root-of-unity, weight-zero and
  `pow_eq_one` patterns in `WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: upstream `RankOne.lean` supplies only
  `frobeniusWeight_eq_zero_of_pow_eq_one`; upstream
  `Mathlib/Analysis/Normed/Field/Basic.lean` supplies only
  `norm_eq_one_of_pow_eq_one`. I read both complete declarations and docstrings.
  Neither states all the item's clauses, so neither can be an exact existing binding.
  No matching side-project declaration was found.
- Direct `rg` for the proposed declaration name in upstream Lean, Mathlib, `lean/Sheaf`
  and the upstream-name index: no collision.

No statement dispute or node fault was found. The existing dependency is sufficient
at weight zero; its allowance of general real weights does not alter this specialization.

Validation uses only `scompile.py` for the delivered file and `deliver2.py` for the
server preflight, dry run and final push. The shared repositories were read only;
all authored files are in this item's sandbox.

## Second reading by Q09

Independent maintainer second reading, 2026-10-18, of immutable delivery
20ba631380c2cbce9f9ccb3cf2301cbf724bd848. This section replaces the worker's
placeholder; the maintainer performed this reading, not a second Q09 worker.

I opened the snapshot item JSON, its sole statement dependency JSON, the delivered
module and this report. I read the master blueprint lemma (order 2627), the
main-20261015 lemma (order 2971) and its separate proof, and the master eigenvalue
source. The item statement agrees verbatim with the blueprint. The dependency's
already adopted complex absolute value corrects the original source's impossible
normalization v_l(q)=1 for l different from p; this delivery makes no new statement
correction. The root-of-unity conclusion holds under the adopted convention.

Hypothesis and conclusion checks:

- `p l r : ℕ`, the two prime instances, `1 ≤ r`, and `l ≠ p` express the ambient
  prime-power convention in the dependency; no new finiteness or continuity premise.
- `PadicAlgCl l` is Mathlib's `AlgebraicClosure ℚ_[l]` (Padics/Complex.lean:54).
  Its unit type expresses the source's nonzero scalar. The positive natural
  exponent in `hζ` expresses exactly a root of unity. Coercion of units preserves
  powers and one; no primitive-root or prescribed-order assumption occurs.
- The fixed ring equivalence `ι` defines the absolute value; the first conjunct
  is exactly that complex norm being one.
- The second conjunct uses the actual published `IsOfWeight`, whose source I
  obtained through `scompile.py --source
  WeilConjectures.EtaleCohomology.Purity.RealSheaves.LinearAlgebra`. Its body is
  `‖ι α‖ = (q : ℝ) ^ (w / 2)`, with `E` an arbitrary field and `w : ℝ`.
  Specializing to zero expresses precisely the node's integer weight zero.
  The scalar assertion needs no Frobenius eigenvector or scheme premise.
- The final conjunct quantifies over every ring equivalence `κ` to ℂ independently
  of `ι`. It includes `κ = ι` and has no topological restriction.

For the single proof step, I read the proof-dependency node
`lem-tw-complex-norm-root-of-unity` in the context clone and its exact Mathlib
binding `Complex.norm_eq_one_of_pow_eq_one`, Analysis/Complex/Basic.lean:101–102.
It requires only the power equality and a nonzero exponent. Mapping `hζ` to ℂ
supplies the equality, and positivity supplies nonzeroness. The weight equality
then reduces by zero real exponent; repeating for `κ` supplies the last clause.
The delivered declaration docstring records precisely these steps and citations.

Edge cases: 1 has exponent one, -1 exponent two, and all higher roots are covered
without primitivity. Exponent zero is correctly excluded (otherwise 2 would pass
the power premise). Zero is excluded by the source's unit domain. Every allowed
prime-power base is positive and its zeroth real power is one. There is no
independent site, scheme, index, or coefficient universe restriction: the fields
are the concrete fields in the source. Empty schemes and zero cohomology groups
play no role in this scalar lemma.

Independent searches used `rg` for the node id, root-of-unity, `pow_eq_one`, weight
zero and the proposed name in project Lean, upstream WeilConjectures, Mathlib,
and the upstream name index. I opened RankOne.lean:53–59 and the complete upstream
Mathlib/Analysis/Normed/Field/Basic.lean. The former concludes only logarithmic
`frobeniusWeight = 0`; the latter concludes only a norm equality. Neither gives
this three-clause statement. The worker's LeanSearch, LeanFinder, Loogle and grep
search records are present; invalid Loogle queries are explicitly reported.
No duplicate definition or full existing theorem was found.

Mechanical checks: the item's `lean.statement` equals the file's signature
verbatim; the commit changes only its `lean` field plus this report and its one
module. There are no new nodes or dependency modules. The file has one theorem
with exactly `by sorry`, no definitions, no lines exceeding 100 characters, and
`autoImplicit false`. Both docstrings identify the source and blueprint. The
public import supplies statement notions; the private Mathlib import supplies
the proof dependency. All parameters are bound. No arbitrary construction,
hollow definition, pro-etale replacement, or dropped route-pivot machinery occurs.
The current shared dropped-node list contains neither direct dependency; no
item-specific route-pivot repair note exists.

Compiler reproduction, using the immutable snapshot:

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q09
lem-tw-root-of-unity-modulus
snapshot/lean/Sheaf/Paper/RootOfUnityModulus.lean`

Exit code 0, no errors or warnings. Output identifies sandbox
`Sheaf/Stage2/Sandbox0.lean` (60.6 seconds reported including wrapper overhead)
and library `Sheaf/Paper/RootOfUnityModulus.lean` (11.9 seconds). The installed
wrapper currently performs these overlay/server checks remotely; no local
compilation is claimed. No global build, direct ssh, repository edit or Git
mutation was performed by this reviewer.

Finding H11: the original second-reading section was only a disclaimer, not a
reading. Replaced it with this independent review. Also corrected the report's
claim that the snapshot dependency records `IsOfWeight`: the record is absent,
but the exact published declaration is available and was inspected and compiled.
The report originally gave no concrete successful compiler output; the reproduction
above now supplies it. No Lean or mathematical statement change was necessary.
