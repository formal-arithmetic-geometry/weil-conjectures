## Worker report

The node is already stated in the source project.  I therefore added no Lean module.
The existing declaration is
`AlgebraicGeometry.Scheme.Hom.degree_pos_of_isAmple_of_nonempty` in
`WeilConjectures.AlgebraicGeometry.Modules.Ample`.
Its signature is:

`theorem Scheme.Hom.degree_pos_of_isAmple_of_nonempty (f : X ⟶ Spec (.of K)) [IsProper f]\n    [Nonempty X] (M : X.Modules) (hample : IsAmple f M) : 0 < f.degree M :=`

The field `f : X ⟶ Spec (.of K)` is the structure morphism of the scheme over the
field `K`; `[IsProper f]` renders properness; `[Nonempty X]` renders nonemptiness;
`M : X.Modules` is the invertible module; and `hample : IsAmple f M` renders the
node's ample hypothesis.  `f.degree M` is the recorded Hilbert degree
(`Scheme.Hom.degree`), and `0 < f.degree M` is positivity.  The node's dimension
parameter `g` is represented by the topological Krull dimension used in the
existing degree definition; no extra dimension hypothesis occurs in Tag 0BEV.

The statement dependencies were checked directly: `def-sc-ample` records
`AlgebraicGeometry.IsAmple` in the same source module, and `def-sc-hilbert-degree`
records `AlgebraicGeometry.Scheme.Hom.degree` there.  Both are exactly the names
used by the existing theorem.

Edge cases checked include the empty scheme (excluded by `[Nonempty X]`),
zero-dimensional schemes (allowed), arbitrary finite or infinite topological
Krull dimension as handled by `Scheme.Hom.degree`, and arbitrary field
characteristic (the theorem has only `[Field K]` from the module variables).

Searches for an independent declaration were made with `msearch.py leanfinder`
(query: “ample module positive degree nonempty proper scheme”; it returned only
unrelated Mathlib hits) and `msearch.py loogle` (query:
`AlgebraicGeometry.Scheme.Hom.degree_pos_of_isAmple_of_nonempty`; no indexed
Mathlib hit).  Grep of the source then found the exact declaration in
`WeilConjectures/AlgebraicGeometry/Modules/Ample.lean` (the theorem at the
`@[stacks 0BEV]` block).  The project DAG search found no existing Lean node
for this item.

## Earlier second reading (a previous round; superseded)

I opened the node and the source declaration independently.  The node asks for a
field, a nonempty proper scheme, an ample invertible module, and strict positivity
of its Hilbert degree.  The source theorem has precisely the corresponding
structure morphism `f`, properness and nonemptiness typeclasses, module `M`,
`IsAmple f M`, and conclusion `0 < f.degree M`; `IsAmple` includes invertibility.
No hypothesis or conclusion is added, dropped, weakened, or strengthened.  The
source's degree uses the node's recorded `Scheme.Hom.degree`, including its
Krull-dimension parameter.  Thus the existing declaration is an exact statement
match and the node is recorded with `existing: true`.

## Second reading by E1

I independently opened the item JSON, both statement-dependency JSON files, and
`WeilConjectures/AlgebraicGeometry/Modules/Ample.lean`, including its section
variables, definitions and theorem at lines 603–605. The source `.tex` is not
installed in this clone. I obtained the upstream Stacks `varieties.tex` in the
sandbox scratchpad and read `lemma-ample-positive`,
`definition-intersection-number`, and `definition-degree` with their surrounding
text. The public sources are [Tag 0BEV](https://stacks.math.columbia.edu/tag/0BEV),
[Tag 0BEP](https://stacks.math.columbia.edu/tag/0BEP), and
[Tag 0BEW](https://stacks.math.columbia.edu/tag/0BEW). The item specializes the
mixed-intersection statement to the whole scheme and repeated copies of one
ample module. This is the source's Hilbert degree, with the normalization used
by the item.

Object/hypothesis/conclusion inventory and matching:

- Field `k`: section variables `{K : Type u} [Field K]`. Verdict: exact; no
  algebraic closure, perfection or characteristic hypothesis.
- Scheme over `k`: `{X : Scheme.{u}}` and `(f : X ⟶ Spec (.of K))`. Verdict:
  exact; `f` supplies the structure morphism. No separate `Over` instance is
  assumed: `hilbertFunction` installs the one determined by `f` internally.
- Properness: `[IsProper f]`. Verdict: exact. No extra Noetherian, separated,
  connected, reduced or integral instance occurs in this theorem.
- Nonemptiness: `[Nonempty X]`. Verdict: exact. This excludes precisely the
  empty scheme excluded by the node.
- Dimension `g`: the node uses `g` as the dimension of `X`, not an independently
  chosen parameter. `Scheme.Hom.degree` uses
  `((topologicalKrullDim X).unbotD 0).toNat` as the iteration count. Verdict:
  exact in this proper nonempty case. Properness over a field entails finite
  type; schemes of finite type over a field have finite dimension. Thus neither
  the empty nor infinite-dimensional fallback in the definition is invoked.
  No dimension hypothesis is lost by calculating `g` from `X`.
- Invertible module `L`: `(M : X.Modules)` together with the first conjunct
  `M.IsInvertible` of `(hample : IsAmple f M)`. Verdict: exact; `M : X.Modules`
  alone does NOT impose invertibility. This clarifies the worker's shorthand.
- Ampleness in `def-sc-ample`: its recorded `AlgebraicGeometry.IsAmple` is
  `M.IsInvertible ∧ ∃ m : ℕ, 0 < m ∧ IsVeryAmple f (M.tensorPow m)`.
  `IsVeryAmple` requires a closed immersion over the base and an isomorphism
  with the pullback of the projective twisting module. On proper schemes this
  agrees with the complete-linear-system formulation in the dependency node:
  any such embedding implies the complete system is an embedding too. The
  dependency's lead note records this equivalence. Verdict: same notion; no
  stronger projectivity assumption in this proper case.
- Hilbert degree in `def-sc-hilbert-degree`: its recorded declaration is
  `AlgebraicGeometry.Scheme.Hom.degree`, not the curve-specific
  `Scheme.Modules.degree`. I read its body: the dimension-th forward difference
  at zero of `f.hilbertFunction M`; the latter is exactly
  `m ↦ Scheme.Modules.eulerChar K (M.tensorPow m)`. I also read
  `degree_eq_factorial_mul_coeff` and `exists_polynomial_hilbertFunction`.
  This is `g!` times the coefficient of degree `g`; in the ample nonempty
  proper setting positivity makes it the leading coefficient. This is the
  normalization justified in step 3 of the node's proof, not a different degree.
  Verdict: exact on the stated domain.
- Sole conclusion: `0 < f.degree M`, strict positivity in `ℤ`. Verdict:
  exact, with no omitted clause or reordered dependent quantifier.

Edge cases: dimension zero is allowed, and the zeroth difference is the Euler
characteristic of the structure sheaf (not the curve degree, which would be
zero). Disconnected and nonreduced proper schemes remain allowed. The zero
module on a nonempty scheme cannot satisfy invertibility, as in the node.
There is no external index set or integer `n` in the statement; the internally
chosen ample tensor exponent is strictly positive, exactly as required.
All characteristics are allowed. The universe `u` is arbitrary; the shared
universe for the field and scheme is the ambient convention of the dependency
API, and any field and scheme fit a common enlarged universe. All section
variables and universes are bound; no auto-implicit parameter is needed.

Independent searches (different queries from the first worker): LeanFinder,
“top self intersection of an ample invertible sheaf is strictly positive”,
returned eight affine-section lemmas, no match; Loogle, `"degree", "Nonempty"`,
returned only `SimpleGraph.degree_pos_iff_nonempty`; LeanSearch, “The degree of a
nonempty projective scheme for an ample invertible sheaf is strictly positive”,
was unavailable with Internal Server Error (not a negative search result).
`rg` for `degree_pos`, Hilbert/positivity and ample/positivity in Mathlib algebraic
geometry, all `WeilConjectures`, and project `lean/Sheaf` found the exact source
theorem. Other source hits were curve-only statements and are not substitutes.
The project absolute-ampleness definition in `Sheaf.AlgebraicGeometry.Ample`
is for another DAG node and another domain; it is not the recorded
`def-sc-ample` declaration. I checked the upstream name index as well.

No Lean or node mismatch was found. The signature in `lean.statement` is
verbatim the existing theorem's signature through `:=`. No new node or dependency
module is necessary. The earlier report's reference to arbitrary infinite
Krull dimension is incorrect for this proper finite-type setting and is
superseded by the dimension explanation above. The description of invertibility
is also clarified above. The existing theorem has a source docstring and a
`sorry` proof; definitions `IsAmple`, `hilbertFunction`, and `degree` have actual
data and no hollow `sorry`. Existing-source reuse requires no new module,
new docstrings, or compilation of the read-only source. No theorem was proved
and no source file was changed. The dry run checks this existing-only delivery.
