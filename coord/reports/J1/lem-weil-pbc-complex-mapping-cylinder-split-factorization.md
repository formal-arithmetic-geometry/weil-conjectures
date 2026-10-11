## Worker report

The module `Sheaf.Algebra.Homology.MappingCylinderSplitFactorization` states
`CochainComplex.exists_mapping_cylinder_split_factorization`, with its only proof `sorry`.
No new definitions or nodes are needed, and no statement correction is needed.

Hypotheses and clauses, individually:

- The additive category A is `{C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C]`, exactly the Mathlib match of `def-weil-additive-category`.
  Both object and morphism universes are explicit and unrestricted.
- Integer-indexed cochain complexes and their square-zero differentials are the existing
  `CochainComplex C ℤ` definition. `{K L : CochainComplex C ℤ}` names the two complexes.
- The morphism commuting with the differentials is `(α : K ⟶ L)` using Mathlib's complex
  morphisms, not a separately defined family of maps.
- The existence of the intermediate complex and three complex morphisms is
  `∃ (T : CochainComplex C ℤ) (i : K ⟶ T) (p : T ⟶ L) (s : L ⟶ T)`.
- Clause (0), pi composed with alpha-tilde equals alpha, is `i ≫ p = α`.
- Clause (1) is `∀ n : ℤ, ∃ (M : C) (e : T.X n ≅ K.X n ⊞ M),
  i.f n ≫ e.hom = biprod.inl`. This specifies an actual complementary object, an
  isomorphism, and the identity identifying the map with the summand inclusion.
  No compatibility of the isomorphisms or complements with differentials is imposed.
  Merely using `IsSplitMono` would be insufficient in an additive category without
  idempotent completeness, so that weaker replacement was avoided.
- Clause (2), pi composed with its section equals the identity, is `s ≫ p = 𝟙 L`.
- The homotopy part of clause (2) is `Nonempty (Homotopy (p ≫ s) (𝟙 T))`.
  Mathlib's `Homotopy` has components in degree minus one and the equation
  `f = dh + hd + g`; it is exactly the node's `f - g = dh + hd` in preadditive Hom groups.
- The lower-bound clause universally quantifies `n₀ : ℤ`; its premise is
  `∀ n : ℤ, n < n₀ → IsZero (K.X n) ∧ IsZero (L.X n)`, and its conclusion is
  `∀ n : ℤ, n < n₀ - 1 → IsZero (T.X n)`.
- The upper-bound clause universally quantifies `n₁ : ℤ`; its premise is
  `∀ n : ℤ, n₁ < n → IsZero (K.X n) ∧ IsZero (L.X n)`, and its conclusion is
  `∀ n : ℤ, n₁ < n → IsZero (T.X n)`.
- The same existentially chosen T satisfies both implications, hence also the
  simultaneously bounded case. `IsZero` expresses the categorical vanishing denoted
  by `K^n = 0` in the node, without imposing equality with a chosen zero object.

Dependency declarations read and used:

- `def-weil-additive-category` is a Mathlib leaf, with no Lean record needed. Its match
  is `CategoryTheory.Limits.HasFiniteBiproducts` in
  `Mathlib.CategoryTheory.Limits.Shapes.Biproducts`, together with
  `CategoryTheory.Preadditive` in `Mathlib.CategoryTheory.Preadditive.Basic`.
  Their full signatures and docstrings were read.
- Imported `Mathlib.Algebra.Homology.Homotopy` supplies complex morphisms and `Homotopy`;
  its full structure and the cochain-complex abbreviation were read.
- Imported `Mathlib.CategoryTheory.Preadditive.Biproducts` supplies the biproduct API.
  `CategoryTheory.Limits.hasBinaryBiproducts_of_finite_biproducts` is marked as a local
  instance: Mathlib deliberately does not register this implication globally.
  This uses a proved Mathlib implication rather than adding a hypothesis on C.
  The biproduct and `biprod.inl` signatures and docstrings were read.

Edge cases checked: arbitrary additive categories, including ones not idempotent complete;
zero K, zero L, the zero morphism, zero categories; negative, zero, and positive degree
bounds; unbounded input complexes; one-sided bounds; simultaneous upper and lower bounds;
empty support when the bounds overlap. No abelian, injective, boundedness, or nonzero
hypothesis was introduced. The degree-n complement need not be a complex. The explicit
source construction `L^n ⊕ K^n ⊕ K^(n+1)` validates both precise bounds.

Source: the local `literature/stacks-project/derived.tex` is absent on this machine, so
I opened the authoritative pages https://stacks.math.columbia.edu/tag/013N,
https://stacks.math.columbia.edu/tag/014G, and https://stacks.math.columbia.edu/tag/013O.
They confirm the factorization, actual direct-summand inclusion, section, homotopy,
and boundedness, and give the matrix construction reproduced step by step in the docstring.
There is no mathematical dispute or node fault.

Searches for an existing statement:

- `msearch.py ... leanfinder "Every morphism of cochain complexes in an additive category
  factors as a degreewise split injection followed by a homotopy equivalence with section
  preserving boundedness"`: eight hits, notably `CochainComplex.cm5b`, its homotopy
  equivalence, mapping-cone decomposition lemmas, and homotopy-cofiber API. No exact
  match; CM5b additionally assumes abelian, enough injectives, and boundedness and
  supplies a different type of factorization.
- `msearch.py ... leansearch "factor a cochain complex morphism into a termwise direct
  summand inclusion and a deformation retraction"`: service unavailable, Internal
  Server Error. This is recorded as unavailable, not a negative search result.
- `msearch.py ... loogle '"mappingCylinder"'`: zero hits.
- An initial Loogle query `Homotopy, biprod.inl` reported unknown identifier
  `biprod.inl`, hence was inconclusive; direct source inspection replaced it.
- `msearch.py ... grep 'mappingCylinder|mapping cylinder|termwise.split|degreewise.split'
  Algebra/Homology`: seven hits in degreewise split exact-sequence and homotopy-category
  files, none the factorization theorem.
- `rg -n 'mappingCylinder|mapping.cylinder|split_factorization'` against
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the project's `lean/Sheaf`:
  no matching declaration. Searching the item id in the source repository also found none.
- Declaration-name and concept search in `dag/lean_names_upstream.json`, Mathlib, source,
  and `lean/Sheaf` found no existing `exists_mapping_cylinder_split_factorization`.

Verification: the final single-file server compilation exited 0 with no warnings (1.2 s).
The delivery dry run printed OK: compilation and preflight passed except for the independent
second-reading section, which the second reader will write. Nothing was pushed.
The first compile revealed that finite biproducts do not automatically activate
Mathlib's binary-biproduct implication; the local instance above repairs this without
changing the statement's mathematical hypotheses.


## Second reading by J1

I independently opened the delivered node, the theorem module, the sole statement
dependency node `def-weil-additive-category`, and its Mathlib declarations. I read
the Stacks `derived.tex` source directly from the official stacks/stacks-project
repository (the local literature checkout is absent), at
`definition-termwise-split-map`, `lemma-make-injective`, and
`remark-compute-modules`, and checked the rendered tags
[014G](https://stacks.math.columbia.edu/tag/014G),
[013N](https://stacks.math.columbia.edu/tag/013N), and
[013O](https://stacks.math.columbia.edu/tag/013O).
The source assumes only an additive category, not an abelian category or existence
of injectives. Its displayed construction gives exactly the sharper bounds in
this already-reviewed DAG node. There is no statement_change, new definition
node, or dependency module in this delivery.

The node's objects, hypotheses, and conclusion clauses matched individually:

- Category A: `{C : Type u} [Category.{v} C]` introduces the same arbitrary category,
 with independent object and morphism universes. Verdict: exact.
- Additivity: `[Preadditive C] [HasFiniteBiproducts C]` uses the dependency's recorded
 Mathlib match. I read `Preadditive.homGroup`, `add_comp`, and `comp_add`, and
 `HasFiniteBiproducts.out`; finite biproducts include the empty biproduct (zero
 object). The local instance `hasBinaryBiproducts_of_finite_biproducts` derives
 binary biproducts from this hypothesis rather than adding another assumption.
 Verdict: exact, including categories without split idempotents.
- Complexes K and L: `{K L : CochainComplex C ℤ}`. I read `HomologicalComplex`
 and the `CochainComplex` abbreviation: the shape is `ComplexShape.up ℤ`, with
 differential from n to n+1 and square-zero composition. Extra off-shape
 components are required to be zero, so add no mathematical data. Verdict: exact.
- Cochain map alpha: `(α : K ⟶ L)` is Mathlib's differential-commuting complex
 morphism. No boundedness condition is assumed. Verdict: exact.
- Intermediate complex and maps: `∃ (T : CochainComplex C ℤ) (i : K ⟶ T)
 (p : T ⟶ L) (s : L ⟶ T)` matches tilde-L, tilde-alpha, pi, and s in that order.
 All witnesses precede the clauses and bounds. Verdict: exact.
- Clause (0): `i ≫ p = α` is pi composed with tilde-alpha, since Lean composition
 is written in traversal order. Verdict: exact.
- Clause (1): `∀ n : ℤ, ∃ (M : C) (e : T.X n ≅ K.X n ⊞ M),
 i.f n ≫ e.hom = biprod.inl`. I read the binary biproduct and `biprod.inl`
 declarations. This gives an actual complement and identifies i with its summand
 inclusion. M and e depend only on the individual degree; no compatibility with
 differentials is imposed. It does not replace a complement with a merely split
 monomorphism. Verdict: exact.
- First part of clause (2): `s ≫ p = 𝟙 L` is pi composed with s equals identity
 as a complex morphism, not merely in the homotopy category. Verdict: exact.
- Second part of clause (2): `Nonempty (Homotopy (p ≫ s) (𝟙 T))` says s composed
 with pi is homotopic to identity. I read `Homotopy.hom`, `zero`, `comm`,
 `dNext`, and `prevD`: for cochains its nonzero homotopy components are precisely
 n to n-1, and `comm` says f = dh + hd + g. This is equivalent to the node's
 subtraction equation. The source's h has id-s*pi = dh+hd; negating h gives the
 direction used in Lean, as the docstring says. Verdict: exact.
- Lower bound: `∀ n₀ : ℤ, (∀ n : ℤ, n < n₀ → IsZero (K.X n) ∧
 IsZero (L.X n)) → ∀ n : ℤ, n < n₀ - 1 → IsZero (T.X n)`.
 `IsZero` is the categorical meaning of vanishing, independent of a chosen
 zero object. The inequalities and shift are exactly those in the node.
 Verdict: exact.
- Upper bound: `∀ n₁ : ℤ, (∀ n : ℤ, n₁ < n → IsZero (K.X n) ∧
 IsZero (L.X n)) → ∀ n : ℤ, n₁ < n → IsZero (T.X n)`.
 The upper bound is unchanged. Verdict: exact.
- Simultaneous bounds: the two universal implications belong to the same
 existential T, hence both hold together for bounded inputs. Bounds are not
 witnesses on which a fresh T could depend. Verdict: exact.

Edge cases: zero K, zero L, alpha=0, and the zero category are admitted. Nonzero,
abelian, idempotent-completeness, injectivity, and boundedness hypotheses are all
absent. Negative, zero, and positive n/n₀/n₁ are covered by ℤ; at n₀=0 the lower
threshold is -1, as required. Empty support and overlapping upper/lower bounds
work using the source's L^n + K^n + K^(n+1). An empty category cannot satisfy the
additive-category hypothesis because it has no zero object; no case of the node
is thereby lost. There is no variable index family requiring a nonempty index
hypothesis, and schemes and characteristic are not involved. Both universes
are explicit; no variable is left unbound.

Independent searches used different wording from the first worker:

- LeanFinder through msearch: "A cochain map admits a factorization through a direct
 summand inclusion and a strong deformation retract with bounded support".
 Eight hits: mappingCone.decomp_to/decomp_from, cm5b and cm5b.fac, and derived
 category fraction/single-object results. No exact declaration. I opened
 `Factorizations/CM5b.lean`: its section assumes Abelian and EnoughInjectives;
 its final theorem assumes lower bounds and gives a mono with degreewise
 injective-kernel epi quasi-isomorphism. It is not the node's theorem.
- LeanSearch through msearch: "cochain map factors through a direct summand
 embedding and a retraction up to homotopy". Service unavailable (Internal
 Server Error); this is inconclusive, not evidence of absence.
- Loogle through msearch: `"Homotopy", "factor"`: twelve hits, all homology/map
 functor factorization or localization declarations, none this theorem. An
 earlier query `"factorization" "Homotopy"` was syntactically invalid and
 supplies no absence evidence; the corrected query above replaced it.
- `rg -n 'deformation.retract|split.*factor|factor.*split|mapping.cylinder|
 mappingCylinder'` on Mathlib/Algebra/Homology, all source WeilConjectures, and
 repository lean/Sheaf: only unrelated comments outside homological algebra;
 no declaration of the required factorization. Existing mapping-cone and
 cylinder constructions are useful proof tools, not duplicates of this
 existence statement with its complete clauses.

H5/H6/H8/H9: no definitions (hollow or otherwise), only one named theorem with
proof `sorry`; both docstrings cite the source and blueprint id. The statement
docstring follows all six node proof steps: three-summand complex and its
matrix, square-zero calculation, maps and identities, explicit complementary
summand isomorphism, signed homotopy, both bounds. Imports supply the complex/
homotopy and additive biproduct APIs used by the statement. Namespace and
topic path follow Mathlib and all lines meet the 100-character limit.

Mismatches found: none. Changes: appended this independent second reading;
the correct Lean module and node record were left unchanged. I also checked
programmatically that `lean.statement` equals the signature verbatim from
`theorem` to before `:=` (with its trailing whitespace removed).

Verification: scompile with the sandbox's absolute module path exited 0,
compiled in 1.1 s, and produced no errors or warnings. An initial invocation
using a relative path from the read-only repository could not locate the
sandbox file; rerunning with its absolute path resolved that invocation error.
