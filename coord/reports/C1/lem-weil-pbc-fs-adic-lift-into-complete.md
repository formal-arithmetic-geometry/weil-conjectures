## Worker report

The module `Sheaf.RingTheory.FormallySmoothAdicLiftIntoComplete` states
`Algebra.FormallySmoothAdic.exists_lift_into_complete`, with `sorry` as its only proof.
No definitions or auxiliary nodes were necessary. No statement correction or disputed
statement. All six proof steps are in the declaration docstring.

Clause-by-clause correspondence:

- The commutative rings R, S and A are three explicit type binders in independent
  universes `u v w`, with `CommRing` instances. The ring map φ is the structure map of
  `[Algebra R S]`; `[Algebra R A]` is the specified R-algebra structure on A. No
  finiteness, Noetherian, local, nonzero, or injectivity hypothesis is imposed.
- The ideal n is `(n : Ideal S)` and formal smoothness for its adic topology is
  `(hS : FormallySmoothAdic R S n)` using the dependency's exact definition.
- The ideals I and J are `(I J : Ideal A)`. Completeness is `[IsAdicComplete I A]`.
- A positive exponent t and the bound J^t ⊆ I are `(t : ℕ) (ht : 1 ≤ t)` and
  `(hJI : J ^ t ≤ I)`.
- Closedness is `(hJ : J = ⨅ (m : ℕ) (_ : 1 ≤ m), J ⊔ I ^ m)`:
  sup is ideal sum, and the doubly indexed infimum ranges over exactly the positive
  natural exponents. Indices m = 0 contribute an empty inner infimum (top), so they
  do not change the intersection.
- The quotient A/J has Mathlib's induced `Ideal.Quotient.algebra` R-algebra structure.
  The quotient algebra map q is `Ideal.Quotient.mkₐ R J`, whose underlying ring map
  is `Ideal.Quotient.mk J`.
- The prescribed algebra homomorphism is `(g : S →ₐ[R] A ⧸ J)`.
- A positive r is `(r : ℕ) (hr : 1 ≤ r)`. The condition g(n^r) ⊆ q(I) is
  `(hg : ∀ x ∈ n ^ r, g x ∈ I.map (Ideal.Quotient.mk J))`.
  For a surjective quotient map, `Ideal.map` is precisely the image ideal q(I).
- The existence conclusion is `∃ f : S →ₐ[R] A`.
- Agreement q ∘ f = g is `(Ideal.Quotient.mkₐ R J).comp f = g`.
- The final bound is `∀ x ∈ n ^ (r * t), f x ∈ I`, conjoined with agreement for
  the same f. It is a prescribed bound for the given witnesses r,t, not merely
  an existential continuity assertion.

Dependency declarations read and used:

- `def-weil-pbc-formally-smooth-adic`: `Sheaf.RingTheory.FormallySmoothAdic`,
  `Algebra.FormallySmoothAdic`. Read the complete docstring and signature; the
  property quantifies over square-zero quotients and maps killing a positive power.
- `def-weil-pbc-adically-complete-ring`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `IsAdicComplete` (extends Hausdorffness and precompleteness). Read its signature,
  module documentation, and the record's bijective-canonical-map characterization.
- `def-weil-pbc-algebra-hom-quotient` is a Mathlib leaf: `AlgHom` from
  `Mathlib.Algebra.Algebra.Hom`, `Ideal.Quotient.algebra` and `Ideal.Quotient.mkₐ`
  from `Mathlib.RingTheory.Ideal.Quotient.Operations`, and the `IdemCommSemiring`
  structure on ideals in `Mathlib.RingTheory.Ideal.Operations`. These are imported
  transitively by the two necessary imports; their declarations and docstrings
  were read in the source checkout.

Edge cases checked before writing: the zero ring is allowed, including its unique
quotient map; I = ⊥ reduces completeness to the discrete case and J^t = 0 to
nilpotence; I = ⊤ and completeness force A to be the zero ring. J = ⊥ allows g
itself as a lift; J = ⊤ forces I = ⊤ by the power condition. n = ⊥ allows all maps;
n = ⊤ forces the appropriate quotient to be zero through the image hypothesis.
The smallest permitted exponents r = t = 1 are included; r = 0 or t = 0 are
excluded exactly as the node specifies. There is no finite-generation assumption
on any ideal, and no field or characteristic restriction. R, S and A have
independent universes; no target ring size is bounded by a new hypothesis.

Searches (2026-10-11):

- `msearch.py ... leansearch "formally smooth adic topology lift to complete ring
  modulo closed ideal"`: service unavailable, Internal Server Error; no verdict.
- `msearch.py ... leanfinder "formally smooth for an adic topology lift algebra
  homomorphism to complete ring modulo closed ideal"`: eight hits, including
  `Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete`,
  `exists_adicCompletionEvalOneₐ_comp_eq`, `exists_lift`, `lift`, and adic completion
  lift helpers. None states adic formal smoothness with an arbitrary closed J.
- `msearch.py ... loogle "Algebra.FormallySmooth, IsAdicComplete"`: one hit,
  `Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete`. Read its full
  signature and docstring: discrete formal smoothness, with J equal to I; not this node.
- `msearch.py ... grep "FormallySmoothAdic|exists_mkₐ_comp_eq_of_isAdicComplete"
  RingTheory`: only the latter theorem in `Smooth/AdicCompletion.lean:94`.
- `rg -n 'FormallySmoothAdic|adic.*lift|lift.*complete'` in both project source
  trees: only the existing definition, uses in other statements, and unrelated
  pro-étale lifting declarations. No equivalent statement.
- `grep -rn 'lem-weil-pbc-fs-adic-lift-into-complete'` in the source checkout:
  no declaration. `rg` on `dag/lean_names_upstream.json` for the node id and the
  new theorem basename found no collision.

The local Stacks source was absent. Read the primary source instead at
https://stacks.math.columbia.edu/tag/07NJ (Lemma 15.38.5). Its full proof uses
exactly the six grid/limit/bound steps recorded in the node and the module.
The source gives the precise final bound n^(rt), and requires J closed and J^t ⊆ I.

## Second reading by C1

I independently read the node statement, its Stacks source place (More on Algebra, Tag 07NJ),
and `Sheaf.RingTheory.FormallySmoothAdicLiftIntoComplete.lean` clause by clause.

- The node's map of commutative rings `R → S` is rendered by the explicit universes,
  `[CommRing R] [CommRing S]`, and `[Algebra R S]`; the target commutative `R`-algebra
  `A` is rendered by `[CommRing A] [Algebra R A]`. Verdict: exact, with no extra
  finiteness, locality, characteristic, or nonzero assumptions.
- The ideal `𝔫 ⊆ S` and adic formal smoothness are exactly `(n : Ideal S)` and
  `(hS : FormallySmoothAdic R S n)`, using the dependency declaration.
- The ideals `I,J ⊆ A` and completeness are `(I J : Ideal A) [IsAdicComplete I A]`.
  Verdict: exact Mathlib `IsAdicComplete` notion.
- The condition `J^t ⊆ I` for some `t ≥ 1` is exactly `(t : ℕ) (ht : 1 ≤ t)` and
  `(hJI : J ^ t ≤ I)`.
- Closedness `J = ⋂_{m≥1}(J+I^m)` is exactly
  `hJ : J = ⨅ (m : ℕ) (_ : 1 ≤ m), J ⊔ I ^ m`; the `m=0` fiber is an empty
  index infimum (top), so it does not alter the positive intersection.
- The quotient `q : A → A/J` and its induced `R`-algebra structure are rendered by
  `A ⧸ J` and `Ideal.Quotient.mkₐ R J`; `g` is exactly an `R`-algebra map
  `S →ₐ[R] A ⧸ J`.
- The continuity condition `g(𝔫^r) ⊆ q(I)` for `r≥1` is rendered by
  `(r : ℕ) (hr : 1 ≤ r)` and
  `hg : ∀ x ∈ n ^ r, g x ∈ I.map (Ideal.Quotient.mk J)`. For the quotient map,
  this mapped ideal is precisely the image `q(I)`. Verdict: exact.
- The conclusion `∃ f : S →ₐ[R] A` is exact. Agreement is exactly
  `(Ideal.Quotient.mkₐ R J).comp f = g`, and the final clause is exactly
  `∀ x ∈ n ^ (r * t), f x ∈ I`, with the same prescribed `r,t`; no existential
  weakening or stronger bound appears. Verdict: exact.

Edge cases checked: zero rings and zero ideals remain admitted; `I = ⊥`, `J = ⊥`,
`I = ⊤`, and `J = ⊤` are all covered by the stated hypotheses. The least allowed
values `r=t=1` are included, while `r=0` and `t=0` are excluded as in the node.
The empty positive-index intersection convention is handled by the dependent infimum.
No characteristic, Noetherian, finite-generation, or universe restriction is added;
the three ring universes are independent, as allowed by the source.

Searches were rechecked in Mathlib, `WeilConjectures/`, and `lean/Sheaf/` using
`rg` for `FormallySmoothAdic`, `lift_into_complete`, and the theorem basename, and
with the recorded LeanSearch/LeanFinder/Loogle queries. The only candidate is
`Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete`, which is the discrete
formal-smoothness special case with quotient by the completeness ideal and therefore
is not this statement. No existing declaration matches.

No mismatch was found and no repair was needed. The module compiled cleanly with
`scompile.py`; its only proof is the required `sorry`, and all declaration/docstring
text carries `(blueprint: lem-weil-pbc-fs-adic-lift-into-complete)`.
