## Worker report

The module `Sheaf.Paper.TorLongExactFirstVariable` states the low-degree long exact Tor sequence in the first variable and naturality in the second variable. It uses Mathlib's `CategoryTheory.Tor'` on `ModuleCat R`, with the connecting maps packaged as a family of `ModuleCat` morphisms (equivalently R-linear maps).

The binders `R`, `Q`, `Q'`, `Q''`, and `N` render the commutative ring and module objects. The hypotheses `hu`, `hv`, and `hExact` render injectivity, surjectivity, and exactness of `u,v`. For every `N`, the first conjunction clause gives exactness of `Tor'_1(v,N)`, the connecting map, `u ⊗ 1`, and `v ⊗ 1`, plus surjectivity at the final term. The final clause states naturality for every linear map `g : N →ₗ[R] N'`; its tensor map is `MonoidalCategory.tensorHom (𝟙 (ModuleCat.of R Q)) (ModuleCat.ofHom g)`.

Dependency used: `def-weil-pbc-tor-modules` is the Mathlib declaration `CategoryTheory.Tor'` in `Mathlib/CategoryTheory/Monoidal/Tor.lean`.

Edge cases checked: the statement allows zero modules and `N = 0`; `N` and `N'` use the same universe as `R`; no finiteness, nonzero, or characteristic assumptions are introduced.

Searches made: LeanFinder/LeanSearch/Loogle and grep searches recorded on the node for long exact Tor sequences. They found only Mathlib's `Tor'`, tensor right-exactness, and homology-sequence infrastructure, with no existing long exact Tor declaration.

## Earlier second reading (a previous round; superseded)

Pending second reader.

## Second reading by E1

Read the item node, its only statement dependency `def-weil-pbc-tor-modules`, and
Mathlib's actual declarations in `CategoryTheory/Monoidal/Tor.lean`,
`Algebra/Category/ModuleCat/Monoidal/Basic.lean`, `ModuleCat/Projective.lean`, and
`ModuleCat/Basic.lean`. Read the Stacks TeX source locally at
`/home/ubuntu/c1-stacks-review/algebra.tex`: the conventions (rings are commutative
with one, including the zero ring), Section 00LY, Lemmas 00M0 and 00M3. Also read
More on Algebra's use in the proof of 0912 and Homology 0111 in the corresponding
local `.tex` files. There are no standing Noetherian, finite, field, or
characteristic hypotheses for this Tor assertion. No node statement correction,
new definition node, or dependency module is present or needed.

Item-by-item statement checklist (all verdicts: matches):

- Object: a commutative ring `R`. Lean: `{R : Type u} [CommRing R]`.
- Objects: the three `R`-modules `Q,Q',Q''`. Lean: the three type binders,
  their `AddCommGroup` instances, and their `Module R` instances.
- Objects: the maps `u : Q → Q'`, `v : Q' → Q''`. Lean: exactly these two
  `R`-linear-map binders.
- Hypothesis: `0 → Q → Q' → Q'' → 0` is short exact. Lean: `hu` is
  `Function.Injective u`, `hExact` is `Function.Exact u v`, and `hv` is
  `Function.Surjective v`. There are no other hypotheses.
- Object: an arbitrary second module `N`, and a second module `N'` for naturality.
  Lean: each `∀ (N : Type u) [AddCommGroup N] [Module R N]`, and the analogous
  `N N'` binders in the naturality clause. The family is chosen before its
  exactness and naturality assertions, so the same maps work for all `N`.
- Notion: `Tor₁` and both its functorial maps are those of the dependency.
  Lean: `Tor' (ModuleCat R) 1`. The opened definition is `Functor.flip` of the
  left derived functor of `tensoringRight`; thus it resolves the FIRST variable.
  Its outer `.map (ModuleCat.ofHom v)` evaluated by `.app N` is `Tor₁(v,N)`;
  its inner `.map (ModuleCat.ofHom g)` is `Tor₁(Q'',g)`. ModuleCat's Abelian,
  monoidal/preadditive, and enough-projectives instances are supplied by the
  imports, not assumed of the modules as extra conditions.
- Conclusion: an `R`-linear connecting map `δ_N : Tor₁(Q'',N) → Q ⊗ N`.
  Lean: `∃ δ : ∀ N ... , ... ⟶ ModuleCat.of R (Q ⊗[R] N)`.
  By the opened ModuleCat definition, these morphisms are precisely linear maps.
- Conclusion: exactness at `Tor₁(Q'',N)`. Lean: first `Function.Exact` clause,
  for `(((Tor' ...).map (ModuleCat.ofHom v)).app ...).hom` and `(δ N).hom`.
- Conclusion: exactness at `Q ⊗ N`. Lean: second `Function.Exact` clause,
  for `(δ N).hom` and `u.rTensor N`.
- Conclusion: exactness at `Q' ⊗ N`. Lean: third `Function.Exact` clause,
  for `u.rTensor N` and `v.rTensor N`. `rTensor` acts on the first factor,
  so these are exactly `u ⊗ 1` and `v ⊗ 1`.
- Conclusion: the last map onto `Q'' ⊗ N` is surjective. Lean:
  `Function.Surjective (v.rTensor N)`, encoding the final arrow to zero.
  No injectivity at the displayed first Tor term is asserted by either statement.
- Conclusion: naturality for every linear `g : N → N'`. Lean: the final
  universally quantified equation. Its left side is `(1_Q ⊗ g).comp (δ N)`;
  its right side is `(δ N').comp Tor₁(Q'',g)`, in exactly the node's order.
  ModuleCat's opened monoidal structure uses `TensorProduct.map` for tensorHom.
  The remaining squares commute by tensor bifunctoriality and naturality of
  the natural transformation `(Tor' ...).map v`; they need no extra choice
  or hypothesis. The node's "so that" clause is consequently accounted for.

Edge cases: the zero ring and all zero modules are admitted, including `N = 0`
and zero terms of the short exact sequence. No nontriviality, characteristic,
Noetherianity, flatness, projectivity, or finite generation is assumed. There is
no index set or scheme, so empty indexing and the empty scheme are inapplicable.
The node fixes degree one, so an `n = 0` binder is inapplicable; the degree-zero
terms are the actual tensor products, not an unidentified Tor-zero object.
`u` is declared as a universe (the identically spelled linear map is a term),
and every variable is explicitly bound. The shared ambient `Type u` is the
recorded dependency's ModuleCat monoidal encoding: the opened Mathlib instance
is for `R : Type u` and `ModuleCat.{u} R`, with tensor unit `R` itself. The
universe is arbitrary, not fixed to `Type 0`; this follows the same ambient
universe convention as the existing Tor statements and introduces no size or
finiteness typeclass hypothesis.

Independent searches, with new wording, made by this reader:

- LeanFinder through `msearch.py`: "connecting homomorphism for tensor product
  derived functors, exact sequence Tor modules". Eight hits, chiefly snake-map
  formulas, homology connecting maps, and Ext exact sequences. None is this
  Tor statement.
- Loogle through `msearch.py`: `CategoryTheory.Tor, Function.Exact`. Zero hits.
  An earlier malformed quoted query returned unrelated indicator lemmas and
  was discarded; it supplies no evidence for the verdict.
- LeanSearch through `msearch.py`: "boundary map Tor tensor product exactness
  for an exact sequence of modules". Service returned Internal Server Error;
  no mathematical verdict is inferred from that unavailable search.
- `msearch.py grep` on Mathlib's CategoryTheory with the word-boundary pattern
  `\bTor.?\b.*(exact|boundary|connecting)|leftDerived.*(exact|sequence)`:
  only the canonical right-exact degree-zero comparison in LeftDerived.lean.
  A broader case-insensitive search was noisy with substrings of "constructor"
  and was refined to this query.
- Direct `rg` on Mathlib, project `lean/Sheaf`, upstream `WeilConjectures`, and
  `dag/lean_names_upstream.json` for `tor_long_exact`, Tor connecting/boundary
  terminology, and Tor exactness: no duplicate. The project hits use the first
  variable sequence in other statements or proof docstrings, and do not state
  this exact sequence. Opened Mathlib's full Tor file: it contains the two Tor
  definitions and projective-input vanishing, not the requested exact sequence.

Mismatches repaired: missing copyright/license header and module docstring;
insufficient theorem proof docstring (replaced by all six node steps, citing the
free-resolution, Tor-map, tensor-right-exactness and snake-lemma nodes); one
104-character naturality line (wrapped). The existing mathematical signature
was right and retained. The node's `lean.statement` was resynchronized verbatim
with the file. No definitions or additional theorems were introduced; the only
proof is `by sorry` as required in stage 2. All lines are at most 100 characters.

Validation: `scompile.py E1 lem-weil-pbc-tor-long-exact-first-variable` on the
repaired module passed, exit 0, in 2.0 seconds, without warnings. The imports
supply respectively Tor, ModuleCat tensor structure, the abelian structure,
and enough projectives; all are used by the displayed statement.
