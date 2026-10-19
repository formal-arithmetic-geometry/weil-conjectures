# Stage-2 statement: lem-cbc-disk-lifting-surjective

## Worker report

The delivery supplies `Sheaf.AlgebraicTopology.DiskLiftingSurjective`.  It defines the
real free two-term disk `CategoryTheory.ChainComplex.disk Λ n`: its terms are a rank-one
`Λ`-module in degrees `n` and `n-1`, the zero module elsewhere, and its only nonzero
successive differential is the identity.  The auxiliary `diskX`, `diskD`, and
`diskD_comp` declarations give the object family, differential, and square-zero proof
with no chosen or postponed data.  The theorem
`CategoryTheory.ChainComplex.disk_lifting_surjective` has the one postponed proof (`sorry`).
The module also imports the dependency repair
`Sheaf.AlgebraicTopology.DoldKanNormalizationEquivalence`.

The theorem has explicit universes and hypotheses `(Λ : Type u) [CommRing Λ]`,
`K C E : ChainComplex (ModuleCat.{u} Λ) ℕ`, `g : C ⟶ E`, and `n : ℕ` with `1 ≤ n`.
Its left clause is `Function.Surjective (g.f n)`.  Its right clause quantifies chain maps
`u : K ⟶ C` and `v : K ⊞ disk Λ n ⟶ E`, assumes the square equation
`u ≫ g = biprod.inl ≫ v`, and supplies `h : K ⊞ disk Λ n ⟶ C` with
`biprod.inl ≫ h = u` and `h ≫ g = v`.  Thus `biprod.inl` is the canonical `j` in the
node, and composition is the categorical chain-map composition.

The theorem docstring records all five source proof steps: choose a preimage of the top
 disk generator; define the lift on the top and lower generators; assemble it with `u`
through the biproduct and check both summands; test the converse with the zero map on `K`
and arbitrary `y` in degree `n`; and evaluate a lift at the top generator.  It cites the
source place and `(blueprint: lem-cbc-disk-lifting-surjective)`.

Dependency declarations used:

- `Sheaf.AlgebraicTopology.DoldKanNormalizationEquivalence`,
  `CategoryTheory.Abelian.DoldKan.doldKanNormalizationEquivalence`, is the repaired
  declaration for `lem-cbc-dold-kan-normalization-equivalence`; its value is Mathlib's
  `CategoryTheory.Abelian.DoldKan.equivalence`, so its inverse and unit/counit isomorphisms
  are present exactly as in the dependency statement.
- Mathlib `ChainComplex.of`, `ModuleCat.of`, `eqToHom`, `biprod.inl`, and
  `Mathlib.Algebra.Homology.HomologicalComplexBiprod` provide the existing chain-complex,
  module, equality-transport, and biproduct interfaces.  No private copy of these notions
  is used.

Edge cases checked before writing: `n = 1` makes the lower disk term degree zero and the
next differential is zero; `K = 0`, `C = 0`, and `E = 0` reduce the lifting square to the
expected disk and zero cases; the zero ring is allowed by `[CommRing Λ]`; and a non-cycle
`y` is handled by the lower generator mapping to its boundary.  The `Fin 0 → Λ` module is
the zero module, so the disk is supported only in the two stated degrees.

Searches made for an existing notion or statement:

- `msearch.py N6 lem-cbc-disk-lifting-surjective leanfinder "chain map right lifting property against a two-term disk complex equivalent to surjective top degree"`: hits were model-category/Joyal-trick and homotopy-class results, with no matching theorem.
- `msearch.py N6 lem-cbc-disk-lifting-surjective loogle "ChainComplex, Function.Surjective"`: no hits; the expected disk identifier is not in Loogle.
- `msearch.py N6 lem-cbc-disk-lifting-surjective grep "disk.*surjective|surjective.*disk" AlgebraicTopology`: no matching Mathlib declaration.
- `rg -n "disk|right lifting|surjective.*degree" /home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the project `lean/Sheaf`: found only unrelated model-category, horn, or two-term constructions; no exact disk-lifting statement.
- `rg -rl 'lem-cbc-disk-lifting-surjective' dag/nodes` found only this node and
  `lem-cbc-simplicial-module-model` as its citer; no duplicate definition node exists.

## Dependency modules

`lem-cbc-dold-kan-normalization-equivalence` had neither a Lean record nor a usable
`mathlib_match`.  The added module states its full notion as the canonical equivalence
`CategoryTheory.Abelian.DoldKan.doldKanNormalizationEquivalence`, directly assigned to
Mathlib's Dold--Kan equivalence.  The declaration has a source and blueprint docstring;
its data is real and contains the inverse and natural isomorphisms.

## Statement corrected

The old statement was the stage-1 informal text beginning “Let `$\Lambda$` be a commutative
ring and let `$K,C,E$` be nonnegative chain complexes...” and used untyped `K\oplus D^n`,
`gu=vj`, and `g_n`.  It could not serve as the exact Lean statement because it did not
specify the coefficient category, the canonical biproduct inclusion, or the categorical
composition orientation.  Following the supporting disk calculation in
`thm-cbc-finite-level-proetale.proof.md`, the corrected node fixes
`ChainComplex (ModuleCat Λ) ℕ`, names `disk Λ n`, `biprod.inl`, and the concrete map
`g.f n`; it adds no mathematical assumption beyond the displayed `1 ≤ n`.

The only citer is `lem-cbc-simplicial-module-model` (`holds: true`): its normalized
simplicial-module complexes and horn splitting instantiate exactly these module-valued
complexes and the same `K ⊞ D^n` summand inclusion.  Its node is not edited.

## Second reading by N6

An independent second reading opened both node files and both modules.  The disk object
family is genuinely zero outside degrees `n` and `n-1`; at `n=1` the degree-zero target
has no further differential.  The differential is transported by `eqToHom` only in the
case `k+1=n`, and `diskD_comp` checks its square is zero.  The theorem's left side is
exactly surjectivity of the degree-`n` component, while the right side quantifies every
commutative square against the canonical `biprod.inl` and requires both lift equations.
The dependency module exposes the existing Dold--Kan equivalence with no weakened
existence-only wrapper.  No mismatch was found.  The parent citer remains valid after the
statement correction.  The only postponed declaration is the theorem proof, as required
for stage 2.
