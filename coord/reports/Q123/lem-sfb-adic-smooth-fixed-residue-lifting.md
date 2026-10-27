## Worker report

The module `Sheaf.RingTheory.AdicSmoothFixedResidueLifting` states
`Algebra.formallySmoothAdic_iff_fixed_residue_artinian_lifting`, with `sorry` as its sole
proof. It records exactly the fixed-residue Artinian lifting equivalence; it introduces no
new definitions. The accepted stage-1 statement and split are unchanged. The prior ending
concerned an already accepted stage-1 split, whereas this dispatch is stage 2 and the current
node has no Lean record. This is precisely the stage handoff in brief-stage2 section 0.
No released repair note for this item was found.

Clause-by-clause correspondence:

- The commutative Noetherian local base is `(R : Type u)` with `[CommRing R]`,
  `[IsLocalRing R]`, and `[IsNoetherianRing R]`. Mathlib local rings are nontrivial and,
  in the commutative case, have exactly one maximal ideal, as the node specifies.
- The finite extension of the residue field is `(k : Type w)` with `[Field k]`,
  `[Algebra (IsLocalRing.ResidueField R) k]`, and
  `[Module.Finite (IsLocalRing.ResidueField R) k]`. `[Algebra R k]` and
  `[IsScalarTower R (IsLocalRing.ResidueField R) k]` express that its R-structure is
  the one through this extension; they do not impose an extra restriction on the field.
- The complete Noetherian local R-algebra is `(C : Type v)` with `[CommRing C]`,
  `[IsLocalRing C]`, `[IsNoetherianRing C]`, `[Algebra R C]`,
  `[IsLocalHom (algebraMap R C)]`, and
  `[IsAdicComplete (IsLocalRing.maximalIdeal C) C]`. Completeness is exactly for its
  maximal ideal, with no completeness hypothesis on R.
- The specified R-algebra residue identification is
  `(eC : IsLocalRing.ResidueField C ≃ₐ[R] k)`.
- The left side is the recorded definition
  `Algebra.FormallySmoothAdic R C (IsLocalRing.maximalIdeal C)`.
- Instead of introducing a redundant category definition, the right side expands its
  objects and maps. Both `(A' A : Type (max u v w))` have `[CommRing]`, `[IsLocalRing]`,
  `[IsArtinianRing]`, and `[Algebra R]`, with specified R-algebra residue equivalences
  `eA'` and `eA`. `IsArtinianRing` is the descending-chain condition on ideals.
  No extra Noetherian, completeness, finiteness, or small-extension hypotheses are imposed
  on the tests. Both test rings have a universe at least that of R, C, and k.
- The arbitrary morphism is `(p : A' →ₐ[R] A)` with `IsLocalHom p` and
  `Function.Surjective p`. For every `a'`, the equation
  `eA (IsLocalRing.residue A (p a')) = eA' (IsLocalRing.residue A' a')`
  expresses the identity on the specified residue field. Because the residue projections
  are surjective, this is precisely equality of the induced residue maps, not a restriction
  on just a subset of residue elements.
- The given element of h_C(A) is `(f : C →ₐ[R] A)` with `IsLocalHom f`, the analogous
  marking equation for every c, and
  `∃ n : ℕ, 1 ≤ n ∧ ∀ c ∈ IsLocalRing.maximalIdeal C ^ n, f c = 0`.
  This is the node's explicit definition of continuity into the discrete Artinian target.
- The existential lift is `f' : C →ₐ[R] A'` with all three same properties: locality,
  identity under the markings, and killing a positive power of the maximal ideal.
  The final equation `p.comp f' = f` is exactly p composed with the lift equals f.
- The outer connective is `↔`, asserting both directions for the fixed data and marking.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, the self-module
  Noetherian condition, equivalently all ideals finitely generated.
- `Mathlib.Algebra.Field.Defs`: `Field` (exposed through the public residue-field import).
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete` (Hausdorff and precomplete),
  from the adic-completion node's companion declaration; no alternate completion is defined.
- `WeilConjectures.RingTheory.FormallySmoothAdic`: `Algebra.FormallySmoothAdic`, whose
  full signature and definition quantify over arbitrary square-zero R-algebra tests and
  maps killing a positive ideal power. This uses the upstream declaration, not its retired
  Sheaf duplicate.
- The statement also uses Mathlib `IsLocalRing.ResidueField`, `IsLocalRing.residue`,
  `IsLocalHom`, `IsArtinianRing`, `AlgEquiv`, and `Module.Finite` directly.
- Proof-only import `Mathlib.RingTheory.HopkinsLevitzki` supplies the recorded match of
  `lem-weil-pbc-artinian-local-noetherian-nilpotent`: the Noetherian instance and
  `isArtinianRing_iff_isNilpotent_maximalIdeal`.
- Proof dependency `lem-sfb-local-square-zero-small-extension-reduction` has no Lean or
  Mathlib record yet. It is not a statement dependency or an object needed to type this
  theorem. Its future use is spelled out in the proof docstring; there is no module to import.

Source and edge cases checked:

Read `literature/stacks-project/formal-defos.tex`, definition-CLambda (Tag 06GC),
lemma-smooth (Tag 0DYL), and `more-algebra.tex`, lemma-fs-local (Tag 0DYG), including
the small-extension and inverse-image-subring parts of the proof. The finite residue
extension matches the finite base-to-field map in the source: R acts on k through R/m_R.
No node correction is needed.

The zero ring is properly excluded for R, C, A, and A' by `IsLocalRing`, which the node
explicitly defines as exactly one maximal ideal. All characteristics and inseparable finite
residue extensions are allowed. A field C is permitted (its maximal ideal is zero).
The exponent begins at 1, not 0. Identity surjections and zero kernel are included: no
nonzero-kernel or small-extension assumption is made. A = k with the prescribed marking
is an allowed test, and distinct markings are retained, not replaced by arbitrary maps
into k. The test universe is `max u v w`, so it cannot become vacuous by lying below the
base or the marked residue field. Arbitrary square-zero rings including the zero ring
remain in the left-hand definition; the proof docstring handles that zero-ring case.

Searches for an existing declaration:

- `msearch.py ... leanfinder "Adic formal smoothness is equivalent to lifting maps through
  surjections of Artinian local algebras with a fixed residue field"`: eight hits, including
  discrete `Algebra.FormallySmooth.exists_lift`, `iff_comp_surjective`,
  `exists_mkₐ_comp_eq_of_isAdicComplete`, and completion maps. None is this fixed-residue
  equivalence for maximal-ideal-adic formal smoothness.
- `msearch.py ... loogle "Algebra.FormallySmooth, IsArtinianRing"`: zero hits.
- `msearch.py ... grep "FormallySmoothAdic|formallySmooth.*[Aa]rtin|[Aa]rtin.*formallySmooth"`:
  zero Mathlib hits.
- `msearch.py ... leansearch "Adic formal smoothness tested on Artinian local rings with
  fixed residue field"`: eight hits on discrete smoothness, cotangent criteria and
  adic-completion lifting, with no exact match.
- `rg` across `lean/WeilConjectures` and `lean/Sheaf` for `FormallySmoothAdic`,
  `fixedResidue`, fixed-residue and residue-lifting patterns: the existing adic definition
  and its transport, closed-fibre, small-kernel and completion results occur, but none
  states this equivalence. More focused `rg` for the proposed declaration and module name
  in both roots and `dag/lean_names_upstream.json` found no collision.
- `rg` for the item id in `lean/WeilConjectures` found no declaration.

Validation: `scompile.py Q123 lem-sfb-adic-smooth-fixed-residue-lifting` compiled the file
both in sandbox mode (6.2 seconds) and as its library module (7.3 seconds), with no errors
or warnings. Every universe and variable is explicit, with `autoImplicit false`.
The only changed field of the copied node is `lean`.

## Second reading by Q123

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
