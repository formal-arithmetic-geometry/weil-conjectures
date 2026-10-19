## Worker report

The module `Sheaf.Algebra.Homology.AlgebraicLocalDualizingNormalization` states
`DerivedCategory.algebraic_local_dualizing_normalization`. Its only theorem has
`by sorry`; it adds no definitions. The statement is unchanged. No new nodes or
dependency repairs are required.

The source was read in `literature/stacks-project/dualizing.tex`, Lemma 0A7L
(`lemma-find-function`) and the opening paragraph of Section 0A7M
(`section-dualizing-local`). The former gives the residue-field shift and the
latter defines normalization. The module docstring reproduces the node's
three-step proof plan, including preservation of scalar action under shifts.

Clause-by-clause correspondence:

- A commutative Noetherian local ring is `(A : Type u) [CommRing A]
  [IsNoetherianRing A] [IsLocalRing A]`. The last class extends `Nontrivial A`,
  so the stated nonzero hypothesis is included. The unique maximal ideal is
  `IsLocalRing.maximalIdeal A`; it requires no independent choice or extra binder.
- The residue field `κ = A/m` is Mathlib's `IsLocalRing.ResidueField A`, defined
  as exactly that quotient, equipped with its canonical A-module structure by
  `ModuleCat.of A (IsLocalRing.ResidueField A)`.
- The ordinary derived category is `DerivedCategory (RingSiteModules A)`,
  with the same `[HasDerivedCategory.{u} (RingSiteModules A)]` size convention
  used by the recorded dualizing predicates. The already defined one-object
  bottom-topology site is an encoding of ordinary A-modules, as in that node.
- The object and its dualizing hypothesis are `(Ω : DerivedCategory
  (RingSiteModules A)) (hΩ : IsAlgebraicDualizing A Ω)`. This predicate retains
  all three conditions: bounded injective representative, finite cohomology,
  and invertibility of the canonical scalar-action map.
- `κ[0]` is `(DerivedCategory.singleFunctor (RingSiteModules A) 0).obj
  (algebraicDualizingModuleSheaf A (ModuleCat.of A (IsLocalRing.ResidueField A)))`.
  The module-to-site helper is the recorded dependency's constant module sheaf,
  not a new construction or an arbitrary representative.
- `∃ s : ℤ` is the stated integer. The first conjunct is `Nonempty` of the
  displayed isomorphism from `(SignedRingedHom.hom ⊥
  (CochainComplex.onePointRingSheaf A) κ[0]).obj Ω` to `κ[0]⟦s⟧`.
  `Nonempty` asserts the existence of an isomorphism without selecting data.
- The second conjunct is `IsNormalizedAlgebraicDualizing A (Ω⟦-s⟧)` for the
  very same s. This includes both the three dualizing conditions and the
  degree-zero residue-field normalization, rather than just vanishing.
- Mathlib's derived shift `⟦s⟧` has `(K[s])^j = K^(j+s)`, matching the node.
  No dimension, Cohen--Macaulay, regularity, completeness or characteristic
  hypothesis has been added.

Dependency declarations read and used:

- `Sheaf.Algebra.Homology.AlgebraicNormalizedDualizing`:
  `DerivedCategory.IsAlgebraicDualizing`,
  `DerivedCategory.IsNormalizedAlgebraicDualizing`, and
  `CategoryTheory.algebraicDualizingModuleSheaf`. All full signatures,
  definitions and source docstrings were read.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.singleFunctor`, and the shift structure.
  This is the recorded declaration for `def-weil-abstract-derived-category`.
- The internal Hom dependency is publicly exposed through the first import.
  `CategoryTheory.SignedRingedHom.hom` is its existing curried presentation:
  its `homFunctor` is defined as `derivedInternalHomOfUniverses.{u,u,u,u}`.
  The full recorded generic declaration and its localization body were read
  in `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`; no second Hom
  notion is introduced.
- The proof-only import `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
  exposes `CochainComplex.isKInjective_of_injective`, the mathlib_match for
  `lem-weil-pbc-bounded-below-injectives-kinjective`; its signature was read.
  The finite-map transfer and field-shift proof nodes currently have no Lean
  record or Mathlib match, so there is no stated module to import for them.
  Neither is needed to type the statement. Their roles remain in its docstring.

Edge cases checked before writing:

- The zero ring is excluded by the local-ring class itself, exactly as required.
- If A is a field and Ω = A[r], then s = r and Ω[-s] = A[0]. In particular
  r = 0 allows s = 0; the existential does not require a nonzero shift.
- For a DVR with Ω = A[0], RHom_A(κ,A) has its sole cohomology in degree 1,
  so s = -1 and Ω[-s] = A[1], which is normalized. This tests the crucial sign.
- Artinian nonreduced local rings and arbitrary characteristics are allowed;
  neither dimension positivity nor reducedness is assumed.
- Ω = 0 is not inadvertently admitted for nonzero A: its scalar-action map
  cannot be an isomorphism. No extra normalization is assumed in the hypotheses.
- Universe u is explicitly bound, and every binder is explicit. No test-object
  quantifier is hidden in a smaller independent universe.

Searches for an existing statement:

- `msearch.py leansearch`, query “A dualizing complex over a Noetherian local ring
  is a shift of a normalized dualizing complex”: eight unrelated normalized
  Moore complex, ordinary dual-module and derived-localization hits; no match.
- `msearch.py leanfinder`, query “Over a Noetherian local ring every dualizing
  complex has a shift whose derived Hom from the residue field is the residue
  field in degree zero”: eight hits, including single-cohomology-object
  representation and Ext dimension lemmas; no dualizing normalization theorem.
- `msearch.py loogle`, query `DerivedCategory, IsLocalRing.ResidueField`:
  zero hits.
- `msearch.py grep`, query `dualizing|normalized.*[Dd]ual`: ten unrelated hits,
  on categorical dualization, ordinary inner-product duals and homotopy fibres;
  no algebraic dualizing complex.
- `rg` over upstream `WeilConjectures` and project `lean/Sheaf`, for
  `algebraic.*[Nn]ormal|[Nn]ormal.*[Dd]ualizing|IsNormalizedAlgebraicDualizing|IsAlgebraicDualizing`:
  the recorded dependency defines the predicates; other hits concern unrelated
  étale, geometric or relative dualizing objects. No normalization statement.
- `grep -rn` for the item id in upstream `WeilConjectures`: no hits.
- A name search for `algebraic_local_dualizing_normalization` in both source
  libraries found no existing declaration before writing.

There is no STATEMENT-DISPUTED issue and no statement correction.

Validation: `scompile.py` passed without errors or warnings, checking both
the sandbox module and its library module path (2.9 seconds each). Delivery
preflight and compilation are also run with `deliver2.py`.

## Second reading by Q41

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
