## Worker report

The module `Sheaf.RingTheory.EtaleRetractionFiniteProductLocal` states
`finite_algebra_is_product_local_rings` from Stacks Project algebra.tex, Tag 04GG,
proof of (8) => (10). The local ring is represented by
`R : Type u` with `[CommRing R] [IsLocalRing R]`. The retraction hypothesis is
`hR`: for every commutative `R`-algebra `R'` with `Algebra.Etale R R'`, every prime
ideal `p` whose comap is the maximal ideal and whose residue-field map is bijective,
there is an `R`-algebra homomorphism `τ : R' →ₐ[R] R` whose maximal-ideal comap is
`p`. The residue-field map is the Mathlib map
`Ideal.ResidueField.mapₐ`; the explicit equality `hp` supplies its locality
condition. The finite algebra is `B` with `[CommRing B] [Algebra R B]
[Module.Finite R B]`. The conclusion gives a natural number `n` (including `n = 0`),
a family `A : Fin n → Type v`, commutative-ring, `R`-algebra, and local-ring
structures on every factor, and a nonempty set of `R`-algebra equivalences from
`B` to the dependent product `∀ i, A i`. The dependent product is the finite
product; when `n = 0` it is the empty product.

The statement uses only Mathlib declarations: `Algebra.Etale`,
`Ideal.ResidueField.mapₐ`, `Algebra.ofId`, `Module.Finite`, and `AlgEquiv`.
The two statement dependencies are the Mathlib leaves `AlgebraicGeometry.Etale`
(the étale-morphism notion recorded by `def-weil-etale-morphism`) and
`AlgebraicGeometry.Scheme.residueField` (the residue-field notion recorded by
`def-weil-residue-field`); their recorded declarations are not imported because
this ring-level statement uses the corresponding Mathlib ring notions directly.

Edge cases checked: `n = 0` is allowed, so the zero algebra is represented by the
empty product; no nontriviality or characteristic assumption is added; arbitrary
universe levels `u` and `v` are explicit; and no finiteness condition beyond the
node's module-finiteness hypothesis is introduced.

Searches made: the node's recorded LeanSearch, LeanFinder, and grep searches found
no existing theorem for this statement (only the field-specific product theorem and
Mathlib's finite étale-idempotent decomposition). `rg` over
`WeilConjectures/` and `lean/Sheaf/` found no declaration with this statement or
name. The Mathlib declarations used above were checked in
`RingTheory/LocalRing/ResidueField/Ideal.lean` and
`RingTheory/Etale/QuasiFinite.lean`; no exact existing declaration was found.

The theorem proof is intentionally `sorry`, as required for stage 2.

## Second reading by M1

I read the sandbox node, its six proof steps, the module, both statement-dependency
nodes and their Mathlib declarations. The local Stacks checkout is absent on this
machine. I fetched the authoritative Stacks `algebra.tex` into
`scratchpad/algebra.tex` from https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex
and read `lemma-characterize-henselian`, its opening hypotheses and proof of
8 => 10 (lines 42115 ff. and 42242 ff.). The source assumes a commutative local
ring only: no Noetherian, characteristic, domain or field hypothesis. Its condition
(8) includes uniqueness, but the node correctly extracts only the existence used
by this implication. No node-statement correction was needed.

Objects, hypotheses and conclusion, item by item:

- The local base `(R, m, κ)` is `{R : Type u} [CommRing R] [IsLocalRing R]`,
  `IsLocalRing.maximalIdeal R` and its `Ideal.ResidueField`. Verdict: exact;
  localization at the maximal ideal identifies this residue field with `R/m`.
- Every ring map `R → R'` is represented by `R'`, `[CommRing R']` and
  `[Algebra R R']` inside `hR`. Verdict: exact; any ring map supplies this
  algebra structure. I changed `R' : Type v` to `Type (max u v)` because the
  old universe excluded neighborhoods in the base universe when `u > v`.
  Mathlib's 00UL decomposition explicitly produces `R' : Type u` even when
  `B : Type v`. Such neighborhoods can be lifted to `max u v`. Conversely
  étale algebras are finitely presented, hence have models in the universe
  of the base; this choice does not impose a mathematical size restriction.
- Étaleness is `Algebra.Etale R R'`. Verdict: exact affine ring formulation,
  expressly allowed by the stage-2 conventions. I read `Algebra.Etale` in
  `RingTheory/Etale/Basic.lean:206` (formally étale and finite presentation),
  and `AlgebraicGeometry.Etale` in `Morphisms/Etale.lean:41` with its
  `HasRingHomProperty @Etale RingHom.Etale` instance at line 56. These are
  the ring and scheme forms of the dependency `def-weil-etale-morphism`.
- The prime `m'` is `(p : Ideal R') [p.IsPrime]`. Its lying over `m` is
  `(hp : p.comap (algebraMap R R') = IsLocalRing.maximalIdeal R)`.
  Verdict: exact; no maximality or locality of `R'` is assumed.
- The induced residue-field isomorphism is `Function.Bijective
  (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) p
  (Algebra.ofId R R') hp.symm)`. Verdict: exact. I read `Ideal.ResidueField`,
  `map`, and `mapₐ` in `LocalRing/ResidueField/Ideal.lean:33–70`: the map is
  induced by the localization local-ring map with this comap equality.
  Bijectivity of this field homomorphism means isomorphism of the specified
  map, not merely an abstract equivalence of fields. I also read
  `Scheme.residueField`, `Scheme.Hom.residueFieldMap` and
  `Spec.residueFieldIso` in `AlgebraicGeometry/ResidueField.lean:45,123,301`;
  they identify the dependency `def-weil-residue-field` with these affine
  Mathlib notions. No private residue-field definition or dependency repair.
- The required retraction is `∃ (τ : R' →ₐ[R] R),
  p = (IsLocalRing.maximalIdeal R).comap τ.toRingHom`. Verdict: exact;
  being an algebra homomorphism into `R` ensures `τ ∘ algebraMap = id`.
  The equality has exactly the required inverse-image direction. There is
  no uniqueness clause beyond the node's existence assumption.
- The arbitrary finite algebra is `{B : Type v} [CommRing B] [Algebra R B]
  [Module.Finite R B]`. Verdict: exact module-finiteness, with no extra
  étale, finite-free, faithful, Noetherian or nonzero hypothesis on `B`.
- The finite number of local factors is `∃ (n : ℕ) (A : Fin n → Type v)`
  with `comm`, `alg` and `loc` supplying `CommRing`, `Algebra R`, and
  `IsLocalRing` for each `A i`. Verdict: exact, permitting `n = 0`;
  actual factors are quotients/subtypes of `B`, so universe `v` suffices.
- The isomorphism as an `R`-algebra is `Nonempty (B ≃ₐ[R] ∀ i, A i)` after
  the dependent factor instances. Verdict: exact dependent finite product,
  with the same quantifier order; no choices or additional conclusions.

Edge cases: the zero algebra `B` is included and gives `n = 0`; the empty
function product is the zero ring. Local factors are nonzero as intended
(`IsLocalRing` extends `Nontrivial`), and zero factors are discarded. The
base is nonzero because it is local in the source's convention. The empty
spectrum of an étale zero algebra contributes no prime, hence no retraction
obligation. No characteristic is excluded. Both `u` and `v` are explicitly
bound, including `u > v`; the repaired `max u v` quantifier covers the
neighborhoods required by the source's argument. There are no free variables.

Independent searches (recorded by `msearch.py` in `searches.jsonl`):

- LeanSearch: “A finite module algebra over a ring admitting sections of etale
  neighborhoods splits as a product of rings with unique maximal ideals”.
  Service returned Internal Server Error; no mathematical verdict from it.
- LeanFinder: “Idempotent decomposition of finite algebras over local rings
  with sections of pointed etale maps into finitely many local factors”.
  Eight hits, including `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`,
  the field-specific `Algebra.Etale.iff_exists_algEquiv_prod`, and étale-locus
  results. None states this theorem: the first is only its decomposition input,
  the product theorem assumes a field and étale algebra.
- Mathlib grep: `henselian|product of.*local|04GG` in RingTheory. Hits in
  Henselian, Artinian/Module and spectrum-localization modules. I read the
  Artinian product signatures: they require Artinian/reduced hypotheses,
  absent here. I also read the full 00UL decomposition signature at
  QuasiFinite.lean:613; it gives only the upstairs idempotents, not this result.
- `rg` on the source `WeilConjectures/`, project `lean/Sheaf/`, and upstream
  declaration-name table, by the proposed name and by “henselian”,
  “etale.*section”, “unique maximal” and “product.*local”. No exact theorem
  or name collision. The project section-lifting/henselian-pair and
  étale-section-idempotent modules concern different statements, not this one.

Mismatches and repairs: fixed the neighborhood universe; expanded the theorem
proof docstring from a one-sentence summary to the node's six steps, explicitly
naming both proof-input nodes, the tensor surjection, prime correspondence,
vanishing last factor, locality and discarding zero factors; added the standard
copyright/license/author header and removed the unused TensorProduct scope.
The node's `lean.statement` is now the verbatim repaired signature. The node's
mathematical statement and dependencies were correct and are unchanged. No
new nodes or dependency modules were necessary. There is one named theorem,
its proof remains `sorry`, and no definitions, hollow data or proved auxiliaries.

Verification: `scompile.py M1 lem-weil-pbc-etale-retraction-finite-product-local`
compiled the repaired module on the server in 1.6 seconds, exit 0, without
warnings or errors. Lines are at most 100 characters and imports are Mathlib.
