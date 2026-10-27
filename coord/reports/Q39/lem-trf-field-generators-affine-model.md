## Worker report

The module `Sheaf.AlgebraicGeometry.FieldGeneratorsAffineModel` states
`AlgebraicGeometry.fieldGeneratorsAffineModel`, with its sole proof left as `sorry`.
No new definition, dependency repair, or statement correction is needed. Its docstring
contains the six-step natural-language proof route from the node.

Hypotheses and objects, matched with the node:

- `k E : Type u`, `[Field k] [Field E] [Algebra k E]` are the two fields and their
  specified coefficient inclusion `algebraMap k E`; a homomorphism from a field to a
  field is injective. A common ambient universe supports the spectra and their morphisms.
- `r : ℕ` includes zero, and `e : Fin r → E` is the given ordered family.
- `he : IntermediateField.adjoin k (Set.range e) = ⊤` says exactly that the smallest
  intermediate field containing all the generators is all of E.
- Every occurrence of A is the actual Mathlib construction
  `Algebra.adjoin k (Set.range e)`, not an arbitrary algebra with assumed properties.
  This is precisely the polynomial subalgebra. Every occurrence of U is
  `Spec (CommRingCat.of (Algebra.adjoin k (Set.range e)))`.

Conclusion clauses, in their Lean order:

1. `IsDomain (Algebra.adjoin k (Set.range e))` is the domain assertion.
2. `RingHom.FiniteType (algebraMap k (Algebra.adjoin k (Set.range e)))` is finite
   type of A over k, using the dependency's recorded ring-homomorphism predicate.
3. `IsFractionRing (Algebra.adjoin k (Set.range e)) E` says that the actual subtype
   inclusion makes E the localization at the nonzero elements of the domain A.
   This is equivalent to the node's explicit statement that every element is a/b
   with a,b in A and b nonzero. No fraction-field hypothesis is added.
4. `IsIntegral (Spec (.of ...))` is integrality of U.
5. `LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k A)))` and
   `QuasiCompact` of that same map express finite type over k, as specified in
   `def-weil-finite-type-morphism`. The source and its structure morphism are canonical.
6. `genericPoint U = (⊥ : PrimeSpectrum A)` identifies the generic point with the
   zero prime; for a domain this bottom prime is the zero ideal.
7. The existential ring equivalence `θ : U.functionField ≃+* E` is required to satisfy,
   for every a in A, `θ (StructureSheaf.toStalk A (genericPoint U) a) = (a : E)`.
   Thus it is the isomorphism induced by the inclusion of A into E, not an arbitrary
   abstract field isomorphism. Because k is contained in A, this condition includes
   k-linearity. Equivalently, this is an A-algebra isomorphism for the canonical stalk
   algebra. `Scheme.functionField` is definitionally the generic stalk in this case.
8. `∃ d : ℕ, topologicalKrullDim U = (d : WithBot ℕ∞) ∧
   Algebra.trdeg k E = (d : Cardinal)` expresses equality and finiteness in the two
   predicates' native codomains; it avoids any truncation of infinite values.
9. The final existential `ε` is a k-algebra homomorphism from the polynomial ring
   indexed by `ULift (Fin r)` into A, with the equation
   `(ε (MvPolynomial.X i) : E) = e i.down` for every variable. These equations determine
   ε uniquely by `MvPolynomial.algHom_ext` and the injective subtype map A → E, so ε
   is precisely canonical evaluation. `Function.Surjective ε` is the required surjection.
10. `IsClosedImmersion (Spec.map (CommRingCat.ofHom ε.toRingHom) ≫
    (AffineSpace.SpecIso ... (.of k)).inv)` is the induced map U → affine r-space.
    The displayed equality after composition with its canonical projection says this
    very immersion is over k. `AffineSpace.SpecIso` is the canonical polynomial-chart
    identification, not an arbitrary isomorphism. `ULift (Fin r)` has the same r variables
    and only places their index type in the ambient scheme universe.

Dependency declarations read and used (statement dependencies):

| Node | Module and declaration/interface |
| --- | --- |
| def-weil-field | Mathlib.Algebra.Field.Defs: `Field` |
| def-pc-field-extension | Mathlib.Algebra.Algebra.Defs: `Algebra`, `algebraMap` |
| def-weil-affine-spectrum | Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Spec`, `Spec.map` |
| def-weil-pbc-finite-type-algebra | Mathlib.RingTheory.FiniteType: `RingHom.FiniteType` |
| def-pc-integral-scheme | Mathlib.AlgebraicGeometry.Properties: `AlgebraicGeometry.IsIntegral` |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType: `LocallyOfFiniteType`; Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: `QuasiCompact` |
| def-sc-function-field | WeilConjectures.AlgebraicGeometry.FunctionField (imported): its documented integral-scheme clause reuses Mathlib.AlgebraicGeometry.FunctionField: `Scheme.functionField` |
| def-kun-topological-krull-dimension | Mathlib.Topology.KrullDimension: `topologicalKrullDim` |
| def-kun-transcendence-degree | Mathlib.RingTheory.AlgebraicIndependent.Basic: `Algebra.trdeg` |
| def-weil-pbc-mv-polynomial-ring | Mathlib.Algebra.MvPolynomial.Basic/Eval: `MvPolynomial`, `MvPolynomial.aeval`, `MvPolynomial.algHom_ext` |
| def-weil-closed-immersion | Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion` |
| def-nagata-relative-affine-space | Mathlib.AlgebraicGeometry.AffineSpace: `AffineSpace`, `AffineSpace.SpecIso` and its canonical projection |

The proof-only project module
`WeilConjectures.RingTheory.FiniteTypeDomainDimensionTrdeg` is imported without `public`:
its `finiteType_domain_ringKrullDim_eq_trdeg` supplies the dimension comparison.
The remaining proof interfaces are available through the statement imports:
`StructureSheaf.IsLocalization.to_stalk`, `functionField_isFractionRing_of_affine`,
`genericPoint_eq_bot_of_affine`, `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`,
`Scheme.Hom.app_surjective`, `IsAffineOpen.preimage`, and the affine-property
closed-immersion criterion. Their DAG records are Mathlib matches, not missing nodes.

Edge cases checked before writing: r = 0 forces the intermediate-field extension to be
trivial, so A is the image of k, U has dimension zero, and the immersion is into affine
zero-space. Repetitions, zero generators, or generators already in k are permitted;
evaluation and its kernel still give the same assertions. Nontrivial finite algebraic
extensions also have dimension zero. Transcendental generators give positive dimension;
no algebraic/finite-module assumption is imposed on E. Arbitrary characteristic is allowed.
The zero ring and empty spectrum cannot occur because A is a subalgebra of a field.
The dimension predicate retains both infinite and empty-space values in general, while
the natural-number witness states their exclusion here.

Searches (2026-10-24; wrapper results are also in searches.jsonl):

- `msearch.py ... leanfinder`: "The subalgebra generated by field generators is an
  integral affine finite type model with that function field, dimension equal to
  transcendence degree and a polynomial closed immersion". Eight hits, including
  `instAlgebraCarrierFunctionFieldSpec` and `functionField_isFractionRing_of_affine`;
  these are component statements, not the whole conjunction.
- `msearch.py ... loogle "Algebra.FiniteType, Algebra.trdeg"`: one hit,
  `trdeg_lt_aleph0_of_finiteType`, only a finiteness assertion, not the affine model.
- `msearch.py ... grep "adjoin.*(fraction|Fraction)|[Ff]raction.*adjoin|essFiniteType_iff"
  FieldTheory`: three hits in FinTrdeg and IntermediateField/Adjoin/Algebra. The scoped
  fraction-ring instance there handles the algebraic part, not the geometric conjunction.
- `rg` in Mathlib for evaluation/adjoin: `MvPolynomial.aeval_range` and
  `Algebra.adjoin_range_eq_range_aeval` identify the polynomial image. The actual
  adjoin constructions and those existing evaluation maps are reused.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id, for
  `fieldGeneratorsAffineModel`, and for adjoin/functionField combinations found no
  duplicate statement. The unrelated TameRadicalNormalization module mentions
  an intermediate-field adjoin. The proposed full declaration name is unused.

Sources opened locally: varieties.tex, theorem-varieties-rational-maps (0BXN), its
essential-surjectivity paragraph; algebra.tex, lemma-dimension-prime-polynomial-ring
(00P0); the full recorded statement-dependency signatures and docstrings in the source
modules listed above. No node fault or disputed statement was found.

## Second reading by Q39

A clause-by-clause rereading of the node and final module checks all the hypotheses and
all ten conclusion items above. It checked especially that E is finitely generated as a
field (not a finite-type algebra hypothesis on E), that the generic-stalk isomorphism
respects the inclusion of A, that the dimension equality has a finite witness, and that
the closed immersion is the one induced by evaluation and commutes with the projection
to Spec k. During elaboration, the generic-stalk condition was written explicitly with
`StructureSheaf.toStalk` instead of relying on inference of the stalk algebra instance;
this retains exactly the canonical compatibility, and no mathematical clause changed.
This is the assigned dispatcher's sole worker's rereading; no independent second worker
was started, in accordance with the task brief. Independent maintainer review is pending.

Validation: the prescribed `scompile.py Q39 lem-trf-field-generators-affine-model`
completed successfully for the final file in both sandbox and library mode, with no
Lean errors or warnings. The library-mode compiler reported 2.3 seconds. Earlier
elaboration errors were repaired; the final file has exactly one theorem and one `sorry`.
