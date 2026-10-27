## Worker report

The module `Sheaf.RingTheory.LocalizedPolynomialResolutionModel` states the entire
node in two theorems, with only `sorry` proofs:
`Algebra.CotangentResolution.exists_localized_polynomial_resolution_model` and
`Algebra.CotangentResolution.exists_self_localized_polynomial_resolution_model`.
`LocalizedPolynomialResolutionModel` bundles the conclusions of the first theorem.
The remaining declarations construct its underlying objects and maps using actual
Mathlib data. No object is selected from an unproved existence assertion.

Sources read: `literature/stacks-project/cotangent.tex`, the whole resolution
remark (Tag 08QI, lines 666–702) and the flat-base-change lemma and proof
(Tag 08QP, lines 957–980). The latter identifies the scalar extension of the
alternating complex with the alternating complex of the scalar-extended simplicial
algebra. Localization exactness is supplied by the node's Mathlib proof dependencies.
The current node is an auxiliary algebra input, not a blueprint unit's statement;
its accepted statement and split are unchanged.

Hypotheses and clauses, individually:

- A commutative ring R, commutative R-algebra T and its structure map are
  `f : Arrow CommRingCat.{u}`, with R = `f.left`, T = `f.right`, map `f.hom`.
  The category permits the zero ring. `resolutionTarget f` gives exactly the
  algebra structure induced by this map, rather than adding a structure hypothesis.
- The multiplicative subset is `S : Submonoid f.left`. Its structure includes 1
  and closure under multiplication. There is no exclusion of zero and no
  nontriviality, regular-element or finite-generation hypothesis.
- The supplied polynomial resolution is `P : Augmentation f`, with
  `hP : IsPolynomialResolution P`, from the recorded dependency module.
  This retains polynomiality, surjectivity in every degree, and quasi-isomorphy
  of the augmented alternating complex, exactly as the node specifies.
- B is the actual `Localization S`. T_S is the actual fraction algebra
  `resolutionLocalizedTarget f S`, whose carrier is
  `LocalizedModule S (resolutionTarget f)`. Its B-algebra structure is
  `LocalizedModule.algebraOfIsLocalization`. The target coefficient map is
  `resolutionLocalizedArrow f S`.
- The conclusion `resolution` is an `Augmentation` over that localized ring map;
  `polynomial` is the recorded `IsPolynomialResolution` predicate on it.
- `resolutionTensorTerm P S n` is the actual algebra tensor product
  `Localization S ⊗[f.left] P_n`. `termIso` identifies it with the nth term
  of the output resolution as a B-algebra. This is the symmetric tensor order
  explicitly allowed by the node and the base-change dependency record.
- `operator` specifies every simplicial operator on pure tensors as
  `b ⊗ p ↦ b ⊗ P(θ)(p)`. It covers both faces and degeneracies and their
  composites, so this is scalar extension of the supplied simplicial algebra.
- `augmentation` prescribes `b ⊗ p ↦ b • (ε(p)/1)`. In the commutative
  localized target algebra this is exactly `(ε(p)/1)b`.
- For every R-module, `moduleIso` gives the B-linear equivalence
  `B ⊗[R] M ≃ₗ[B] LocalizedModule S M`. The module universe `v` is explicit
  and independent of the base-ring and simplicial-resolution universe `u`.
- `fraction` gives `(r/s) ⊗ m ↦ (r • m)/s`; `inverse_fraction` gives
  `m/s ↦ (1/s) ⊗ m`. `naturality` quantifies over every module morphism h
  and every tensor x, using the recorded `LinearMap.baseChange` and
  `LocalizedModule.map` for the two actual induced maps.
- `resolutionAlgebras P` is `Under.lift P.algebra P.base` followed by the
  inverse of Mathlib's `commAlgCatEquivUnder`. Thus the original terms and
  coefficient maps are retained. `resolutionModuleAugmented P` forgets
  multiplication on the actual lifted augmentation cocone; its triangle
  proofs are the supplied `P.triangle`, not new assumptions or postponed data.
- `resolutionModuleComplexAugmentation` uses Mathlib's alternating-face
  augmentation and extension along `ComplexShape.embeddingDownNat`. Its source
  is the dependency's `negativeComplex` construction on the underlying modules,
  with degree -n equal to P_n and zero positive terms.
- `complexIso` is an actual isomorphism in the arrow category of cochain
  complexes of B-modules. Its left object is the alternating complex of Q and
  its right object includes the augmentation target T_S[0]. The other arrow is
  the image of the *whole augmentation morphism* of P under
  `(ModuleCat.localizedModuleFunctor S).mapHomologicalComplex`.
  An arrow isomorphism includes the commuting augmentation square and inverse
  complex maps. This states an augmented-complex isomorphism, not homology alone.
- `complex_fraction` specifies the left complex map in every nonpositive
  degree: the element represented by `(r/s) ⊗ p` goes to `(r • p)/s`.
  `resolutionComplexElement` uses the actual extension-by-zero term isomorphism.
  Mathlib's categorical localization shrinks its fraction modules; the explicit
  `equivShrink` only expresses the canonical carrier identification.
  Together with the isomorphism this also determines the inverse fraction map.
- `coordinates` quantifies over every n, every `E : Type u`, and every supplied
  R-algebra coordinate isomorphism R[E] → P_n. It produces a B-algebra
  coordinate isomorphism B[E] → Q_n, satisfying the actual coefficient formula
  `b • map (algebraMap R B) p ↦ b ⊗ c(p)`. Taking p = X_e or p = 1 gives
  the variable and coefficient identifications. E is not assumed finite or nonempty.
- The second theorem takes exactly a polynomial resolution of B over R.
  It supplies the general model L, the B-algebra isomorphism ψ from S⁻¹B to B,
  a polynomial resolution Q over the identity map B → B, and a natural ring
  isomorphism e identifying its simplicial terms with those of L.
- Its first formula specifies ψ(b/s) = `(Localization.mk 1 s) * b`;
  `Localization.mk 1 s` is the inverse of s/1 even though B is not a field.
  The next two formulas require e to preserve the B-coefficient maps and to
  transport the augmentation through ψ. The last formula gives precisely
  `ε(p) * b` on the tensor generators. The explicit `_root_.id` only unfolds
  the presentation of the target ring as the right endpoint of the ring arrow.

Dependency declarations used:

- `Sheaf.RingTheory.CotangentResolutionCoherence`:
  `Algebra.CotangentResolution.Augmentation`, `IsPolynomialResolution`,
  `negativeComplex` (the underlying alternating-and-extension construction).
  The full recorded signatures and docstrings were read, including the
  coefficient compatibility in polynomiality and all clauses of resolution.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: `LinearMap.baseChange`,
  read at lines 656–674. The tensor product is Mathlib `TensorProduct`,
  with coefficient-first order as authorized in the dependency record.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule`,
  `LocalizedModule.mk`, `LocalizedModule.map`, and
  `LocalizedModule.algebraOfIsLocalization`; the recorded abbreviation,
  fraction operations, induced maps and coefficient algebra were read.
- Proof dependencies are imported from
  `Mathlib.RingTheory.Localization.BaseChange`
  (`IsLocalizedModule.rTensor`, `IsLocalizedModule.map_lTensor`, signatures
  and docstrings read at lines 242–264),
  `Mathlib.LinearAlgebra.TensorProduct.Defs` (`TensorProduct`),
  `Mathlib.RingTheory.TensorProduct.MvPolynomial`
  (`MvPolynomial.algebraTensorAlgEquiv`, formula read at lines 94–108), and
  `Mathlib.Algebra.Module.LocalizedModule.Exact`
  (`LocalizedModule.map_exact`, statement and proof read at lines 34–53).
- Additional standard implementation interfaces are
  `commAlgCatEquivUnder`, `Under.lift`, `Under.liftCocone`, the ordinary
  forgetful functors, `AlgebraicTopology.AlternatingFaceMapComplex.ε`,
  `HomologicalComplex.extendMap`, `HomologicalComplex.extendXIso`,
  and `ModuleCat.localizedModuleFunctor`; their definitions were inspected.

Edge cases checked before and during writing:

1. If 0 belongs to S, B and every localized module are zero, the tensor terms
   are zero, and the displayed algebra and complex equivalences remain valid.
   No `Nontrivial` or `NonZeroDivisors` assumption has entered the signatures.
2. S = {1} gives the identity localization; the fraction and augmentation
   formulas become the ordinary tensor-unit identifications.
3. Polynomial variable sets can be empty, finite, or infinite. No Fintype or
   finiteness assumption occurs; polynomiality is the dependency's own predicate.
4. The zero source ring, zero target algebra, zero module and rings with
   zero divisors are included. No cancellation of nonunits is assumed.
5. n = 0 includes the augmentation square, because `complexIso` is an arrow
   isomorphism. Positive cohomological degrees use extension by zero.
6. The T = B case retains the actual inverse-unit formula and gives a
   resolution over the identity B → B, not just over B → S⁻¹B.

Searches actually run:

- `msearch.py ... leanfinder`, query
  "Localization of an augmented simplicial polynomial algebra resolution with
  natural tensor fraction isomorphisms": eight hits, including
  `Algebra.Presentation.tensorModelOfHasCoeffsInv_aeval_val`, group-resolution
  objects and Dold–Kan functors. None states this full resolution theorem.
- `msearch.py ... loogle`, query `IsLocalization, TensorProduct`: twelve hits,
  including `IsLocalization.tensorRight`, `tensor`, `algebraLid`, `moduleLid`,
  `tensorProduct_isLocalizedModule`. They supply tensor/localization components,
  not polynomial resolution preservation with augmented-complex and coordinate data.
- `msearch.py ... grep`, pattern
  `simplicial.*localiz|localiz.*simplicial|resolution.*localiz`, subdirectory
  `RingTheory`: zero hits.
- `msearch.py ... leansearch`, query
  "Localization of an augmented simplicial polynomial resolution is a polynomial
  resolution over the localized coefficient ring": eight hits on localization
  of polynomials, algebra extensions, localized-module instances and unrelated
  homotopy-category localization; no full match.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the proposed declaration names found none.
  Keyword searches found the parent `LocalizationCotangentVanishing` and
  unrelated localized projective-dimension results, not this theorem.
- `grep -rn` for the exact node id in `lean/WeilConjectures` returned no hits.
  No duplicate statement or private copy of a dependency is introduced.

No statement correction, dependency repair, new independent notion, or disputed
statement is needed. The bundled model and carrier-view helpers belong to this
node's assertion; they do not replace the dependency's definition of resolution.

## Second reading by Q26

Author's second pass (the maintainer supplies the independent review). I reread
the original node, the complete dependency definition and the completed module.
The general theorem includes each hypothesis without a finiteness or nonzero
restriction. The term isomorphisms are algebra isomorphisms, so multiplication
and coefficients are preserved. The operator field includes both faces and
 degeneracies; the augmentation formula includes the localization of ε(p).
The arrow-category complex isomorphism retains the target map as well as the
complex itself, and its degreewise fraction formula specifies the intended
comparison. The coordinate clause covers each supplied presentation, rather
than asserting only that some polynomial presentation exists. The second theorem
includes ψ, its inverse-unit normalization, the identity-map resolution, and the
ε(p)b formula. No clause was removed or added as a mathematical hypothesis.
Compiler feedback required tensor notation to be opened, the implicit S argument
of `algebraOfIsLocalization` to be named, and `_root_.id` to avoid collision with
`Algebra.id`; these are elaboration corrections only.

All variables and universes are explicit (`set_option autoImplicit false`).
Every definition contains actual data. The only postponed proofs are the two
named theorem conclusions carrying this node's id and full natural-language proofs.
