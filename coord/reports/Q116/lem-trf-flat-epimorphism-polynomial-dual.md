## Worker report

The module `Sheaf.Algebra.Homology.FlatEpimorphismPolynomialDual` states
`ModuleCat.exists_flatEpimorphism_polynomialDual_iso`. Its sole theorem has proof
`sorry`. The three supporting definitions contain real data: the ordered graph
sequence, the recorded Koszul complex extended to integer degrees, and a predicate
specifying the normalized first isomorphism by a Koszul roof. No dependency record,
node statement, statement dependency, or proof step is changed.

Source read: `literature/stacks-project/dualizing.tex`,
`lemma-upper-shriek-localize` (Tag 0C0H), including its self-base-change paragraph.
The item explicitly supplies the non-Noetherian generalization under polynomial
perfectness, with its six-step argument. The signed dual and comparison conventions
were checked against `WeilConjectures.RingTheory.KoszulDualComplex`,
`KoszulConormalComparison`, `KoszulRegularSequenceDualComplex`,
`KoszulDerivedDualEvaluation`, and `KoszulExtRoofRepresentatives`.

Hypothesis and clause correspondence:

- Commutative rings and their map R→A: `{R A : Type u} [CommRing R]
  [CommRing A] [Algebra R A]`, with map `algebraMap R A`. An algebra structure
  on commutative rings is precisely the given ring map.
- Flatness: `hflat : (algebraMap R A).Flat`, the dependency's `RingHom.Flat`.
- Ring-isomorphism multiplication A⊗_R A→A: `hmul : Function.Bijective
  (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A)`. This is the actual
  multiplication homomorphism, rather than existence of an unrelated equivalence.
  Bijectivity of a ring homomorphism is equivalent to its being a ring isomorphism.
- Polynomial presentation and n≥0: `n : ℕ`,
  `p : MvPolynomial (Fin n) R →ₐ[R] A`, and `hp : Function.Surjective p`.
  The algebra-hom condition says that the presentation factors the specified R-map.
- Perfectness of A[0] over P: `hperfect : DerivedCategory.IsPerfectRingComplex
  ((restrictScalars p.toRingHom).mapDerivedCategory.obj
  ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A A)))`.
  The imported definition is exactly a bounded finite projective model; no
  finiteness or smoothness hypothesis is substituted for it.
- Ordinary unbounded module derived categories: `DerivedCategory (ModuleCat …)`
  and explicit `HasDerivedCategory` binders, with independent localization
  universes `wP`, `wS`, `wA`. No derived category of sheaves is substituted.
- P_A=P⊗_R A=A[x₁,...,xₙ]: written in its canonical polynomial presentation
  `MvPolynomial (Fin n) A`. This is the node's second displayed description,
  so no new arbitrary base-change ring is introduced.
- Images a_i: `fun i ↦ p (MvPolynomial.X i)`. The graph quotient map is
  `MvPolynomial.eval` at exactly this family. Its coefficients are fixed and each
  variable maps to its prescribed image.
- First isomorphism in D(A): the first existential `e` has source the actual
  `derivedCoinduction (MvPolynomial.eval …)` applied to S[0] and target
  `(DerivedCategory.singleFunctor (ModuleCat A) (n : ℤ)).obj (ModuleCat.of A A)`.
  A single object in degree n is canonically A[0][-n] with the library's shift
  convention. Thus this is the exact derived assertion, not only its cohomology.
- Ordered dual Koszul normalization: `IsOrderedPolynomialDualGraphIso n … e`.
  Its `ε` is a quasi-isomorphic graph Koszul augmentation, normalized on every
  degree-zero element to the specified polynomial evaluation. Its `z` represents
  the adjunction mate of `e.inv`, after shifting the augmentation and applying the
  canonical single/restriction comparison. Its `y` is a cycle in the RECORDED
  `ExteriorAlgebra.koszulDualComplex`; its inclusion is exactly z's top functional.
  The final equality evaluates that functional on
  `exteriorPower.ιMulti S n (fun i ↦ Finsupp.single i 1)` and then evaluates
  coefficients in A, obtaining 1. This is the wedge of the dual conormal basis
  in the original order. It is tied to e via the actual adjunction; no arbitrary
  identification of cohomology is allowed. Because e is A-linear, the inverse
  image of 1 specifies the whole top-cohomology identification.
- Second isomorphism: `Nonempty (((derivedCoinduction p.toRingHom).obj
  (P[0]))⟦(n : ℤ)⟧ ≅ A[0])`, expanded in the file with the single functors.
  Its ambient category is D(A), with the original coinduction functor and action.
  Thus A-linearity is encoded in the morphism type itself.
- Zero ring, empty variable list, arbitrary bases: there is no `Nontrivial`,
  positive-n, Noetherian, domain, or regular-ring binder.

Dependency declarations used, with their recorded modules:

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat` (definition and signature read).
- `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`: `MvPolynomial`,
  `MvPolynomial.aeval`, `MvPolynomial.algHom_ext`, and `MvPolynomial.eval`.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex` (full bounded-model definition read).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `Q`, `singleFunctor`, `singleFunctors`.
- `Sheaf.Algebra.Homology.DerivedCoinductionAdjunction`:
  `ModuleCat.derivedCoinduction` and `ModuleCat.derivedCoinductionAdjunction`.
  The full source was read, including its ordinary precomposition action,
  K-injective model, evaluation counit, and derived construction.
- `WeilConjectures.RingTheory.KoszulDualComplex`:
  `ExteriorAlgebra.koszulDualComplex` and the underlying `koszulComplex`.
  The former has differential (-1)^(q+1) times precomposition, as required.

Proof-only dependency modules imported privately:
`Sheaf.Algebra.Homology.BaseChangeRHomPerfect` (`baseChangeRHomPerfect`),
`Sheaf.Algebra.Homology.DerivedHomProjectiveResolution`
(`derivedHom_projectiveResolution`),
`WeilConjectures.RingTheory.KoszulConormalBasis`
(`exists_koszul_conormal_basis`),
`WeilConjectures.RingTheory.KoszulRegularSequenceDualComplex`
(`exists_unique_koszul_conormal_comparison`),
`Mathlib.Algebra.Homology.DerivedCategory.TStructure`
(`exists_iso_singleFunctor_obj_of_isGE_of_isLE`), and
`WeilConjectures.RingTheory.RegularSequenceKoszulRegular`
(`isKoszulRegularOn_of_isWeaklyRegular`). Flat tensor exactness is available from
`Mathlib.RingTheory.Flat.Basic` through the public flat-ring-map import.

Edge cases checked before writing:

- n=0: the graph Koszul complex and its signed dual have just the degree-zero
  coefficient term. The wedge indexed by `Fin 0` is 1. Shifting by zero and the
  normalized augmentation impose the usual evaluation identification.
- A=0: all A-modules and coinduction objects vanish. The normalization equation
  reads 0=1 in the zero ring, so it still holds. No proper-ideal regularity
  convention is imposed on the graph sequence.
- General non-Noetherian R: the graph equations remain successive monic
  nonzerodivisors, and perfectness is assumed exactly over P. No unmentioned
  coherence or regularity assumption enters the signature.
- R=A with identity map: the graph quotient gives the usual ordered polynomial
  Koszul dual, so the two conclusions and shift signs agree.
- Rings of different sizes can be regarded in a common ambient `Type u`;
  localization universes are independent and are not forced equal to u.

Searches for an existing statement (2026-10-24):

- `msearch.py … leanfinder "For a flat ring epimorphism R to A with perfect
  polynomial presentation P the derived coinduction of P to A shifted by the
  number of variables is A"`: 8 hits, including `Algebra.Smooth.flat`,
  `Algebra.Smooth.formallySmooth`, and formally smooth cotangent criteria;
  no derived polynomial duality statement.
- `msearch.py … leansearch "The derived dual of a perfect polynomial presentation
  of a flat ring epimorphism is the algebra shifted by the number of variables"`:
  8 hits, including `RingHom.Flat`, `Module.Dual.congr`, and ordinary polynomial
  finite presentation; no match.
- `msearch.py … loogle "Algebra.IsEpi, MvPolynomial"`: 0 hits.
- `msearch.py … grep "derivedCoinduction|polynomial.*dual|flat.*epimorphism"
  RingTheory`: 1 unrelated degree-bound comment in MvPolynomial.Basic.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for flat epimorphisms,
  polynomial duality and graph Koszul constructions found
  `PolynomialRelativeDualProperties` and the flat SURJECTION derived self-tensor
  lemma; neither states this theorem or its normalization. Read their signatures.
- `grep -rn` for this node id in `lean/WeilConjectures`: no match.
- Exact searches for all four proposed declaration names in both library roots
  and `dag/lean_names_upstream.json`: no match.
- The example `Sheaf.CategoryTheory.CompactObject` is withdrawn locally; its
  node points to `WeilConjectures.CategoryTheory.CompactObject`, which was read
  for the current module header and docstring conventions.

No statement correction, new independent notion, dependency repair, or
STATEMENT-DISPUTED issue was needed. The graph helpers are part of this node's
own normalization interface and are listed in `lean.declarations`.

## Second reading by Q116

Reopened the node and the module for a separate clause-by-clause self-review.
This dispatcher assignment forbids starting another agent; the maintainer's
independent review remains the independent reading of the delivery.

Checked flatness against `hflat`; multiplication against the fixed `lmul'` map;
the compatible surjective polynomial presentation against `p` and `hp`; and
perfectness against the actual restricted A[0], rather than the dual object.
Checked that both isomorphism types live in D(A). The first target is degree n,
which is A[-n]; the second source is shifted by +n. The first normalization
uses the graph equations in `Fin n` order, actual dual-complex cycles, and the
adjunction mate of the SAME `e.inv`. A normalization only saying that some
unrelated top-cohomology equivalence exists would be inadequate; this file
instead includes the roof equality. The augmentation equation rules out an
arbitrary unit multiple of the quotient map. The final wedge evaluation is 1,
with no conormal-order permutation. The second isomorphism is intrinsically
A-linear through `derivedCoinduction p.toRingHom`.

Checked n=0 and the zero ring in the predicate as well as the main statement.
No hidden positivity, nontriviality, Noetherianity or localization-universe
restriction was found. Corrected only Lean import visibility and syntax during
compilation; no mathematical hypothesis or conclusion was changed.
