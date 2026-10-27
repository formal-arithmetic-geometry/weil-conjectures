## Worker report

The module `Sheaf.RingTheory.PolynomialAugmentationBoundary` states
`Algebra.CotangentResolution.polynomial_augmentation_boundary`, with one `sorry` and no new
construction. Its three conjuncts express the constant comparison, the criterion for an
arbitrary augmentation, and the existence and properties of the specified standard resolution.
No statement correction or disputed assertion was necessary.

Clause-by-clause correspondence:

- Commutative rings and the homomorphism A → B are `f : Arrow CommRingCat.{u}`: its left and
  right objects carry commutative ring structures and its arrow is the given ring homomorphism.
  There are no characteristic, finiteness, injectivity, or nontriviality hypotheses.
- An augmented simplicial A-algebra over f is the existing `Q : Augmentation f`. Its fields
  are the simplicial commutative algebra, the natural base map, the augmentation, and the
  equation that their composite is f in each degree. In particular the A-structure is present,
  rather than assumed on unrelated ring maps degree by degree.
- The additive alternating complex is the existing `negativeComplex` convention:
  `alternatingFaceMapComplex` followed by extension along `ComplexShape.embeddingDownNat`.
  That embedding sends n to -n and inserts zero objects in positive degrees. Its differential
  is the alternating face sum; the actual additive augmentation uses this same embedding.
- The first conjunct applies Mathlib's `AlternatingFaceMapComplex.ε` to the augmented constant
  simplicial additive group underlying B, with identity augmentation, and extends the map
  along `embeddingDownNat`. `ε_app_f_zero` identifies its degree-zero map with the identity;
  `ε_app_f_succ` makes the other components zero. The target is the extension of the degree-zero
  single complex, namely B[0]. `QuasiIso` asserts isomorphy on every integer cohomology group.
- The second conjunct quantifies over EVERY `Q : Augmentation f`. Its first hypothesis is
  `∀ n : ℕ, Function.Surjective (Q.augmentation.app (op ⦋n⦌))`, including n = 0. Its second
  hypothesis is `QuasiIso (additiveAugmentation Q)`, the stated map to B[0]. Its conclusion is
  `SSet.Enhanced.trivialKanFibration` of the actual augmentation whiskered with the forgetful
  functor. This reducible alias is `SSet.modelCategoryQuillen.I.rlp`; I contains all boundary
  inclusions, including the empty boundary in dimension zero. No polynomial hypothesis is
  imposed on this general criterion.
- The final conjunct asserts existence of `P : Augmentation f` with `IsStandard P`. This is
  the existing EXACT specification by equality of terms and heterogeneous equality of maps,
  not arbitrary polynomial algebras isomorphic to the prescribed terms. `standardTerm f 0`
  is A[B] and its successor is A[standardTerm f n], so these are G^(n+1)B. `standardBase` is C.
  `standardAugmentation` iteratively evaluates variables. `standardFace` evaluates the
  outer layer for i = 0 and otherwise applies the previous face to variable labels; this is
  G^i ε G^(n-i). `standardDegeneracy` inserts X_(X_p) for i = 0 and otherwise applies the
  previous degeneracy to labels; this is G^i δ G^(n-i), with δ induced by e ↦ X_e. The existing
  definitions were read in full, including their degree-zero formulas. Thus the free-algebra
  and forgetful adjunction in the prose is rendered by its actual prescribed polynomial
  formulas, without introducing a second definition of that adjunction or of the resolution.
- `IsPolynomialResolution P` supplies each remaining algebraic clause: in every degree an
  arbitrary `E : Type u`, a polynomial ring isomorphism respecting every coefficient from A,
  surjectivity of the specified augmentation, and `QuasiIso (additiveAugmentation P)`.
  The variable sets are arbitrary; there is no `Finite` or `Fintype` binder.
- The explicit existential `g` is a natural transformation of functors to `Type u`, from the
  underlying constant B to the underlying simplicial set of P. The two `Relation.EqvGen`
  clauses assert the two composites are homotopic to their respective identities. The
  generating relation is `Nonempty (SSet.Homotopy a b)`, namely simplicial cylinder homotopy;
  its equivalence closure is homotopy by a finite chain, as in Stacks and the recorded 08P2
  dependency. There is no additive or multiplicative structure imposed on g or its homotopies.
- The last conjunct applies the same trivial Kan predicate to P's actual augmentation,
  again including dimension zero.

Dependency declarations read and used:

- `Mathlib.AlgebraicTopology.SimplicialObject.Basic`: `CategoryTheory.SimplicialObject`,
  `CategoryTheory.SimplicialObject.δ`, `.σ`; the recorded functor-category definition.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`;
  this statement only needs the underlying complex/quasi-isomorphism part of that node,
  and consequently introduces no localization-universe assumption.
- `Sheaf.AlgebraicTopology.TrivialKanFibration`: `SSet.Enhanced.trivialKanFibration`, read
  together with the Mathlib family I of boundary inclusions to check n = 0.
- `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`: `MvPolynomial`, `MvPolynomial.aeval`,
  `MvPolynomial.algHom_ext`, already used by the prescribed polynomial construction.
- Added the already landed definition node `def-trf-cotangent-resolution-data` to stmt_deps,
  as authorized by brief-stage2 §5. Its recorded module
  `Sheaf.RingTheory.CotangentResolutionCoherence` supplies `Algebra.CotangentResolution`'s
  `Augmentation`, `standardTerm`, `standardBase`, `standardAugmentation`, `standardFace`,
  `standardDegeneracy`, `IsStandard`, `negativeComplex`, `additiveAugmentation`, and
  `IsPolynomialResolution`. None is copied or redefined. No other field is changed besides
  stmt_deps and lean.
- Plain proof imports include `Sheaf.AlgebraicTopology.SurjectiveQuasiIsoTrivialKan` with
  `CategoryTheory.SimplicialObject.trivialKanFibration_of_surjective_of_quasiIso`;
  `Sheaf.CategoryTheory.AdjunctionStandardSimplicialHomotopy` with
  `CategoryTheory.Adjunction.exists_standardSimplicialHomotopy`;
  `Sheaf.AlgebraicTopology.SimplicialAbelianSetHomotopyQuasiIso` with
  `AlgebraicTopology.quasiIso_alternatingFaceMap_of_underlying_homotopy_equivalence`.
  The first uses integer chain degrees n, while the last uses cochain degrees -n; the proof
  docstring explicitly records the reindexing. All full signatures and docstrings were read.

Source check: read cotangent.tex, definition-standard-resolution (08PM), the first proof of
lemma-pi-shriek-standard (08PT), and remark-resolution (08QI); simplicial.tex,
lemma-standard-simplicial-homotopy (08ND), lemma-qis-simplicial-abelian-groups (08P1), and
lemma-homotopy-equivalence (08P2). They agree with the node and the explicit interfaces.

Edge cases checked before writing: zero B is allowed, as is the identity A → A; no domain
or nonzero condition is introduced. Characteristic two changes the arithmetic of signs but
not the alternating differential definition. At n = 0 surjectivity and the empty boundary
are both retained. At n = 1 the two constant faces cancel; at n = 2 their signed sum is the
identity, giving the required constant-complex parity. Positive degrees are zero by the
actual embedding, rather than by a new hypothesis. Infinite rings and variable sets are
included, and arbitrary ring universes are covered by u (with a common containing universe
for the two rings, as in the existing definition interface).

Searches made (msearch.py Q22 lem-trf-polynomial-augmentation-boundary):

- leanfinder: "standard simplicial polynomial commutative algebra resolution augmentation is
  a quasi-isomorphism and a trivial Kan fibration". Eight hits, headed by
  `SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv`, representation-theoretic
  standard complexes, and Dold–Kan normalization. The extra-degeneracy result requires a
  contraction in a preadditive category, whereas here the contraction is only on sets.
  The representation and normalization statements do not state this polynomial augmentation.
- loogle: "CommAlgCat.free, SimplicialObject.Augmented" returned zero hits (unknown
  identifier CommAlgCat.free); no such free-commutative-algebra adjunction API was presumed.
- grep: "polynomial.*resolution|resolution.*polynomial|toSingle", AlgebraicTopology,
  returned five matches, all in AlternatingFaceMapComplex's actual augmentation definition.
  That definition was read and is used directly in the first conjunct.
- leansearch: "constant augmented simplicial abelian group alternating complex augmentation
  quasi-isomorphism standard polynomial resolution". Eight hits: `ChainComplex.augment`,
  alternating constant complexes, `AlternatingFaceMapComplex.ε`, augmented simplicial
  objects and representation-theoretic resolutions. The existing ε is used, but none gives
  the entire node's assertion.
- loogle: "AlgebraicTopology.AlternatingFaceMapComplex.ε" returned ε and its degree-zero
  and positive-degree component lemmas; all three signatures were read.
- rg in lean/WeilConjectures for polynomial/resolution combinations found graded Koszul and
  affine bounded polynomial resolutions, not the present assertion. The prescribed grep
  for the exact node id in lean/WeilConjectures returned no hits.
- rg in lean/Sheaf found CotangentResolutionCoherence's exact construction and its registered
  definition node. Its existence theorem states much more coherence, not this criterion or
  the constant comparison. We reuse its definitions instead of writing another standard
  polynomial construction. The new theorem name was absent.

Import-graph note for the maintainer: the landed definition node shares its module with the
DOWNSTREAM theorem lem-trf-cotangent-resolution-coherence. Adding the reverse proof import
from that module to this one would close an import cycle. Under stages/2-statements.md §3.7
that automatic proof import must be omitted; the existing shared definitions are reused here.
No upstream file is edited by this delivery.

Validation: scompile.py compiled this module as a private sandbox and as its actual library
module, with no errors or unexpected warnings. The final module is checked again by the
prescribed delivery dry run.

## Second reading by Q22

A separate manual pass reopened the node statement, the delivered signature, and the full
Augmentation/IsStandard/IsPolynomialResolution definitions. It checked all three conjuncts
against the clauses above, especially the constant-to-single map, arbitrary Q without a
polynomial hypothesis, the coefficient-preserving polynomial isomorphisms, and the set-only
inverse and homotopies. It also checked both constant face cancellations and n = 0 boundary
lifting. No hypothesis or conclusion mismatch was found. This is the worker's second pass;
the maintainer supplies the independent review required by this dispatcher assignment.
