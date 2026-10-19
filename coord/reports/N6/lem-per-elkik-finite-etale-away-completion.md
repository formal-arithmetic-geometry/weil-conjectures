## Worker report

The module `Sheaf.RingTheory.ElkikFiniteEtaleAwayCompletion` states
`CommRingCat.elkik_finiteEtaleAway_completion` with its sole theorem proof `sorry`.
Its auxiliary definition `CommRingCat.finiteEtaleAwayProperty` specifies the objects
of the two categories in this very statement; it is a predicate with real data,
not a separate mathematical input or a new independent notion. The definition
and theorem both carry this node's blueprint identifier and source.

The previous worker's stale-assignment diagnosis concerned stage 1: N0's merge
split this node and its proof inputs. The current node is `split`, without a
`lean` record; this delivery does stage 2 and does not split it again.

The source was read directly in ILO, Exposé V, Theorem 1.2.4, printed p. 64
(PDF page 70). It gives an equivalence for finite schemes étale over the open
complement of the completion centre. Passing to affine coordinate algebras
reverses both categories and gives precisely the algebra statement in this node.
No statement correction is needed.

Hypothesis and clause correspondence:

- A commutative ring B: `(B : CommRingCat.{u})`; its carried ring is commutative.
- Noetherian: `[IsNoetherianRing B]`.
- An ideal I of B: `(I : Ideal B)`.
- A henselian pair: `[HenselianRing B I]`, the dependency's recorded Mathlib
  henselian-pair notion. This is the root-lifting form equivalent to the node's
  finite-algebra idempotent criterion, as its dependency record documents.
- The completion B̂: `AdicCompletion I B`, with its actual canonical B-algebra
  instance from `Mathlib.RingTheory.AdicCompletion.Algebra`. No arbitrary
  completion model or map is introduced.
- Commutative B-algebras C and B-algebra homomorphisms: `Under B`.
  Its objects are ring maps B → C, its morphisms are commuting ring maps;
  `CommRingCat.toAlgHom` is the explicit algebra-hom interpretation.
- Finite as B-modules: `Module.Finite B C` in `finiteEtaleAwayProperty`.
- Étale over Spec B minus V(I): `Etale (Spec.map C.hom ∣_ U)`, with U the open
  `(PrimeSpectrum.zeroLocus (I : Set B))ᶜ`. The open proof is the actual
  complement of a closed zero locus. `morphismRestrict` restricts both source
  and target, so points above V(I) are unrestricted.
- The source category: `(finiteEtaleAwayProperty B I).FullSubcategory`;
  `ObjectProperty.FullSubcategory` retains all morphisms of `Under B`.
- The analogous target category: the same property and full-subcategory
  construction for `.of (AdicCompletion I B)` and
  `I.map (algebraMap B (AdicCompletion I B))`, exactly the extended ideal IB̂.
- The functor C ↦ B̂ ⊗[B] C: the existing
  `CommRingCat.tensorProd B (.of (AdicCompletion I B))`. Its definition's object
  is `mkUnder B̂ (B̂ ⊗[B] C)`, with the left tensor-factor B̂-algebra structure;
  its morphism is `Algebra.TensorProduct.map (AlgHom.id B̂ B̂) (toAlgHom f)`.
  Composing with the source inclusion and applying the target's
  `ObjectProperty.lift` restricts this exact functor.
- Well-definedness is asserted by `∃ h : ∀ C, targetProperty (tensorProd.obj C.obj), ...`
  in the conclusion. It is not assumed. The proof h changes no data: `lift`
  uses it only as the property field of the target full-subcategory objects,
  while the tensor functor supplies every object and every morphism.
- Equivalence: `.IsEquivalence` on this restricted canonical tensor functor.
- The particular algebraization conclusion: `∀ E` in the target full
  subcategory, `∃ C` in the source full subcategory,
  `Nonempty (tensorProd.obj C.obj ≅ E.obj)`. An isomorphism in `Under B̂`
  consists of mutually inverse B̂-algebra homomorphisms, exactly an isomorphism
  of the B̂-algebras in the node. The isomorphism is allowed to be noncanonical,
  as in the source; the base-change functor is fixed canonically.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`; its docstring says all ideals are finitely generated.
- `def-weil-pbc-henselian-terminology`: `HenselianRing`,
  `Mathlib.RingTheory.Henselian`, reexported by the recorded
  `WeilConjectures.Mathlib.RingTheory.Henselian` module. The recorded module's
  `IsStrictlyHenselianLocalRing` and the `HenselianLocalRing` signatures were
  also read; their stronger local hypotheses are not used here.
- `def-weil-pbc-adic-completion`: `AdicCompletion`,
  `Mathlib.RingTheory.AdicCompletion.Basic`, imported through `.Algebra`.
  The compatible-sequence definition and its canonical ring/algebra instances were read.
- `def-weil-finitely-generated-module`: `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs`, defined by finite generation of the top submodule.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`, imported through `.Morphisms.Etale`.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`, its actual affine-local definition.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`,
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, the quotient by bilinearity relations,
  used by the actual `CommRingCat.tensorProd` construction in
  `Mathlib.Algebra.Category.Ring.Under.Basic`.

The already-stated proof dependencies are imported without `public`, using
their recorded modules or Mathlib matches: étale base change and composition,
completion as tensor product, finite-type Noetherianity, integrality of finite
algebras, integral henselian-pair permanence, Noetherianity and completeness of
completion, quotients modulo ideal powers, affine permanence, affine-proper-finite,
and the closed-embedding-affine criterion. The four unstated proof inputs
`lem-per-etale-away-completion-hom-lifting`,
`lem-per-completed-etale-jacobian-torsion`,
`lem-per-rig-etale-jacobian-algebraization`, and
`lem-per-henselian-pair-proper-clopen-lift` have no recorded Lean modules and
therefore cannot be imported yet; none is needed to type the statement.
The theorem docstring gives all six proof steps of the node, with the input names.

Edge cases checked before writing:

- I = 0: V(I) is the whole spectrum, so the étale condition is on the empty
  open and places no restriction on finite algebras. Completion along zero
  is B, so the equivalence specializes to the identity situation.
- Nilpotent I: the same empty complement is retained, and completion is B;
  no reducedness or separation hypothesis is imposed.
- The zero ring and zero algebra are admitted. No `Nontrivial`, `IsDomain`,
  local-ring, characteristic, or nonempty-spectrum assumption appears.
- I = ⊤ for nonzero B is excluded by the actual henselian-pair Jacobson
  condition, not by an extra hypothesis of this statement. The zero-ring case remains.
- Ramified or nonreduced finite algebras on V(I) are included; the restriction
  is only to its open complement, not a global `Algebra.Etale B C` assumption.
- Universes: for every u, all rings/algebras use `CommRingCat.{u}` and all
  categories are its full algebra categories. There is no separately smaller
  universe of test algebras and no extra universe equality hypothesis.

Searches made before writing:

- `msearch.py ... leanfinder "Elkik equivalence finite algebras etale away from henselian ideal and its adic completion"`:
  eight hits, including `StandardEtalePresentation`, `Algebra.IsEtaleAt`, and
  ordinary étale finite-presentation lemmas; none is Elkik's equivalence.
- `msearch.py ... loogle "CommAlgCat.baseChange, HenselianRing, AdicCompletion"`:
  zero hits; `CommAlgCat.baseChange` is unknown. The base-change functor was
  subsequently found by reading the Mathlib category sources, not duplicated.
- `msearch.py ... grep "Elkik|etale.*[Aa]way|[Aa]way.*[Cc]ompletion"`:
  22 hits on ordinary local étale presentations and localizations; no completion equivalence.
- `rg` on the upstream `WeilConjectures` and project `lean/Sheaf` for
  `Elkik|elkik|finiteEtaleAway|FiniteEtaleAway|lem-per-elkik-finite-etale-away-completion`:
  no upstream match; the side project has unrelated Popescu proof references
  and the Gabber partial-algebraization proof's citation of this unstated theorem.
- Further Mathlib category-source searches for base change and tensor functors
  found `CommRingCat.tensorProd` in `Algebra/Category/Ring/Under/Basic.lean`;
  its complete object/map construction and `tensorProdIsoPushout` were read.
  `FiniteEtale.baseChange` was also found, but requires global étaleness and
  therefore cannot represent these categories.
- `rg` for `FiniteEtaleAway|finiteEtaleAway|etaleAway|EtaleAway` across the DAG,
  project, and upstream found only unrelated étale-near-prime declarations.
  No existing declaration states this equivalence or names these categories.

Validation: the prescribed `scompile.py N6 lem-per-elkik-finite-etale-away-completion`
compiled the delivered file cleanly, both as sandbox and library module (2.3 seconds each).
There is one named theorem, with its whole proof `sorry`; the auxiliary definition has
no postponed data or proofs. No statement dispute, dependency repair, or new node is needed.

## Second reading by N6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
