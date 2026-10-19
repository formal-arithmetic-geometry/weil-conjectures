## Worker report

The module `Sheaf.TraceFormula.AlgebraicShriekCalculus` states
`AlgebraicGeometry.nonempty_algebraicShriekCalculus`. Its sole postponed theorem is this
existence theorem. The structure packages witnesses instead of choosing a functor from a
sorry-backed existence statement. Its auxiliary definitions have actual data. All auxiliary
names belong to the calculus of this node, rather than an independent mathematical notion.

The source was read in `literature/stacks-project/dualizing.tex`: the construction in
`section-relative-dualizing-complex-algebraic`, and `lemma-right-adjoint`,
`lemma-RHom-ext`, `lemma-composition-right-adjoints`, `lemma-well-defined`, `lemma-flat-bc`,
`lemma-composition-shriek-algebraic`, and `lemma-upper-shriek-localize`. The node's longer
unbounded open-immersion proof is preserved in the theorem docstring. In particular the
composition proof uses Q'=B[y] in the B-scalar extension, as the node corrects the source's
printed Q. No statement correction is needed.

Hypothesis and clause correspondence:

* Commutative rings are `CommRingCat.{u}`. This bundles the `CommRing` instances without
  changing the objects; `u` is arbitrary. `algebraicShriekD R` is literally Mathlib
  `DerivedCategory (ModuleCat.{u} R)`, using `HasDerivedCategory.standard` in universe u+1.
  No existence of unusually small derived Hom sets is assumed.
* The standing Noetherian hypotheses are `[IsNoetherianRing R] [IsNoetherianRing A]` on
  `shriek` and the relevant comparison fields. Finite type is `RingHom.FiniteType φ`.
* `shriek φ hφ` is a functor D(R) → D(A). A single existence package allows comparisons
  involving different ring maps to refer to the same functors. The choice of witnesses is
  not made by a definition in this delivery.
* A chosen polynomial presentation is universally quantified in `polynomialModel`: n : ℕ,
  `p : MvPolynomial (Fin n) R →+* A`, `Function.Surjective p`, and the equation
  `p.comp MvPolynomial.C = φ`. This is precisely an R-algebra presentation, expressed
  without installing a separate `Algebra R A` instance.
* The model is the functor `extension MvPolynomial.C ⋙ coinduction p ⋙ shiftFunctor _ n`.
  Thus its value is RHom_P(A,K ⊗ᴸ_R P)[n]. `extensionAdj` characterizes derived scalar
  extension as left adjoint to the actual exact restriction of scalars. This characterizes
  the usual derived tensor functor up to its adjunction-compatible isomorphism; it is not
  an unconstrained substitute functor. Derived change of rings on module sheaves supplies
  this scalar extension after the one-object ringed-site identification used in the DAG.
* `polynomialModel` provides a natural isomorphism for EVERY presentation, not merely
  an isomorphism on individual objects. Two presentations compare through the same
  `shriek φ hφ`; no orientation or equality independent of polynomial coordinates is
  asserted.
* Clause (i), surjections: `surjection` gives `shriek φ hφ ≅ coinduction φ`.
  `coinductionAdj` is the right adjunction to `(ModuleCat.restrictScalars φ).mapDerivedCategory`.
  `coinductionModel` supplies the K-injective model for every K-injective I, not a
  bounded-injective special case. Its target is Q of the termwise Mathlib
  `ModuleCat.coextendScalars φ`, literally Hom_R(A,I) with the natural A-action.
  Mathlib's `CoextendScalars.smul_apply` reads `(a • h) a' = h (a' * a)`.
  Applying derived restriction and its `mapDerivedCategoryFactors` forgets the action
  and gives Q of the ordinary Hom_R(A,I) complex, exactly the ordinary RHom in 0A71.
  The equation in `coinductionModel` compares the derived counit with Q of the actual
  termwise restriction/coinduction counit, which is evaluation at 1. No second
  definition of RHom is introduced.
* Arbitrary-ring coinduction composition is `coinductionComp`. Its R,B,C binders carry
  no Noetherian, finite-type, surjectivity, flatness or boundedness hypotheses.
  The isomorphism is a natural isomorphism of functors. The equation uses the actual
  restriction-composition isomorphism and equates the two successive evaluation
  counits with the composite-map counit; uniqueness of right adjoints determines the
  canonical comparison with that equation.
* Clause (ii) is `composition`, with Noetherian R,B,C, finite-type a,b,
  and `∃ n : ℤ, K.IsGE n` as precisely K ∈ D⁺(R). The composite
  finite-type proof is supplied directly by `hb.comp ha`.
  The target is composite-map shriek in D(C). The identity field compares
  the actual identity-map shriek with the identity functor; its finite-type proof
  is provided directly by `RingHom.FiniteType.id`.
* Clause (iii) is `flatBaseChange`: R,R' are Noetherian, φ is finite type and ρ is flat.
  `algebraicShriekBaseRing φ ρ` is literally `A ⊗[R] R'`, with algebra structures
  induced by φ and ρ in the definition. `algebraicShriekBaseLeft` is a ↦ a tensor 1,
  and `algebraicShriekBaseRight` is r' ↦ 1 tensor r'. The latter is the actual φ'.
  The displayed isomorphism is in D(A') and has precisely the two tensor expressions
  in the node, for `∃ n, K.IsGE n`. The A' Noetherian instance and finite-type proof
  are supplied internally by `algebraicShriekBaseNoetherian` and
  `algebraicShriekBaseFiniteType`, direct instantiations of existing Mathlib
  finite-type stability and the finite-type-algebra Noetherian theorem. No extra
  hypotheses on the base change are exposed to the caller.
* Clause (iv) is `openImmersion`, with the recorded Mathlib predicate
  `IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))`. It compares the entire shriek
  functor with derived scalar extension. There is no boundedness hypothesis here.

Dependency declarations and imports:

* `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`. Its size convention is
  implemented with the standard u+1 localization.
* `def-pur-derived-internal-hom`: the recorded
  `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`,
  `CategoryTheory.derivedInternalHomOfUniverses`, is imported. The ordinary-module
  first argument A[0] used here is concretely described by the Hom model under
  restriction, not replaced by a new derived internal Hom construction.
* `lem-pur-derived-change-of-rings`: the recorded
  `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`,
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`, is imported. Its universal
  scalar-extension functor transports to the module scalar extension characterized
  here by its tensor/restriction adjunction. Its cochain/K-flat model remains the
  proof input; this delivery does not rewrite its ringed-site interface.
* The remaining statement dependencies are exactly Mathlib `IsNoetherianRing`,
  `RingHom.FiniteType`, `MvPolynomial`, `RingHom.Flat`, `Spec`, `Spec.map`, and
  `IsOpenImmersion`, from their recorded modules (read in the pinned source).
* Ordinary coinduction and its action are the existing Mathlib `coextendScalars`,
  `CoextendScalars.equiv`, `CoextendScalars.smul_apply`, and
  `restrictCoextendScalarsAdj` in `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`.
* The recorded stated proof dependencies are imported without `public`; the two
  newly split, unstated proof inputs `lem-trf-perfect-algebra-coinduction-tensor`
  and `lem-trf-pseudocoherent-rhom-flat-base-change` have no module to import.

Edge cases checked: n=0 is admitted by `Fin 0` and integer shift 0. Both factors in
composition may have zero generators. Zero rings are allowed throughout: no
`Nontrivial` hypotheses occur, so the empty open and zero target category are
included. The open-immersion clause admits unbounded K, whereas (ii) and (iii)
explicitly require only a lower bound. Arbitrary-ring coinduction is unbounded and
has no Noetherian assumption. The identity field is an isomorphism with the actual
shriek functor, not an identity-isomorphic-to-itself tautology. Flat base change
uses the tensor product with the specified maps, not an arbitrary ring or square.

Searches for a matching existing declaration:

* `msearch.py leanfinder "Algebraic upper shriek polynomial presentation derived
  coinduction composition flat base change"`: eight hits on ordinary algebra
  presentations and their base change; none on the derived polynomial calculus.
* `msearch.py loogle "ModuleCat.coextendScalars, ModuleCat.restrictCoextendScalarsAdj"`:
  the ordinary restriction/coinduction adjunction was found and its full source
  read. It is used rather than duplicated; it is not the derived calculus.
* `msearch.py grep "coinduction|upperShriek|algebraicShriek|coextendScalars" Algebra`:
  seven hits, ordinary coextension and enough-injective modules; no derived calculus.
* `msearch.py leansearch "right adjoint derived restriction of scalars coinduction
  ring polynomial upper shriek"`: eight hits, ordinary scalar restriction and
  representation coinduction, no polynomial upper-shriek comparison.
* `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, the Mathlib source,
  `dag/lean_names_upstream.json` and `lean/Sheaf` found no occurrence of this node's
  id or proposed declarations. Broader searches for `coinduction`, `upperShriek`,
  `relativeDualizing` found sheaf/étale six-functor constructions, not this algebraic
  construction. Ordinary coextension was found and reused as described above.

## Second reading by Q93

Author's self-check, following the dispatcher's prohibition on starting other agents;
the maintainer supplies the independent review. I reopened the node and the source
and checked the statement clause by clause as above. The initial development draft
was rejected during this self-check: it lacked the lower-bound composition clause,
constrained arbitrary-ring composition to Noetherian rings, had an identity tautology,
and did not fix the tensor-product base change or the coinduction counit. The delivered
interface replaces all of those drafts. The polynomial model now holds naturally for
every presentation; the open-immersion clause has no bound. Only the final existence
theorem is postponed, with the node's thirteen-step proof in its docstring. No data
is extracted from it, and no original node field other than `lean` is changed.
