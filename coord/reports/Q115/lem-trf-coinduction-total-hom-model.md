## Worker report

The module `Sheaf.Algebra.Homology.CoinductionTotalHomModel` states
`ModuleCat.coinduction_total_hom_model`, with a single postponed proof. It introduces
no definitions, auxiliary axioms, new nodes, or dependency repairs. The node's
statement, statement dependencies, proof and proof dependencies are unchanged.

Source read: `literature/stacks-project/dualizing.tex`, labels
`lemma-right-adjoint` (0A70) and `lemma-RHom-ext` (0A71), including their preceding
construction and proofs; `derived.tex`, `definition-K-injective` (070H).
The expanded eight-step proof is retained in the theorem docstring.

Clause-by-clause correspondence:

- The commutative rings and their map are `{P A : Type u} [CommRing P]
  [CommRing A] (φ : P →+* A)`. Both rings can always be placed in a common
  universe; there is no characteristic or nontriviality restriction.
- Unbounded cochain complexes are `CochainComplex (ModuleCat.{u} P) ℤ` and
  `CochainComplex (ModuleCat.{u} A) ℤ`, without support predicates. Ordinary
  modules are precisely the ordinary-module presentation of sheaves on the
  one-object identity-cover ringed site mentioned by the node.
- The existing product total Hom is `CochainComplex.moduleHomComplex`.
  Its degree-n elements are Mathlib's `HomComplex.Cochain`, indexed by all
  triples `(p,q,hpq : p+n=q)` and containing arbitrary families of linear
  maps. Thus the quantifiers on cochains impose no finite-support condition.
- `U` is the termwise functor `(restrictScalars φ).mapHomologicalComplex (.up ℤ)`.
  `J` is the termwise functor `(coextendScalars φ).mapHomologicalComplex (.up ℤ)`.
  These are used directly, without private copies or a second construction.
- The first conjunct is the displayed A-action `(a • h) b = h (b * a)`.
  The second states that the differential is postcomposition with `I.d p q`.
  The third identifies the underlying P-complex of J(I) with the existing
  `moduleHomComplex` from A[0], where A as a P-module is
  `(restrictScalars φ).obj (ModuleCat.of A A)` and degree-zero concentration
  is `CochainComplex.singleFunctor ... 0`. The isomorphism records precisely
  that the product definition has only its p=0 factor in this case.
- The fourth conjunct is an existential family `T E I` of isomorphisms
  of P-module complexes with exactly the source and target in the node.
  Its first two clauses specify `((T E I).hom.f n z).v p q hpq x = z.v ... x 1`
  and `((T E I).inv.f n z).v ... x a = z.v ... (a • x)` for every integer n,
  every factor p,q, and every input. Existence is only asserted by the theorem;
  no definition chooses unspecified data from it.
- The next two clauses give both Hom differential identities explicitly,
  using `δ n m`. In adjacent degrees its formula is
  `d_target z - (-1)^n z d_source`; in other degrees both sides vanish.
  `T E I` being an actual complex isomorphism also contains the inverse laws
  and chain-map commutation.
- Naturality under simultaneous precomposition α and postcomposition β is
  the next clause, expressed through `Cochain.ofHom` and `Cochain.comp`.
  The left side is T(J(β) z α); the right side is β T(z) U(α).
  Setting either chain map to an identity gives each individual naturality
  identity. The inverse's naturality follows by applying the inverse T.
- The final two clauses inside the T existential take genuine `Homotopy f g`
  and state that the image of `Cochain.ofHomotopy h` has differential equal
  to the difference of the transposed degree-zero cochains. This is exactly
  the homotopy equation in the node, both for T and its inverse, with no
  claim restricted to homotopy classes.
- The next outer conjunct states that J also takes a homotopy k between β,β'
  to `H : Homotopy (J.map β) (J.map β')`, with the degreewise formula
  `(H.hom p q h) a = k.hom p q (h a)` from the node's fifth proof step.
- K-injective preservation is the implication `I.IsKInjective → (J.obj I).IsKInjective`.
  No injectivity hypothesis is required by the preceding Hom-complex clauses.
- The final conjunct quantifies over any K-injective I, any
  `Y : DerivedCategory (ModuleCat.{u} P)`, and any representing isomorphism
  `DerivedCategory.Q.obj I ≅ Y`. It asserts an isomorphism in the derived
  category from `Q.obj (U.obj (J.obj I))` to
  `(ordinaryModuleDerivedInternalHom P).obj (op (Q.obj A[0]), Y)`.
  This uses the recorded ordinary-module derived internal Hom, not a second
  derived coinduction definition or an unspecified bifunctor. The actual
  A-action on its chosen representing complex was specified in the first
  conjunct. Nothing restricts I to a fixed functorial replacement.
- There are no boundedness, flatness, finiteness or Noetherian binders.

Dependency declarations read and used:

- `WeilConjectures.Algebra.Homology.ModuleHomComplex`:
  `CochainComplex.moduleHomComplex` and its full terms/differential.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`, with its null-homotopy condition;
  Mathlib `Homotopy`, `HomComplex.Cochain.ofHomotopy` and `HomComplex.δ`
  give the stated homotopy equations. The dependency is a Mathlib match and
  does not require a separate Lean record or specialization module.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory` and `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`:
  `CategoryTheory.ordinaryModuleDerivedInternalHom`, the recorded existing
  ordinary-module presentation of the K-injective-derived internal Hom.
  Its publicly imported generic ringed-site interface remains available.
- `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`:
  `ModuleCat.restrictScalars`, `ModuleCat.coextendScalars`, their component
  actions, and `ModuleCat.restrictCoextendScalarsAdj`. These supply actual
  termwise constructions. Zero-morphism preservation is already available;
  no additional additivity or exactness hypothesis was introduced.

Edge cases checked before drafting: identity P→P (usual evaluation from P[0]),
the zero ring A (both sides vanish), zero E or I, the nonflat quotient
ℤ→ℤ/2, and cochain degrees -1, 0 and 1. Restriction is exact for the nonflat
quotient as well; the argument uses unchanged underlying groups. In degree -1,
`-(-1)^(-1)=+1`, so δ gives dh+hd as required for homotopies. Full products,
unbounded complexes and arbitrary characteristics remain admitted. The chosen
common universe does not force an independent smaller test universe or exclude
any rings/modules after raising to a common universe.

Searches for an existing whole statement (through the prescribed msearch wrapper):

- LeanFinder: "Restriction and coinduction give an isomorphism of total Hom
  complexes by evaluation at one and preserve K-injective complexes". Eight hits,
  including `CochainComplex.isKInjective_of_iso` and complex restriction
  isomorphisms. None states the total-Hom transposition and all its clauses.
- Loogle: "ModuleCat.restrictScalars, ModuleCat.coextendScalars". Twelve hits,
  including `restrictCoextendScalarsAdj`, `HomEquiv.fromRestriction`,
  `HomEquiv.toRestriction` and `CoextendScalars.equiv`. Read their signatures,
  docstrings and implementation: these are module-level constructions, reused
  here, rather than the theorem about unbounded total Hom complexes.
- Mathlib grep: "coextend|coinduc|IsKInjective" in `Algebra/Homology`. Hits give
  K-injectivity, homotopy equivalences and unrelated coinductive homotopies,
  without the requested coinduction theorem.
- LeanSearch: "Total Hom complex restriction coinduction adjunction with
  evaluation at one preserves K-injective complexes". Eight hits include
  representation coinduction, the K-injectivity definition and homology limits;
  none is this statement.
- Project rg: `coinduc|coextend|restrictCoextend|ordinaryModuleDerivedInternalHom`
  in the project algebra/homology and paper modules, and
  `coinduction|coextendScalars|restrictCoextend` in upstream algebra modules.
  Existing downstream modules `DerivedCoinductionAdjunction`,
  `AlgebraicShriekDerivedHomAdjunction`, and `PerfectAlgebraCoinductionTensor`
  use these same ordinary coextension constructions, but their theorems have
  different derived adjunction/perfect-tensor statements and do not state
  all clauses of this node. We use Mathlib's actual termwise construction
  directly to avoid an import dependency on a downstream consumer.
- Project rg for `lem-trf-coinduction-total-hom-model` in `lean/WeilConjectures`
  and for `coinductionTotalHom|total_hom.*coind|coinduction.*total` in
  `lean/Sheaf`: no existing declaration of this item or name collision.

No statement fault or disputed statement was found.

## Second reading by Q115

The dispatcher forbids other agents, so this is a second pass by the same worker;
the maintainer's delivery review is independent. Re-read the original node and the
final signature with the source and dependency declarations open. The ring-map
binders, unrestricted ℤ complexes and all four recorded dependencies agree.
Checked the first three conjuncts against the definition J(I)=Hom_P(A[0],I),
its action and differential. Checked the T and S formulas at each factor,
and the order of the α and β compositions in the naturality identity.
Checked both homotopy equations against `δ_ofHomotopy` and the separate J(k)
formula against the node's fifth proof step. The K-injective implication is
separate from the unconditional comparison, and the final derived isomorphism
uses the existing ordinary-module RHom and any representative of Y.
The first compiler pass required explicit `CoextendScalars.equiv φ (I.X q)`
to present coextended elements as linear maps; all evaluation formulas now use
that existing equivalence. Also replaced field notation on the inferred
`HomologicalComplex` by the fully qualified `CochainComplex.IsKInjective`.
These were elaboration changes and do not alter any mathematical clause.
No mathematical mismatch was found; no node correction or dependency repair
was needed. No helper definition or extra postponed theorem was introduced.

Validation: final `scompile.py Q115 lem-trf-coinduction-total-hom-model`
compiled both sandbox and library module cleanly (33.6 s and 16.2 s), with
no errors or warnings. Only the named theorem has a `sorry` proof.
