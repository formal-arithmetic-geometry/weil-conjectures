## Worker report

Item: `lem-sfb-simplicial-algebra-shuffle-normalization`. Delivered module:
`Sheaf.AlgebraicTopology.SimplicialAlgebraShuffleNormalization`; principal declaration:
`AlgebraicTopology.SimplicialAlgebraShuffleNormalization.exists_shuffle_normalization`.
The theorem is the sole postponed proof. Every helper definition has real data. No node
statement, dependency list, proof plan, source, or other existing field was changed.

The theorem asserts existence of the specified normalization functor, rather than
choosing an arbitrary replacement. Its term identifications and the quotient-component
equation force the differential and natural maps; its representative multiplication
equation forces exactly the displayed shuffle. This is an existence statement about the
canonical construction, with no subsequent definition made by choosing an unconstrained object.

Clause-by-clause correspondence (names in the module's namespace):

- Commutative ring D: `variable (D : Type u) [CommRing D]`. Simplicial commutative
  D-algebra: `P : SimplicialObject (CommAlgCat.{v} D)`. There are no extra assumptions
  on characteristic, flatness, an augmentation, or nontriviality.
- Independent universes: u for D and v for P's carriers. `modules` sends E to
  `ModuleCat.of (ULift.{v} D) (ULift.{u} E)` and maps x to the lift of f(x.down).
  Scalars act by their down projection. This is canonical scalar transport, with
  underlying D-linear equivalence to E; no equality u=v is imposed. Integer cochains
  and their tensor products live at max u v. The flatness conclusion explicitly
  restricts scalars along `ULift.ringEquiv.symm : D ≃+* ULift.{v} D`.
- C(P)^(-n)=P_n, alternating differential, zero positive terms and zero differential
  out of zero: `chains` composes the existing alternating-face functor with
  `ComplexShape.embeddingDownNat.extendFunctor`; `chainsTerm` is its canonical
  negative-degree term isomorphism. The extension sends n to -n and is zero elsewhere.
- J_0=0 and J_n the sum of degeneracy images: `degenerates` is bottom at zero and
  `iSup` of `LinearMap.range (P.σ i).hom.toLinearMap` over `Fin (n+1)` at n+1.
  The supremum of these submodules is exactly their sum. No ordinary ideal is used.
- P_n/J_n: `quotient`. The binder `e P n` identifies the normalization's degree -n
  with the canonical lift of this quotient module. The first conjunct says that
  `q.app P` is the actual quotient map, under `chainsTerm` and e. Since q is a chain
  map and its components are surjective, this fixes the quotient differential.
  The third conjunct makes every positive cochain term zero.
- Displayed multiplication: `shuffle D P p q x y` sums over the existing finite
  `SimplexLatticeShuffle.LatticePath p q`. Its two monotone coordinate maps are
  A_k=#(μ below k) and B_k=#(ν below k). Their repeated edges are ν and μ,
  respectively, so P(A)x and P(B)y are the exact degeneracy strings in the node.
  The existing `pathSign` counts vertical-before-horizontal inversions, exactly the
  sign of the increasingly listed μ block followed by ν. The fourth conjunct
  equates `mul` of any quotient representatives with the class of this sum. Because
  the multiplication is defined on quotient objects, this also states well-definedness.
- Associative, unital, graded-commutative dg D-algebra and Leibniz: the functor N
  lands in `CommMon (CochainComplex (ModuleCat (ULift D)) ℤ)`. `MonObj` is the same
  monoid-in-complexes notion used by the recorded `DgAlgebra.Algebra` interface,
  here with D-linear coefficients instead of integral coefficients. Associativity
  and unity are its monoid laws; multiplication being a chain map is the signed
  Leibniz identity; `IsCommMonObj` uses the Koszul braiding furnished by the imported
  upstream cochain monoidal API, giving (-1)^(pq) in degrees -p,-q. Linearity supplies
  the central D-action. No independent dg-algebra definition is introduced.
- Unit [1]: `unit`, the degree-zero component of `MonObj.one` applied to 1, is
  equated to `(e P 0).inv (ULift.up (Submodule.Quotient.mk 1))` in conjunct five.
- Functoriality in all simplicial D-algebra maps: N is a functor into dg algebras,
  and q is a natural transformation from `chains` to its underlying-complex functor.
  The quotient-component equation forces N.map to be the usual induced quotient map.
- Natural quotient quasi-isomorphism: q is natural and conjunct two says
  `QuasiIso (q.app P)` for every P, with no flatness assumption.
- Direct summand in every degree: conjunct six supplies a D-linear section s of the
  actual quotient map with `(degenerates D P n).mkQ.comp s = LinearMap.id`.
- Flatness consequence: conjunct seven assumes `∀ n, Module.Flat D P_n` and asserts
  flatness of every integer-degree term of N, including the zero positive terms,
  after the canonical scalar restriction described above.
- Constant D and, more generally, constant E: `constant`, `degreeZero`, and the
  isomorphisms c identify N(const E) with E[0]. The explicit degree-zero equation
  sends [x] to x (both canonically lifted); the zero terms force its other components.
  The (0,0) shuffle formula gives ordinary multiplication, and the specified unit
  gives 1, so this is the canonical dg-algebra identification. Taking v=u and E=D
  gives exactly N(D)=D[0], including when the original D and input carrier universes
  elsewhere differ. The theorem includes every constant algebra in its input universe.
- Augmentation: ε is any simplicial D-algebra map P→constant E. The maps a E have
  degree-zero component the identity under `chainsTerm` and `degreeZeroTerm`; their
  targets are concentrated at zero, so they are the canonical C(const E)→E[0].
  The next two equations assert q/constant compatibility and the factorization
  `q_P ≫ N(ε) ≫ c_E = C(ε) ≫ a_E`. The final implication is precisely that if
  C(P)→E[0] is a quasi-isomorphism, then its induced normalized augmentation is too.
  N(ε) is a dg-algebra map by its codomain, and c_E respects the ordinary algebra
  structure by the preceding constant identification.

Dependency declarations read and used:

- `Mathlib.AlgebraicTopology.SimplicialObject.Basic`:
  `CategoryTheory.SimplicialObject`, `.δ`, `.σ`; functor and operator signatures read.
- `Sheaf.CategoryTheory.DgAlgebraDerivedCategory`:
  `CategoryTheory.DgAlgebra.Complex`, `.Algebra` and the defining monoid-in-complexes
  docstrings. Its public upstream monoidal import supplies the Koszul braiding.
  Mathlib `CommMon`, `MonObj.mul`, `MonObj.one`, and `IsCommMonObj` provide exactly
  the coefficient-general version of the same definition; the derived localization
  itself is not needed to state this normalization theorem.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, and
  `Mathlib.RingTheory.Flat.Basic`: `Module.Flat` and `Module.Flat.of_retract`.
- Proof import `Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence`:
  `AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex`;
  also read `NormalizedMooreComplex.objX`, `.objD`, and `.obj` (positive-face kernels).
- Proof import `Mathlib.Algebra.Homology.Homotopy`:
  `Homotopy.homologyMap_eq` and `CategoryTheory.Functor.mapHomotopy`.
- `Sheaf.AlgebraicTopology.SimplexLatticeShuffleBoundary`:
  `AlgebraicTopology.SimplexLatticeShuffle.LatticePath`, `.pathSign`, and
  `.shuffle_boundary_augmentation_naturality`; read the full helper definitions and
  statement. The first two are also used by the actual shuffle formula, hence public import.
- `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`:
  `HomologicalComplex.homology`, available through the dg-algebra module; the
  homology/quasi-isomorphism convention is the dependency's existing one.
- Additional existing APIs: `ComplexShape.embeddingDownNat`,
  `HomologicalComplex.extendXIso`, `HomologicalComplex.singleObjXSelf`,
  `ModuleCat.restrictScalars`, and `ULift.ringEquiv`.

Source reading: Stacks `simplicial.tex` at lemma-splitting-abelian-category,
lemma-decompose-associated-complexes, remark-degenerate-subcomplex and
lemma-quasi-isomorphism; the latest blueprint direct-images proof paragraph (3).
The blueprint is only the application, as the node honestly records; no assertion
that Stacks proves the shuffle algebra structure is made. The theorem docstring
carries all thirteen steps of the node's proof, naming its non-elementary inputs.

Edge cases checked: n=0 has J=bottom and zero outgoing differential; p=q=0 has one
path of sign +1 and gives ordinary multiplication. For (0,q) or (p,0), the empty
coordinate string is the identity and the unit computation applies. For p=q=1,
the sum is s_1(x)s_0(y)-s_0(x)s_1(y), agreeing with the stated sign convention.
Constant E has J_n=top for n>0 because a degeneracy is the identity. Both zero and
nonzero rings and all characteristics are included. No division or assumption about
2 is used. Arbitrary independent ring/carrier universes survive the scalar transport.
No false or ill-typed clause was found; no STATEMENT-DISPUTED flag is needed.

Searches performed through msearch.py and direct rg (raw msearch results are in the
sandbox's searches.jsonl):

- LeanFinder, `Normalization of a simplicial commutative algebra has an associative
  unital graded commutative shuffle product`: eight graded-tensor-product hits;
  none states normalization with its shuffle algebra structure.
- Loogle, `"shuffle"`: zero hits.
- LeanSearch, `The normalized complex of a simplicial commutative algebra has the
  shuffle multiplication`: eight hits, including NormalizedMooreComplex.obj,
  DoldKan.N₁ and Idempotents.DoldKan.N; these are additive normalization only.
- msearch grep, `shuffle|Shuffle|normalizedMooreComplex`, AlgebraicTopology:
  25 hits, additive Moore and Dold–Kan constructions, no whole-statement match.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for shuffle/Shuffle and
  simplicial-algebra wording found the existing simplex lattice shuffle and
  bicosimplicial totalization helpers, plus unrelated tensor reordering. Neither
  is this statement. The full lattice-boundary source was read and reused.
- Direct rg for the item id in `lean/WeilConjectures` found nothing; rg for
  `SimplicialAlgebraShuffleNormalization|exists_shuffle_normalization` in Mathlib,
  WeilConjectures, Sheaf and `dag/lean_names_upstream.json` found no declarations.

Validation: scompile.py compiled both its module-mode sandbox check and the module
itself cleanly (43.2 s and 33.7 s). The initial compile errors in finite-path inference,
SimplexCategory map construction and module universes were repaired; no compiler
warning remains. No global build or direct shared-repository write was performed.

## Second reading by Q29

I reread the unchanged node and the final module clause by clause in a separate pass.
The quotient equation fixes the maps and differential; the shuffle equation quantifies
over all representatives; CommMon fixes associativity, unity, signed commutativity and
Leibniz, rather than merely asserting an unrelated algebra exists. I checked the sign
on (1,1) and empty strings, the section equation's direction, and the augmentation
factorization's order. The constant comparison is an actual complex isomorphism with
its degree-zero normalization, so it is canonical and multiplicative by the (0,0)
formula. I also checked that the universe repair transports coefficients canonically,
rather than imposing equality of ring and carrier universes. This is the worker's
second pass; the independent reading is the maintainer review specified in the brief.
No new or dependency nodes are required: all helpers are the constructions explicitly
introduced by this node, using already recorded simplicial and dg-algebra notions.
