## Worker report

States `AlgebraicGeometry.ProEtale.FiniteScalarCompletion.finite_scalar_local_model_complete`
in `Sheaf.Paper.FiniteScalarLocalModelComplete`. Its sole theorem has proof `sorry`.
Seven concrete helper declarations assemble finite free modules, coordinatewise quotient
maps, the actual quotient transitions, the degree-zero quotient sequence/tower, and its
scalar quotient chain maps. They belong to this node's stated free-case normalization;
no independent mathematical notion or new DAG node is introduced.

Hypotheses and clauses, checked against the full node and source:

- The prime is `(l : ℕ) [Fact l.Prime]`. The finite extension is `(E : Type u)
  [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`.
  The integer ring, its spectral norm topology, the chosen uniformizer, positive finite
  quotients, and transition maps are exactly those in the coefficient-extension and
  completion dependencies. No new topology or uniformizer is chosen here.
- `(T : Scheme.{u})` is arbitrary. Its site is the recorded `Scheme.ProEt` small site
  (object universe u+1, morphism universe u). Abelian sheaves and internal modules have
  coefficients in universe u+1; the recorded `DerivedCategory` is the ordinary unbounded
  localization. No site-universe equality or bound on the scheme is added.
- `Modules l E T` is the recorded category of modules over `ring l E T`, namely the
  pullback of the continuous condensed integer ring. `finiteModule l E T n` is the actual
  quotient coefficient sheaf, restricted to integral modules. Index n denotes exponent
  n+1 throughout; thus every positive level is included and exponent zero is excluded.
- The local-model hypothesis is exactly the recorded
  `HasFiniteConstantLocalModel (DerivedNakayama.integerRing l E) T M`.
  Opening its definition gives a pro-etale cover, on each member a finite presentation
  over the condensed ring on the point, and a module isomorphism after pullback.
  As its docstring specifies, these presentations are finite scalar matrices, equivalently
  the scalar cokernels/constant scalar extensions in the node. We reuse this encoding,
  rather than arbitrary finite-presentation matrices on the scheme.
- The first conjunct states `IsDerivedComplete` for `Q(singleFunctor.obj M)` for every
  such local-model M. This is M[0]. Unfolding the recorded completeness predicate tests
  invertibility of the specified strict-tower augmentation on a K-flat representative;
  `completion_triangle_comparison` identifies it with c of the node. This is invertibility
  of the canonical unit, rather than merely existence of an abstract object isomorphism.
- The second conjunct explicitly records the global scalar model: a finitely presented
  condensed-point module P is pulled back using `DerivedNakayama.pullback`. The same
  scalar finite-matrix encoding as the local-model dependency is used. It admits every
  finitely presented ordinary scalar A-module, including torsion. No flatness or
  torsion-freeness condition is imposed on P.
- The third conjunct ranges over every `d : ℕ` and first states completeness of
  `freeComplex l E T d`. This is the degree-zero finite power `Mod.finiteFree B d`.
- Its remaining clauses range over any canonical `PrincipalReductionConeData` from the
  recorded simultaneous principal calculus. The existential q is one chain map in the
  category of strict towers, from `CompletionTriangle.tower` to `quotientTower`.
  The latter is built from `powerStep`, the finite coordinate power of the actual
  `quotientStep`, so naturality of q asserts compatibility with those actual transitions.
  This is stronger data than unrelated levelwise derived isomorphisms, as required.
- The first condition on q says every level is a quasi-isomorphism. The next fixes its
  degree-k components to `data.χ ... .hom ≫ biprod.fst ≫ quotientChainMap.f k`:
  quotient on the unshifted coordinate, zero on the shifted coordinate. The following
  equation sends `data.j` to that very scalar quotient chain map. Thus the map is the
  canonical augmented cone-to-quotient comparison required by the node.
- `b` is the inverse-limit cone map into the strict quotient Roos complex. Its coordinate
  equation against `roosχ` is precisely `(0, family of scalar quotients)` in that
  dependency's coordinate order (the shifted coordinate is first). It determines b in
  every degree, and hence specifies all scalar quotient projections and zero homotopy.
- `e` is an isomorphism in the derived category from the finite free complex to that
  Roos derived limit, with `e.hom = Q.map b`. The last clause universally quantifies
  over natural augmentations `a : 𝟭 ⟶ CompletionTriangle.complexCompletion ... data`.
  If its component on `freeComplex` has exactly the `roosχ` coordinate formula of
  `CompletionTriangle.completion_triangle_comparison`, namely zero in the shifted
  coordinate and `Pi.lift (fun n ↦ (data.j n).app freeComplex)` in the other coordinate
  in every degree, then `a.app freeComplex ≫ roosF.map q = b`. This uses the same q
  fixed by the quotient and augmentation clauses above. Localizing, and using that
  dependency's equality `c ≫ κ = Q.map (a.app freeComplex)`, gives
  `c ≫ κ ≫ Q.map (roosF.map q) = e.hom`. Thus the comparison obtained from q carries
  the actual completion unit to the cone with the specified scalar projections.
  On a finite free complex ordinary tensor computes derived tensor. The isomorphism
  e is in the derived category, not just a per-degree cohomology identification.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; its public coefficient extension module defines
  `coefficientExtensionAbsoluteValue`, `coefficientExtensionIntegers`,
  `coefficientExtensionUniformizer`, `coefficientExtensionRing` and
  `coefficientExtensionTransition`. The full coefficient definitions were read.
- `def-weil-size-convention` is metatheoretic; its recorded explicit universe convention
  is followed, without adding a new Lean definition.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `CondensedRing.moduleObjectDerivedPushforward` and `moduleObjectDerivedPullback`,
  the total derived functors in the ordinary module-object derived categories.
- `Sheaf.SixFunctors.ProEtale.DerivedCompletion`:
  `IsDerivedComplete`; `AdicCompletion.Modules`, `ring`, `finiteModule`, `finiteUnit`,
  `quotientStep`, `augmentation`, `roos`, and `completionMap`. Their full definitions
  fix the coefficients, transition maps, and completion unit used here.
- `Sheaf.Paper.CompletionTriangleComparison`:
  `CompletionTriangle.tower`, `complexCompletion`, `completion_triangle_comparison`;
  its public `PrincipalReductionConeCalculus` supplies `PrincipalReductionConeData`,
  `IsCanonical` and the cone coordinates; its public `RoosConeCalculus`/`StrictRoosModel`
  supply `roosF`, `roosχ` and their coordinate convention.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `HasFiniteConstantLocalModel`, with its actual cover and scalar finite-presentation
  isomorphisms, and `Mod.IsFinitelyPresented`/`Mod.finiteFree` from the upstream module
  `WeilConjectures.CategoryTheory.ModuleObjects.Free` (definitions read).

All recorded proof-dependency modules are imported, including the integral limit and
constant comparison, extension DVR, flat cyclic resolution, principal and Roos calculi,
cone/short-exact comparison, surjective tower, scalar finite-flat resolution, derived SES
triangle, triangle two-out-of-three, weakly-etale localization, coefficient-sections
localization, exact localized module restriction, countable products and covering
conservativity. Proof-only modules have non-public imports. The theorem docstring gives
all five node proof steps with the strict transition and augmentation normalizations.

Edge cases: d=0 gives the zero finite biproduct, zero quotient tower and zero augmentation;
no positive-rank condition occurs. The zero module and torsion scalar presentations are
allowed. There is no assumption of qcqs, Noetherianity, finite dimension, characteristic,
nonemptiness, or finitely many covering objects. In particular the empty scheme and
covers needed for it remain allowed. Positive exponent 1 is index 0 in the API.

Searches before writing:

- msearch leanfinder: "A proetale module sheaf locally a finitely presented constant
  scalar model over l adic integers is derived complete with normalized free quotient
  tower"; eight hits concerned scalar adic completion/BDeRham, no matching theorem.
- msearch loogle: "IsDerivedComplete, Module.FinitePresentation"; zero hits, unknown
  identifier `IsDerivedComplete` in the public Mathlib search index.
- msearch grep: "IsDerivedComplete|finite_scalar_local_model|scalar.*complete";
  five irrelevant Mathlib hits (ordinary scalar adic-completion and other scalar APIs).
- msearch leansearch: "Finite constant scalar local models of proetale integral l adic
  module sheaves are derived complete"; eight ordinary `IsAdicComplete`/`AdicCompletion`
  declarations, not this assertion about coefficient sheaves and a strict derived tower.
- Direct rg of `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
  for the target name, namespace and helper names found no exact assertion or declaration
  collision. `grep -rn` of the node id in `lean/WeilConjectures` found none.
  Concept searches found and reused the recorded local-model and completion APIs;
  the qcqs finite-model completeness theorem has a different hypothesis and omits the
  strict free-tower normalization, so is not an exact existing match.

The supplied CompactObject example module is withdrawn in the current checkout; its
node record was read, and current public-module/docstring conventions are followed.
No statement correction or disputed statement is needed. The node remains unchanged
outside `lean`. No dependency record is changed.

Validation before return: prescribed scompile.py compiled the original file in sandbox form and as
`Sheaf.Paper.FiniteScalarLocalModelComplete`, with no errors or warnings (19.9 s and
17.1 s respectively). All variables and universes are explicit; autoImplicit is false.

## Repair of returned delivery H3

The immutable returned head was 6f86a2bcbed4. Its final existential ψ was free:
choosing its hom as the inverse augmentation followed by e.hom did not connect ψ
to q. Removed ψ entirely and replaced that clause by the universal coordinate-pinned
strict augmentation identity described above. The theorem docstring and proof plan
now name this identity. All other hypotheses and clauses are retained, including
rank zero, torsion scalar models, arbitrary schemes, and actual quotient transitions.
No change to the natural-language node statement or its dependencies is required.
The saved packet's initial prescribed dry run passed (f710d2f8cce); this repair
addresses the mathematical return that mechanical preflight does not detect.

Self-check: compared the new formula directly with the public signature and proof
docstring of `CompletionTriangle.completion_triangle_comparison`. Its a supplies
the universally quantified coordinate condition. The formula is imposed in all
degrees since every integer is p+1 for an integer p. The fixed Roos coordinates
determine the strict augmentation, so there is no remaining freely chosen comparison
isomorphism. Applying `roosF.map` to the same q sends those j_n coordinates to the
quotient coordinates already required of b. This also applies when d=0.

Repair validation: prescribed scompile.py compiled the revised file in sandbox form
(15.1 s) and library-module form (24.1 s), exit 0 with no errors or warnings.
Checked that the node differs from the current shared node only in `lean`, that
`lean.statement` is verbatim from the revised theorem, that every Lean line is at
most 100 characters, and that the only postponed proof is the named main theorem.

## Second reading by Q82

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
