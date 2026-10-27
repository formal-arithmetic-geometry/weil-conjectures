## Worker report

Q22, stage 2, 2026-10-22. This delivery adds the first Lean statement of
`lem-sfb-proper-wcontractible-closed-fibre-rigidity` in
`Sheaf.Paper.ProperWContractibleClosedFibreRigidity`. It retains the current
NA/L-reviewed stage-1 split, including every statement, proof and metadata field.
The earlier Q22 refusal confused completion of stage 1 with completion of stage 2:
the current live node has no `lean` record. No second split is attempted.

The only postponed theorem is
`AlgebraicGeometry.ProEtale.CondensedRing.proper_wContractible_closedFibre_rigidity`.
Its proof is `sorry`; its docstring transcribes all eight current proof steps and
the nodes they use. The seven supporting declarations give real data: evaluation,
the section restriction and its right-derived pullback, the quotient scheme and
its quotient map, the map of fibre products and the resulting restriction map.
They are constructions belonging to this item's comparison, not new independent
mathematical notions. No definition contains `sorry` or chooses an unspecified map.

Hypotheses and coefficient clauses:

- `ℓ : ℕ` and `[Fact ℓ.Prime]` fix the prime. `PadicAlgCl ℓ` fixes the
  standard algebraic closure with its existing norm topology. The existing
  `PadicAlgCl.FiniteIntermediateField ℓ` supplies the finite subextensions E.
- `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`, `[MonObj Λ]` and
  `[IsCommMonObj Λ]` give a commutative condensed ring. The explicit `hΛ`
  disjunction is exactly the six families in the statement: finite discrete A
  with `∃ n, ∀ a, (ℓ ^ n) • a = 0`; continuous-map ℤ_ℓ; the valuation ring
  of a finite E; continuous-map ℚ_ℓ; continuous-map E; and continuous-map Ω.
  Ring-object isomorphisms allow the same rings with different presentations.
  A finite A is represented in `Type 0` without restricting finite isomorphism
  classes; all modules, schemes and site objects keep the required size.
- The explicit six-family disjunction follows the already landed sibling
  `QcqsProperSerreHeartBound`. The recorded `IsLocalizingAdmissibleCoefficient`
  has since gained a seventh, distinct finite-subextension-valued Ω case.
  Using that predicate unqualified would strengthen this theorem; the disjunction
  preserves this item's exact all-continuous-map convention. No coefficient
  topology is redefined, and no equality of those two Ω sheaves is assumed.
- `{X Y : Scheme.{u}}`, `[CompactSpace Y]`, `f : X ⟶ Y` and `[IsProper f]`
  give exactly the quasi-compact base and proper morphism.
- `R : Type u`, `[CommRing R]`, `[IsWContractibleRing R]`,
  `w : Spec (CommRingCat.of R) ⟶ Y` and `[WeaklyEtale w]` give precisely
  the affine w-contractible object of the small pro-etale site, including R=0.
- `M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  (condensedRingObj Λ X)` is an ordinary internal Λ_X-module. Its hypothesis
  `ObjectProperty.weakSerreCoproductClosure.{u + 1}
  (IsConstantModelConstructible Λ X) M` is the specified intersection of
  replete classes closed under kernels, cokernels, extensions and small ambient
  coproducts. Its existing API contains zero by the empty coproduct. Extensions
  mean both ends in a short exact sequence imply the middle, as in the node.
  The generators are the recorded finite constant scalar-model notion, not the
  upstream arbitrary-matrix finite-presentation notion.

Every conclusion and canonical object:

- `wContractibleClosedPointScheme R` is literally
  `Spec (CommRingCat.of (R ⧸ Ideal.jacobson (⊥ : Ideal R)))`.
  `Ideal.jacobson ⊥` is the intersection of all maximal ideals, since the
  additional containment condition `⊥ ≤ m` is automatic.
- `wContractibleClosedPointImmersion R` is `Spec.map` of that quotient map;
  it is neither a chosen closed subscheme nor an arbitrary closed immersion.
- `IsAffine C`, `IsReduced C`, `∀ p : PrimeSpectrum (R/J),
  p.asIdeal.IsMaximal`, and `IsWContractibleRing (R/J)` render affineness,
  reducedness, dimension at most zero (also the empty scheme), and
  w-contractibility of this exact affine scheme. The residue-field conjunct is
  `∀ c : C, IsSepClosed (C.residueField c)`.
- `IsClosedImmersion i` and `Set.range i = closedPoints (Spec R)` give the
  closed immersion and exactly the closed-point subspace. A closed immersion
  is a homeomorphism onto its range, so equality of these sets gives the asserted
  identification of topological subspaces.
- `pullback f w` is X_W and
  `pullback f (wContractibleClosedPointImmersion R ≫ w)` is X_C.
  The first projection is the specified a:X_C→X. `properClosedFibreMap`
  is the induced X_C→X_W, made with `pullback.lift` and both projections.
- `closedFibreModuleEvaluation Λ X U` is exactly the composite of module
  forgetting, sheaf-to-presheaf forgetting and evaluation at `op U`.
  Its `rightDerivedFunctor` derives evaluation IN THE MODULE CATEGORY,
  not evaluation after deriving an unrelated abelian-sheaf forgetful functor.
- `closedFibreModuleSectionsRestriction` evaluates the actual module
  adjunction unit at U, then restricts on the target site along the explicitly
  constructed map `id_Z → U ×_X Z`. It incorporates the coefficient map in
  the recorded `upperStar Λ a` rather than inserting a new identification.
- `closedFibreModuleDerivedRestriction` is
  `Functor.rightDerivedPullback (upperStar Λ a)` of that section map.
  Exact inverse image acts termwise. Its defining normalization is the section
  map followed by the derived unit; hence the degree-zero map is the ordinary
  section restriction. This convention is built into the canonical construction.
- The final `IsIso ((properClosedFibreDerivedRestriction Λ f R w).app
  ((DerivedCategory.singleFunctor _ 0).obj M))` is the actual isomorphism
  in `DerivedCategory Ab.{u+1}`. Its source is derived evaluation on X_W.
  Its target is derived evaluation at the terminal object of the X_C-site
  after exact a^*, which is RΓ(X_C,a^*M). Exact termwise pullback of M[0]
  is canonically a^*M[0]. No per-degree-only replacement is made.
- There are no Noetherian, finite-presentation, invertibility, completion,
  lattice, solidness, field-of-definition or nonemptiness hypotheses.

Dependency declarations read and used (public imports state the interface;
ordinary imports retain already stated proof inputs):

- `Sheaf.Paper.LocalizingAdmissibleCoefficients`:
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`, read to
  check the coefficient convention and the extra finite-subextension clause.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward`
  and `moduleObjectDerivedPullback`, the ordinary uncompleted derived setting.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `IsConstantModelConstructible`, with `HasFiniteConstantLocalModel` and
  `IsFiniteConstantStratified`, used as the closure's generator property.
- `WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.WeakSerreCoproductClosure`:
  `CategoryTheory.ObjectProperty.weakSerreCoproductClosure`, whose signature
  and full intersection definition were read, including extension and zero clauses.
- `WeilConjectures.RingTheory.ProEtale.WContractible`:
  `IsWContractibleRing`, and the inherited `IsWStrictlyLocalRing`,
  `IsWLocalRing` and `WLocalSpace`, with their full definitions read.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`:
  `Scheme.ProEt` and `Scheme.ProEt.mk`; weakly etale maps, not pro-etale-only maps.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift`.
- `def-weil-size-convention` has no declaration by design. Explicit `universe u`,
  `Scheme.{u}`, `Ab.{u+1}`, the existing small site and index `u+1` implement it.
- Existing `condensedRingObj`, `CondensedRing.upperStar`,
  `CondensedRing.upperStarLowerStarAdjunction` are the actual upstream
  pulled-back ring and module operations. Their signatures and unit construction
  were read in ModuleObject/Basic and ModuleObject/UpperLowerStar/Defs.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback`:
  `Functor.rightDerivedPullback`, read in full through its unit factorization.
  It supplies the canonical map without a new postponed theorem about maps.

The module imports every currently recorded proof-dependency module. The three
proof-only nodes `lem-sfb-wcontractible-jacobson-henselian`,
`sk-thm-pbc-henselian-h0` and `lem-sfb-closed-torsion-rigidity-serre-transfer`
have no usable Lean record; this does not prevent stating the item, and their
mathematical uses are preserved explicitly in the proof docstring. Other proof
leaves with Mathlib matches are covered by the imported geometry, adjunction,
homology and finite-presentation libraries.

Edge cases checked by reading the definitions: R=0 gives the empty spectrum,
all geometric point quantifiers are vacuous, and the section restriction is still
defined. Empty X or Y, the zero finite ring A, M=0, f=id and empty coproducts
are not excluded. No `Nontrivial R` or nonempty-family binder occurs. The
zero-dimensional clause uses maximality of every prime, so it does not assert
Krull dimension equals 0 on the empty spectrum. The topology on Ω is precisely
`continuousMapRingObj (PadicAlgCl ℓ)`. The closure includes arbitrary maps
between members, not only maps between the generators.

Searches for an existing statement:

- `msearch.py ... leanfinder` with “Proper cohomology over a weakly contractible
  affine scheme agrees with restriction to its reduced closed point subscheme”:
  8 hits, involving affine spectra, limit sections and reduced schemes; none
  supplies the comparison or its six-coefficient weak Serre class.
- `msearch.py ... loogle` with `AlgebraicGeometry.IsProper, IsWContractibleRing`:
  0 hits; Loogle does not index the project's `IsWContractibleRing` identifier.
- `msearch.py ... grep` with `proper.*rigid|rigid.*proper|closed.*fibre.*cohom`
  under Mathlib/AlgebraicGeometry: 0 hits.
- `msearch.py ... leansearch` with “Proper henselian cohomology restriction to
  the closed points of a weakly contractible affine scheme for condensed modules”:
  result recorded by the search wrapper; no matching theorem found.
- `rg` in BOTH `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  closed-fibre/proper-rigidity expressions: no exact declaration. The related
  `QcqsProperSerreHeartBound` cites the node only in its proof plan; it states
  a uniform vanishing bound and does not supply this comparison.
- A targeted search found the existing generic weak Serre coproduct closure;
  its full definition was reused. Existing derived-pullback searches found
  `Functor.rightDerivedPullback`, also reused.

No statement correction or new/dependency node is needed. The mathematical source
for the full norm-topological transfer remains WANTED exactly as the reviewed
node records; this delivery does not claim to prove that transfer or supply a new
literature justification for it.

Validation: prescribed scompile.py passed sandbox and library-path compilation,
13.0 s and 22.9 s, with no errors or unexpected warnings. All binders are explicit,
`autoImplicit` is false, and the file has no line longer than 100 characters.
The node's lean.statement is copied verbatim from the theorem signature.

## Second reading by Q22

A second in-thread reading compared the current live statement with all eight
supporting declarations and the final theorem. No other agent was started,
as the dispatcher explicitly prohibits it; the independent mathematical review
is the maintainer's delivery review. This is the worker's own second pass,
not a claim of independent approval.

Checked the six coefficient alternatives against the live admissibility predicate:
the latter's extra finite-subextension-valued Ω alternative is deliberately not
included. Checked that both the source and target derive section functors from
module objects; checked the target evaluation is on the terminal X_C object;
checked that the map comes from the module unit with the specified quotient lift.
Checked the geometry conjunct by conjunct, including actual residue fields and
closed-point range equality. Checked that w is only required weakly etale and
that no nonempty or finite-presentation restriction slipped in. The initial
compile caught a mistaken positional use of the implicit arguments of
`pullback.condition`; it was repaired to named arguments before the successful
compile. No mathematical statement was changed.
