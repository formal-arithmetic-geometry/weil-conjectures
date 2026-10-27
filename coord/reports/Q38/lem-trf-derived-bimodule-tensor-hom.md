## Worker report

Item: lem-trf-derived-bimodule-tensor-hom. The delivery supplies
`Sheaf.Algebra.Homology.DerivedBimoduleTensorHom`, with main statement
`ModuleCat.derived_bimodule_tensor_hom`. Its only new theorem has proof `sorry`.
All eleven helper definitions contain actual data, using existing localization,
closed adjunction, evaluation, coinduction and single-degree embedding constructions.
The natural-language node statement and its seven proof steps are unchanged.

I read the full item, all five statement dependencies and their recorded interfaces,
the ordinary-module Hom-complex implementation, the fixed-second-factor derived tensor
statement, and the native derived closed structure. I read dga.tex at
lemma-tensor-hom-adjunction (09LN) and lemma-tensor-hom-adjoint (09LT), including their
proofs. These specialize to the rings and bimodule in this node. The seven-step
mixed-ring adaptation already in the node is reproduced in the theorem's docstring.

Hypotheses and clauses, matched to Lean:

- A homomorphism of commutative rings S → B: `{S B : Type u} [CommRing S]
  [CommRing B]` and `(f : S →+* B)`. The module universe is explicit, and the
  chosen small morphism universes are supplied by
  `[HasDerivedCategory.{u} (ModuleCat.{u} S)]` and its B analogue. These are the
  usual ordinary-module derived categories, not categories of arbitrary sheaves.
  Any two rings fit a common universe; no dimension or cardinal bound is imposed.
- E, X in D(B) and V in D(S): the comparison and the main theorem quantify over
  `DerivedCategory (ModuleCat.{u} B)` and `DerivedCategory (ModuleCat.{u} S)`.
  These are the recorded `DerivedCategory` of def-weil-abstract-derived-category.
- Restriction U: `(ModuleCat.restrictScalars f).mapDerivedCategory`, the existing
  exact restriction functor. It is never assumed to preserve K-injectivity.
- E as a B-S bimodule: the S-action is precisely restriction along f; no extra
  arbitrary action is supplied. `derivedBimoduleHom f E` is the concrete composite
  `derivedCoinduction f ⋙ ihom E`. Ordinary coinduction has carrier Hom_S(B,I)
  and action `(b h)(b') = h(b'b)`.
- J_E(V) represented by Hom_S(E,I), with its B-action: the first conjunct makes
  `derivedBimoduleHomModel f Ec I` an isomorphism for EVERY B-complex Ec and EVERY
  S-K-injective I. Its source is Q Hom_B(Ec,Hom_S(B,I)). The next conjunct provides
  a chain isomorphism T from its restriction to the recorded
  `CochainComplex.moduleHomComplex (U Ec) I`. Its first coordinate equation is
  `T(z)(x) = z(x)(1)` via `coinductionEvaluation`. Its second equation says
  `ev_1 (b • T⁻¹(z)(x)) = z(b • x)`, exactly the retained precomposition action.
  This is a B-linear model of the specified object, rather than only an S-object
  with an unmentioned action. The arbitrary-representative quantifiers and the
  functor on the derived categories give independence of representatives.
- Derived tensor: `derivedBimoduleTensor f E = tensorRight E ⋙ U`, so its value
  at X is exactly U(X tensor_B^L E). The native monoidal structure is the existing
  K-flat derived tensor, with the existing fixed-factor functor imported; no
  tensor operation or K-flat predicate is redefined here.
- The displayed derived isomorphism: for each E the theorem supplies a natural
  isomorphism `derivedBimoduleHomLeft f E ≅ derivedBimoduleHomRight f E`, whose
  components are the DEFINED `derivedBimoduleComparison f E X V`. The source is
  U RHom_B(X,J_E(V)); the target is RHom_S(U(X tensor_B^L E),V). The comparison
  consists of native closed currying over B followed by the existing enriched
  coinduction isomorphism. Thus its components are not arbitrary chosen maps.
- Naturality: the natural isomorphism is on `D(B)ᵒᵖ × D(S)`, giving all X and V
  squares. The next displayed equality is the E-square, with `MonoidalClosed.pre a`
  on the J side and precomposition by `U.map (X ◁ a)` on the tensor side. Both
  directions are contravariant in E, as they must be.
- Taking H⁰ gives the Hom-set adjunction: H⁰ of an R-derived object is represented
  by maps from the native tensor unit R[0]. `MonoidalClosed.curry' g` is the
  canonical H⁰ class of g in RHom_B. `bimoduleScalarUnit f` is the actual map
  S[0] → U(B[0]) induced by f, using the existing single-functor comparisons.
  The bijectivity conjunct identifies Hom_D(B)(X,J_E(V)) with the H⁰ of the
  restricted internal Hom. The following curry' equation says that postcomposing
  with the enriched comparison gives the H⁰ class of precisely
  `((derivedBimoduleAdjunction f E).homEquiv X V).symm g`.
  This makes the H⁰ square commute with the actual composite adjunction; it is
  stronger than merely asserting the existence of an unrelated Hom-set bijection.
- Evaluation as counit: the next conjunct equates the counit with
  `derivedBimoduleEvaluation f E V`. That map first exchanges J and E using the
  canonical signed derived braiding, evaluates `E tensor RHom_B(E,Coind V)` over B,
  then evaluates coinduction at one. Under T this is exactly h tensor e ↦ h(e).
  The actual adjunction definition supplies the unit and both triangle identities.
- Compatibility with any K → S: the final conjunct quantifies over every
  commutative K and every `(k : K →+* S)`. It asserts invertibility of the
  RESTRICTED comparison in D(K), and the restricted H⁰ and evaluation squares.
  Every map uses `(restrictScalars k).mapDerivedCategory.map`; RHom_S is retained,
  and is never replaced by RHom_K. This also covers identity ring maps.
- No flatness of B/S, perfection of E, or boundedness of V: none of these occurs
  in any binder. K-injectivity appears only in the representative computation,
  exactly as in the node; arbitrary derived E, X and V remain unrestricted.

Dependency declarations used:

- def-weil-abstract-derived-category: Mathlib.Algebra.Homology.DerivedCategory.Basic,
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`.
- lem-pc-derived-tensor-second-factor-functor:
  Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor,
  `DerivedCategory.exists_derivedTensor_second_factor_functor`. Its K-flat tensor
  is the native derived tensor used here, not a new tensor definition.
- def-pur-derived-internal-hom:
  Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses,
  `CategoryTheory.derivedInternalHomOfUniverses` (generic ringed-site presentation).
  The ordinary-module native `ihom` presentation and its NORMALIZED identification
  with Hom into K-injectives are already exposed by the added landed
  lem-trf-algebraic-shriek-derived-hom-adjunction; we use that interface instead of
  constructing another ordinary-module RHom or a private one-point-site transport.
- def-sc-module-total-hom-complex:
  WeilConjectures.Algebra.Homology.ModuleHomComplex,
  `CochainComplex.moduleHomComplex`; its actual homogeneous cochains and signed
  differential are reused verbatim in the representative clause.
- def-pur-kinjective-complex is a Mathlib leaf with no lean record:
  Mathlib.Algebra.Homology.HomotopyCategory.KInjective,
  `CochainComplex.IsKInjective`, exactly its null-homotopy condition on acyclic sources.
- Landed definition dependency def-trf-derived-coinduction (superset record repaired under §1(B)):
  Sheaf.Algebra.Homology.DerivedCoinductionAdjunction,
  `ModuleCat.derivedCoinduction`, `derivedCoinductionModel`,
  `derivedCoinductionAdjunction`, `coinductionComplexFunctor`, `coinductionEvaluation`.
- Added landed statement dependency lem-trf-algebraic-shriek-derived-hom-adjunction:
  Sheaf.Algebra.Homology.AlgebraicShriekDerivedHomAdjunction,
  `ModuleCat.algebraicShriek_derivedHom_adjunction`, `coinductionHomComparison`,
  `coinductionHomLeft`, `coinductionHomRight`. The chosen enriched coinduction
  comparison is determined uniquely: eP and eA are fixed by their transposed
  evaluation equations, T by every coordinate, and θ by its naturality and its
  components on all Q(E),Q(I) for K-injective I. The helper selecting θ therefore
  postpones only this characterization proof, not unspecified mathematical data.

All recorded, stated proof-dependency modules are imported directly. This includes
K-flat resolutions and predicates, the module Hom quotient, quasi-isomorphism
invariance, and localized Hom into K-injectives. The Mathlib complex tensor and
ordinary-module K-flat declarations are imported directly as well. The coinduction definition node and enriched-coinduction theorem were checked
transitively: neither reaches this item, so no DAG cycle is introduced. No new node
is needed. The coinduction definition record is repaired as described below.

Edge cases checked mathematically: zero E, X or V; the zero ring B; identity S → S;
E=B[0]; shifts of the free rank-one module in positive and negative degrees; unbounded
E and V (all Hom coordinates are products indexed by ℤ, with no truncation); the
nonflat map ℤ → F_p with E=X=F_p and V=ℤ, where both sides retain the nonzero
Ext¹_Z(F_p,Z); and arbitrary/identity K → S. Taking H⁰ for the nonflat example does
not replace the enriched isomorphism with an assertion only about H⁰. These cases
need neither perfectness nor an unmentioned resolution-preservation assumption.

Searches actually run, via msearch.py under this group and item:

- LeanFinder: “Derived mixed ring tensor Hom adjunction for unbounded module complexes
  retaining scalar actions by precomposition”. Eight hits: tensorHom, ιTensorObj,
  HasTensor, tensorObj and related tensor-existence declarations. None states the
  mixed-ring derived comparison.
- Loogle: `ModuleCat.restrictCoextendScalarsAdj`. One hit, the ordinary restriction /
  coextension adjunction. Reused through the existing derived coinduction interface;
  it does not itself state this derived bimodule theorem.
- Mathlib grep: `bimodule|tensorHomAdjunction`, subdirectory Algebra/Homology.
  Zero hits.
- LeanSearch: “Derived tensor Hom adjunction over two commutative rings with scalar
  action by precomposition”. Eight hits, including ModuleCat.monoidalClosedHomEquiv,
  restrictCoextendScalarsAdj and ordinary tensor/Hom contraction maps; no exact match.
- Local rg in lean/WeilConjectures and lean/Sheaf for bimodule, mixedHom,
  moduleRHom, derivedModuleHom, moduleDerivedHom, the item id and proposed names.
  Found the parent polynomial-diagonal reduction and ordinary module-object
  bimodules, not this theorem. The subsequent exact-name search also included
  dag/lean_names_upstream.json and found no name clash. The useful adjacent
  enriched coinduction theorem was opened in full and reused, rather than copied.

Compilation: scompile.py compiled the complete module under its sandbox name and
library module name against the live server sources, in 12.0 s and 11.9 s, with
exit 0 and no errors or non-sorry warnings. Initial braiding-interface errors were
repaired by importing the existing native derived braided instance; no additional
hypothesis or local instance was added. The dry-run and final delivery are performed
using deliver2.py. No live source was edited and no direct git command was run.


## Dependency modules

`def-trf-derived-coinduction`: the landed `existing: true` record named only
`ModuleCat.derivedCoinduction`. Under §1(B), its declaration list is extended to
also own `coinductionComplexFunctor`, `coinductionEvaluation`,
`derivedCoinductionModel`, and `derivedCoinductionAdjunction` in the unchanged
`Sheaf.Algebra.Homology.DerivedCoinductionAdjunction` module. These supply the
complex construction, evaluation at one, canonical K-injective comparison, and
canonical derived adjunction used by this item. Their bodies are existing Mathlib
constructions; they use neither `.choose` nor `_spec` of the coinduction theorem.
The dependency node changes only in `lean`; no new module or duplicate definition
is supplied.

## Returned-delivery repair

H2 on immutable head `1d6f0d804eae`: removed
`lem-trf-derived-coinduction-adjunction` from the item's `stmt_deps` and replaced
it with `def-trf-derived-coinduction`, extending the latter's existing definition
ownership record as requested. The Lean file is unchanged. The genuine theorem
dependency `lem-trf-algebraic-shriek-derived-hom-adjunction` remains: its normalized
comparison is selected by `bimoduleCoinductionHomIso`, so it is required to define
the consumer's statement. This is an interface ownership repair and does not
change the item's statement or proof plan.

The saved packet's initial `deliver2.py --no-push` passed (commit `bfadd8fe522`),
but the independent H2 return requires this additional repair regardless of the
mechanical gate. Compared the saved item with current main: the original packet
differed only in `lean` and its two added statement dependencies. The repaired
packet retains that Lean statement and all previously accepted clause mappings.

## Self-check by Q38

I reread the five coinduction helper signatures and their complete bodies. They
are direct complex-functor, counit, right-derived-functor, canonical model-iso,
and derived-adjunction constructions, respectively. The definition node's
signature remains verbatim and its declaration list is a strict superset of
the landed list. Checked that only `lean` changes in the dependency node and
only `lean` and `stmt_deps` change in the item relative to current main. The
item's Lean file and theorem signature are unchanged from the independently
accepted version; no mathematical clause, hypothesis, universe, or edge case
is altered. No independent agent was started, as required by the dispatcher.

## Second reading by Q38

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
