## Worker report

The item is stated by `AlgebraicGeometry.ProEtale.coefficientHeart_commonStratification`
in `Sheaf.Paper.CoefficientHeartCommonStratification`. Its conclusion is the explicitly
expanded three-clause proposition `CoefficientHeartStratificationAssertions`. There is
one postponed theorem, with the complete seven-step DAG proof in its docstring. All
other declarations in this delivery are definitions with real data. The item's statement,
statement dependencies, proof and proof dependencies are unchanged.

Hypotheses and clause-by-clause reading:

- The scheme X is `X : Scheme.{u}` with `[IsNoetherian X]`. No separatedness, base field,
  finite-type, characteristic, or invertibility assumption is imposed.
- The fixed prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. `hΛ` says the condensed ring is either the
  continuous-function condensed ring of a finite intermediate field E of the fixed
  algebraic closure of Q_ℓ, or the recorded bounded-finite-subextension-image Qbar ring.
  `FiniteDimensional ℚ_[ℓ] E` is exactly finite extension, including degree one. These are
  the source's fixed-closure coefficient choices. The coefficient parameter is a sheaf
  of rings, so equality identifies the multiplication too; it is not equality of bare
  abelian sheaves with an independently chosen ring structure. The commutative ring-object
  instance is the source's commutative coefficient structure. No discrete topology is used.
- Part (1), finitely many inputs: `∀ (n : ℕ) (P : Fin n →
  X.FiniteLocallyClosedStratification)`. The output `∃ R` has the same finite scheme
  stratification type. This recorded dependency supplies locally closed subsets, cover,
  disjointness, genuine scheme domains, immersions and equality of their ranges.
  `∀ j a, ∃ b, R.stratum a ⊆ (P j).stratum b` is common refinement. It asserts no scheme
  factorization. `∀ a, ConnectedSpace (R.domain a)` is connectedness, including nonemptiness.
  For every `k : Fin (R.n + 1)`, the union of strata with `a.val < k.val` is open. The
  indexing starts at zero, so these are exactly the prefixes S_1 through S_k, also including
  the empty prefix and the whole space.
- Part (2), actual locally closed restriction: the universal S and T, `i : S ⟶ X` with
  `IsImmersion i`, and `j : T ⟶ S` with `IsImmersion j` are the two actual locally closed
  inclusions. `M` is a module over the pulled-back condensed coefficient on S. Lisse is
  `IsLisseCoefficientModule`, namely a pro-etale cover on which `Mod.IsFree` holds; the
  latter is the existing existential finite-rank free-module definition. The conclusion
  uses the canonical `CondensedRing.upperStar Λ j`, not an arbitrary functor or a constant
  discrete coefficient ring.
- Part (2), any refinement adapted to a constructible sheaf: for arbitrary finite P and R,
  `∀ a, HasFiniteConstantLocalModel Λ ((upperStar Λ (P.immersion a)).obj M)` is precisely
  adaptation in sk-def-sfb-constructible (1),(2). On Noetherian X all locally closed strata
  are constructible, so no extra constructibility premise is needed. The image-containment
  premise is the stated refinement relation. Every R-stratum restriction is lisse in the
  conclusion. In particular, this includes R=P, and covers the finite-constant-model
  adaptation as well as the usual finite-free adaptation over these field coefficients.
  The sheaf need not arrive with a separately chosen proof of constructibility: the supplied
  adapted stratification already witnesses it. No requirement that T factor through S is
  introduced by this clause.
- Part (3), each stratum: for every finite R and every a, `PreservesFiniteLimits` and
  `PreservesFiniteColimits` state exactness of module restriction. The natural isomorphism
  after `Mod.forget` identifies it with the abelian inverse image `upperStar Ab ...`.
  This is the transported meaning of g*=g^-1: its domain and codomain are the specified
  coefficient-module categories, so literal equality with a functor on abelian sheaves
  would be ill-typed. The canonical comparison exists in the imported framework.
- Part (3), injectivity and surjectivity: for all module objects A,B and f:A→B, `Mono f`
  and `Epi f` are respectively equivalent to `∀ a, Mono (upperStar.map f)` and
  `∀ a, Epi (upperStar.map f)`. In this abelian category these are injective and
  surjective sheaf morphisms (surjectivity locally, not sectionwise).
- Part (3), every sequence: for all A,B,C and arbitrary arrows f,g,
  `imageSubobject f = kernelSubobject g` iff the same equality holds after restriction to
  every stratum. Mathlib's abelian exactness criterion identifies this with exactness at B.
  Equality itself forces fg=0, so no global complex condition is silently assumed.
  Applying the universal assertion to adjacent pairs covers longer sequences, including
  injectivity and surjectivity at the ends by the preceding clause.

Dependency declarations used:

- `def-constructible-stratification`: `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`,
  `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification` and its topological parent.
  Read the complete structures and docstrings. In particular the old stronger upstream
  `Scheme.Stratification` is not used as the statement's input type.
- `sk-def-sfb-constructible`: repaired here in `Sheaf.Paper.ScalarConstructible` with
  `HasFiniteConstantLocalModel`, `HasScalarConstructibleStratification`,
  `IsScalarConstructible`, `ScalarConstructible`, `scalarBoundedConstructible`,
  `ScalarBoundedConstructible`, `HasScalarTorAmplitude`, `ScalarConstructibleFiniteTor`,
  all in `AlgebraicGeometry.ProEtale`. Read its source node, its complete audit signatures,
  and the blueprint's current definition. Its first clause permits the scalar-matrix
  formulation directly; no missing equivalence theorem is assumed to define the data.
- Existing `CategoryTheory.Mod.finiteFree` and `Mod.IsFree` from
  `WeilConjectures.CategoryTheory.ModuleObjects.Free`; canonical coefficient ring
  `condensedRingObj` and `upperStarFromPoint` from
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`; canonical module restriction
  `CondensedRing.upperStar` from its `UpperLowerStar.Defs`; `derivedTensor` from its
  `Derived.Tensor`. These retain the small pro-etale site object universe u+1 and morphism
  universe u, and Ab values in u+1; no universe equality is imposed.
- `Profinite.padicSubfieldCondensedRing`, `padicAlgClCondensedRing` from
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic` give the precise coefficients.
  The latter uses bounded finite-subextension image rather than all continuous maps.
- All published proof modules of the item's plan are imported non-publicly: common
  refinement (`WeilConjectures.ConstructibleSheaf.Refinement`), reduced subschemes,
  Noetherian strata detection, pro-etale inverse image, the surjective-closed cover
  refinement and condensed-module equivalence, and Mathlib's permanence, fibre product,
  Noetherian component and connectedness modules. The cartesian-coefficients audit is
  implemented in the imported ModuleObject.Basic and UpperLowerStar.Defs. Definitions
  of immersions, locally closed sets and irreducible components come through these
  imports. No proof dependency import is omitted to conceal an unstated helper.

Edge cases checked before writing and again against the compiled declarations:

- n=0 is allowed; no first input is selected. Empty X permits R.n=0. Connected output
  domains exclude empty pieces, while input strata may be empty.
- Every prefix including k=0 and k=R.n is present. R.n=0 still has its empty prefix.
- Rank zero uses `Mod.finiteFree ... 0`; zero modules and empty covers are allowed.
- S and T may be empty. The actual immersion binder handles nonreduced subschemes;
  refinements only compare images, so no invalid factorization between scheme structures
  is required.
- Restriction and detection concern every finite stratification, without assuming its
  prefixes are open or its strata connected. An empty family on empty X gives the true
  vacuous detection assertion in the zero sheaf category.
- A pair f,g need not be a complex before detection: image-kernel equality detects its
  zero composite too. Mono and epi are categorical sheaf notions, not pointwise evaluation
  on all sections.
- Scalars need not be fields in the repaired dependency: e.g. integer torsion is allowed
  by finite scalar cokernel presentations; its local-model predicate does not replace
  finitely presented modules by finite free modules for general condensed rings.

Searches made (the machine-recorded results are in searches.jsonl):

- LeanFinder: `finite common refinement connected stratification scheme and exact lisse
  restriction condensed coefficient sheaves`; 8 unrelated affine-transition-limit and
  Nobeling exactness results. A second query without "and" likewise returned only those
  unrelated results. No full statement match.
- Loogle: `AlgebraicGeometry.Scheme.Stratification,
  CategoryTheory.Functor.PreservesFiniteLimits`; unknown project identifier, no hits.
  Follow-up `"Mod.finiteFree"` has no Mathlib hits; the project declaration was read locally.
- LeanSearch: `constructible sheaves over condensed rings finite constant local models and
  lisse finite free proetale restrictions`; 8 hits about light/discrete condensed sheaves,
  constant sheaves and finite generation. None supplies the finite scalar model or this lemma.
- Mathlib grep: `commonRefinement|common_refinement|IsLocallyFree` in CategoryTheory;
  zero hits. Direct rg of the item id in upstream WeilConjectures: no match. Direct rg of
  IsLisse/IsLocallyFiniteFree and finite constant model names in the project and the
  module-object framework found finite discrete-coefficient and adic notions, not this
  condensed local-free predicate or full statement.
- Project/source grep found the older refinement and finite presentation declarations;
  their full signatures/docstrings were read. The first restricts input strata to be
  constructible; the latter allows nonconstant coefficient matrices. Existing finite-stalk
  IsConstructible was also read and rejected for this coefficient category. The exact new
  declaration names were searched in upstream, lean/Sheaf and dag/lean_names_upstream.json
  with no collision. `scompile.py --source Sheaf.Paper.CondensedConstructibleLocalModels`
  confirmed that guessed module is absent; no declaration was inferred from its name.

Validation: both delivered modules compile separately through scompile.py in dependency
order, with no errors or warnings. The only sorry is the named item theorem. The repaired
module compiled in about 2.6 seconds, and the item in about 3 seconds. No global build,
source-checkout modification or direct Git command was run. No statement correction and
no STATEMENT-DISPUTED flag is needed.

## Dependency modules

`sk-def-sfb-constructible` is repaired under section 1(B). Its audit lists three declarations,
which were opened in the older source or the exact side-framework source when absent there.
`Mod.IsFinitelyPresented` is the reusable general finite-presentation predicate;
`ProEtale.IsLocallyFinitelyPresented` permits matrices of arbitrary coefficient sections;
`ProEtale.IsConstructible` concerns discrete modules with finite stalks. The last two cannot
express this node's condensed scalar constant models. The new module keeps the ordinary
module-object category and canonical pullbacks, and defines its models using cokernels of
finite-free Lambda-module maps at the profinite point, then canonical point pullback.
Endomorphisms of the free rank-one module at that point are Lambda(*): hence these maps are
exactly scalar matrices, as the source explicitly permits. Pullback is right exact and
preserves finite sums, so its cokernel is Lambda_U tensor the finitely presented scalar
cokernel; this is a real construction, without a choice from an existence theorem.
The independent local-model detail node's equivalence theorem remains open: this delivery
uses the equivalent matrix formulation expressly included in the owning definition node,
not a newly assumed equivalence or a duplicate general presentation predicate.

For qcqs X, `IsScalarConstructible` uses the finite constructible-stratification condition;
otherwise it tests all affine opens. `ScalarConstructible` has exactly the ambient morphisms.
The bounded predicate asks for finite cohomological bounds and scalar-constructible homology
in every degree. Its full subcategory is Dbc. Tor amplitude tests ordinary derived tensor
with every module sheaf in degree zero, and its finite existential interval defines the
Dctf full subcategory of Dbc. These definitions impose no derived completeness. All eight
declarations have source/blueprint docstrings and real defining terms. The dependency node
changes only in lean, with the required explanation in lean.note. No new DAG nodes are added.

## Second reading by Q29

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fix (NT-cc, 2026-10-18)

Since this delivery's base, group N7 has landed `sk-def-sfb-constructible` on newtargets-dag as
`Sheaf.Paper.CondensedConstantConstructibility` (`HasFiniteConstantLocalModel`,
`IsFiniteConstantStratified`, `IsConstantModelConstructible`, ... ; reviewed pass). This
delivery's section 1(B) repair of the same node (`Sheaf.Paper.ScalarConstructible`) would have
duplicated the notion and declared `AlgebraicGeometry.ProEtale.HasFiniteConstantLocalModel` a
second time. The dependency change is therefore left out (the node keeps N7's landed record,
merge_delivery --revert-nodes sk-def-sfb-constructible), and so is `ScalarConstructible.lean`.
The item module now imports N7's module (plus the stratification and free-module modules that
came in through the dropped one), and the adaptation hypothesis of clause (2) reads
`HasFiniteConstantLocalModel Λ (P.domain a) (...)` with N7's explicit scheme argument. N7's
predicate uses a finitely presented Lambda-module on the point. That is equivalent to the
dropped scalar-matrix cokernel form, so the item's mathematics and its `lean.statement` are unchanged.
The fixed module compiles clean through nt_compile.py (4.2 s); its axioms are propext, sorryAx,
Classical.choice and Quot.sound.
