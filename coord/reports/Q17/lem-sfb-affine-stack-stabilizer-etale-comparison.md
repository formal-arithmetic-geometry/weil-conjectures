## Worker report

Item: lem-sfb-affine-stack-stabilizer-etale-comparison. Group Q17, stage 2,
2026-10-23. Module: Sheaf.AlgebraicGeometry.AffineStackStabilizerEtaleComparison.
Declaration: AlgebraicGeometry.exists_affineStack_stabilizer_etale_comparison.
The sole theorem has proof `by sorry`. No definitions or other theorems are added.
The accepted statement, statement dependencies, proof, and proof dependencies are unchanged.

The earlier worker's stage-1 stale-assignment ending does not apply to this task:
coord/brief-stage2.md §0 explicitly says a reviewed stage-1 split is stage-2 input.
The live node is split and reviewed by NW/L, has no Lean record, and queue.tsv lists
it in stage 2. No released repair note exists for this item. This delivery records
its statement without reopening the split.

Sources read: stacks-more-morphisms.tex, Tag 0DUS,
lemma-etale-separated-over-well-nigh-affine (statement and complete proof), and
Tag 0DUR, lemma-moduli-space-finite-affine. The recorded dependency interfaces
were read in StablePointedModuliGroupoids.lean and AlgebraicSpace.lean, together
with the scheme property declarations in the pinned Mathlib sources. The theorem
contains all six accepted proof steps in its docstring, including categorical
uniqueness, invariant affine opens, the groupoid comparison, overlap cocycles,
stack descent, and separatedness descent.

Hypotheses and clauses, individually:

- A scheme S in the size convention: `{S : Scheme.{u}}`; the two total categories
  have explicit, independent object and morphism universes `v₁ w₁ v₂ w₂`.
  Test schemes are `Over S`, so the tests use the same scheme universe as S.
- A/S and B/S are Deligne--Mumford stacks: `A`, `B : BasedCategory (Over S)` and
  `hA : IsDeligneMumfordModuliStack A`, `hB : IsDeligneMumfordModuliStack B`.
  This uses the recorded CFG, descent, diagonal, and atlas conditions.
- An affine cover: `U : Over S`, `hU : IsAffine U.left`, and
  `p : BasedFunctor (discreteModuli (yoneda.obj U)) A`.
- The cover is representable, surjective, finite, flat, and locally of finite
  presentation: `hp` tests every scheme T and every t into A. It provides a
  scheme V, a projection f to T, and an equivalence to the actual 2-base change.
  `ModuliTwoIso` identifies its first projection with `yoneda.map f`.
  `IsFinite f.left`, `Flat f.left`, `LocallyOfFinitePresentation f.left`, and
  `Surjective f.left` are exactly the four scheme properties. Finite
  representable maps to scheme tests have scheme sources, so these witnesses
  express the stated finite cover, with no extra choice of a global presentation.
- The quotient has affine scheme target: `M : Over S`, `hM : IsAffine M.left`.
  `q : BasedFunctor A (discreteModuli (yoneda.obj M))` is the given map.
- Uniform categorical: `hq` quantifies over every algebraic space M₁/S and
  every a : M₁ → h_M. Flatness is the premise testing every representable étale
  scheme chart b of M₁, with `Flat (yoneda.preimage (b ≫ a)).left`.
  It then quantifies over every algebraic space Z/S. The displayed
  `Function.Bijective` is composition from Hom(M₁,Z) with the actual first
  projection `moduliTwoFiberFst (discreteModuliMap a) q` of M₁ ×_M A.
  Thus both existence and uniqueness of the factorization are retained.
- The given h : B → A is `h : BasedFunctor B A`.
- Representability by spaces is `hrep : IsRepresentableByAlgebraicSpaces h`.
- Étaleness is `het`: every algebraic-space presentation of every scheme
  base change, recognized by `HasSpaceBaseChange`, satisfies the recorded
  `SpaceMapIsEtale` chart condition. Representability ensures these tests exist.
- Separatedness is `hsep`: for these same base changes with projection a,
  `AlgebraicSpace.IsRepresentableWith (fun _ _ f ↦ IsProper f.left)
  (pullback.diagonal a)` is properness of the relative diagonal, with every
  scheme base change checked. It is not properness of a itself.
- The isomorphism of automorphism sheaves is `haut`: for every T/S and
  b in `Functor.Fiber B.p T`, the canonical `moduliFiberMap h T` is bijective
  on b ≅ b. These are actual automorphisms in the fibre, not isomorphism
  classes of objects. Testing every scheme and every object tests all
  restrictions of b, hence is precisely the sheaf isomorphism condition.
- The output is an S-scheme `N : Over S` and an S-morphism `f : N ⟶ M`.
- Separated and étale output map: `IsSeparated f.left ∧ Etale f.left`.
- The required S-map from B: the existential
  `qB : BasedFunctor B (discreteModuli (yoneda.obj N))`.
- The square is 2-cartesian: the existential `e` goes from B to the recorded
  2-fibre product of N → M with q, and `e.toFunctor.IsEquivalence`.
  Its first projection is qB. Its second projection is exactly h.toFunctor,
  enforced by the explicit equality using `ObjectProperty.ι` and `Comma.snd`.
  The isomorphisms in the comma objects supply commutativity of the square.
  These strict projection equalities are an explicit comparison convention:
  from a 2-commutative square the canonical comparison has these projections;
  conversely such an e supplies that square and its comparison equivalence.

Dependency declarations used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom;
  affine schemes use Mathlib's IsAffine.
- def-weil-size-convention is its recorded metatheoretic convention, realized by
  the explicit universe declarations; it contributes no importable declaration.
- Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids:
  CategoryTheory.IsDeligneMumfordModuliStack, discreteModuli, discreteModuliMap,
  moduliTwoFiberProduct, moduliTwoFiberFst, ModuliTwoIso, moduliFiberMap,
  IsRepresentableByAlgebraicSpaces, HasSpaceBaseChange, SpaceMapIsEtale.
  Its BasedCategory/BasedFunctor and Fiber interfaces are the Mathlib ones.
- Sheaf.AlgebraicGeometry.AlgebraicSpace:
  AlgebraicGeometry.AlgebraicSpace, AlgebraicSpace.IsEtale,
  AlgebraicSpace.IsRepresentableWith. This module is publicly provided by the
  stable-pointed dependency; no private algebraic-space definition is introduced.
- Mathlib.AlgebraicGeometry.Morphisms.Finite: AlgebraicGeometry.IsFinite.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: AlgebraicGeometry.Flat.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:
  AlgebraicGeometry.LocallyOfFinitePresentation.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: AlgebraicGeometry.IsProper,
  AlgebraicGeometry.IsSeparated.
- Mathlib.AlgebraicGeometry.Morphisms.Etale (publicly supplied by the stable-pointed
  dependency): AlgebraicGeometry.Etale.
- Mathlib.CategoryTheory.Limits.FunctorCategory.Basic supplies presheaf limits;
  the relative diagonal is Mathlib's pullback.diagonal.

Already recorded proof dependencies are imported privately, as required:
Sheaf.AlgebraicGeometry.SeparatedEtaleSpaceScheme
(AlgebraicSpace.exists_scheme_of_separated_etale),
Sheaf.AlgebraicGeometry.EtaleSpaceLocallyQuasiFinite
(AlgebraicSpace.chartwise_isLocallyQuasiFinite_of_etale),
Sheaf.AlgebraicGeometry.AffineGroupoidIntegralInvariants
(isIntegral_affineGroupoid_invariants),
WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
(Scheme.Hom.IsFiniteLocallyFree), and
WeilConjectures.AlgebraicGeometry.IsSeparatedOfSurjectiveUniversallyClosed
(isSeparated_of_surjective_universallyClosed).
The remaining proof-only nodes have no recorded Lean modules at the time of writing;
their accepted proof statements are preserved and named in the docstring.

Edge cases checked before writing and again against the final signature:
empty U/A/B/M are not excluded; no Nonempty, field, characteristic, finite-type,
quasi-compactness, finite index, or Noetherian hypothesis is added. B need not
admit one finite affine cover, and N is not required affine or quasi-compact.
Nontrivial stabilizers are retained: the test is bijectivity on the canonical
maps of automorphisms, not triviality. All algebraic spaces M₁ and Z are allowed,
including non-schemes; identity and arbitrary flat base changes are included.
In particular q is not assumed representable, and no geometric-point-bijection
or universal-homeomorphism hypothesis is added to its categorical property.
There is no independent smaller universe of test schemes that could make tests
vacuous. The conclusion remembers h, rather than asserting an unrelated
abstract equivalence of stacks.

Searches made on 2026-10-23 (msearch.py Q17 and this item, logged in searches.jsonl):

- leanfinder: "A separated etale stabilizer preserving map of Deligne Mumford stacks
  with finite flat affine cover descends to a cartesian etale map of categorical
  quotient schemes". Eight hits: scheme Etale, stability, scheme small étale
  categories; none is the stack comparison.
- loogle: `"stabilizer", "etale"`. Zero hits.
- grep: `UniformCategorical|uniformCategorical|StabilizerPreserv|stabilizer.preserving|well.nigh.affine`.
  Zero hits in Mathlib.
- leansearch: "Etale stabilizer preserving maps of stacks descend along a uniform
  categorical affine quotient". Eight hits on scheme descent, étaleness, and
  abstract morphism-property descent; none states this stack comparison.
- rg on lean/WeilConjectures and lean/Sheaf for
  `uniformCategorical|UniformCategorical|FiniteFlatAffineCover|StabilizerPreserv|stabilizerPreserv|IsSeparated.*Moduli|Has.*Cover|IsModuli.*Etale|SpaceMapWith`:
  only unrelated cover definitions; no existing comparison or categorical-quotient
  interface. The exact item-id search over both library roots returned no hits.
- rg over both library roots and Mathlib for the proposed declaration name:
  zero hits. DAG keyword searches show the statement-only related groupoid and
  coarse-space nodes; none supplies an existing Lean declaration for this item.

No node fault, statement correction, or STATEMENT-DISPUTED flag.
The first scompile.py run compiled both the sandbox and actual library module
cleanly (3.6 s and 3.8 s), with no errors or warnings.

## Second reading by Q17

Direct-dispatch worker self-check; no second agent was started, as the dispatch
explicitly forbids it. The maintainer's independent review reads this delivery.
I reread the node and final Lean signature after the successful compile. Every
hypothesis and conclusion is mapped above. In particular, the uniform property
quantifies over algebraic spaces, properness is on the relative diagonal, the
stabilizer map is the one induced by h on every fibre, and the comparison fixes
both projections. These checks found no mismatch requiring a change to the
accepted node. The signature has no hidden let, unbound variable, private
notation, hollow definition, or extra hypothesis. Only the lean record changes.
