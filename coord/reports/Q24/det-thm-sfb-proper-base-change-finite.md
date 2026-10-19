## Worker report

The delivery states `AlgebraicGeometry.ProEtale.CondensedRing.finiteProperBaseChange` in
`Sheaf.Paper.FiniteProperBaseChange`. Its only postponed proof is that theorem's `sorry`.
The docstring reproduces all eight DAG proof steps, including the geometric-fibre bound,
finite-proper Tor hypotheses, boundedness of the tensor input, and identification of the
canonical projection map by its transpose. The node's mathematical statement is unchanged.

Two helpers belong to this theorem's coefficient/map interface, rather than introducing
independent mathematical notions:

* `finiteProperCoefficientRing A` bundles the existing `Sheaf.sheafifyRingPresheaf`
  construction applied to the constant `ULift A` ring presheaf on `Profinite`. Its data are
  written in full. Commutativity uses the existing
  `Functor.isCommMonObj_compForget₂` and sheafification instances. No existence theorem or
  unproved choice supplies its data. This is the constant condensed ring underlying a finite
  discrete ring, without adding topology binders or restricting coefficients to `Type 0`.
* `finiteProperAmbientExchange Λ sq` is `CategoryTheory.mateEquiv` for the actual derived
  pullback/direct-image adjunctions. The input is the inverse composition isomorphism for
  `p',g`, the square equality, and the forward composition isomorphism for `g',p`.
  This constructs the canonical unit/square/counit arrow on the ambient unbounded categories.
  In particular it does not assume constructible direct image or a restricted adjunction.

Hypotheses and clauses, in the order of the node:

| Node | Lean |
| --- | --- |
| Finite commutative ring A | `(A : Type u) [CommRing A] [Finite A]` |
| Prime ell | `(ℓ : ℕ) [Fact ℓ.Prime]` |
| Killed by a power of ell | `_hA : ∃ r : ℕ, (ℓ ^ r : ℕ) • (1 : A) = 0`; multiplying this equality by any element gives the whole-ring assertion |
| Standing field, positive characteristic different from ell | `(k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]` |
| X,Y separated finite type over that same field | `X Y : Over (Spec (.of k))`, with `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on both structure morphisms |
| p is a k-morphism and proper | `(p : X ⟶ Y) [IsProper p.left]` |
| Dctf | The exact dependency `ConstantModelConstructibleFiniteTor (finiteProperCoefficientRing A).X`; its objects have bounded constant-model-constructible cohomology and finite Tor amplitude |
| (1) Rp_* maps Dctf(X,A) into Dctf(Y,A) | The first universally quantified conjunct requires `constantModelBoundedConstructible ... Y.left ⊓ DerivedCategory.finiteTorAmplitude _` of `(lowerStar ... p.left).rightDerivedFunctor.obj K.obj` |
| (2) A cartesian square | The second conjunct binds `g,p',g'` and `sq : ChosenCartesianSquare g' p' p.left g`; the chosen fibre-product identification and both projection equalities are retained |
| (2) The specified exchange is an isomorphism for every K in Dctf | `IsIso ((finiteProperAmbientExchange ... sq.toCommSq).app K.obj)` in the full derived category on Y' |
| (3) K in Dctf(X,A), M in Dctf(Y,A) | The third conjunct binds both objects of the recorded full subcategories |
| (3) The specified projection map is an isomorphism | `IsIso ((((derivedUpperStarLowerStarAdjunction ... p.left).rightAdjointProjectionMap (leftDerivedUpperStarTensor ... p.left)).app K.obj).app M.obj)` |

Clause (2) follows the node's arbitrary-base-change/ambient-category formulation: X',Y'
are arbitrary schemes in the same size convention, and there is no properness, flatness,
smoothness, or constructibility assumption on g or on the pulled-back object. No
constructibility statement for a non-standing base-change scheme is added. Clauses (1)
and (3) use exactly the standing X,Y and p of the source.

Dependency declarations read and used:

* `sk-def-sfb-dc-setting`: the recorded
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` was read
  both locally and through `scompile.py --source`. Its current setting is `Over (Spec k)`
  with separated finite-type structure morphisms and positive characteristic distinct
  from ell. These conditions are explicit binders here. The theorem does not use a
  compactification, since its map p is already proper.
* `sk-def-sfb-constructible`:
  `Sheaf.Paper.CondensedConstantConstructibility`, declarations
  `constantModelBoundedConstructible` and `ConstantModelConstructibleFiniteTor`, are used
  verbatim. No generic local-finite-presentation substitute is used.
* `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `IsProper`;
  its `UniversallyClosed` structure implies quasi-compactness, so locally finite type
  agrees here with finite type.
* `def-weil-pbc-cartesian-square`: `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`,
  `ChosenCartesianSquare` and its `toCommSq`; full signatures and projection fields read.
* `def-weil-pbc-proetale-operations`: the recorded
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` is imported. The theorem uses
  the internal-module presentation of these same ordinary identified-coefficient
  operations, publicly available through the recorded setting module:
  `CondensedRing.upperStar`, `lowerStar`, `derivedUpperStarLowerStarAdjunction`, and
  `leftDerivedUpperStarComp` in the published
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`. The current
  server source was read in full for those signatures and docstrings. These are exact
  pullback and K-injective-derived direct image over the pulled-back coefficient ring.
* `sk-def-sfb-derived-tensor-hom`: the recorded
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom` and its tensor imports
  give the relative K-flat derived tensor on the identical internal-module categories.
* `def-weil-pbc-adjunction-mate`: its Mathlib match `CategoryTheory.mateEquiv` in
  `Mathlib.CategoryTheory.Adjunction.Mates` is used directly; its full component formula
  and inverse were read.
* Added landed statement dependency `new-proetale-derived-module-pullback-monoidal`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`, in particular
  `leftDerivedUpperStarTensor` and its canonical representative characterization.
  This current source is missing in the local old checkout and was read through
  `scompile.py --source`. Its comparison is derived from the ordinary tensorator;
  `Adjunction.rightAdjointProjectionMap` is then the exact counit mate in clause (3).

Every recorded proof-dependency module with a usable declaration is imported normally
(without public). The two proof nodes `det-pe-finite-tor-comparison-noetherian` and
`sk-thm-pe-constructible-comparison` have no current Lean record or Mathlib match and
therefore supply no import; they remain proof obligations for stage 3. The proper
base-change-stability Mathlib match is already included by the properness import.

Edge cases checked before writing:

* A=0 and annihilating exponent r=0 are included. No Nontrivial instance is imposed.
  In the proof r can be enlarged to a positive exponent. A finite ring of infinite
  global dimension is included: only the objects have finite Tor amplitude.
* The zero complex, empty X or Y, and empty geometric fibres are included. No Nonempty,
  positive-dimension, or positive-cohomology-degree hypotheses occur.
* Identity p or g, nonflat g, and arbitrary chosen Cartesian identifications are
  included. The mate depends only on the given square commutativity, rather than on
  an extra chosen natural isomorphism. Properness of p' is not an added hypothesis.
* The coefficient and scheme universe is an arbitrary explicitly bound u. The profinite
  and pro-etale site size conventions and coefficients in Ab.{u+1} are retained.
  The constant-ring construction uses ULift, rather than restricting finite rings to
  the Type-0-only continuous-function implementation.
* All degrees and Tor intervals are inherited from the recorded predicates. The theorem
  adds no numerical bound and no coefficient regularity or completion assumption.

Searches for an existing exact declaration:

* `msearch.py ... leansearch "Proper pushforward of bounded constructible finite Tor etale
  sheaves satisfies base change and projection formula"`: eight hits, ordinary sheaf
  pushforwards and structure-sheaf module pushforward, no derived finite-coefficient theorem.
* `msearch.py ... leanfinder "Proper direct image preserves bounded constructible finite Tor
  complexes for finite coefficients and satisfies base change and projection formula"`:
  eight hits, morphism-property base-change stability, constructible images of subsets,
  and light condensed-module results, no match.
* `msearch.py ... loogle "AlgebraicGeometry.IsProper, CategoryTheory.IsIso"`: zero hits.
* `msearch.py ... grep "proper.*base.?change|projection.?formula|constructible.*Tor"
  AlgebraicGeometry`: 25 hits, scheme morphism properties and pretopology, no match.
* `rg` of the source `WeilConjectures/`, shared `lean/Sheaf/`, and
  `lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/` found scalar-coefficient
  projection maps, the restricted bounded-constructible exchange, and the current
  canonical monoidal module. None states these three clauses for the newly recorded
  constant-model Dctf. `grep -rn` for the item id in source `WeilConjectures/` found no
  declaration. The upstream-name-index search found no item-id match.
* Targeted DAG searches found the already landed monoidal interface node, which is cited
  rather than rewritten. Searches found no ambient internal-module mate with the new
  helper's name. The helper specializes the existing general mate/composition machinery.

No statement dispute or source correction is needed. No new DAG nodes or dependency
modules are introduced. The only DAG changes are the item's Lean record and the added
landed monoidal statement dependency.

## Second reading by Q24

Self-review with the node and final module open: the coefficient helper is constructed
from the sheafified constant ring, with no sorry data or auxiliary topology hypotheses.
The three conjuncts use precisely the dependency's constant-model Dctf. The first is
membership after Rp_*; the second asserts invertibility of the actual ambient mate at
each allowed K; the third is invertibility of the right-adjoint tensor projection at
both K and M. The standing field and scheme hypotheses and proper k-morphism are explicit.
No arbitrary exchange/comparison arrow, existence-only isomorphism, coefficient equivalence,
regularity or completion has been assumed. A preliminary scalar-presentation draft was
replaced by the current internal-module statement after reading the newer server monoidal
interface. A subsequent size review replaced the Type-0 continuous-function coefficient
model by the universe-polymorphic sheafified constant-ring construction.

The dispatcher forbids starting other agents and assigns the maintainer the independent
review of this delivery. This section records the worker's own second pass, not a claim
that a separate worker has reviewed it.

## Validation

The prescribed `scompile.py` check passed both the sandbox module and the final library
module, with no errors or warnings. The file retains only the expected theorem `sorry`;
both helper definitions contain their complete construction. A documentation-only module
index was added afterwards and is included in the delivery dry-run compile. The copied
node differs from the shared node only in `lean` and the added landed statement dependency.
There is no item-specific maintenance repair note.
