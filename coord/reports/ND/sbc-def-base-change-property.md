## Worker report

The module `Sheaf.AlgebraicGeometry.CumulativeUniversalBaseChangeProperty` adds only
`AlgebraicGeometry.Etale.CumulativeUniversalBaseChangeProperty`. The single-degree and
universal single-degree notions already exist in the source and are reused without copies.
There are no theorem declarations, proofs or `sorry`s in this delivery. The node is unchanged
outside its `lean` field. No statement correction, new node or dependency module is needed.

Clause-by-clause correspondence:

- Schemes and their morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Positive integer n: `(n : ℕ) (_hn : 0 < n)`. Positive integers are represented by positive
  natural numbers, with no lost case.
- n invertible on S: `(_hinv : IsUnit (n : Γ(S, ⊤)))`. This is the source convention for
  invertibility of the constant integer on a scheme.
- Nonnegative degree: `(q : ℕ)`; the existing property uses `(q : ℤ)`.
- Coefficients Z/nZ: `ULift.{u + 1} (ZMod n)`. ULift makes the ring live in the existing
  module-sheaf coefficient universe; it changes neither the ring nor its modules. For
  positive n it is finite and killed by n. Thus the two proof binders give exactly the
  coefficient domain of `IsSmoothBaseChangeCoefficients` for this fixed ring. They are
  deliberately proof parameters, rather than extra conjuncts in the property.
- Fixed-base BC(f,n,q) is the existing `AlgebraicGeometry.Etale.BaseChangeProperty`
  specialized to that coefficient ring and degree `(q : ℤ)`. Its full signature and body
  were read in `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs`: for arbitrary
  `T Y : Scheme.{u}`, `g : T ⟶ S`, `e : Y ⟶ T`, `h : Y ⟶ X`, it requires
  `[QuasiCompact g] [QuasiSeparated g]`, `sq : IsPullback e h g f`, and every
  `F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`; the conclusion is
  `IsIso (Etale.baseChangeHomologyMap Λ sq q F)`. This is exactly the permitted module
  formulation of abelian sheaves annihilated by n.
- The square dependency is `ChosenCartesianSquare h e f g` and its
  `ChosenCartesianSquare.baseChangeInverseImageIso`, in
  `Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso`. The underlying square is Cartesian;
  in the source predicate its exchanged orientation is `IsPullback e h g f`. Existence
  of the chosen pullback identification and the pullback property are equivalent. The
  definition of the exchange depends on the commutative square, so quantifying over all
  chosen identifications gives the same condition.
- The map dependency records `Etale.derivedBaseChangeMap` in
  `WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded` and explicitly authorizes its
  existing degreewise bounded-below presentation `Etale.baseChangeHomologyMap` in `Defs`.
  The latter is the homology of the exchange evaluated on the sheaf in degree zero. Its
  signature, docstring and implementation were read; the existing fixed-degree predicate
  uses precisely that map. As already recorded in the dependency, the comparison between
  bounded-below and unbounded presentations remains proof work, not a new map definition.
- The fixed-base cumulative condition is the expression
  `∀ r : ℕ, r ≤ q → BaseChangeProperty (ULift.{u + 1} (ZMod n)) f (r : ℤ)`.
  It combines the existing definition and needs no duplicate named predicate.
- Universal single-degree BC is the existing `Etale.UniversalBaseChangeProperty`: it
  quantifies over every `S' X' : Scheme.{u}`, `a : S' ⟶ S`, `b : X' ⟶ X`, `f' : X' ⟶ S'`
  with `IsPullback b f' f a`, then asks `BaseChangeProperty Λ f' q`. There is no qcqs
  restriction on a or on its composite with the horizontal side. Invertibility of n on
  the new base follows from pullback; no additional invertibility hypothesis is added.
- UBC through q is exactly the new body
  `∀ r : ℕ, r ≤ q → UniversalBaseChangeProperty (ULift.{u + 1} (ZMod n)) f (r : ℤ)`.
  The lower bound is enforced by the natural-number index, so no negative degrees are
  inadvertently included. The Stacks cumulative convention was checked directly in
  `literature/stacks-project/etale-cohomology.tex`, Remark `remark-base-change-holds`
  (Tag 0F02), which quantifies over both successive base changes.

Dependency imports: `SmoothBaseChangeCoefficients` provides
`AlgebraicGeometry.Etale.IsSmoothBaseChangeCoefficients` and the ambient sheaf conventions;
`BaseChangeInverseImageIso` provides the chosen Cartesian-square convention and comparison.
The scheme-conventions node is explicitly a convention-only record: Scheme, QuasiCompact
and QuasiSeparated are the Mathlib definitions used by the source predicate. The imports
also document exactly which convention modules underlie this specialization.

Edge cases checked before writing: q = 0 includes degree zero, not an empty range; q > 0
includes both endpoints. n = 1 is allowed (zero coefficient ring and zero sheaves);
n = 0 is excluded by the explicit positivity proof. Empty schemes and empty pullbacks are
allowed. No smoothness, finiteness, separatedness or nonemptiness hypothesis is imposed on
f or on arbitrary base changes. All test schemes use the same scheme universe, so the
base-change quantifier does not become vacuous in a smaller independent universe.
There is no claim that fixed-base BC implies universal BC. No statement is disputed.

Searches performed:

- `msearch.py ... leansearch "cohomological base change property etale sheaves"`:
  service unavailable (Internal Server Error); no mathematical verdict inferred.
- `msearch.py ... leanfinder "universal cohomological base change property for etale sheaves"`:
  eight hits on etale topology and stability of etale morphisms, no predicate match.
- `msearch.py ... loogle '"baseChange"'`: twelve hits on scalar extension for modules,
  no cohomological predicate.
- `msearch.py ... grep 'BaseChangeProperty|UniversalBaseChangeProperty'`: no Mathlib hits.
- `rg` in source WeilConjectures for BaseChangeProperty, baseChangeProperty and the node id:
  found and read `Etale.BaseChangeProperty` and `Etale.UniversalBaseChangeProperty` in
  `SixFunctors/Etale/SmoothBaseChange/Defs.lean`. Neither is copied. Source induction
  theorems use cumulative quantifiers inline; there is no named cumulative definition.
- `rg` in project `lean/Sheaf` for the same names and UBC: found consumers of the source
  predicates, no cumulative definition. Checked the proposed declaration name against
  the source and project search results; no collision found.

Validation: server single-file compilation passed cleanly (2.6 seconds for the delivered
module; nice 19, two threads, 60 seconds per file). The delivery dry run printed OK: compile and preflight passed, with only the independent
second-reading section reserved for the second reader. Nothing was pushed. The second reader supplies their own
independent reading and performs delivery.

## Second reading by ND

I independently read the item JSON, the sandbox module, the blueprint defining paragraph,
Stacks `etale-cohomology.tex`, Remark `remark-base-change-holds` (Tag 0F02), all four
statement-dependency records and their declarations. The source remark introduces only
schemes, a morphism and an integer before its two successive Cartesian squares; it does
not impose smoothness, Noetherianness or finiteness on the schemes. The node explicitly
restricts its coefficient domain to positive n invertible on S, and distinguishes the
single-degree condition from the Stacks cumulative universal condition. I compared the
Lean with that node, rather than replacing its condition by the unrestricted Stacks domain.

Object, hypothesis and clause checklist (all pass):

1. Schemes X and S and their morphism f: `{X S : Scheme.{u}} (f : X ⟶ S)`.
   No geometric property of f is assumed.
2. Integer n at least one: `(n : ℕ) (_hn : 0 < n)`. This parametrizes every positive
   integer and excludes precisely the node's excluded nonpositive integers.
3. n invertible on S: `(_hinv : IsUnit (n : Γ(S, ⊤)))`, the source's explicit global
   section convention. This is a domain proof parameter, not an assumption that a
   quantified sheaf or horizontal morphism must satisfy.
4. Nonnegative q: `(q : ℕ)`. Degrees passed to the upstream map are cast to ℤ.
5. The coefficient ring Z/nZ: `ULift.{u + 1} (ZMod n)`. This is the same ring after a
   size lift. Its modules are precisely abelian groups killed by n, not a class of
   locally constant or constructible sheaves. For positive n the ring is finite and
   killed by n. Reading `IsSmoothBaseChangeCoefficients` confirms that the two proof
   parameters supply its remaining conditions; no coefficient hypothesis is lost.
6. Fixed-base single-degree BC: the already existing `Etale.BaseChangeProperty` in
   `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs`, specialized to that ring,
   quantifies over `{T Y : Scheme.{u}}`, `g : T ⟶ S`, `e : Y ⟶ T`, `h : Y ⟶ X`,
   `[QuasiCompact g] [QuasiSeparated g]`, `IsPullback e h g f`, and
   `F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`. Its conclusion is exactly
   `IsIso (Etale.baseChangeHomologyMap Λ sq q F)`. Both qcqs hypotheses are on g,
   and none is imposed on h, e or f. This renders each quantifier and the whole
   single-degree isomorphism clause without making a second definition.
7. The square: I read `ChosenCartesianSquare` and
   `ChosenCartesianSquare.baseChangeInverseImageIso`, not just their names. The
   structure's identification with the pullback respects both projections. Its
   existence is precisely the pullback property used by the existing predicate
   (with the two sides exchanged). The canonical comparison is the inverse of
   `Etale.squareUpperStarIso`. A choice of the identification adds no mathematical
   restriction to a condition quantifying over every Cartesian square.
8. The map: I read `Etale.baseChangeHomologyMap`, its source/target functors,
   `Etale.baseChange` in `MorphismDefs`, and `derivedBaseChangeMap` in
   `DerivedUnbounded`. The degreewise map is homology of the bounded-below exchange
   at F[0]; source is H^r(f^* Rg_* F[0]), target H^r(Rh_* e^* F[0]). Exact inverse
   images identify these with the displayed classical sheaves. The map dependency
   explicitly records this existing bounded-below presentation. The compatibility
   with the unbounded exchange is comparison proof work already acknowledged there;
   the delivery invents neither a map nor a replacement cohomology theory.
9. Fixed-base cumulative condition: as the module documents, the bounded forall of
   `BaseChangeProperty` is `∀ r : ℕ, r ≤ q → BaseChangeProperty Λ f (r : ℤ)`.
   It has both endpoints and uses the same maps. No extra named definition is needed.
10. Universal single-degree condition: reading `UniversalBaseChangeProperty` gives
    every `a : S' ⟶ S`, `b : X' ⟶ X`, `p' : X' ⟶ S'` with
    `IsPullback b p' f a`, followed by `BaseChangeProperty Λ p' r`.
    There is no qcqs condition on a or on the composite of a with g. Invertibility
    pulls back; the definition does not add a new test-base hypothesis.
11. Cumulative universal condition: the new definition's body is exactly
    `∀ r : ℕ, r ≤ q → UniversalBaseChangeProperty (ULift.{u + 1} (ZMod n)) f (r : ℤ)`.
    Interchanging the independent degree and square universal quantifiers gives
    precisely the two successive squares and all nonnegative degrees through q in
    Stacks 0F02 on the node's coefficient domain. It makes no assertion that the
    fixed-base condition implies the universal one.

Edge cases: q = 0 tests degree zero, not an empty degree range. n = 1 permits the zero
coefficient ring and its zero module sheaves; n = 0 is intentionally excluded. Empty
schemes, empty pullbacks and zero sheaves are all admitted. There is no index-set
nonemptiness requirement, characteristic restriction beyond invertibility of n, or
extra finiteness assumption. The bound variable r is natural, so negative degrees are
not inadvertently required. All test schemes share universe u with X and S, and all
module sheaves have the dependency's universe u+1; no smaller independent test universe
makes the universal condition vacuous. Every variable and universe is bound.

Independent searches used different phrases as well as declaration names:

- LeanFinder: `Etale cohomology exchange isomorphism in all degrees up to a bound after
  arbitrary extension of base scheme`: eight algebraic etaleness/morphism hits, none
  a cohomological predicate.
- Loogle: `"UniversalBaseChangeProperty"`: zero Mathlib hits.
- LeanSearch: `For every Cartesian square the cohomology exchange morphism is invertible
  in nonnegative degrees up to q`: unavailable, Internal Server Error; no verdict drawn.
- `rg` through Mathlib, source WeilConjectures and project lean/Sheaf for cumulative
  names, bounded-forall predicates, `base.change.*(property|holds)`,
  `universal.*base.change` and `cohomological.*base.change`: the source's two existing
  predicates and their consumers were found; no existing named cumulative predicate.
  `Induction.lean` uses cumulative quantifiers inline. The new name does not collide.

No mismatch found; no Lean or node change was necessary. There are no new nodes,
dependency modules or statement corrections to review. The module has real definition
data, no sorry, no theorem proofs, no local notation or hidden instances. Its source
and declaration docstrings carry the required blueprint id; this definition node has
no proof steps. The node's `lean.statement` is verbatim the declaration signature.

Validation: reran server-only scompile.py from the sandbox. It compiled the delivered
module cleanly in 2.5 seconds (and its three side imports separately), nice 19, two
threads, 60 seconds per file. The first invocation used a relative path from the
read-only repository and found no such file; rerunning from the sandbox resolved it
without any compiler or source change. Delivery dry run and push follow this reading.
