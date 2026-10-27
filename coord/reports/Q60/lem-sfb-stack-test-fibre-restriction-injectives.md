## Worker report

The module `Sheaf.AlgebraicGeometry.StackTestFibreRestrictionInjectives` states
`CategoryTheory.moduliTestFibreRestriction_exact_preservesInjectives`. Its definitions
construct literal module precomposition along the actual recorded 2-fibre projection;
its three theorem proofs are `sorry`. No node statement or dependency list is changed.

Hypotheses and clauses:

- The fixed size convention is rendered by explicit universes `u v w v' w'`;
  `S : Scheme.{u}`, `X : BasedCategory.{v,w} (Over S)` and
  `Y : BasedCategory.{v',w'} (Over S)` keep their universes independent. Modules have
  universe `max (u+1) v w v' w'`, containing both total sites and the scheme tests.
- `hX : IsAlgebraicModuliStack X` and `hY : IsAlgebraicModuliStack Y` express exactly
  the two algebraic-stack hypotheses. Their `.1.1` components are the recorded
  fibred-in-groupoids hypotheses used to construct the structure sheaf.
- `h : BasedFunctor X Y` is the arbitrary stack morphism over S. There are no
  representability, quasi-compactness, quasi-separatedness or flatness assumptions.
- `V : Over S` is the test S-scheme. The object over V is written as
  `y : BasedFunctor (discreteModuli (yoneda.obj V)) Y`, exactly the convention in
  def-sfb-stable-pointed-moduli-groupoids: a map from V means an object over V.
  The 2-Yoneda identification retains its automorphisms. Every test object admits
  this description; no representability of Y or special test object is imposed.
- `etale : Bool` encodes the two choices of topology: true is the comap of
  `Scheme.etalePrecoverage`; false is the recorded `moduliFppfTopology`. Both keep
  the whole total category, including every scheme map as an arrow.
- `moduliTestFibre h y` is `moduliTwoFiberProduct h y`, not a replacement by
  isomorphism classes or an arbitrary fibre object. `moduliTestFibreProjection` is
  the recorded `moduliTwoFiberFst` projection, forgetting the scheme-test factor.
- `moduliTestFibreModuleRings` uses `moduliStructurePresheaf`, forgetting
  commutativity. In the fppf case this is the recorded `moduliModuleRings` up to
  irrelevant sheaf-condition proof. The etale case changes only the topology.
- `moduliTestFibreRestrictedRings` is precisely continuous precomposition of that
  ring by the projection. On a triple over T it is the same lifted Gamma(T,O_T),
  with the same pullback maps. Thus the asserted inverse-image structure-ring
  identification is built into the definition, not supplied as a hypothesis.
  The source's canonical `ULift.ringEquiv` identifies these values with Gamma(T,O_T).
  We retain this transported presentation on the fibre, avoiding another independently
  lifted presentation with a different universe. This is the same ringed site.
- `moduliTestFibreRestriction` is Mathlib's `SheafOfModules.pushforward` along
  the projection with identity structural ring map. Its presheaf is precomposition;
  at (x,t,alpha) its module is M(x). `PresheafOfModules.pushforward₀Obj` reuses
  M's restriction maps and scalar action, and the identity scalar restriction changes
  none of them. Morphisms are the original sectionwise linear maps as well.
- The theorem's four conjuncts express additivity, exactness through preservation
  of finite limits and finite colimits, and preservation of injective objects.
  The categories of module sheaves on these small sites are abelian, so the middle
  two conjuncts are exactly short-exact-sequence preservation. Mathlib's
  `Functor.PreservesInjectiveObjects` means that for every I, `Injective I` implies
  `Injective (restriction.obj I)`. The module categories contain all module sheaves;
  there is no quasi-coherence predicate anywhere in the statement.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack` and its underlying `IsModuliStack`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsFibredInGroupoids`, `discreteModuli`, `moduliTwoFiberProduct`,
  `moduliTwoFiberFst`, and `BasedFunctor` from Mathlib's BasedCategory module.
- `Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra`:
  `moduliSchemeForget`, `moduliFppfTopology`, `moduliStructurePresheaf`, and
  `moduliStructurePresheaf_isSheaf`. No quasi-coherent-algebra specialization is used.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, used by
  the scheme etale precoverage; this is the recorded etale-morphism predicate.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `CategoryTheory.Injective`
  and `CategoryTheory.Adjunction.map_injective`. The preservation class comes from
  `Mathlib.CategoryTheory.Preadditive.Injective.Preserves`.
- Plain proof imports: `Sheaf.AlgebraicGeometry.AlgebraicStackTotalEqualizers`
  (`hasEqualizers_of_isAlgebraicModuliStack`) and
  `Sheaf.CategoryTheory.RingedSiteSliceExactShriek`
  (`exists_exact_moduleLeftAdjoint_of_sliceEquivalences`). Other proof dependencies
  have no recorded Lean statement in the supplied DAG and contribute no import.

The helper sheaf-condition and continuity theorems express obligations of the same
canonical restriction construction in this node, with source/proof docstrings, and
are listed in lean.declarations. They are not new independent mathematical notions.
Definitions have real data; no existence theorem is used to choose an arbitrary functor.

Source checked: local `literature/stacks-project/stacks-sheaves.tex`,
lemma-functoriality-sheaves (06TS), lemma-pullback-injective-modules (06X2), and
its faithful-functor/equalizer route. The main theorem docstring carries all six
steps of the accepted node proof and names their DAG inputs.

Edge cases checked: empty V or an empty fibre gives the usual module category on
that site; no nonempty binder occurs. Identity h still uses the same 2-fibre
projection. Nontrivial stabilizers are retained by the comma/full-subcategory
construction. A closed immersion V into a target test is allowed: no flatness of
the test map or of h is used. Zero modules and arbitrary non-quasi-coherent modules
are included. Both Boolean values retain the same objects, ring values and maps.
The site and coefficient universes are never forced equal.

Searches for an existing statement:

- msearch LeanFinder: "restriction to a test scheme fibre of an algebraic stack is
  exact and preserves injective modules". Eight hits: scheme-module abelian structure,
  local injectivity and scheme restrictions; none states this stack-fibre result.
- msearch LeanSearch: "restriction of module sheaves to a test fibre of an algebraic
  stack preserves injective objects". Eight hits about scheme open restriction,
  scalar restriction, sheaf sections and local injectivity; no matching result.
- msearch Loogle: `"preservesInjectiveObjects"`. Eleven hits include the existing
  preservation class and the adjunction transfer theorem, but no test-fibre statement.
  Those existing Mathlib notions are used directly.
- msearch grep: `stack.*injective|injective.*stack|moduli.*[Rr]estriction`.
  Four unrelated Mathlib hits (affine limits, universally injective maps, minimal primes).
- Direct rg in lean/WeilConjectures and lean/Sheaf for the node ID, moduli injectivity,
  and stack injectivity found no statement matching this node. Exact node-ID grep in
  WeilConjectures found none. Broader moduli restriction searches found the existing
  fppf precomposition API and small-etale restriction API, read for comparison;
  neither supplies the two-topology test-fibre result. The restricted-universe
  `fibredBigEtaleTopology` in FibredRelativeCech has the same defining etale comap;
  our Boolean selector writes that comap for independent site universes and uses
  the existing fppf topology in its other branch.

Validation: scompile.py compiled the sandbox module and its actual library module
cleanly on 2026-10-24 (9.5 s and 3.7 s). The first attempt identified an invalid
instance attribute on a theorem with explicit Prop arguments; the attribute was
removed, leaving an ordinary named theorem used explicitly in definitions.
No statement fault or STATEMENT-DISPUTED issue was found.

## Second reading by Q60

A second pass by the delivering worker checked the node and module together against
every row above: both topologies, arbitrary h, actual 2-fibre product, original module
values/actions/maps, structure-ring precomposition, exact additivity, and injective
preservation are present. The test-object-as-map encoding agrees with the recorded
moduli convention. Independent site universes and empty fibres are allowed. No
hypothesis is supplied as an assumption merely to type the functor: its sheaf and
continuity obligations are named theorems of this node. No mathematical correction
was needed. The maintainer's independent delivery review is separate from this
self-check; no second agent was started, as instructed by the dispatch brief.
