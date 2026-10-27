## Worker report

The module states `CategoryTheory.ringedSite_strictPerfect_local_nullHomotopy`,
with its sole proof `sorry`, exactly the local null-homotopy assertion of
Stacks 08FP(2), `sites-cohomology.tex`, lemma-local-homotopy. The proof docstring
includes every step of the accepted finite descending induction. No definitions,
axioms, new nodes, dependency repairs, or statement corrections are introduced.

Hypotheses and clauses, matched individually:

- The arbitrary site is `{C : Type c} [Category.{v} C] (J : GrothendieckTopology C)`.
  Object and morphism universes remain independent. Coefficients live in
  `max c v r`, large enough for the site and with an arbitrary additional universe.
- The commutative ring sheaf is `R : Sheaf J CommRingCat.{max c v r}`.
  `sheafCompose J (forget₂ CommRingCat RingCat)` takes its underlying ring sheaf,
  preserving the actual ring operations. No arbitrary coefficient map is chosen.
- `U : C`; `.over U` is the actual localized ring sheaf on `J.over U`.
  The complexes `P K` have values in the recorded `ringedSiteModules` for that ring.
- The integer `a : ℤ` is arbitrary. Both complexes are indexed by all of `ℤ`.
- `hbounded` asserts that `P.X j` is zero outside a finite integer interval `[l,b]`.
- `hfinite` gives, for each degree, a natural number `n`, maps `i` into and `p` out of
  `SheafOfModules.free (ULift (Fin n))`, and `i ≫ p = 𝟙 (P.X j)`. This is precisely
  a direct summand of a finite free sheaf, not global projectivity or freeness.
- `hbelow` says `IsZero (P.X j)` whenever `j < a`.
- `hacyclic` says `IsZero (K.homology j)` for all `a ≤ j`; this is the cohomology
  sheaf, not its sections. `K` has no lower or upper support hypothesis.
- `(w : P ⟶ K)` is an arbitrary chain map, with the usual differential compatibility
  in Mathlib's morphism structure.
- The conclusion supplies `S : Sieve U` and `S ∈ J U`, then a homotopy on every
  arrow `f : V ⟶ U` belonging to `S`. A covering sieve is itself a covering family
  (indexed by its arrows). Conversely a covering family generates such a sieve;
  further restriction carries a homotopy to each arrow of that sieve. These are
  equivalent formulations, with no separatedness or representability condition.
- Each component `h j` maps the actual restriction of `P.X (j+1)` to the actual
  restriction of `K.X j` by `SheafOfModules.overMap` along `f`.
- For every integer `j`, the conclusion gives
  `w^(j+1)|V = h j ≫ d_K^j|V + d_P^(j+1)|V ≫ h (j+1)`.
  In ordinary right-to-left notation this is exactly
  `w^m|V = d_K^(m-1) h^m + h^(m+1) d_P^m`, with `m=j+1` and `h^m=h (m-1)`.
  Translation by one is a bijection on the integers, so every degree occurs.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  transparent abbreviation of Mathlib's `SheafOfModules`, retaining its morphisms
  and its canonical abelian structure.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, and its imported Mathlib cochain and homology API:
  integer-indexed `CochainComplex`, `HomologicalComplex.homology`. No derived
  localization hypothesis is needed for this assertion about actual complexes.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`,
  `SheafOfModules.overFunctor`, `over`, `Hom.over`, `overMap`, `overFunctorMap`;
  `Mathlib.CategoryTheory.Sites.Over`, `GrothendieckTopology.over`, `Sheaf.over`:
  the recorded slice and relocalization, sectionwise with the correct coefficients.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`, `SheafOfModules.free`:
  the coproduct of rank-one module sheaves, the actual finite free sheaf.
- Added the already landed `def-sp-ringed-topos-binary-descent-models` to
  `stmt_deps`: its module `Sheaf.CategoryTheory.RingedToposBinaryDescentDefs`
  exposes `CategoryTheory.binaryDescent_hasSheafify` and
  `CategoryTheory.binaryDescent_wEqualsLocallyBijective`, the existing small-model
  abelian sheafification instances. They supply the canonical abelian/homology
  API at `max c v r` without adding mathematical assumptions or new instances.
  A module-mode compiler probe confirmed synthesis without any sheafification,
  abelian, homology, or essentially-small binder; the probe was then removed.
- `Mathlib.Algebra.Category.Ring.Limits` supplies preservation of limits by
  `forget₂ CommRingCat RingCat`, needed to compose the coefficient sheaf.
- Proof-only imports retain the recorded proof plan:
  `Sheaf.CategoryTheory.LocalizedModuleExactForSystems` (`localizedSystemExact`),
  `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
  (`CategoryTheory.moduleSheaves_colimits_forgetful`),
  `Mathlib.CategoryTheory.Sites.Sheafification` (`presheafToSheaf`, `toSheafify`),
  `Mathlib.CategoryTheory.Sites.EpiMono` (`Sheaf.isLocallySurjective_iff_epi'`, the
  mathlib_match of the local-surjectivity dependency), and
  `Sheaf.CategoryTheory.SiteCoveringAxioms` (`Precoverage.IsSiteForCoverings`).

Edge cases checked before and after writing: `P=0` admits the identity covering
and zero homotopy; empty support intervals force precisely this case, so no
`l ≤ b` or `a ≤ b` restriction is needed. Rank `n=0` is allowed (`Fin 0` is empty).
A complex concentrated in degree `a` requires a lift from `K^(a-1)` and is covered
by the displayed degree-`a` equation; no cohomology hypothesis below `a` is needed.
Negative `a`, nontrivial cohomology below `a`, and unbounded `K` are all included.
An empty covering sieve, if covering in the topology, gives a vacuous local
conclusion, as it should; no Nonempty condition is imposed. No points, affine
objects, quasi-compactness, terminal object of the ambient site, finite-cover
hypothesis, or pullback hypothesis on the ambient category is imposed.

Searches made (2026-10-24):

- msearch.py leanfinder: “On a ringed site a chain map from a bounded complex of
  finite free retract module sheaves to an upper acyclic complex is locally null
  homotopic”: eight results, mainly K-projective/K-injective null homotopies.
- msearch.py loogle: `CochainComplex.IsKProjective, Homotopy`: four K-projective
  declarations, all requiring global K-projectivity and an acyclic target.
- msearch.py grep: `local.*(nullHomotop|homotopyZero)|strictlyPerfect.*homotopy|IsStrictlyPerfect`:
  no Mathlib match.
- msearch.py leansearch: “A chain map from a bounded complex of finite free
  summand sheaves to a complex with zero cohomology in degrees at least a is locally
  null homotopic”: eight results, the same K-projective lemmas and constructors
  of null homotopies from already supplied components.
- rg in project `lean/Sheaf` and `lean/WeilConjectures` for strictly perfect,
  `nullHomotop`, `homotopyZero`, finite-free retracts, and the node id; grep -rn for
  the node id in WeilConjectures: no exact statement. Scheme-only strict perfect
  results use a different site; `PerfectConstantLocalNullHomotopy` treats constant
  coefficients and constant finite-projective source models, not arbitrary
  ringed-site finite-free retract sheaves. Existing free and restriction notions
  were reused; no private copies were introduced.

Validation: scompile.py compiled the delivered file in sandbox mode and as its
actual library module, both with exit status zero and no warnings (2.2 s and
2.0 s). Earlier instance-search failures were repaired by importing the existing
ring limits and small-model sheafification interfaces, without larger time limits.
No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by NW

Self-check of the node and final signature: verified the finite-interval and
finite-retract assumptions separately, cohomology vanishing at the inclusive
boundary `a`, the absence of any bound on `K`, the arbitrary chain map, covering
sieve membership, and the two compositions in every homotopy equation. Reindexing
`h j` as `h^(j+1)` preserves every integer degree. The temporary sheafification
binders were removed after the existing small-model instance import supplied
them. This is a worker self-check, not an independent second reader; the brief
assigns independent review to the maintainer and prohibits starting other agents.
