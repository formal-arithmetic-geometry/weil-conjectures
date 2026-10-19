## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleTorLocalGlobal` states
`AlgebraicGeometry.Scheme.hasFiniteCoefficientProEtaleTorAmplitude_iff_locally`,
with proof `sorry`. Its helper `CategoryTheory.coefficientModelSliceRestriction`
specializes the recorded exact derived slice restriction to the standard
localizations used by the recorded Tor predicate. The helper has real data:
it applies `ringedDerivedRestrictionSized` with the standard global and slice
localization instances. It introduces neither a replacement tensor nor a
replacement module category.

The preceding worker's stale-assignment diagnosis confused stages: Q05's
2026-10-17 landing reviewed the stage-1 split, not a Lean statement. The base
node has `reviewed` but no `lean` or `reviewed_lean`. This delivery preserves
that reviewed natural statement and its proof plan and adds only `lean`.

Hypothesis and clause correspondence:

- A scheme X is `(X : Scheme.{u})`. Quasi-compactness of its underlying space
  is `[CompactSpace X]`, with no Hausdorff or quasi-separatedness assumption.
- The arbitrary commutative coefficient ring is
  `(A : Type (max v (u + 1))) [CommRing A]`. The independent universe `v`
  permits arbitrary coefficient size relative to X; no equality of the
  scheme and coefficient universes is required.
- The chosen small model is the existing
  `coefficientProEtaleSiteModel.{u, v} X`, namely `AsSmall X.ProEt`, and its
  topology is `coefficientProEtaleModelTopology.{u, v} X`. These are the
  coefficient-sized equivalent model already used by the recorded
  `HasCoefficientProEtaleTorAmplitude`; they retain the pro-etale topology.
- The constant ring sheaf is
  `ConstantCompletion.constant (coefficientProEtaleModelTopology X) A`,
  definitionally `(constantSheaf _ CommRingCat).obj (CommRingCat.of A)`.
- The arbitrary unbounded derived object is the binder
  `M : ConstantCompletion.D (...)`. This is the standard derived localization
  of `ringedSiteModules (siteModuleRings ...)`, hence Mathlib's module-sheaf
  category. There is no boundedness or constructibility condition.
- Clause (1) is `HasFiniteCoefficientProEtaleTorAmplitude X A M`. Its recorded
  definition is `∃ a b : ℤ, HasCoefficientProEtaleTorAmplitude X A M a b`.
  The latter unfolds to `HasCoefficientModelTorAmplitude`: it includes
  `a ≤ b` and vanishing against EVERY degree-zero module for every integer
  `q` with `q < a ∨ b < q`, on every K-flat representative of M. K-flat
  resolutions exist by the imported resolution interface, so this is the
  derived-tensor test, independent of the representative, not a vacuous
  quantification over possibly nonexistent models.
- Clause (2)'s "for every site object U" is the binder `∀ U`.
  `∃ S : Presieve U, Sieve.generate S ∈ ... U ∧ ...` is an arbitrary
  covering family expressed without an artificial indexing universe.
  A presieve is a collection of arrows into U. Such a collection is a
  covering precisely when its generated sieve belongs to the topology.
  Conversely every indexed covering family gives its image presieve;
  repeated arrows carry the same restriction and need no separate bound.
- For EVERY member of that covering, `∀ V (f : V ⟶ U), S f → ...` asserts
  `∃ a b : ℤ, HasCoefficientModelTorAmplitude ... a b`. The existential is
  inside the arrow quantifier, so each member may have its own interval.
- The coefficient ring on V is exactly `(constant ... A).over V`, and the
  object on it is `(coefficientModelSliceRestriction ... V).obj M`.
  The helper is the recorded `ringedDerivedRestrictionSized` of the
  underlying ring sheaf, with standard localizations. Forgetting
  commutativity commutes definitionally with sectionwise restriction.
- The slice `HasCoefficientModelTorAmplitude` quantifies over ALL module
  sheaves on `J.over V`, not merely restrictions of global test modules.
  It includes the ordered interval and the same cohomology vanishing
  clause as (1), with the restricted ring and object.
- The equivalence is `↔`. There are no further hypotheses on M, A or X.

Recorded dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` (and its
  morphisms); `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`:
  `AlgebraicGeometry.Scheme.ProEt`, `Scheme.ProEt.topology`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, through `ConstantCompletion.Mod`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory.standard`, through `ConstantCompletion.D`.
- `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`:
  `CategoryTheory.ringedDerivedRestrictionSized` (the specialization of
  `ringedDerivedRestrictionGeneral` with independent localization sizes).
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, the exact restriction used by that functor;
  `Mathlib.CategoryTheory.Sites.Over`: `Sheaf.over`, `GrothendieckTopology.over`.
  The localized-site node's `mathlib_match` supplies these, with no missing
  Lean record to repair.
- `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude`:
  `CategoryTheory.HasCoefficientModelTorAmplitude`,
  `AlgebraicGeometry.Scheme.HasCoefficientProEtaleTorAmplitude` and
  `HasFiniteCoefficientProEtaleTorAmplitude`. The slice uses its generic
  predicate, and the global side uses its recorded scheme specialization.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, whose factorization identifies
  cohomology on representing complexes with derived cohomology. The Tor
  predicate tests the homology of the K-flat total tensor representative.

The module also imports every available recorded proof-dependency module:
`LocalizedModuleExactIndependent`,
`RingedTopoiCanonicalTensorPullbackOfUniverses`, `SiteTorIntervalRestriction`,
`SiteCoveringAxioms`, `RingedSiteDerivedRestrictionUniverses`, and
`WeilSiteDerivedTensorDescent`; and the Mathlib exact-functor/cohomology
comparison. The module and theorem docstrings cite Stacks Tags 08FZ/09C2.
The theorem docstring gives all six proof steps of the reviewed DAG plan.

Edge cases checked before writing: X may be empty, M may be zero, A may be
the zero ring, and an interval may have equal endpoints. No inhabitedness,
nonzero-ring, strict-endpoint, or nonempty-cover binder excludes these.
Presieves permit the empty covering of an empty object. The proof plan's
insertion of 0 in the finite sets of bounds handles empty X. Slice tests are
arbitrary module sheaves, the key nontrivial point in the forward implication.
Quasi-compactness is essential: on an infinite discrete union of points,
complexes with increasingly distant degree shifts have local finite Tor
intervals but no uniform global interval. The statement does not omit that
hypothesis or impose Noetherianity to replace it.

Sources opened locally: `sites-cohomology.tex`, definition-tor-amplitude,
lines 12377-12399 (Tag 08FZ); `proetale.tex`,
lemma-describe-constructible-complexes and its uniformity sentence,
lines 5787-5808 (Tag 09C2). The node isolates the quasi-compactness argument;
it does not borrow the constructibility/completeness assumptions of the
surrounding application. No statement correction or dispute was needed.

Searches made:

- `msearch.py leanfinder`, "Finite Tor dimension of module sheaf complexes
  on a quasi-compact pro-etale site is equivalent to local finite Tor
  dimension on covering families": eight hits about finite presentation,
  local generators and quasicoherent modules, none the desired theorem.
- `msearch.py leansearch`, "Local finite Tor dimension of a complex on a
  quasi-compact pro-etale site implies a uniform global Tor interval":
  eight hits including projectiveDimension_ne_top_iff, local etaleness and
  derived t-structure bounds; none the required equivalence.
- `msearch.py loogle`, `"TorAmplitude"`: zero hits.
- `msearch.py grep`, `torAmplitude|tor_amplitude|TorAmplitude`: zero hits
  in Mathlib.
- `rg` over `WeilConjectures` and `lean/Sheaf` for
  `HasCoefficientModelTorAmplitude`, local/global Tor patterns, and the item
  id: found the existing coefficient Tor predicates and consumers, not this
  equivalence. The upstream match was an unrelated torsor-lifts docstring.
  Read the existing generic ringed-site Tor restriction theorem rather than
  restating it. No existing declaration supplies the item's equivalence.

No new nodes, dependency repairs, or changes to the reviewed statement.

Validation: the prescribed `scompile.py Q44 lem-sfb-proetale-tor-local-global`
compiled the delivered file cleanly both as a sandbox module (27.4 s) and
under its library module name (6.2 s), with no errors or warnings. An initial
missing-instance error was repaired by explicitly installing the standard
localization instance on `SheafOfModules ((siteModuleRings R).over V)`.
This changes no mathematical structure or hypothesis. All variables and
universes are explicitly bound; every line of the module is at most 100
characters. The only postponed proof is the item's theorem.

## Second reading by Q44

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
