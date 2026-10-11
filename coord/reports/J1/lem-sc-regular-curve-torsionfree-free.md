## Worker report

The module `Sheaf.AlgebraicGeometry.RegularCurveTorsionfreeFree` states
`AlgebraicGeometry.Scheme.Modules.regular_curve_torsionfree_iff_finiteLocallyFree`.
The only proof is `sorry`; no definition or additional theorem is introduced.

Hypotheses and clauses, in the node's order:

- An integral scheme is `(X : Scheme.{u}) [IsIntegral X]`. Mathlib's integral predicate
  includes nonemptiness, reducedness and irreducibility.
- Regularity is `hregular : ∀ x : X, ∃ U : X.affineOpens,
  x ∈ U.1 ∧ IsRegularRing Γ(X, U)`. This is precisely the defining affine-neighbourhood
  condition specified in the regular-scheme dependency's `lean.note` and `mathlib_match`.
  `IsRegularRing` includes Noetherianity. No global Noetherian or field-base hypothesis is added.
- Topological dimension at most one is `hdim : topologicalKrullDim X ≤ 1`.
- The coherent O_X-module is `(F : X.Modules)` together with
  `hcoherent : RingedSpace.IsCoherent X.toRingedSpace F`.
- Its torsion subsheaf being zero is `IsZero (kernel (toSkyscraper (LinearMap.id :
  F.presheaf.stalk (genericPoint X) →ₗ[X.functionField]
  F.presheaf.stalk (genericPoint X))))`. The torsion-subsheaf dependency explicitly
  identifies its inclusion with a kernel of this exact map. Thus the categorical kernel
  is the same submodule up to unique isomorphism, not a new torsion notion or an arbitrary
  witness. Coherence on this regular scheme implies quasi-coherence, so the dependency's
  quasi-coherence assumption is available in the future proof, not added to our statement.
- The equivalence is `↔ F.IsFiniteLocallyFree`.
- The rank clause is the second conjunct, `F.IsFiniteLocallyFree →
  F.IsFiniteLocallyFreeOfRank (Module.finrank X.functionField
  (F.presheaf.stalk (genericPoint X)))`. The fixed-rank predicate supplies a covering with local free
  generating families all of the specified finite cardinality. It expresses both constancy and equality with the
  generic vector-space dimension. The implication correctly scopes this assertion to the
  locally free case; it asserts no constant rank for an arbitrary coherent torsion module.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`
  (`def-pc-integral-scheme`).
- `Sheaf.AlgebraicGeometry.Coherent`, `AlgebraicGeometry.RingedSpace.IsCoherent`
  (`pqf-def-coherent`). This is the actual ringed-space coherence definition, not the
  source repository's finite-presentation stand-in.
- `Mathlib.AlgebraicGeometry.FunctionField`, `AlgebraicGeometry.Scheme.functionField`
  and its integral-scheme field instance (`def-sc-function-field`, whose record expressly
  delegates its arbitrary integral-scheme clause to Mathlib). The component-product
  declaration in `Sheaf.AlgebraicGeometry.FunctionField` was read; it is irrelevant to
  the integral-scheme clause and is not duplicated or substituted.
- `Mathlib.RingTheory.RegularLocalRing.Defs`, `IsRegularRing` and
  `IsRegularLocalRing` (`def-weil-regular-scheme`), following the recorded inline scheme form.
- `Sheaf.AlgebraicGeometry.TorsionSubsheafQuotient`,
  `AlgebraicGeometry.Scheme.Modules.torsion_subsheaf_quotient`
  (`lem-sc-torsion-subsheaf-quotient`), whose full signature and docstring specify the kernel
  used above; `AlgebraicGeometry.Scheme.Modules.toSkyscraper` comes from its import
  `WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`,
  `SheafOfModules.IsFiniteLocallyFree` and `SheafOfModules.IsFiniteLocallyFreeOfRank`:
  their full definitions use locally free local-generators data, with finite bases and
  bases of cardinality exactly the specified natural number, respectively.

Source read: https://stacks.math.columbia.edu/tag/0CC4 (Lemma 31.11.11).
The local `literature/stacks-project/divisors.tex` is absent on this machine; the official
Stacks page gives exactly the integral, regular, dimension ≤ 1 and coherent hypotheses
and the torsion-free/finite-locally-free equivalence. The node's final rank clause follows
from local constancy on the connected integral scheme as its recorded proof explains.
The four proof steps with their supporting node ids are included in the theorem docstring.

Edge cases checked: the empty scheme is already excluded by integrality, not by an added
hypothesis. A field spectrum (dimension zero) is included. A DVR spectrum and a finite free
module satisfy the criterion. A nonzero DVR module R/(t) has nonzero torsion kernel and is
not locally free, so both sides of the equivalence are false. The zero module is finite
locally free of rank zero and its generic finrank is zero. Schemes need not be quasi-compact,
separated, or curves over a specified field. The universe u is explicit; no auto-bound
variables or universes occur.

Searches for an existing statement:

- `msearch.py ... leanfinder "coherent torsion free module on integral regular scheme
  dimension at most one is finite locally free"`: eight hits, all on integrality/domain
  properties, none stating the equivalence or the rank clause.
- `msearch.py ... loogle "SheafOfModules.IsLocallyFree, Module.finrank"`: zero hits.
- `msearch.py ... grep "torsionFree.*[Ll]ocally[Ff]ree|[Ii]s[Tt]orsion[Ff]ree.*[Ii]s[Ll]ocally[Ff]ree"`:
  zero hits in Mathlib.
- `rg` on the source `WeilConjectures/AlgebraicGeometry/Modules` for torsion-freeness
  and local-freeness found existing local-free definitions and affine/rank lemmas, but
  no regular-curve criterion. The source's `Modules/Coherent.lean` supplies no such statement.
- Search for the exact blueprint id throughout `WeilConjectures` and `lean/Sheaf`:
  no declaration. Search `lean/Sheaf/AlgebraicGeometry` for torsion and regular curves:
  the torsion-subsheaf dependency exists, but this equivalence does not.
- Full-name search in `dag/lean_names_upstream.json`: no collision.

No statement correction, missing notion, unusable dependency, or disputed statement was found.
The server compiler returned exit code zero without warnings after the affine-open
membership was written explicitly as `x ∈ U.1`.


## Second reading by J1

Independent object/hypothesis/conclusion list, matched against the node and the Lean:

1. Object: an arbitrary scheme X. Lean `(X : Scheme.{u})`; verdict: exact,
   with explicit universe u and no base field or morphism specified.
2. Hypothesis: X integral. Lean `[IsIntegral X]`; verdict: exact. I opened
   Mathlib.AlgebraicGeometry.Properties: the class supplies nonemptiness and domain
   sections on every nonempty open; its reduced/irreducible characterization agrees
   with def-pc-integral-scheme. No empty scheme is removed beyond the node's own assumption.
3. Hypothesis: X regular. Lean `hregular : ∀ x : X, ∃ U : X.affineOpens,
   x ∈ U.1 ∧ IsRegularRing Γ(X, U)`; verdict: exact. I read the whole
   def-weil-regular-scheme record and Mathlib.RingTheory.RegularLocalRing.Defs.
   IsRegularRing extends IsNoetherianRing and asks for regular localizations at all
   primes. This is precisely the node's affine-neighbourhood definition, with no global
   Noetherian or quasi-compact condition. The alternative stalkwise characterization
   is a stage-3 bridge, not a different notion used here.
4. Hypothesis: topological dimension at most one. Lean `hdim : topologicalKrullDim X ≤ 1`;
   verdict: exact. I opened Mathlib.Topology.KrullDimension: this is the supremum of
   lengths of chains of irreducible closed subsets, in WithBot ENat.
5. Object: O_X-module F. Lean `(F : X.Modules)`; verdict: exact. The module category
   coincides with the scheme's ringed-space SheafOfModules category used by coherence.
6. Hypothesis: F coherent. Lean `hcoherent : RingedSpace.IsCoherent X.toRingedSpace F`;
   verdict: exact. I read pqf-def-coherent and Coherent.lean: finite type plus finite-type
   kernels of every finite free map on every open, with no hollow data. Coherence on a
   locally Noetherian scheme yields quasi-coherence; an extra quasi-coherence instance
   need not, and does not, appear among the theorem's hypotheses.
7. Conclusion: torsion subsheaf zero iff F finite locally free. Lean the first conjunct
   `IsZero (kernel (toSkyscraper (LinearMap.id : ...))) ↔ F.IsFiniteLocallyFree`;
   verdict: exact. I read lem-sc-torsion-subsheaf-quotient, its full module and final
   KernelFork clause, and upstream FlatPullbackStalk.toSkyscraper. Its app sends a section
   to its generic germ (identity on the generic stalk), so this is the precise canonical
   kernel, not a chosen subobject, arbitrary map, or replacement torsion predicate.
   Kernel objects are unique up to isomorphism and IsZero is invariant under that choice.
   The locally free predicate uses covering generator data with isomorphisms from free
   modules and finite indexing families, as checked in the upstream LocallyFree module
   and Mathlib's IsLocallyFreeData; verdict: exactly finite local freeness.
8. Conclusion: in this locally free case the rank is constant and equals the generic
   vector-space dimension. Lean the second conjunct
   `F.IsFiniteLocallyFree → F.IsFiniteLocallyFreeOfRank
   (Module.finrank X.functionField (F.presheaf.stalk (genericPoint X)))`;
   verdict: exact. I opened def-sc-function-field and Mathlib's functionField:
   its integral-scheme clause is literally the generic stalk with its field instance.
   I opened IsFiniteLocallyFreeOfRank: one covering has all indexing families equivalent
   to Fin r. This states a single rank everywhere, with the r specified here. Finite
   local freeness makes the generic stalk finite dimensional, so finrank faithfully
   expresses its dimension. The implication correctly restricts the clause to the
   locally free case rather than imposing local freeness on torsion modules.

Source: the local Stacks tex file is absent. I independently opened the official Tag 0CC4
page and the official Stacks repository's divisors.tex, labels section-torsion-free and
lemma-torsion-free-over-regular-dim-1. The lemma introduces exactly integral regular X,
dimension at most one, and coherent F. The preceding section works with quasi-coherent
modules; here this follows from coherence and local Noetherianity. No field, separation,
quasi-compactness or global Noetherian hypothesis is assumed throughout. The next ranks
section defines generic rank by the generic stalk over its residue field, identical to
k(X) for integral X. Constant local-free rank on irreducible X is the node's elementary
addition. The theorem docstring reproduces all four node proof steps with their supporting
ids. Nothing is proved except the required sorry placeholder. All five imports contribute
used definitions or the dependency's canonical map. No new definition node or dependency
module was delivered, so H12/H13 introduce no additional audit obligations. No statement
correction is present.

Edge cases: dimension zero (Spec of any field) is included; no characteristic is fixed.
The zero module is allowed and has fixed rank zero, with Fin 0 indexing permitted.
A DVR module R/(t) has zero generic stalk but nonzero generic-map kernel, and is not locally
free: both sides of the equivalence are false and the rank implication is vacuous.
Finite free DVR modules give rank equal to generic dimension. Empty X is excluded exactly
by integrality. Empty opens cause no problem (their sheaf sections are zero); there is no
external index set or nonemptiness premise. Non-quasi-compact regular integral schemes are
included. All variables and u are bound explicitly, with no independent test universe.

Independent searches, using different terminology from the worker:

- msearch leanfinder: "vector bundle criterion torsionless coherent sheaf nonsingular
  scheme Krull dimension one" returned eight unrelated vector-bundle/rank-at-stalk hits,
  none an equivalent scheme criterion.
- msearch loogle: "IsRegularRing, SheafOfModules.IsLocallyFree" returned no hits.
- msearch grep: "torsion.*[Ff]ree|[Ff]ree.*torsion" found ordinary algebraic torsion-free
  module results, not this sheaf theorem. Direct rg of the pinned Mathlib locally free,
  regular-ring and dimension sources confirmed the definitions used here.
- Independent rg on WeilConjectures/AlgebraicGeometry/Modules for "torsion|regular"
  found only a finite-pushforward proof comment, not this statement. Independent rg on
  lean/Sheaf/AlgebraicGeometry found the torsion kernel dependency and regular hypotheses
  of other theorems; no duplicate criterion. The exact declaration and blueprint-id
  search in WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json found no existing
  declaration (only a citer's proof comment).

Mismatches and changes: no Lean/node mismatch was found; the theorem and node were retained.
I corrected the worker report's imprecise description "every local free basis" to the
actual existential covering with fixed-cardinality generating families. No mathematical
statement or definition changed. The prescribed scompile.py compiled the module in 2.2 seconds with exit code 0 and
no warnings. deliver2.py --no-push returned OK: preflight and compilation passed.
