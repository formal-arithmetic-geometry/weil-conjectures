## Worker report

The module `Sheaf.SixFunctors.FlatModelGeneration` states all three clauses of
`det-sf-flat-model-generation` separately on the small etale and small pro-etale sites.
There are six named theorems, each with proof `sorry`, and six explicit helper definitions
belonging to this node. Every declaration has its source and blueprint docstring; theorem
docstrings contain the relevant complete steps of the current node's proof.

The shared DAG was updated during this retry. I refreshed the sandbox node from the current
split node, including its explicit conventions and twelve recorded statement dependencies.
These conventions expand Dctf into bounded constructible cohomology and finite Tor amplitude;
the previously reported unstated `sk-def-sf-categories` is no longer a prerequisite. This
worker makes no statement correction and states no other DAG node. The only node differences
are `lean` and four added, already-landed statement dependencies listed below.

### Hypotheses and clause correspondence

- Finite commutative coefficients: all six theorems bind `(A : Type ...) [CommRing A]
  [Finite A]`. The etale module convention is `A : Type (u+1)` and
  `ModuleCat.{u+1} A`. The intrinsic pro-etale convention is `A : Type u`, with the
  canonical coefficient ring `ULift.{u+1,u} A` used by `proEtaleConstantRing X A`.
  This is the recorded intrinsic constant-ring encoding, not a coefficient-stage
  specialization. No prime, exponent-invertibility, characteristic, field, finite-type,
  or chosen base-field hypothesis is added. Every finite ring can be represented in the
  chosen small coefficient universe; ULift is the canonical ring lift.
- Noetherian scheme: `(X : Scheme.{u}) [IsNoetherian X]` in all six theorems, the Mathlib
  Noetherian condition (locally Noetherian and quasi-compact). Pro-etale site objects remain
  in `Type (u+1)` and morphisms in `Type u`.
- A module sheaf F: `Sheaf X.smallEtaleTopology (ModuleCat A)` on the etale side;
  `proEtaleRingModules X (proEtaleConstantRing X A)` on the pro-etale side. Both are ordinary
  module sheaves and their uncompleted unbounded derived categories.
- Constructibility: `_hc : IsConstructibleEtaleModuleSheaf F`, respectively
  `_hc : IsConstructibleProEtaleCoefficientModuleSheaf X (ULift A) F`. The latter coefficient
  sheaf is definitionally `proEtaleConstantRing X A`. It is the recorded intrinsic finite
  partition notion, with no etale-origin hypothesis.
- Flatness: `_hf : ObjectProperty.flat F` on etale sheaves and
  `_hf : SheafOfModules.IsFlatOnSite ... F` on intrinsic pro-etale modules. The first is the
  existing exactness predicate for tensor on both sides; symmetric tensor makes this the
  same ordinary flatness condition as the recorded ringed-site definition. The second
  uses exactly the recorded sheafified sectionwise tensor with independent site universes.
- Clause (1): `etale_flatConstructible_orderedStratification` and
  `proEtale_flatConstructible_orderedStratification` give an existential
  `str : LocallyClosedStratification X`. Its inherited `n : Nat`, pairwise-disjoint locally
  closed parts, covering condition, domains and actual scheme immersions give the finite
  partition with its subscheme structures. `FlatModelOrderedStratification str` asserts
  closedness of every tail and openness of the part in the subtype of that tail. In
  particular it does not assert ambient openness of each stratum.
- Restrictions are exactly `(Etale.upperStar ... (str.immersion k)).obj F`, respectively
  `proEtaleConstantModulePullback (str.immersion k) A F`. The latter includes the canonical
  tensor extension along the constant-section coefficient comparison.
- The helpers `FlatModelEtaleLisseProjective` and `FlatModelProEtaleLisseProjective` combine
  existing module local constancy with explicit finiteness and `Module.Projective` at every
  geometric point. Etale stalks are the module-valued `pointSmallEtale` sheaf fibers at all
  separably closed field-valued points. Pro-etale stalks are the recorded
  `finiteCoefficientModuleStalkFunctor`, restricted along the actual constant germ, so
  `Module.Projective (ULift A)` is explicitly imposed on the original coefficient module.
  Finite as a set is equivalent to finite generation over the finite coefficient ring;
  projective plus finite generation means a summand of a finite free module.
- Clause (2): `etale_flatConstructible_extensionFiltration` and its pro-etale analogue
  quantify over every `str` with the ordering and projective-lisse restriction conditions,
  for the same flat constructible F. They conclude `FlatModelExtensionFiltration` with
  exactly the factors `(flatModelEtaleExtension ...).obj (a_k^* F)`, respectively the
  pro-etale version. The helper gives `M : Fin (n+1) -> Mod`, `IsZero (M 0)`, an isomorphism
  `M (Fin.last n) ~= F`, and for every k a `ShortComplex.ShortExact`
  `0 -> M k.castSucc -> M k.succ -> a_{k!}L_k -> 0`. Thus this is an actual finite sheaf
  filtration with one specified quotient per stratum, not just membership in an abstract
  extension closure or a statement about complexes.
- `flatModelEtaleExtension` and `flatModelProEtaleExtension` construct the actual
  `g_* j_!` with `j = a.toImage`, `g = a.imageι`. No factor or canonical map is chosen from
  bare existence. Immersion into Noetherian X supplies a Noetherian domain space and hence
  quasi-compactness; the existing Mathlib instance makes `a.toImage` open. On the pro-etale
  side the published intrinsic realization equivalences transport exactly the recorded
  fixed-module extension and direct image, including their scalar actions.
- Each clause-(2) factor is named `G` with the explicit equality to that constructed
  factor. The conclusions assert that G is flat and constructible and that `single G 0`
  has constructible cohomology in every degree, zero cohomology outside one finite ordered
  interval, and finite Tor amplitude. This spells out precisely `G[0] in Dctf`, using
  `DerivedCategory.hasTorAmplitudeIn` or `HasFiniteProEtaleTorAmplitude` as appropriate.
  The existential with equality is a transparent name for the factor, avoiding hidden
  `let`/`have` terms in the statement.
- Clause (3): `etale_flatConstructible_thickGeneration` and its pro-etale analogue state
  equality of the expanded Dctf object property with `ObjectProperty.triangEnvelope` of
  all objects isomorphic to `a_!L[0]`, for arbitrary schemes S, immersions `a : S -> X`,
  and projective-lisse L. There is no extra stratification/factorization hypothesis on
  these generators. Mathlib's envelope closes under shifts, finite extensions/cones,
  retracts (direct summands) and isomorphisms, so this equality gives both minimality and
  the reverse containment. The zero object is included among the generators by L=0.

### Dependency declarations

All twelve original recorded statement dependencies were read, including their signatures
and docstrings, and are imported publicly:

- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `Scheme.IsConstructibleEtaleModuleSheaf`.
- `Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf`:
  `Scheme.IsConstructibleProEtaleCoefficientModuleSheaf`.
- `Sheaf.AlgebraicGeometry.LocallyClosedStratification`:
  `Scheme.LocallyClosedStratification`, inheriting `Topology.Stratification`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, its Q localization,
  and the existing derived-category structures.
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`: reexports
  `Etale.DerivedCategory.hasTorAmplitudeIn` (and defines its lower-bound sibling).
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`: `Scheme.HasProEtaleTorAmplitude` and
  `Scheme.HasFiniteProEtaleTorAmplitude`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `Etale.openImmersionLowerShriek`, with `Etale.upperStar`/`lowerStar` from its public import.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`:
  `ProEtale.openImmersionLowerShriek` and its public inverse/direct-image definitions.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`: `Scheme.Hom.image`, `imageι`, `toImage`.
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`: `IsImmersion` and its existing instance
  making `toImage` an open immersion for quasi-compact immersions.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`, the
  Noetherian-space instance and quasi-compactness of maps from a Noetherian space.

Four already-landed nodes are added to `stmt_deps` for interfaces used explicitly here:

- `def-weil-proetale-geometric-stalk`:
  `Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor`,
  `Scheme.finiteCoefficientModuleStalkFunctor`.
- `def-weil-proetale-locally-constant-sheaf`:
  `Sheaf.Paper.ProEtaleFixedModuleLocalConstancy`, which publicly retains
  `Scheme.IsLocallyConstantProEtaleModuleSheaf` from the intrinsic interface.
- `def-weil-extension-by-zero`: `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`,
  `Scheme.sfIntrinsicModuleEquivalence` (and its existing intrinsic extension by zero).
- `def-weil-pbc-proetale-operations`:
  `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations`, which retains
  `Scheme.proEtaleConstantModulePullback` and the intrinsic coefficient operations.

Every recorded proof-dependency module is imported for stage 3, using ordinary non-public
imports where it is used only in the proof. The two genuine proof dependencies
`det-pe-finite-tor-comparison-noetherian` and `sk-thm-pe-constructible-comparison` have no
recorded modules yet, so there is no module to import for them. No circular parent
`sk-lem-sf-flat-model` import is used. The source proof is recorded step by step in the
six theorem docstrings, including the nonreduced-stratum argument.

### Edge cases

The empty scheme is permitted, with `str.n = 0`. Ordered tails and the restriction clauses
then have empty quantifiers. The finite filtration has one object M0, required zero and
isomorphic to F, exactly the empty extension tower. The positive-number convention in the
constructibility dependency also permits the empty scheme via one empty stratum; it does
not force our resulting stratification to have a stratum. Empty strata are allowed.
The zero sheaf and zero coefficient ring are permitted: there is no `Nontrivial`, rank,
nonempty geometric-point family or positive-stratum binder. A zero projective constant
model is allowed. The clause-(3) generator family is nonempty even for empty X by the
identity immersion and zero sheaf. Neither reducedness of the strata nor the incorrect
claim that an immersion with open underlying image must itself be open is assumed.
Cohomological and Tor intervals have independent witnesses, as the source requires;
bounds are not fixed to [0,0] or made to depend on a test sheaf.

### Searches

- msearch LeanFinder, query: "A flat constructible sheaf over a finite commutative ring has
  ordered strata with finite projective stalks and a filtration by extension by zero, which
  generate its thick finite Tor derived category". Eight hits on finite-type/presentation
  module sheaves, condensed modules and rank loci; none states this result.
- msearch LeanSearch, query: "For a finite commutative ring on a Noetherian scheme, flat
  constructible sheaves have ordered locally closed strata with projective stalks and a
  sheaf filtration by extensions by zero, generating the thick finite Tor constructible
  category on the etale and pro-etale sites". Eight hits on finite-type module sheaves,
  scheme flat stalk maps and scheme modules; none states this result.
- msearch Loogle, query: `ObjectProperty.triangEnvelope, ShortComplex.ShortExact`.
  Zero hits; the service reports unknown `ObjectProperty.triangEnvelope`. The local
  Mathlib source was then opened: `Mathlib.CategoryTheory.Triangulated.Generators` provides
  exactly the envelope operation used here.
- msearch grep, query: `flatConstructible|ctfGenerators|iteratedExtension`, subdirectory
  `CategoryTheory`: zero Mathlib hits.
- rg of Mathlib, the upstream WeilConjectures tree and `lean/Sheaf` for `ctfGenerators`,
  `constructibleFiniteTor`, `Stratification`, `IsFiniteLocallyConstantSheaf`, the new
  declaration names and `det-sf-flat-model-generation`. No existing declaration covers
  all three clauses on both sites. Upstream `Etale.ctfGenerators` uses derived operations
  and an arbitrary factorization; its envelope equality assumes a finite-type scheme over
  a field and invertible exponent, and does not give our finite sheaf filtration. Its
  full signatures and docstrings were read. `Sheaf.SixFunctors.FlatModel` gives related
  downstream flat-model/generation assertions, but not clauses (1)--(2) here, and its
  proof depends on this node. It is not imported or restated.

No new independent definition node and no dependency repair module are needed. The six
helper definitions render components of this one node and are all listed in
`lean.declarations`; they do not replace a dependency definition or introduce a second
Dctf predicate. No `STATEMENT-DISPUTED` flag or node statement fault remains.

### Validation

The final formatted module compiled cleanly through the prescribed wrapper, including its
check under the delivered module name. All universes and variables are bound explicitly
(`set_option autoImplicit false`); every theorem body is exactly `by sorry`, and all
definition data are constructed. The twelve recorded declarations match the module, the
primary signature is recorded verbatim, and every line is at most 100 characters.
The required final check is `deliver2.py Q64 det-sf-flat-model-generation --no-push`.
This report does not contain a second reading; the independent second reader supplies
that after the worker handoff. Nothing is pushed by this worker.

## Second reading by Q64

I reread the source node `det-sf-flat-model-generation`, its blueprint proof, all recorded
statement dependencies, and `Sheaf/SixFunctors/FlatModelGeneration.lean` independently.
The item is a statement with three clauses, and the Lean file renders it as six theorems
(etale and intrinsic pro-etale versions) plus six named helper definitions.

- The objects are a finite commutative coefficient ring `A`, a Noetherian scheme `X`, and a
  module sheaf `F` on either small site.  These are rendered by the explicit `A`, `X`,
  `IsNoetherian X`, and `F` binders in all six theorem signatures.  Etale coefficients use
  `A : Type (u+1)` and `ModuleCat A`; intrinsic pro-etale coefficients use `A : Type u`,
  `proEtaleConstantRing X A`, and the canonical `ULift A` stalk coefficient.  This is the
  unequal site-universe convention of the recorded pro-etale operations, not an extra
  equality of universes.  Verdict: matches the node's ordinary constant-ring convention.
- The hypotheses that `F` is constructible and flat are rendered by
  `IsConstructibleEtaleModuleSheaf F` and `ObjectProperty.flat F` on the etale side, and by
  `IsConstructibleProEtaleCoefficientModuleSheaf X (ULift A) F` and
  `SheafOfModules.IsFlatOnSite ... F` on the intrinsic pro-etale side.  No field, characteristic,
  finite-type, prime, exponent, reducedness, or nonempty hypothesis is added.  Verdict: matches.
- Clause (1)'s finite locally closed partition and its ordering are rendered by
  `LocallyClosedStratification`, `FlatModelOrderedStratification`, and the quantifier over
  `Fin str.n`.  The latter says each tail union is closed and the corresponding stratum is
  open in that tail.  The restrictions are exactly `Etale.upperStar ... (str.immersion k)` and
  `proEtaleConstantModulePullback ...`; the two lisse/projective helpers state local constancy,
  finite stalks, and `Module.Projective` at every geometric point.  Verdict: every clause is
  present with the source's scheme-immersed strata.
- Clause (2)'s ordered extension tower is rendered by
  `FlatModelExtensionFiltration`: `M 0` is zero, `M (Fin.last m)` is isomorphic to `F`, and
  each successive map has the specified factor as its short-exact quotient.  The following
  existential names each factor `G` by an equality to the canonical `g_* j_!` construction
  (`flatModelEtaleExtension` or `flatModelProEtaleExtension`) and asserts flatness,
  constructibility, bounded constructible homology, a finite cohomological interval, and the
  recorded finite Tor-amplitude predicate.  This is precisely the node's expanded `Dctf`
  convention and does not weaken the factor assertion.  Verdict: matches.
- Clause (3)'s smallest replete full subcategory is rendered as equality with
  `ObjectProperty.triangEnvelope`.  Its generator property quantifies over every scheme `S`,
  immersion `a`, and lisse finite-projective `L`, and identifies the generator with the degree
  zero single complex of the canonical extension.  The envelope supplies shifts, cones,
  finite biproducts, retracts, and isomorphisms; finite biproducts are already obtainable by
  extensions in the additive derived category.  Verdict: matches the stated closure.

The helper definitions were checked against the dependency declarations.  The tails use the
actual `stratum` subsets; the filtration uses `ShortComplex.ShortExact`; both extension maps
factor through the scheme-theoretic image (`toImage`, `imageι`); and the pro-etale extension
transports the canonical fixed-module operation through `sfIntrinsicModuleEquivalence`.  No
private duplicate of a dependency notion was introduced.  The dependency modules for the four
added interfaces (geometric stalk, pro-etale local constancy, intrinsic extension by zero, and
intrinsic finite operations) were opened and their declarations match the uses here.

Edge cases checked: `str.n = 0` is permitted, so an empty scheme has an empty partition and an
empty extension tower; `Fin 0` quantifiers are vacuous and `Fin.last 0` still gives the required
zero/final isomorphism.  The zero sheaf and zero ring are allowed; no `Nontrivial`, rank, or
geometric-point existence is assumed.  Empty strata and nonreduced immersed stratum schemes are
allowed.  The characteristic is unrestricted, and all coefficient/site universes are explicit.

Searches were repeated with msearch LeanFinder and LeanSearch, Loogle, and `rg` over Mathlib,
the upstream `WeilConjectures` tree, and repository `lean/Sheaf` for flat-constructible
stratification, finite-Tor constructibility, and thick-generation declarations.  The hits were
generic derived-category, local-constancy, or finite-presentation infrastructure; no declaration
states this three-clause result.  The related `Sheaf.SixFunctors.FlatModel` declarations use
this node and are downstream, so they cannot replace it.

No mismatch was found and no source-based statement correction was required.  The module was
compiled with `scompile.py` after this reading; it completed cleanly with only the permitted
`sorry` proofs.  The node copy retains the worker's statement and dependency additions verbatim.
