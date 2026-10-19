## Worker report

The module `Sheaf.Paper.LocallyConstantTensor` states
`SheafOfModules.locallyConstantFiniteType_derivedTensor`, Stacks Tag 094H.
Its proof is `sorry`; no theorem is proved. The original statement is unchanged.

Clause-by-clause correspondence:

- A small site is `C : Type u`, `[Category.{u} C]` and `J : Precoverage C`, with
  `HasIsos`, `IsStableUnderComposition`, `IsStableUnderBaseChange`, and `HasPullbacks`.
  Sheaves use the associated `J.toGrothendieck`, exactly the dependency's site convention.
- The commutative Noetherian ring is `B : Type u`, `[CommRing B]`, `[IsNoetherianRing B]`.
- Coefficients are `(constantSheaf J.toGrothendieck CommRingCat).obj (CommRingCat.of B)`,
  then forgotten to rings by `sheafCompose`. This is the constant ring sheaf, with its
  commutative structure available to the existing tensor API.
- `K L : DerivedCategory (SheafOfModules ...)` are precisely the two derived objects.
  `[HasDerivedCategory.{w} ...]` chooses the morphism universe and localization, without
  requiring small derived Homs in the site universe.
- The two D-minus conditions are `hK` and `hL`: an integer bound above which
  `(DerivedCategory.homologyFunctor ... i).obj K/L` is `IsZero`. They concern cohomology,
  not vanishing of terms of a chosen representative.
- `hKlc` and `hLlc` assert `IsLocallyConstantFiniteType` for every integer cohomology degree.
  The new predicate quantifies over every object, a covering sieve on it, and every arrow
  in that sieve; its local model is a `ModuleCat B` value satisfying `Module.Finite B M`.
  The isomorphism is in sheaves of modules over the restricted coefficient sheaf, so is
  linear, not merely an isomorphism of underlying sets or abelian groups.
- `P Q` are arbitrary K-flat representatives, `hP/hQ : CochainComplex.IsKFlat ...`, with
  `eP/eQ : DerivedCategory.Q.obj P/Q ≅ K/L`. These name the K-flat resolutions used in
  the node's explicit tensor convention, not extra restrictions on K or L. Any derived
  object admits such representatives. Conversely the conclusion applies to every choice.
- The conclusion is for every `i : ℤ`, local constancy of finite type of the homology
  sheaf of `CochainComplex.mapBifunctor P Q` with the exact
  `SheafOfModules.monoidalCategory` tensor. This computes H^i of derived tensor under the
  node's convention, via `DerivedCategory.homologyFunctorFactors`.
- There is no assumption of points, terminal object, finiteness of the site, finite
  cardinality of B or M, or a common trivializing cover in every cohomological degree.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (all ideals finitely generated).
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`
  (sheafification of the identity-restriction constant presheaf).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`; `...HomologySequence`: `DerivedCategory.homologyFunctor` and factors.
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` record: `Precoverage` and its four
  axioms, `Precoverage.toGrothendieck`, `Sheaf` (object cohomology H' itself is not needed).
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`.
- `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlat`; it uses precisely acyclicity of
  total tensor, and the commutative-ring-sheaf tensor API.
- `Sheaf.Paper.StrictPerfectCoefficientPackage`:
  `SheafOfModules.strictPerfectConstantPresheaf`, read in full: constant module values,
  identity restriction maps, and original linear maps on morphisms. Reused, not copied.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite` is finite generation of top.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, sectionwise restriction to the localized ringed site.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification` along a locally bijective ring presheaf unit.
  The new module names the two required local-bijectivity proofs separately, with `sorry`.
  Their proof plans use the same section sets before and after forgetting commutativity.

Proof-dependency modules with existing lean records are imported non-publicly, as the
stage-3 plan requires. Dependencies without recorded modules have no import added:
ringed-slice extension-tensor, bounded-constant-model, exact module sheafification, and
Noetherian pseudo-coherence criterion; localized ringed sites and derived cohomology use
Mathlib matches already available through the public imports.

Edge cases checked mathematically: zero ring and zero modules are allowed; finite type
means finite generation, not cardinality. Empty covering sieves are allowed exactly when
covering in J. An empty site makes the objectwise condition vacuous as it should. Bounds
may be negative; complexes need not be bounded below. Zero complexes qualify. If a lower
truncation cutoff exceeds its upper bound, the zero model handles it. No finite refinement
across all integers is demanded. A common universe u for site and coefficients ranges over
all small data by enlarging u; the derived Hom universe w remains independent.

Searches: msearch LeanFinder for derived tensor and for arbitrary-site locally constant
finite type modules returned condensed-category constructions, not this assertion or
predicate. Loogle `CochainComplex.IsKFlat, CategoryTheory.constantSheaf` had no hits and
reported the project-specific first identifier unknown. msearch grep
`locallyConstant.*tensor|locally_constant.*tensor|constant.*SheafOfModules` in Algebra and
`IsLocallyConstantFiniteType|strictPerfectConstantPresheaf|locallyConstant.*[Tt]ensor` in
Mathlib had zero hits. LeanSearch for arbitrary-site local constancy returned Internal
Server Error (unavailable). Source and Sheaf rg found no matching predicate/theorem;
concept searches found the reused strictPerfectConstantPresheaf and only scheme-specific
lisse predicates. DAG searches found no definition for arbitrary sites;
`blueprint_refs.py search 'locally constant finite'` returned zero blueprint nodes.
Search output is recorded in searches.jsonl and the new node's mathlib_searches.

Server-only scompile compiled both delivered modules separately in dependency order,
with no errors or warnings. The only deferred proofs are the main theorem and two named
local-bijectivity lemmas, each with a natural-language proof plan. No node fault or
STATEMENT-DISPUTED issue was found.

## New nodes

`def-weil-pbc-site-locally-constant-finite-type` supplies the general-site local constant
finite-generation condition used verbatim in Tag 094H. The covering-sieve condition is
exactly local isomorphism to a constant finitely generated module, on every object. Its
constant model sheafifies the existing constant module presheaf along the forgotten
commutative-ring sheafification unit and then restricts to the slice; restriction of a
constant sheaf to a slice is the constant sheaf there. The two named helper lemmas assert
local injectivity/surjectivity of that unit after forgetting commutativity, with full
proof plans; the definition's data contain no sorry. Existing DAG and library local
constancy notions apply to schemes or condensed sites, not arbitrary small sites, so none
can replace this predicate. Search queries and concrete results appear above and in the
node. No dependency module or statement correction is needed.

## Second reading by NU

Independent reading against the original item node, both delivered modules, every
statement dependency record, and Stacks sites-cohomology.tex, lines 14356–14378
(Tag 094H). I also read sites-modules.tex, Definition 093Q: local constancy is
objectwise triviality on a covering, with isomorphisms in the coefficient category.
The preceding lemmas with a final object do not impose that hypothesis on 094H.

Object/hypothesis/conclusion checklist, with verdicts:

- Small site: `{C : Type u} [Category.{u} C]`, `J : Precoverage C`, and its
  HasIsos, composition, base-change, and covering-pullback instances render exactly
  def-weil-pbc-sites-and-cohomology. HasPullbacks asks for pullbacks along covers,
  not arbitrary categorical pullbacks. Associated sheaves use `J.toGrothendieck`.
  Verdict: same site notion; no final object or points assumed.
- Commutative Noetherian coefficient ring: `(B : Type u) [CommRing B]
  [IsNoetherianRing B]`. Mathlib defines the latter as Noetherianity of B as its
  own module. Verdict: precisely the ring in the node, with no field or nonzero
  hypothesis. Constant coefficients use `constantSheaf` in commutative rings,
  followed by `sheafCompose` forgetting commutativity; this retains its tensor API.
- Two objects of D-minus: `K L : DerivedCategory (SheafOfModules ...)`, with
  `hK` and `hL` existential integer upper bounds on vanishing of
  `DerivedCategory.homologyFunctor`. I read DerivedCategory.Basic and
  HomologySequence: these are localization at quasi-isomorphisms and the induced
  cohomology functors. Verdict: cohomology bounded above, no termwise or lower bound.
- All input cohomology locally constant of finite type: `hKlc`, `hLlc`, each
  quantified over every integer. Verdict: the new predicate below supplies exactly
  this property; no cover shared between infinitely many degrees is required.
- Derived tensor: arbitrary `P Q`, `hP/hQ : CochainComplex.IsKFlat`, and
  `eP/eQ : DerivedCategory.Q.obj P/Q ≅ K/L`. I read KFlat.IsKFlat (acyclic total
  tensor against every acyclic complex), and the tensor dependency record and
  upstream SheafOfModules.monoidalCategory (localized presheaf tensor).
  Verdict: the node explicitly defines derived tensor using K-flat replacements;
  these universally quantified choices render that convention without changing
  the objects or demanding that K and L themselves be complexes of flat terms.
- Conclusion: `∀ i : ℤ, IsLocallyConstantFiniteType ...
  ((CochainComplex.mapBifunctor P Q (curriedTensor ...)).homology i)`.
  Verdict: every cohomology sheaf of the derived tensor, with no additional clause;
  homologyFunctorFactors identifies it with derived-category cohomology.

New-node review (H12): def-weil-pbc-site-locally-constant-finite-type matches
Definition 093Q and the finite-type usage in 094H. Its definition says
`∀ V, ∃ S, S ∈ J V ∧ ∀ U f, S f → ∃ M, Module.Finite B M ∧ Nonempty (...)`.
The isomorphism is between module sheaves restricted by `overFunctor`, whose
signature I read in PushforwardContinuous. The constant model uses the actual
constant presheaf `strictPerfectConstantPresheaf` (identity restriction maps and
original linear maps), then module sheafification along the commutative-ring unit.
I read PresheafOfModules.sheafification: its locally bijective ring map produces
exactly modules over the target ring sheaf. The two named local-bijectivity lemmas
are propositions about the unchanged section sets; they supply proof data only.
No chosen unknown module or ring occurs in the definition. Restricting the global
constant model to a slice gives the slice constant model. Passing from covering
families to covering sieves is equivalent: pull back each trivialization for the
forward direction, and take the sieve arrows as the covering in the reverse.
All six cited dependency notions are present, the new-node metadata has the
required fields, and no dependency module was needed. The ringedSiteModules
record is a transparent abbreviation of the exact SheafOfModules used here.

Edge cases: zero ring and zero modules are admitted; finite means finitely generated,
not finite cardinality. Empty covering sieves are permitted only when covering.
The empty category gives the intended vacuous objectwise property; no nonempty
or terminal-object assumption is present. Every integer degree (including zero
and negative degrees) is covered, with arbitrary integer bounds. No characteristic,
prime, or positive-rank restriction occurs. Site, coefficients, and modules share
u, which ranges over all small data in the dependency convention; any particular
set-sized data fit a common enlarged universe. The derived Hom universe w is
independent, and HasDerivedCategory chooses localization size, not a finiteness
hypothesis on Hom sets.

Independent H4 searches: LeanFinder query "Sheaves of modules locally isomorphic
to sheafifications of constant finitely generated modules on covering slices"
returned Mathlib SheafOfModules.IsFiniteType/LocalGeneratorsData and finite
presentation results. I opened Generators.IsFiniteType: it asks for finitely many
local generators, without constant transition data, so is not this notion.
Loogle `"IsLocallyConstant"` returned predicates on functions on topological
spaces only. LeanSearch for "A module sheaf locally isomorphic on covering slices
to a constant finitely generated module" was unavailable (Internal Server Error),
not absence evidence. Independent rg searches for `locally.?constant`, `lisse`,
and `locally.?trivial` in Mathlib Sites, upstream WeilConjectures, this project's
Sheaf, and the DAG found topological, condensed, scheme/etale, and local-relation
notions, but no general-site replacement for this predicate or theorem. I also
checked the existing constant-module construction and reused it as written.

Mismatch and repair: the new predicate's source citation named only 094H, where
local constancy is used rather than defined. I added the exact Definition 093Q
citation to its module/declaration docstrings and its new-node source place.
No mathematical statement, signature, hypothesis, construction, or proof was
changed. There is no statement correction or disputed statement. Both signatures
were checked verbatim against their node lean.statement records; all universes
and variables are explicitly bound. Only the main theorem and the two named
local-bijectivity theorems have sorry proofs, with source and proof plans.
