## Worker report

The module `Sheaf.CategoryTheory.ConstantRingModuleSheaves` states
`CategoryTheory.constant_ring_module_sheaves`, with `sorry` as its entire proof.
It defines the canonical scalar restriction and a predicate spelling out the
compatibility conditions on an extended action. These helpers belong to this
node's construction, are listed in `lean.declarations`, and have actual data.
No new node, dependency repair, or statement correction is needed. Nothing
outside the field `lean` of the item's node copy changes.

Hypotheses and clauses, matched against the node:

- The site is `C : Type u` with `Category.{v} C` and
  `J : GrothendieckTopology C`. This is Mathlib's covering-sieve topology and
  sheaf limit condition; no fibre products, subcanonicity, or terminal object
  are assumed. Sieve pullback does not require categorical pullbacks.
- The size convention is implemented by the explicitly declared universes
  `u v` and common bound `max u v` for rings and module carriers. Site object
  and morphism universes remain independent. This is the bound used by
  Mathlib's small-site concrete sheafification, also used by the project's
  `siteConstantModuleFunctorGeneral`. The convention permits choosing a
  common small skeleton and bound before the statement. No `HasSheafify`
  hypothesis or identification of the two site universes was added.
- The coefficient is `Λ : Type (max u v)` with `[CommRing Λ]`.
  `(Functor.const Cᵒᵖ).obj (RingCat.of Λ)` is the constant ring presheaf with
  identity restrictions. `(constantSheaf J RingCat).obj (RingCat.of Λ)` is
  exactly its ring sheafification; `toSheafify J ...` is its unit.
- Fixed-ring module-valued sheaves are literally
  `Sheaf J (ModuleCat.{max u v} Λ)`. Their morphisms are the bundled linear
  natural transformations supplied by this category.
- Modules over the constant ring sheaf use the dependency's transparent
  `ringedSiteModules` abbreviation, hence the existing `SheafOfModules`
  category. Its sectionwise module structures, semilinear restrictions,
  underlying abelian sheaf condition, and sectionwise linear morphisms are
  unchanged Mathlib definitions.
- `constantRingModuleRestrictionPresheaf` applies the existing
  `PresheafOfModules.restrictScalars` to that precise unit. Constant ring
  restrictions make its restrictions ordinary Λ-linear maps.
  `constantRingModuleRestriction` packages this into a functor to the claimed
  sheaf category; the abelian sheaf condition is reflected by forgetting
  module structure. Its maps use `ModuleCat.restrictScalars` on the original
  components. Thus the equivalence is tied to canonical scalar restriction,
  rather than an unconstrained equivalence between the two categories.
- The first existential provides `e` in the node's orientation, from modules
  over the constant ring sheaf to fixed-ring module-valued sheaves, with
  `e.functor = constantRingModuleRestriction J Λ`. Both
  `e.functor.Additive` and `e.inverse.Additive` are asserted. The bundled
  equivalence supplies the two quasi-inverse natural isomorphisms.
- The equality `e.inverse ⋙ SheafOfModules.toSheaf _ = sheafCompose J ...`
  asserts retention of underlying abelian sheaves AND maps by the inverse.
  Forward restriction already retains them by its explicit construction.
- For every original module-valued sheaf `N`, `∃! m` quantifies over module
  structures on exactly the existing section types `N.obj.obj X`, with their
  original additive group structures. This is uniqueness of the action on
  the SAME abelian sheaf, not uniqueness only up to an unspecified isomorphism.
- `IsConstantRingModuleActionExtension` explicitly asserts both
  `N.map f (s • x) = R.map f s • N.map f x` and
  `iota.app X a • x = a • x`. The latter RHS is the original Λ-action;
  explicit `@SMul.smul ... (m X).toSMul` selects the proposed extended action.
- The last conjunct covers every `f : N ⟶ M` and any extended actions `m,n`.
  Assuming their compatibility predicates, it asserts sectionwise extended
  scalar linearity. This renders every original linear natural map linear
  over the sheafified ring, including maps between distinct sheaves.
- There is no nonzero-ring, positive characteristic, nonempty-site, nonempty
  object, or nonempty-cover hypothesis.

Dependency declarations read and used:

- `def-weil-size-convention`: metatheoretic convention; no declaration.
- `def-weil-pbc-sheafification`:
  `Mathlib.CategoryTheory.Sites.Sheafification`,
  `CategoryTheory.presheafToSheaf`, `CategoryTheory.toSheafify`,
  `CategoryTheory.sheafificationAdjunction`; the constant-sheaf import
  publicly imports this module. Their full definitions identify the unit.
- `def-weil-pbc-constant-sheaf`:
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `CategoryTheory.constantSheaf`, explicitly constant presheaf followed by
  `presheafToSheaf`.
- `def-weil-sheaf-of-modules-category`:
  `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`, transparently `SheafOfModules`.
- Proof leaf `lem-cbc-sieve-module-sheafification`:
  `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`,
  `PresheafOfModules.sheafificationAdjunction`,
  `PresheafOfModules.sheafificationCompToSheaf`, and its finite-limit
  preservation instance, as recorded by its `mathlib_match`. Its source and
  full signatures were read, including the invertible counit, full/faithful
  instances and underlying-unit formula. This is a proof-only import.

The main theorem's docstring carries the six proof steps from the node:
matching module limits; the scalar sheafification adjunction and invertible
abelian unit on a sheaf; transported action `c(s • eta(x))`; uniqueness by
fullness applied to the identity; linearity of every map by fullness; and
identity underlying maps for inverse equivalences and additivity. The source
`literature/stacks-project/sites-modules.tex`, lemma
`lemma-sheafification-presheaf-modules` (Tag 03CY), was read at lines 814–849.
Its proof is omitted; the node's agent argument supplies the arbitrary-sieve
constant-ring specialization, as the module explicitly acknowledges.

Edge cases checked before finalizing:

- Empty category: the universal sectionwise assertions are vacuous and both
  categories have the unique empty diagram, so the equivalence still applies.
- Zero ring: all fixed-ring unital modules are zero. The sheafified zero ring
  has the corresponding zero module category; no forbidden nonzero structure
  is requested.
- An empty covering sieve: the sheaf condition forces the appropriate section
  object terminal, and the unique module action extends; empty covers are
  allowed by `GrothendieckTopology`.
- The coarsest topology: every presheaf is a sheaf, the ring is constant, and
  the statement specializes to the usual identity scalar restriction.
- A site without fibre products: all constructions use sieve sheafification,
  not products or pullbacks of objects of the site.
- Distinct site object/morphism universe levels are retained; the coefficient
  bound is their maximum. All variables and universe levels are explicitly
  bound; `autoImplicit` is disabled.

Searches for an exact existing statement and for names:

- `msearch.py leanfinder`: "Sheaves valued in modules over a fixed commutative
  ring are equivalent to sheaves of modules over its constant ring sheaf on
  an arbitrary Grothendieck topology" returned eight hits, led by
  `SheafOfModules.unit`, `forgetToSheafModuleCat`, and the underlying-sheaf
  functor. No complete equivalence. The forgetful functor hit requires an
  initial object of the opposite category, which the present node does not.
- `msearch.py loogle`: `PresheafOfModules, ModuleCat` returned twelve hits,
  including evaluation, Hom components and the initial-object-dependent
  forgetful functor. No exact statement.
- `msearch.py leansearch`: "A module valued sheaf has a unique action of the
  sheafification of the constant ring presheaf extending its scalar action"
  returned eight hits on `PresheafOfModules.Sheafify.SMulCandidate` and
  `PresheafOfModules.sheafify`. These supply the scalar-extension ingredient,
  not the complete stated equivalence and its uniqueness/linearity clauses.
- `msearch.py grep`: `constant.*(ModuleCat|SheafOfModules)|constantSheaf.*(equiv|Equiv)`
  in `Algebra/Category/ModuleCat` returned zero hits. Direct `rg` of the same
  Mathlib subtree agreed. Direct reading of `Presheaf.lean`,
  `Presheaf/ChangeOfRings.lean`, `Sheaf.lean`, and
  `Presheaf/Sheafification.lean` established which generic constructions to reuse.
- `rg` of the upstream `WeilConjectures` and this project's `lean/Sheaf`
  searched constant/module/equivalence patterns and this item id;
  `grep -rn` of the item id in upstream found no declaration. Broader
  constant-ring searches identified the existing étale specializations:
  `EtaleConstantRingModuleEquivalence`, `ModuleSheafConstantRingEquivalence`,
  and `ConstantRingModuleSheafEquivalence`. Their declarations were read:
  they require a scheme and its small étale site (one is further ZMod-specific),
  so they do not state this arbitrary-sieve-site theorem. The restriction
  helpers in `AdicStratifiedPerfect` and `TorAmplitudeKFlatResolution` are
  likewise pro-étale/étale scheme-specific. `FieldScalarPresheafRingMap` has
  a topological opens site and the opposite conversion direction.
- `rg` of `dag/lean_names_upstream.json`, upstream, and `lean/Sheaf` for all
  four proposed full-name stems found no conflicts.

Validation: `scompile.py NA lem-cbc-constant-ring-module-sheaves` compiled the
single delivered module cleanly, both as sandbox and library path. The only
postponed proof is `CategoryTheory.constant_ring_module_sheaves`. All helper
definitions have real data and use existing functor laws and sheaf-condition
reflection. There are no file-local instances or notation, no private copies
of the categories, no `#check` lines, and no lines longer than 100 characters.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
