## Worker report

The module `Sheaf.Paper.ProEtaleFiniteScalarRestrictionConstructible` states
`AlgebraicGeometry.Scheme.proEtaleFiniteScalarRestriction_constructible` and the two
witness clauses `proEtaleFiniteScalarRestriction_sameTrivializations` and
`proEtaleFiniteScalarRestriction_sameStratification`. All three proofs are `sorry`.
No mathematical definition is introduced or replaced. Each postponed proof has the
source and the corresponding steps of this DAG node in its docstring.

Hypothesis and conclusion matching:

- A Noetherian scheme is `(X : Scheme.{u}) [IsNoetherian X]`.
- The finite commutative rings are `(A B : Type u) [CommRing A] [CommRing B]
  [Finite A] [Finite B]`. The ring homomorphism is `(a : A →+* B)`, without
  surjectivity, flatness, nontriviality or a chosen algebra structure.
- The site is the original `X.ProEt` with `ProEt.topology X`. Its object and morphism
  universes remain u+1 and u; they are not forced equal. The constant commutative
  rings are `proEtaleConstantRing X A/B`, namely `constantSheaf` applied to
  `CommRingCat.of (ULift.{u+1,u} A/B)`. These are the exact coefficient objects of the
  recorded constructibility predicate. Coefficient rings use the same universe as
  the recorded definition; the module objects and sections use u+1.
- The induced map a_X is the actual
  `(constantSheaf (ProEt.topology X) CommRingCat.{u+1}).map
  (CommRingCat.ofHom a.ulift)`, not a freely chosen sheaf map.
- Its restriction functor is the existing `proEtaleRingRestrictScalars` at that map.
  Unfolding this abbreviation gives the recorded `SheafOfModules.restrictScalars`
  after forgetting commutativity. Its two exactness clauses are
  `PreservesFiniteLimits` and `PreservesFiniteColimits`; additivity is the existing
  Mathlib instance, not an extra hypothesis.
- The unbounded termwise derived functor is Mathlib's existing
  `Functor.mapDerivedCategory`. The already available named finite-limit and
  finite-colimit proofs are passed explicitly to it. This avoids adding any
  exactness assumption or file-local instance. Its localization normalization is
  `Functor.mapDerivedCategoryFactors` in the imported exact-functor module.
- Preservation of each constructible sheaf is the implication between the recorded
  `IsConstructibleProEtaleModuleSheaf` predicates in the third conjunct.
- For every q, the fourth conjunct is a natural isomorphism between the two
  composites of derived restriction and `DerivedCategory.homologyFunctor`. Its
  component at every L is exactly H^q(D(a_X)L) ≅ Res H^q(L), and naturality includes
  every morphism in the unbounded derived category.
- The fifth conjunct uses `IsZero` in both module categories to preserve and reflect
  cohomological vanishing, for every L and every integer q. It therefore preserves
  and reflects every specified vanishing bound and keeps any original [r,s].
- Bounded constructibility in the last conjunct is explicitly the standard
  `DerivedCategory.TStructure.t.bounded` property together with constructibility of
  every integer cohomology sheaf. The same conjunction is asserted after restriction.
  This uses the recorded bounded-subcategory definition, not a private predicate.
- The unchanged-strata clause fixes an arbitrary input `S : Stratification X` and
  carries the very same per-stratum local-constancy and finite-geometric-stalk
  conditions to the restricted sheaf. A positive number of strata, if supplied by
  the original constructibility witness, is unchanged because S itself is unchanged.
- The unchanged-cover clause fixes S, i, I, U, f and the original covering condition
  `_hc`. Given the original module-sheaf trivializations `_ht` with models M j, it
  returns trivializations on the identical U j with models
  `(ModuleCat.restrictScalars a.ulift).obj (M j)`. No cover refinement or arbitrary
  replacement model is substituted.

Dependency interfaces read and used:

- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`
  (sheafification of the constant presheaf), including its map on ring homomorphisms.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`,
  `ProEt.topology` and its covering precoverage.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, with the unchanged module presheaf and sheaf proof.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules` with the inherited category and Abelian instance.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `HasDerivedCategory.standard` and Q. Existing
  `proEtaleRingModules_hasDerivedCategory` supplies the standard localization.
- `Sheaf.Paper.ProEtaleConstructibleSheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleProEtaleModuleSheaf`, its precise positive
  finite stratification, localized constant-model condition and finite geometric stalks.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`: `DerivedCategory.Plus`,
  `Minus`, `Bounded`, their defining `TStructure.t.plus/minus/bounded`, and
  `isGE_iff/isLE_iff`. The bounded clause uses the same underlying object property.
- The new definition dependency `def-pe-proetale-ring-restrict-scalars` records the
  existing `proEtaleRingRestrictScalars` and its two exactness helpers in
  `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`. The adjunction theorem
  itself is neither a statement dependency nor used to choose any data.
- The imported constructibility module also exposes the recorded
  `proEtaleConstantModulePullback`, `proEtaleGeometricModuleStalk`,
  `IsLocallyConstantProEtaleModuleSheaf` and `proEtaleConstantModuleSheafOver`.
  The currently recorded universe-general local-constancy module and geometric-stalk
  functor module are included as proof imports, without altering the fixed-universe
  specialization used by the recorded constructibility definition.
- Proof imports retain the available dependency modules for constant-ring inverse
  image, module sheafification, exact-functor cohomology and module-sheaf colimits.

Edge cases checked mathematically before writing: the empty scheme is permitted and
its positive one-stratum witness can use the empty stratum; a stratum can be empty;
empty cover indices give vacuous trivializations when they are covers; the zero
coefficient ring is allowed (a unital map from it can only have zero target); the
zero complex and any integer degree, including negative degrees, are allowed;
identity maps, Z/4 → Z/2, and non-surjective F_2 → F_4 all have the intended restricted
action. Finite B-module generators are not asserted to remain A-generators: instead
the finite underlying stalk set generates the restricted A-module. No nonemptiness
or nonzero-ring assumption was introduced. No statement correction or dispute.

Searches performed (2026-10-21):

- msearch.py leanfinder: “Restriction of scalars along any finite commutative ring
  map preserves constructible pro-etale module sheaves and cohomology bounds”.
  Eight hits concerned formally etale algebras and ring-map base change; no match.
- msearch.py leansearch: “An exact restriction of scalar functor on sheaves commutes
  with derived cohomology and preserves constructibility”. Eight hits included
  `SheafOfModules.restrictScalars`, presheaf restriction, module restriction and
  coextension; no pro-etale constructibility-and-bounds theorem.
- msearch.py loogle: `SheafOfModules.restrictScalars, Functor.mapDerivedCategory`
  returned no hit because of the second identifier. A follow-up
  `SheafOfModules.restrictScalars` returned the exact functor, additivity and
  object/map formulas; these definitions are reused.
- msearch.py grep: `restrictScalars.*constructib|constructib.*restrictScalars` in
  Mathlib returned zero hits.
- rg of the source `lean/WeilConjectures` and project `lean/Sheaf` for the item id,
  `restrictScalars.*[Cc]onstruct|[Cc]onstruct.*restrictScalars`, and scalar restriction
  helpers found no statement of this node. Source
  `ConstructibleSheaf/RestrictScalars.lean` and
  `SixFunctors/Etale/Derived/Finiteness/CoefficientDevissage.lean` concern the etale
  site and its fixed-module constructibility predicate. The latter's arbitrary
  finite-ring theorem was read; it is not a direct match for this intrinsic
  pro-etale statement. CompletedIntegral.lean concerns completed coefficient sheaves.
- Source and project searches found existing general ring-sheaf restriction and
  exactness in ProEtaleRingSheafChangeAdjunction.lean, so those are reused rather
  than defining another restriction functor. The more specialized old
  ProEtaleDirectImageRestrictionOfScalars.lean helper was read but is not needed.

## Second reading by Q83

A separate reading pass by the same worker compared the full node with all three
signatures. The dispatcher prohibits starting another agent; the maintainer's
independent review is separate from this self-check. The primary statement includes
all seven hypotheses (scheme, Noetherian, both rings, commutativity, finiteness and
map), exactness, all constructible sheaves, every unbounded derived object and degree,
natural cohomology comparison, vanishing in both directions and bounded
constructibility. The second and third signatures explicitly retain the original
covers and stratification. The reading checked exactness and the explicit same-cover/same-stratum clauses. Inspection also found that the generic
exactness declarations are only local instances in their defining module: the
current derived-functor terms pass these existing proofs explicitly. No hypothesis
of surjectivity, flatness, nonzero coefficients or boundedness on arbitrary L occurs.
The repair adds the existing-definition attachment described below. No dependency
module or correction to the mathematical node is needed.

## Prior validation (2026-10-21, before the H2 return)

The required initial dry run reproduced the earlier missing published artifacts before
reaching this module. An explicit-prerequisite import attempt, together with concurrent
private dependency compiles, let scompile.py reach the statement. It diagnosed ambiguous
lift universes in the bare `a.ulift` terms. Every coefficient map now uses the explicit
`a.ulift.{u + 1, u + 1}`, matching the existing `ULift.{u + 1, u}` coefficients on both
sides. This changes no mathematical hypothesis, conclusion, coefficient object or site.
The temporary prerequisite imports have been removed; the mathematical imports are
those of the retained packet.

The resumed self-check reread the current constructibility predicate, the generic
restriction and named exactness declarations, and Mathlib's derived functor signature.
The three signatures still match all clauses described above. Only `lean` and the added scalar-restriction definition dependency differ from the
current node.
All three theorem proofs remain whole `sorry`; no definitions or instances were added.
The primary signature in `lean.statement` was refreshed verbatim after the universe fix.
No line exceeds 100 characters. A fresh project/source search found only the previously
noted etale-site scalar-restriction theorems, with no duplicate intrinsic pro-etale one.

Validation uses only the prescribed scompile.py and deliver2.py wrappers; no live files,
launcher tools, or compiled artifacts were edited, and no direct Git command or global
build was run.

Final scompile.py validation passed cleanly in both modes: sandbox 9.4 seconds and
library 5.1 seconds, with no errors or warnings. The required deliver2.py --no-push
then printed `OK (dry run): commit 394fe733224 passes the preflight and compiles`.
The retained packet has completed the hypothesis-by-hypothesis self-check above and
is ready for the maintainer's independent review.

## New nodes

`def-pe-proetale-ring-restrict-scalars` attaches, with `existing: true`, the exact
commutative-ring-sheaf specialization already defined in
`Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`:
`AlgebraicGeometry.Scheme.proEtaleRingRestrictScalars`, together with
`proEtaleRingRestrictScalars_preservesFiniteLimits` and
`proEtaleRingRestrictScalars_preservesFiniteColimits` in the same namespace.
Its source is the restriction construction preceding
`lemma-adjointness-tensor-restrict` in Stacks `sites-modules.tex`, with the exactness
of kernels and cokernels in Tag 03DA. This is the restriction used by the current
blueprint integral-criterion reductions proof, second paragraph, last sentence.
The signature is copied verbatim from the existing abbreviation; no new Lean module,
definition, theorem proof, or instance is supplied.

The new node's hypotheses and clauses match the existing declarations as follows:
`{T : Scheme.{u}}` is the arbitrary scheme; `{R S : Sheaf (ProEt.topology T)
CommRingCat.{u + 1}}` are arbitrary commutative ring sheaves on its original small
site; `(a : R ⟶ S)` is their arbitrary map; the target
`proEtaleRingModules T S ⥤ proEtaleRingModules T R` is precisely module restriction.
The abbreviation body applies `SheafOfModules.restrictScalars.{u + 1}` to
`(sheafCompose ... (forget₂ CommRingCat RingCat)).map a`; its sections and maps are
unchanged and its scalar action is composed with a. The named limit and colimit
helpers have these same binders and respectively conclude `PreservesFiniteLimits`
and `PreservesFiniteColimits`. They are explicitly passed to `mapDerivedCategory`
in the delivered theorem. The general underlying Mathlib construction remains owned
by `def-pc-sheaf-restrict-scalars`, which this new node cites.

Fresh searches for this attachment, recorded also in `mathlib_searches`:

- `msearch.py leansearch`, query “Restriction of scalars for sheaves of modules over
  a commutative ring sheaf on a small pro-etale site is exact”: eight hits, including
  `SheafOfModules.restrictScalars` and its underlying-presheaf formula.
- `msearch.py loogle`, query `SheafOfModules.restrictScalars`: four hits, giving the
  functor, additivity, object and map formulas.
- `msearch.py leanfinder`, query “Restriction of scalar rings on sheaves of modules
  preserves finite limits and finite colimits”: eight hits, including restriction
  and finite-limit preservation for forgetful functors.
- `msearch.py grep`, query `restrictScalars|preservesFiniteLimits|preservesFiniteColimits`
  under `Algebra/Category/ModuleCat/Sheaf`: fifteen hits, including the general
  restriction definition and sheaf-module finite-limit interfaces.
- `rg -l proEtaleRingRestrictScalars` in `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/nodes` finds the existing Sheaf definition and its users; no upstream name
  match and no definition node owning this specialization and exactness interface.
  The existing adjunction node lists the helpers, but its actual theorem concludes
  a derived adjunction compatibility, not this definition. `blueprint_refs.py search
  'restriction of scalars'` finds 58 blueprint nodes, including general sheaf and
  module-object restriction. `blueprint_refs.py ancestor` identifies
  `det-prop-integral-criterion-reductions`; the new node's `via` prepends this item.

The new attachment preserves the empty-scheme, zero-ring, identity-map and arbitrary
non-surjective-map cases, without finiteness or Noetherian assumptions. The site
universes remain u+1/u; the section/module universe is u+1. Nothing is redefined.

## Return repair H2(2) and repeated self-check (2026-10-21)

The initial required dry run of the retained packet passed as commit `087862b6527`.
The maintainer's independent return nevertheless identifies a genuine dependency
classification defect. Replaced the packet's added statement dependency
`lem-weil-pbc-ring-sheaf-change-adjunction` by the new definition attachment
`def-pe-proetale-ring-restrict-scalars`, as the return explicitly prescribes.
The main branch's original seven statement dependencies are retained. The theorem
and proof dependency lists, natural-language statement and all three Lean declarations
are unchanged. The repaired record cites the actual functor and both exactness helpers;
no conclusion of the adjunction theorem, `.choose`, or arbitrary comparison is used.

The repeated reading opened the original node, all three retained Lean statements,
the existing abbreviation and both helper signatures/docstrings, the general Mathlib
restriction construction, and the source's restriction and kernel/cokernel paragraphs.
It confirms that the new attachment introduces exactly the actual specialization
needed to state the derived functor, with no changed mathematical hypothesis or
conclusion. The report's clause-by-clause mapping and edge-case checks remain valid.
The new definition node has all H12 fields, no proof dependencies, no postponed
proof, and an existing record rather than another implementation. Its `stmt_deps`
are exactly the three definition citations in its statement. This resolves the sole
numbered return point. No statement correction or dependency module is required.

Post-repair scompile.py passed cleanly: sandbox 12.5 seconds, library 13.2 seconds.
The self-check verified the verbatim primary signature, all three whole-sorry proofs,
100-character Lean lines, exact new-node citations and JSON layout. Relative to the
read-only main node, the only changed fields are `lean` and the one added definition
dependency. The Lean file is retained unchanged from the returned packet.
