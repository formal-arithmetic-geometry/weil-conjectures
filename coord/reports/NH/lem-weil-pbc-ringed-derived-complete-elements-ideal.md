## Worker report

The module `Sheaf.CategoryTheory.RingedSiteCompleteElementsIdeal` states
`CategoryTheory.ringedSite_complete_elements_ideal`; its only proof is `sorry`.
The original statement is unchanged. Three definition nodes supply the missing
section localization, derived restriction, and reusable local vanishing predicate.
Every definition has real data and no postponed construction or axiom.
The definition node for section localization also records the named proof obligation
`ringedSiteSectionLocalization_compatible`, with proof `sorry`; this is the
compatibility of restricting f along composites, proved by functoriality and Over.w.
Only this proof is postponed, never the section values or the transition maps.

Hypothesis and clause correspondence:

- The small site is `{C : Type u} [SmallCategory C] (J : GrothendieckTopology C)`.
  `R : Sheaf J CommRingCat.{u}` is the sheaf of commutative rings.
- `K : DerivedCategory (ringedSiteModules ... R)` is the arbitrary unbounded
  derived module object. `HasDerivedCategory.{w}` on the original site and on
  every slice records localization size choices, not boundedness or an
  extra mathematical condition. No independent test-site universe is used.
- `IsRingedSiteCompleteElement J R K U f` is exactly the displayed vanishing
  criterion: existing `derivedInternalHom` on the slice applied to
  `O_U[1/f][0]` and `K|U`, with vanishing expressed by `Limits.IsZero`.
  The new restriction definition chooses `Q.objPreimage K`, restricts this
  actual complex using `SheafOfModules.overFunctor`, and applies slice `Q`.
  Exactness of restriction guarantees this is the derived restriction; it
  does not replace K by an arbitrary input object or assume the conclusion.
- `I : ∀ U, Ideal (R.obj.obj (op U))` and the first conjunct identify the
  *whole* set of vanishing sections with an ideal at every U. Thus zero
  membership, closure under addition and under multiplication by any
  section are encoded by the existing `Ideal` structure. There is no
  additional, unconstrained notion of complete elements.
- The second conjunct says `f ∈ I U` restricts along every `a : V ⟶ U`
  to `R.obj.map a.op f ∈ I V`.
- The third conjunct says membership descends from every covering sieve
  `S ∈ J U`. These two conditions on the subpresheaf I, together with the
  existing sheaf condition on R, are exactly the sheaf condition: compatible
  local sections glue uniquely in R, and local membership puts the glued
  section in I. This covers sites without pullbacks or a chosen basis.
- The final conjunct explicitly states the local finite-generator consequence.
  On every arrow in a covering sieve it allows a finite tuple `b : Fin r → R(V)`,
  each satisfying the *actual* vanishing predicate, and requires the restricted
  section x to lie in `Ideal.span (Set.range b)`. It concludes that x satisfies
  the vanishing predicate on U (hence, in particular, locally). A section of an
  ideal sheaf generated locally by the b_i has exactly this locally finite-span
  description. Refining the generating cover to the cover on which its sections
  admit finite combinations gives the displayed sieve condition. Conversely this
  formulation only uses ideal closure and sheaf descent, so does not strengthen
  the asserted ideal-sheaf property. Tuples may vary over the cover; no global
  generating tuple or quasi-coherence is assumed.

Dependency declarations used and read:

- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  the transparent general-site alias for Mathlib `SheafOfModules`, including
  its category and abelian structures. No scheme-only definition is used.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, `Q.objPreimage` and
  `DerivedCategory.singleFunctor`: the recorded localization and degree-zero object.
- `Sheaf.Algebra.Homology.DerivedInternalHom`,
  `CategoryTheory.derivedInternalHom`: the recorded ringed-site internal Hom,
  not ordinary global Hom or an assumed abstract bifunctor.
- `Mathlib.CategoryTheory.Sites.Over`, `GrothendieckTopology.over`, `Sheaf.over`,
  and `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`,
  `SheafOfModules.overFunctor`: the slice site and actual restriction.
- `Sheaf.Algebra.Homology.RhomIntoKInjectiveLocal`,
  `CategoryTheory.module_overFunctor_preservesZero`: the existing closed witness
  needed to map complexes. Its entire signature and source docstring were read.
  Exactness/representative independence is already established by the existing
  `CategoryTheory.localizedModule_restriction_quasiIso` in
  `Sheaf.Algebra.Homology.LocalizedModuleRestrictionQuasiIso`.
- Mathlib `SheafOfModules.unit`, `unitHomEquiv`,
  `PresheafOfModules.sectionsMk`, `Functor.ofSequence`, and `Limits.colimit`
  construct O_U[1/f]. The transition is right multiplication by f restricted
  to each slice object. For the commutative sheaf in the item this is the
  usual localization. Colimits of module sheaves are sheafified presheaf
  colimits, and the sectionwise repeated-multiplication colimit is R[1/f].
- The proof-only imports are the recorded Mathlib leaves
  `Localization.existsUnique_algebraMap_eq_of_span_eq_top` in
  `Mathlib.RingTheory.Localization.Away.Basic`, and module sheafification
  finite-limit preservation in
  `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` (colimits follow
  from its left adjoint). Signatures and docstrings were opened.
  `lem-weil-pbc-ringed-localization-rhom-calculus` has no recorded module,
  so no import is invented for it. Its proof use is carried in the docstring.

Edge cases checked before writing: f=0 gives the zero sequential colimit, so
its internal Hom vanishes; f=1 gives O_U and the expected vanishing condition;
K=0 gives the whole ideal at every U; a zero ring has its unique ideal; r=0
has empty range and zero span. The empty site makes all objectwise assertions
vacuous, as appropriate. A covering empty sieve forces the usual sheaf zero
sections on that object, and the descent clause still applies. No reducedness,
Noetherian assumption, points of the site, pullbacks, finite generation of R,
or cohomological bound on K is introduced.

Searches for an existing item: msearch leanfinder, "Elements f of a ring sheaf
for which derived internal Hom from localization at f vanishes form an ideal
sheaf", returned scheme ideal data and Tilde constructions, not this statement.
Loogle `SheafOfModules, Localization.Away` returned zero hits; msearch grep
`derived.?complet.*ideal|ideal.*derived.?complet` returned zero hits. LeanSearch
was attempted and returned Internal Server Error. Project and upstream rg,
including the exact item id and proposed declaration names, found no match.
The upstream name index was also searched. The new nodes carry verbatim outputs
of the additional shared searches (LeanSearch, LeanFinder, Mathlib grep).
Definition-node scanning and `tools/blueprint_refs.py search localization` found
no node for these three derived/section constructions: the existing localized
ringed-site node describes the underlying slice site and underived restriction.
Mathlib's sheaf `Localization` module is categorical localization at locally
bijective maps, not inversion of f. TopCat's localization presheaf applies only
to topological spaces, and Tilde applies only to spectra.

Source checked directly: `literature/stacks-project/algebraization.tex`,
`lemma-hom-from-Af` (0997) and `lemma-ideal-of-elements-complete-wrt` (0998).
The theorem docstring carries all six original proof steps, including binary
localization surjectivity, the Hom-cone calculation, sheaf locality and r=0.
No statement correction or disputed statement was needed.

## New nodes

`def-weil-pbc-ringed-site-section-localization`: defines the actual repeated-
multiplication colimit of O_U-modules. For commutative coefficients it is the
sheafification of sectionwise localization at f. Source: Tag 0997's telescope
resolution, and the localized module used in Tag 0998. The definition permits
rings as coefficients for the module telescope; the item uses commutative rings.
The section values are constructed explicitly. Their compatibility is the named
proof obligation `ringedSiteSectionLocalization_compatible`, as required for a
proof needed inside a definition; its natural-language proof is in its docstring.
Shared searches listed above and recorded verbatim in the node found no general
ringed-site section-localization module construction. No data is sorry.

`def-weil-pbc-ringed-site-derived-restriction`: defines K|U using restriction of
Mathlib's canonical representative of the existing localization. Source: K|U
in Tags 0997/0998, with slice restriction as in Modules on Sites, Tag 03DH.
The shared searches found only underived restriction and general localization
machinery, not this ringed-site derived-object specialization. Existing
`SheafOfModules.overFunctor` and its zero-morphism witness are used directly.
Choosing the Q representative uses its proved essential-surjectivity interface,
not a mere existence theorem with an undetermined, sorry-chosen object.

`def-weil-pbc-ringed-site-complete-element`: the Prop-valued local vanishing
criterion from Tags 0997/0998, using the two construction nodes and the recorded
`derivedInternalHom`. It introduces no replacement Hom functor or completeness
hypothesis. Shared searches found no declaration for this ringed-site criterion.
The internal local instance reconciles definitionally equal slice coefficient
sheaves and changes no data. This definition cites the other two new nodes;
the item cites it, so every added node is reachable from the item.

## Earlier second reading (a previous round; superseded)

I independently opened the item node, all four delivered modules, and all three
new definition nodes. I read algebraization.tex at lemma-hom-from-Af (0997)
and lemma-ideal-of-elements-complete-wrt (0998), including the preceding
localization calculation. Tag 0998 assumes a ringed site and an arbitrary
unbounded derived object, with no Noetherian or coherence condition. Tag 0997
identifies its T-vanishing condition with the internal-Hom condition in the node.
The node deliberately works with a small site and commutative ring coefficients,
matching the recorded derived-internal-Hom interface.

Object, hypothesis and conclusion checklist (node order):

1. A small site C: `{C : Type u} [SmallCategory C]` and
   `(J : GrothendieckTopology C)`. Verdict: exact; no chosen points,
   pullbacks or basis of covers are required.
2. A sheaf of commutative rings O: `(R : Sheaf J CommRingCat.{u})`.
   Verdict: exact. Forgetting to RingCat is solely the coefficient interface
   for the recorded `ringedSiteModules` alias, not a replacement coefficient ring.
3. An arbitrary K in D(O): the `K : DerivedCategory (ringedSiteModules ... R)`
   binder. Verdict: exact. The two HasDerivedCategory binders specify localization
   sizes on C and its slices. They impose no boundedness or algebraic finiteness.
   Taking the standard sufficiently large localization universe supplies them.
4. For each U and f in O(U), the set defined by
   RHom(O_U[1/f], K|U)=0: `IsRingedSiteCompleteElement J R K U f`.
   I unfolded this definition: `DerivedCategory.singleFunctor _ 0` embeds the
   constructed localization module in degree zero; the second argument is
   `ringedSiteDerivedRestriction`; `derivedInternalHom (J.over U) (R.over U)`
   is the recorded internal Hom on that same slice; `IsZero` is zero in the
   derived category, not only vanishing global sections or one cohomology group.
   Verdict: exact, including the order and variance of the two Hom arguments.
5. These whole sets are ideals: `exists I : forall U, Ideal (R.obj.obj (op U))`
   together with the biconditional in the first conjunct. Verdict: exact.
   It is not an assertion about an arbitrary smaller subideal. `Ideal` supplies
   zero membership, addition and multiplication by every section (and negatives).
6. They form a sheaf of ideals: the second conjunct quantifies over every
   `a : V ⟶ U` and uses `R.obj.map a.op`; the third quantifies over every
   covering sieve S and descends membership from all its arrows. Verdict: exact.
   Restriction makes the subsets a subpresheaf. Any matching family glues uniquely
   in the given ring sheaf R; sieve descent ensures its glued section is in I.
   Conversely a subsheaf of R has exactly this local-membership property.
7. Locally finite generators b_1,...,b_r imply local membership for every
   section of the generated ideal: the last conjunct takes a covering sieve,
   a section x, and, on each covering arrow, a tuple `b : Fin r → R(V)`
   of actual complete elements with the restriction of x in
   `Ideal.span (Set.range b)`. Verdict: equivalent consequence. Sections of
   a generated ideal sheaf are locally finite linear combinations; refine the
   cover to express such combinations and apply this conjunct. Its conclusion
   is membership on U, equivalent to local membership by the preceding sheaf
   clause. Allowing the finite tuple to vary on the cover adds no strength to
   ideal closure and descent, and requires no globally chosen generators.

I opened the recorded dependency signatures, not merely their names:
`ringedSiteModules` is transparently Mathlib `SheafOfModules`, and its abelian
instance is available on a small site; `DerivedCategory` and Q are the unbounded
localization; the actual `derivedInternalHom` constructs the functor by localizing
the Hom complex after functorial K-injective replacement. I also read
`SheafOfModules.overFunctor`, `overMap` and `overFunctorMap`, the Mathlib match of
`def-pur-localized-ringed-site`; they really evaluate modules on the slice.
`module_overFunctor_preservesZero` supplies the proved complex-functor witness.
`localizedModule_restriction_quasiIso` proves that this restriction preserves
quasi-isomorphisms, so restricting a Q-preimage really computes K|U.

New-node reading (H12/H13):

- `def-weil-pbc-ringed-site-section-localization`: the module is precisely the
  sequential colimit named in the node. I opened Mathlib `unit`, `unitHomEquiv`
  and `PresheafOfModules.sectionsMk`: the inverse equivalence sends the family
  of restrictions of f to right multiplication by f on the rank-one left module.
  This agrees with the noncommutative telescope in the definition node and with
  O_U[1/f] for the commutative coefficients of the item. The compatibility lemma
  is a named proof obligation with a functoriality/Over.w proof plan; no section,
  map or colimit data is sorry. Tag 0997's displayed telescope resolution is the
  source of this construction.
- `def-weil-pbc-ringed-site-derived-restriction`: the body restricts the genuine
  complex `DerivedCategory.Q.objPreimage K` then applies the slice Q, exactly as
  its node says. I checked Mathlib `Functor.objPreimage` and `objObjPreimageIso`:
  their essential-surjectivity interface supplies a representative of K, not
  unspecified data extracted from a sorry existence theorem. Exact restriction
  makes different representatives isomorphic after Q. This is the K|U used by
  0997/0998 and Modules on Sites, Section 03DH.
- `def-weil-pbc-ringed-site-complete-element`: the definition is precisely the
  predicate in checklist item 4 and cites both constructions. The internal
  letI only identifies definitionally equal presentations of the slice coefficient
  sheaf; there is no local notation, replacement RHom, or hollow hypothesis.

All three nodes have definition kind, split status, self-contained statements,
matching cited stmt_deps, source document/place, empty proof/proof_deps,
mathlib_match null, the three search kinds, worker/item/date/group provenance,
blueprint ancestry through this item, none audits and the item's chapter/unit.
They are reached through the complete-element dependency. No dependency module
needs repair. The theorem docstring follows all six node proof steps, including
surjectivity of the binary-localization map, the Hom-cone calculation, sheaf
locality and the empty generating tuple. Every declaration has its source and
blueprint attribution. Both remaining theorem proofs are sorry, as stage 2 requires.

Edge cases: the empty category makes the objectwise conclusions vacuous; an
empty covering sieve forces zero ring sections by the sheaf condition, and is
allowed in both descent clauses. K=0 yields the whole ring ideal; f=0 has zero
telescope, while f=1 has the unit module as telescope. Zero coefficient rings
are allowed. `Fin 0` gives empty range and zero span. There is no characteristic
restriction. The site, coefficients and modules share arbitrary u (so any small
site/ring pair can be placed in a sufficiently large common universe), and w is
an explicit derived-localization size rather than an independent test universe.

Independent searches: msearch LeanFinder, "Vanishing RHom from a section
localization is stable under addition and glues on covering sieves", returned
sheafification/local-injectivity and ordinary sheaf cohomology declarations,
none this statement. Loogle `SheafOfModules, "localization"` returned only
`PresheafOfModules.instIsLocalizationSheafOfModulesSheafificationInverseImageFunctorOppositeAbWToPresheaf`;
I opened its module: this localizes the category at sheafification equivalences,
not a module at a section. LeanFinder for "Restriction of an unbounded derived
sheaf of modules to the over site and colimit of multiplication by a section
on the unit sheaf" returned presentations, sheafification and spectrum Tilde
constructions, none the three new notions. I independently searched project
and upstream Lean and Mathlib by localization, telescope, complete/ideal and
derived restriction. `ModuleCat.localizedModuleFunctor` was opened: it is for
one ring and its modules, not ring sheaves on an arbitrary site. The DAG scan
found scheme-open derived restriction, scalar restriction and coefficient-specific
completeness nodes, but no duplicate of these general-site notions; the existing
localized-ringed-site node concerns only the slice and underived restriction.
The worker's LeanSearch failure is recorded as unavailable, not as a no-match.

Mismatches found: none in the statement, constructions or new-node records.
Changes: appended this independent reading; retained all Lean and node signatures.
No statement correction, target change or disputed statement is needed.
Validation: all four delivered files compiled separately through scompile.py on
its server overlay, nice 19, two threads, 60 seconds per file; no errors or warnings.
All universes and variables are explicitly bound. The initial compile invocation
used repository-relative paths instead of sandbox paths and failed before any
compiler ran; rerunning from the sandbox completed cleanly.

## Second reading by NH

Independent reading on 2026-10-15: I opened the four sandbox modules, all four
node records, the recorded dependency nodes and their declarations, and
algebraization.tex at lemma-hom-from-Af and lemma-ideal-of-elements-complete-wrt
(Tags 0997/0998), including the surrounding localization calculation. The source
assumes a ringed site and an arbitrary unbounded derived object. Its T criterion
is equivalent to the node's internal-Hom criterion by 0997. No statement_change
is present or needed.

Object/hypothesis/conclusion checklist, in node order:

1. Small ringed site: `{C : Type u} [SmallCategory C] (J : GrothendieckTopology C)`.
   Verdict: exact; no points, pullbacks, chosen covering basis or scheme required.
2. Commutative ring sheaf: `(R : Sheaf J CommRingCat.{u})`. Verdict: exact.
   `sheafCompose` only forgets commutativity for the module-category interface.
3. Arbitrary K in D(O): the `DerivedCategory (ringedSiteModules ...)` binder.
   Verdict: exact. The original/slice `HasDerivedCategory.{w}` instances specify
   localization sizes, and do not impose boundedness, coherence or finiteness.
4. S_K(U): `IsRingedSiteCompleteElement J R K U f`. Verdict: exact after unfolding.
   `singleFunctor _ 0` puts the telescope in degree zero; `ringedSiteDerivedRestriction`
   restricts K; `derivedInternalHom (J.over U) (R.over U)` has localization in its
   contravariant input and restricted K in its covariant input. `IsZero` concerns
   the whole derived object, not merely global Hom or a single cohomology group.
5. Whole set is an ideal: `∃ I : ∀ U, Ideal ...` and the first conjunct's iff.
   Verdict: exact; the iff excludes replacing the set by a smaller ideal.
   The existing `Ideal` structure supplies zero, addition and multiplication
   by arbitrary sections, as well as additive inverses.
6. Sheaf of ideals: the second conjunct preserves membership under every arrow,
   and the third descends membership along every covering sieve. Verdict: exact.
   Together these define a subpresheaf of R with local membership; matching
   sections glue uniquely in R, and descent places the glue in the subset.
7. Locally generated ideal consequence: the final conjunct uses a covering sieve
   and, on each arrow, `b : Fin r → R(V)`, actual complete-element membership,
   and `Ideal.span (Set.range b)` membership for the restriction of x. Verdict:
   equivalent consequence. Sections of the generated ideal sheaf locally have
   such finite expressions; refining the cover supplies this premise. Global
   membership in the conclusion is equivalent to local membership by clause 6.
   Varying the tuple on the cover introduces no additional strength beyond
   ideal closure and descent.

Dependency and new-node reading: `ringedSiteModules` is transparently the existing
Mathlib `SheafOfModules`; `DerivedCategory` is unbounded localization.
I read the actual `derivedInternalHom` construction and its signature: it uses
Hom complexes after functorial K-injective replacement on the same slice category.
Mathlib `overFunctor`, `over`, `overMap`, and `overFunctorMap` give precisely the
underived restriction in def-pur-localized-ringed-site, not derived restriction.
`module_overFunctor_preservesZero` is the existing zero-preservation witness.
The existing `localizedModule_restriction_quasiIso` supplies exact restriction
without extra hypotheses, justifying use of a representative.

For def-weil-pbc-ringed-site-section-localization I opened Mathlib `unit`,
`unitHomEquiv` and `sectionsMk`. The inverse equivalence maps a compatible section
s to the linear map a ↦ a • s, so the delivered transition is right multiplication
by the restricted f. Its sequential colimit is the telescope in 0997 and hence
O_U[1/f] for commutative R. The named compatibility theorem states precisely
functoriality of section restriction on the opposite slice, with its complete
Over.w proof plan. It is recorded in lean.declarations and its proof alone is
postponed; all section, map and colimit data are constructed.
For def-weil-pbc-ringed-site-derived-restriction I opened Mathlib `objPreimage`
and `objObjPreimageIso`: essential surjectivity supplies an actual representative
isomorphic to K. Restricting it termwise and applying slice Q therefore defines
K|U, independently up to isomorphism. No object is chosen from a sorry existence
claim. For def-weil-pbc-ringed-site-complete-element the definition renders the
criterion in checklist 4 exactly; its local instance reconciles definitionally
equal slice coefficient presentations. All three new nodes match their modules,
source places, cited dependencies and required provenance/search/blueprint fields;
the item reaches all three. None needs a dependency-module repair.

Edge cases: empty site gives vacuous objectwise clauses; empty covering sieves are
allowed and descent uses R's sheaf condition. Zero rings and arbitrary characteristic
are included. f=0 has zero telescope; f=1 has the unit telescope; K=0 gives the
whole ideal. `Fin 0` has empty range and zero span. No scheme is assumed, so empty
schemes are included through their sites. Universes u and w are bound explicitly;
no independent smaller test universe or equality between separately given universes
is imposed. All declarations use autoImplicit false. The theorem docstring follows
all six node proof steps, including binary-localization surjectivity, the Hom-cone
calculation, sheaf locality and r=0. Both postponed proofs are whole named theorem
proofs; no theorem was proved during this reading.

Independent duplicate searches: LeanFinder query "Sections whose derived Hom from
the module telescope of multiplication by f is zero form a subsheaf of ideals"
returned spectrum Tilde and scheme IdealSheafData declarations, not this theorem.
Loogle `SheafOfModules, "localization"` returned only categorical localization at
sheafification equivalences, not inversion of a section. I searched Mathlib, the
upstream WeilConjectures tree and project Sheaf sources for complete elements,
derived completeness and ideals, telescopes and slice derived restriction. The
upstream Complete/Principal module was opened: it treats constant coefficients
and a nonzerodivisor, not this arbitrary ring-sheaf section criterion. DAG definition
scanning found no duplicate general-site telescope or derived restriction.
`def-weil-pbc-module-localization` is ordinary localization of a module over one
ring; `lem-weil-pbc-localization-free-resolution` is a theorem about a resolution,
not a recorded definition of the sheaf construction. The worker's recorded
LeanSearch service failure remains an unavailable search, not evidence of absence.

Mismatches found: none. Changes: appended this independent second reading; retained
all Lean and node signatures. Validation: all four delivered modules compiled
separately through scompile.py, in dependency order, on the server overlay with
nice 19, two threads and 60 seconds per file, with no errors or unexpected warnings.
