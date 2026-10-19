## Worker report

The node already has an exact implementation in
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`; no Lean module is written.
The recorded primary declaration is
`AlgebraicGeometry.ProEtale.preservesFiniteLimits_upperStar`, with supporting
`AlgebraicGeometry.ProEtale.upperStarLowerStarAdjunction`,
`AlgebraicGeometry.ProEtale.additive_upperStar`, and
`AlgebraicGeometry.ProEtale.preservesHomology_upperStar`.

The node's statement is rendered clause by clause as follows. The arbitrary morphism
`g : Z ⟶ Y` and coefficient category `A` are the section variables of the source
module, with `A : Type u'`, `[Category.{u + 1} A]`, `[Abelian A]`, and
`[IsGrothendieckAbelian.{u + 1} A]`, and `Z Y : Scheme.{u}`. The pullback in the
node is the existing `ProEtale.upperStar A g`, written `(g)^*[A]`. Its finite-limit
clause is exactly the source instance
`PreservesFiniteLimits (g)^*[A]` in
`ProEtale.preservesFiniteLimits_upperStar`; the global instance
`ProEtale.preservesFiniteLimits_op_lan_overPullback_of_isGrothendieckAbelian`
provides the displayed Kan-extension premise for every morphism `g`. The phrase
“being also a left adjoint” is rendered by
`ProEtale.upperStarLowerStarAdjunction A g : (g)^*[A] ⊣ (g)_[A]` (the source
notation is `(g)_*[A]`). The source's `ProEtale.additive_upperStar` and
`ProEtale.preservesHomology_upperStar` then render additivity and exactness; the
latter is the named `PreservesHomology` instance obtained from finite limits and
left-adjoint colimits.

The statement dependencies were read in full. `def-sfb-finite-upper-star` records
`AlgebraicGeometry.ProEtale.upperStar` in the same source module, and
`def-sfb-finite-upper-lower-star-adjunction` records
`AlgebraicGeometry.ProEtale.upperStarLowerStarAdjunction` there. Their source
signatures use the same arbitrary `g`, coefficient hypotheses, site universes, and
upper/lower-star constructions as this node.

I checked the identity morphism, arbitrary non-weakly-etale morphisms (including a
proper morphism), empty schemes, and the zero Grothendieck abelian category. The
source has no weakly-etale, quasi-compactness, separation, finiteness, or
nonemptiness assumption on `g`, `Z`, or `Y`; the global filtered-colimit Kan instance
handles the empty finite diagram and the identity case. Exactness is expressed by
`PreservesHomology`, so kernels and cokernels are included rather than only finite
limits.

Searches made before recording the existing declaration:

- `msearch.py ... leanfinder "pullback upperStar preserves finite limits exact every morphism pro étale sheaves Grothendieck abelian"` returned generic finite-limit/sheaf-pullback candidates and no exact project theorem.
- `msearch.py ... loogle "AlgebraicGeometry.ProEtale.preservesFiniteLimits_upperStar, PreservesFiniteLimits, PreservesHomology"` returned no indexed hit.
- `msearch.py ... grep "preservesFiniteLimits_upperStar|preservesHomology_upperStar" WeilConjectures` returned no hit through the wrapper's older search index.
- Direct `rg` in the read-only source found `preservesFiniteLimits_upperStar` at
  `UpperLowerStar/Defs.lean:256`, `additive_upperStar` at line 267, and
  `preservesHomology_upperStar` at line 273. Reading the complete declarations and
  docstrings confirmed that they are the exact current implementation.
- Direct `rg` over `lean/Sheaf` and the DAG found no separate project declaration of
  this node; the only relevant current implementation is the recorded upstream one.

No statement correction, new node, dependency module, or statement dispute is needed.


## Second reading by Q61

I independently read the item node, its exact blueprint statement and proof, both
statement-dependency nodes, and their recorded source declarations. I also opened
`def-sfb-finite-lower-star`, from which the coefficient assumptions are inherited,
and the site definition. There is no repair note for this item. The source is the
blueprint node `lem-sfb-finite-upper-star-exact` (order 1512), not a Stacks lemma
restricted to weakly etale morphisms. I read Stacks `proetale.tex`, Tag 098M,
`lemma-fibre-products-proetale`, and `sites.tex`, Tag 00X3, `lemma-directed`,
including the preceding equalizer argument. The former assumes only a scheme and
an ambient big site containing it; the latter assumes terminal objects and
preservation of fibre products. Neither imposes a condition on the scheme map g.

The statement checklist and its Lean rendering are:

1. A Grothendieck abelian coefficient category A, inherited from
   `def-sfb-finite-lower-star`: `(A : Type u') [Category.{u + 1} A]
   [Abelian A] [IsGrothendieckAbelian.{u + 1} A]`. This is an arbitrary category,
   with no concrete-category, module-category, ring, field or finiteness
   specialization. Verdict: exact.
2. Arbitrary schemes Z and Y, and every morphism g from Z to Y:
   `{Z Y : Scheme.{u}} (g : Z ⟶ Y)`. In particular the final theorem section has
   no `[WeaklyEtale g]`; that instance is confined to the earlier optional
   shortcut section. Verdict: exact.
3. The specified small pro-etale sites and sheaf categories:
   `Sheaf (Scheme.ProEt.topology Y) A` and the corresponding category for Z.
   Mathlib's `Scheme.ProEt` is `MorphismProperty.Over @WeaklyEtale ⊤ Y`, with all
   morphisms over Y; `Scheme.ProEt.topology` is the topology from the fpqc,
   weakly-etale precoverage. These are the sites used by both dependency
   declarations. The site's object and morphism universes remain distinct;
   the independent coefficient-object universe u' is not restricted. Verdict:
   exact, with the inherited enlarged coefficient Hom universe u+1.
4. The pullback of `def-sfb-finite-upper-star`:
   `ProEtale.upperStar A g`, source lines 213-228, is precisely
   `Functor.sheafPullbackConstruction.sheafPullback` along
   `MorphismProperty.Over.pullback @WeaklyEtale ⊤ g`. I opened the construction:
   it includes the underlying presheaf, applies the left Kan extension along
   opposite base change, and sheafifies. No second inverse-image construction
   is used. Verdict: exact.
5. Preservation of all finite limits:
   `ProEtale.preservesFiniteLimits_upperStar` has conclusion
   `PreservesFiniteLimits (ProEtale.upperStar A g)`. Its displayed Kan-extension
   premise is not an extra mathematical hypothesis: the globally registered
   `ProEtale.preservesFiniteLimits_op_lan_overPullback_of_isGrothendieckAbelian`
   in `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`
   supplies it for every g under exactly the same coefficient hypotheses. The
   recorded module publicly imports that module. I read the full signature and
   proof, and compiled both `inferInstance` and the explicitly typed application
   `ProEtale.preservesFiniteLimits_upperStar A g` without adding that premise.
   Verdict: exact as an existing declaration package.
6. Being a left adjoint: the second dependency is precisely
   `ProEtale.upperStarLowerStarAdjunction A g : upperStar A g ⊣ lowerStar A g`.
   It is the composite sheafification/Kan-extension adjunction for the same
   functors and gives the stated natural Hom equivalences. Verdict: exact.
7. Exactness: `ProEtale.additive_upperStar` supplies additivity, and
   `ProEtale.preservesHomology_upperStar` supplies preservation of kernels and
   cokernels. I opened Mathlib's `Functor.PreservesHomology` definition; it
   asserts both universal-property preservation statements. Finite colimits
   also synthesize from the adjunction. As a direct consumer check, for an
   arbitrary `S : ShortComplex (Sheaf (Scheme.ProEt.topology Y) A)` and
   `hS : S.ShortExact`, `hS.map_of_exact (ProEtale.upperStar A g)` typechecks as
   `(S.map (ProEtale.upperStar A g)).ShortExact`. Thus the last clause really
   covers every short exact sequence, not just the finite-limit clause.
   Verdict: exact.

Edge cases: finite limits include the empty diagram and therefore the terminal
object. The filtered Kan index has an object furnished by the terminal site
object even when the finite diagram is empty. No nonempty-scheme assumption is
present: empty Z and empty Y (when a map exists) are included; an empty scheme's
site is not assumed to be the empty category. Identity maps and arbitrary maps
that are not weakly etale are included. The zero coefficient category and zero
sheaves are included. There is no integer degree or characteristic parameter,
and no characteristic restriction. Universe u and the independent object
universe u' are bound; all imported section parameters were checked in compiler
output. No equality of site object and morphism universes was introduced.

Independent searches used different words from the first worker:

- `msearch.py ... leansearch "Inverse image on the small proetale site with
  Grothendieck abelian coefficients is exact and preserves finite limits for
  arbitrary scheme morphisms"`: eight generic sheaf-pullback, sheafification,
  and exact-functor candidates; no separate geometric statement. The generic
  sheaf-pullback result is exactly the construction used by the existing source.
- `msearch.py ... leanfinder "inverse image proetale sheaves abelian coefficients
  preserves kernels cokernels short exact sequences"`: eight generic condensed
  and sheaf-category results, no exact additional match.
- `msearch.py ... loogle "Functor.PreservesHomology"`: no indexed declaration
  (unknown identifier in the remote index); checked its actual Mathlib source
  directly instead.
- Direct `rg` with `upperStar.*exact|exact.*upperStar` and
  `upperStar.*PreservesHomology|PreservesHomology.*upperStar`, and finite-limit
  variants, across Mathlib, upstream WeilConjectures and project lean/Sheaf
  confirmed the recorded existing implementation. The project
  `ProEtaleToposFunctorialityInverseImage` has only an AddCommGrp specialization
  as one conjunct and cites this item; it is not a replacement. The generic
  `SixFunctors/UpperLowerStar/Defs.lean` uses the same conditional construction,
  rather than an independent arbitrary-coefficient pro-etale exactness theorem.
  The corresponding etale and Weil-sheaf results concern different categories.

I checked the node's six proof steps against the source implementation:
finite limits of the site and base-change preservation give cofiltered comma
indices; their opposites are nonempty filtered categories; pointwise Kan
extension is their colimit; AB5 gives finite-limit preservation; inclusion and
sheafification preserve finite limits; finally the adjunction gives finite
colimits and preservation of kernels and cokernels. The existing source's
filtered-colimit theorem supplies precisely the non-weakly-etale case. No new
proof obligation or construction is hidden by this attachment.

Mismatch/repair: there was no mathematical mismatch. The displayed primary
signature is conditional, so a bare attachment to it would need justification;
the worker had already identified the correct globally available premise. I
made that support explicit by its full name in `lean.note`, together with
the independently compiled consumer checks. The primary signature remains
verbatim equal to source, and all other node fields are unchanged. No statement
correction, new node, dependency module, hollow definition or new theorem was
needed. Existing upstream declarations are reused, so no duplicate statement
module or new source/blueprint docstring is introduced.

Validation: the revised scratch `check/Check.lean` compiled through the required
`scompile.py Q61 lem-sfb-finite-upper-star-exact` wrapper with no errors and no
warnings. It checks all seven items above with fully bound universes and only
the inherited hypotheses. `#print axioms` for both
`preservesFiniteLimits_upperStar` and `preservesHomology_upperStar` reports only
`propext`, `Classical.choice`, and `Quot.sound`. The probe is scratch evidence,
not a delivered module; there are no new Lean files to land.

The first dry run exposed a wrapper-generated long-line warning when the long
fully qualified support-instance name was added to `lean.declarations`: its
auto-generated `#check` line exceeded 100 characters. The support is therefore
named in `lean.note` instead; it remains publicly imported and was explicitly
checked in the clean scratch probe under the open namespace. The four existing
recorded declarations and the primary signature are unchanged. No tool or live
source was edited.

Further source-location mismatch found and repaired: server preflight correctly
rejected the old module as the declaration's source. `scompile.py --source
WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs` shows that it is now
only a compatibility re-export of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`.
I fetched and read the entire latter module through the same authoritative
source wrapper. It contains the identical coefficient and scheme binders, the
identical upper/lower-star definitions, the verbatim recorded primary signature,
and all four supporting declarations discussed above. I changed only
`lean.module` to this canonical defining module and documented the relocation
in `lean.note`; the branch remains slopmaster2. The worker report's old path
is superseded by this finding. The statement dependencies' compatibility imports
still expose exactly the same constants and need no repair. The scratch probe
now imports the canonical defining module directly.
