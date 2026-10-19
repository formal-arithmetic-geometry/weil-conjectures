## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicOpenUnit` states
`AlgebraicGeometry.Scheme.sfIntrinsicOpenUnit_isIso`. Its only postponed proof is
that theorem, with `sorry` and the complete node proof in its docstring.
The mathematical statement is unchanged. Its current dependency's intrinsic
constant-ring module objects and extension functor are used literally.

Clause-by-clause reading:

- “For an open immersion j”: `{U X : Scheme.{u}} (j : U ⟶ X)` and
  `[IsOpenImmersion j]`. There are no finiteness or separation assumptions on schemes.
- “on pro-etale module sheaves”: `(A : Type u) [CommRing A] [Finite A]` is precisely
  the finite constant-coefficient convention of `def-weil-extension-by-zero`;
  `M : proEtaleRingModules U (proEtaleConstantRing U A)` is its recorded source category.
  No constructibility, boundedness, nonzero-coefficient, or stalk-conservativity
  condition is imposed. The site is the existing small pro-etale site, with its
  object/morphism universes unchanged; module values have universe `u+1`.
- “the adjunction unit M → j^*j_!M”: the actual arrow is
  `(sfIntrinsicExtensionByZeroAdjunction j A).unit.app M`. Its adjunction's left
  functor is definitionally the recorded `sfIntrinsicExtensionByZero j A`.
  Its right functor is sectionwise open restriction transported through the same
  canonical coefficient-realization equivalences. This defines the named unit;
  no arbitrary morphism or existence-only choice of an adjunction is substituted.
- “is an isomorphism”: `IsIso` of that exact unit component, without replacing
  the conclusion by a mere abstract isomorphism of its endpoints.

The original proof is retained: on an object over U all covering objects remain
there, so the defining presheaf restricts to M. Sheafification preserves that
restriction. The adjunction identifies the unit with the identity on sections.
The canonical coefficient equivalences transport this invertibility. The unit
adjunction's implementation has real data, obtained by composition of existing
adjunctions, and no new postponed theorem is required for its definition.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence` and
  `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero`
  (`def-weil-extension-by-zero`). The current published source was also checked
  with `scompile.py --source Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage`
  (`def-weil-pbc-proetale-operations`) publicly retains
  `Sheaf.AlgebraicGeometry.ProEtaleOperations` and its
  `AlgebraicGeometry.Scheme.proEtaleRingModules`; constant rings are the published
  `AlgebraicGeometry.Scheme.proEtaleConstantRing`. Its recorded operations and
  canonical identified-coefficient interface were read; the item is underived.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionByZeroAdjunction`:
  `AlgebraicGeometry.Scheme.proEtaleExtensionByZero_adjunction` was read in full.
  It is retained publicly by the repair module, but its slice-site endpoints
  cannot directly type the current intrinsic extension-by-zero unit.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`:
  `AlgebraicGeometry.ProEtale.openImmersionRestriction`,
  `AlgebraicGeometry.ProEtale.openImmersionLowerShriek`, and
  `AlgebraicGeometry.ProEtale.openImmersionLowerShriekAdjunction`.
  The restriction is actual precomposition with the localization functor.
  The coefficient category is the existing
  `ModuleCat.{u+1} (ULift.{u+1,u} A)`.
- Mathlib `CategoryTheory.Equivalence.toAdjunction` and
  `CategoryTheory.Adjunction.comp`: the intrinsic adjunction is the composition
  of the inverse realization adjunction on U, the existing localization
  adjunction, and the forward realization adjunction on X.

The already recorded `lem-weil-extension-by-zero-adjunction` is added to
`stmt_deps`, because its repaired canonical adjunction now occurs in the unit's
signature. It remains a proof dependency too. No other node fields change.

Edge cases checked before writing: U empty (there is a unique zero module sheaf),
j the identity, M the zero module, A the zero ring, X empty, and a non-clopen open
immersion all satisfy the same sectionwise unit calculation. No nonemptiness,
nontrivial-ring or clopen hypothesis has been added. The small-site object
universe `u+1` and morphism universe `u` are not equated. The finite coefficient
universe `Type u` is inherited verbatim from the currently recorded extension
functor rather than independently restricted.

Searches performed:

- `msearch.py leansearch`, query “extension by zero sheaves modules restriction
  unit isomorphism”: service returned Internal Server Error, recorded unavailable.
- `msearch.py leanfinder`, query “The unit of extension by zero along an open
  immersion followed by restriction is an isomorphism for sheaves of modules”:
  eight hits, including scheme Zariski restriction adjunctions; none states
  the intrinsic pro-etale open extension unit.
- `msearch.py loogle`, query `CategoryTheory.Adjunction, CategoryTheory.IsIso`:
  twelve hits, including generic fully faithful adjunction facts; none is this
  specified pro-etale module construction.
- `msearch.py grep`, query `isIso.*unit|unit.*[Ii]so`, subdirectory
  `CategoryTheory/Sites`: twenty-five reported hits on generic sheaf equivalences,
  Kan extensions and sheafification, without the specified module unit.
- `rg` on upstream `WeilConjectures` for the item id: no blueprint-id hit.
  Search for `isIso_openImmersionLowerShriekAdjunction_unit` finds the existing
  fixed-category pro-etale theorem (and its etale counterpart). Its full file,
  docstring and signature were read. It concerns fixed-A-valued sheaves and the
  upstream localization adjunction, whereas the currently recorded extension
  dependency is an intrinsic ring-module functor. It gives the expected
  mathematical calculation but is not literally a declaration about this unit.
- `rg` on project `lean/Sheaf` and the upstream declaration list for
  `sfIntrinsicOpenRestriction`, `sfIntrinsicExtensionByZeroAdjunction` and
  `sfIntrinsicOpenUnit_isIso`: no existing declaration. The published
  coefficient-comparison, extension and exactness modules were inspected.

Sources checked: the node's complete stored statement and proof, the recorded
Lean dependencies and framework note, and
[Stacks 03DI](https://stacks.math.columbia.edu/tag/03DI) and
[Stacks 09AE](https://stacks.math.columbia.edu/tag/09AE).
The recorded local blueprint markdown is absent in this checkout; no statement
correction is needed, and the source's extension construction is explicit in the
node and these Stacks references. No `STATEMENT-DISPUTED` finding.

Validation: both delivered modules passed `scompile.py NG
lem-exc-proetale-open-unit` separately in dependency order, with no diagnostics.
The required final check is `deliver2.py NG lem-exc-proetale-open-unit --no-push`;
the second reader performs delivery.

## Dependency modules

`lem-weil-extension-by-zero-adjunction` is repaired under section 1(B) by
`Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction`. Its recorded
localized-site `Nonempty` adjunction acts on `proEtaleExtensionByZero`, whose
source is a slice-site module category. The current extension-by-zero node instead
records `sfIntrinsicExtensionByZero` on intrinsic constant-ring modules on U.
Thus the old record does not expose the adjunction needed to name this unit.
The repair retains the old module by public import, defines canonical intrinsic
restriction by the already published coefficient equivalences and actual
sectionwise restriction, and constructs `sfIntrinsicExtensionByZeroAdjunction`
by composing three existing adjunctions. Its type states exactly that the
current extension functor is left adjoint to restriction. There is no new
choice of coefficients, arbitrary map, or postponed proof. Only this dependency's
`lean` field is changed, with the reason in `lean.note`; no statement or
mathematical notion is changed and no new node is introduced.

## Second reading by NG

I independently read the item node, both delivered modules, both dependency node
records, and the published sources of the extension functor, intrinsic coefficient
realization, ordinary operations, and upstream localization adjunction. The node
has no `statement_change`, and this reading requires no mathematical correction.
The module and node signatures are retained unchanged.

The objects, hypotheses, and conclusion, item by item:

1. Schemes U and X: `{U X : Scheme.{u}}`. These are arbitrary schemes in the
   existing small-site convention, not affine or Noetherian schemes. Verdict: exact.
2. An open immersion j from U to X: `(j : U ⟶ X) [IsOpenImmersion j]`.
   No quasi-compact, separated, clopen, or nonempty assumption occurs. Verdict: exact.
3. The coefficient ring implicit in “module sheaves”: `(A : Type u) [CommRing A]
   [Finite A]`. I read the full statement of `def-weil-extension-by-zero`: it
   explicitly introduces a finite commutative ring and the constant ring sheaves
   A_U and A_X. Finiteness is inherited from that definition, rather than added
   to make this lemma true. `proEtaleConstantRing U A` is the published constant
   CommRingCat sheaf of `ULift A`, not an arbitrary coefficient ring sheaf.
   Verdict: exact in the coefficient convention of the dependency.
4. A module sheaf M on U: `(M : proEtaleRingModules U (proEtaleConstantRing U A))`.
   I opened `proEtaleRingModules`: it is `ringedSiteModules` of the constant
   commutative ring sheaf after forgetting commutativity. These are all module
   sheaves, with no constructibility, finite-presentation, or derived-category
   restriction. Verdict: exact.
5. The specified extension j_!: `sfIntrinsicExtensionByZero j A` is literally
   the declaration recorded for `def-weil-extension-by-zero`. Its data is the
   inverse realization on U, the upstream localization lower shriek, and the
   forward realization on X. No private substitute is used. Verdict: exact.
6. Restriction j^*: `sfIntrinsicOpenRestriction j A` applies the inverse
   realization on X, `ProEtale.openImmersionRestriction`, then realization on U.
   I opened the middle functor: it precomposes with the actual localization
   functor, so its sections at V → U are the original sections at V → X.
   The realization is the published associated-module-sheaf construction along
   constant scalars; its inverse equivalence is determined by that functor.
   Thus this transports ordinary restriction, with the same scalar action.
   Verdict: exact.
7. The adjunction unit M → j^*j_!M:
   `(sfIntrinsicExtensionByZeroAdjunction j A).unit.app M`. The repaired
   adjunction's left functor is the recorded extension functor and its right
   functor is the restriction just checked. Its data is a composition of
   `(sfIntrinsicModuleEquivalence U A).symm.toAdjunction`, the upstream
   `openImmersionLowerShriekAdjunction`, and the forward equivalence adjunction
   on X. I checked `Adjunction.comp` and `Equivalence.toAdjunction`; their unit
   is the transported canonical unit, including the equivalence unit factors.
   This is an actual named map, not an unspecified isomorphism or an arbitrary
   choice of adjunction. Verdict: exact.
8. The only conclusion: `IsIso` of that unit component, for every M following
   j and A in the binders. No converse, existence replacement, or extra conjunct
   is asserted. Verdict: exact.

Source reading: the local literature checkout has no Stacks .tex files or the
recorded blueprint markdown. I fetched `sites-modules.tex` and `proetale.tex`
from the Stacks project's own GitHub source into this item's scratchpad and read
the relevant sections, including their surrounding assumptions.
`sites-modules.tex`, `section-localize` and `lemma-extension-by-zero` (03DI),
assume only a ringed site and an object of it. They give restriction by
evaluation, and extension by zero by sheafifying the direct sum indexed by
arrows to that object. For an open immersion there is at most one such arrow,
giving exactly the dependency node's presheaf. `proetale.tex`,
`section-extension-by-zero` and `definition-extension-zero` (09AE), apply this
to weakly etale scheme morphisms and module sheaves over a constant ring.
Open immersions qualify; no finiteness assumption on the schemes is present.
The finite coefficient convention is the explicit specialization in our DAG.
I also read `lemma-sheafification-presheaf-modules` (03CY), which supplies the
unique linear factorization and Hom correspondence used by the adjunction.
The item's proof docstring includes the full slice-cover argument, restriction
of the presheaf, preservation by sheafification, identification of the unit with
the identity, and transport through coefficient equivalences.

Dependency repair review (H13): the old declaration
`Scheme.proEtaleExtensionByZero_adjunction` concerns modules on the slice site
and only asserts `Nonempty` of an adjunction. Its left functor is not the
currently recorded intrinsic extension functor, so it cannot name this unit.
The delivered repair publicly retains that interface and supplies precisely the
intrinsic adjunction needed by the dependency node. Its two new definitions
have real data; no theorem is proved and no new `sorry` is introduced there.
The `lean.declarations` list contains both new definitions. Its `lean.note`
explains the old interface mismatch. The item adds the already recorded
adjunction proof dependency to `stmt_deps` because the named adjunction occurs
in its signature. This is the only non-`lean` field change. There are no new
definition nodes to review.

Edge cases: U empty, X empty (hence U empty), the identity immersion, M zero,
and A the zero ring are all allowed. On the empty site the sheaf condition
still gives the zero module sheaf up to unique isomorphism; no `Nonempty` or
`Nontrivial` hypothesis occurs. Arbitrary characteristic and non-clopen opens
are allowed. There is no index set, integer degree, or n parameter here, so
empty-index and n = 0 exclusions do not arise. Site objects remain in universe
u+1 and morphisms in u; module values are in u+1, as in the recorded dependency.
No equality between site universes is imposed. The scheme and finite-ring
binders use the existing dependency interface, with arbitrary universe u.

Independent searches, using queries different from the worker's:

- `msearch.py leanfinder`: “Restriction of extension by zero to an open
  subscheme gives the original module sheaf via the adjunction unit” returned
  eight hits about Zariski module restriction and related section formulas;
  none has this intrinsic pro-etale unit as its statement.
- `msearch.py loogle`: `CategoryTheory.Adjunction.unit, CategoryTheory.IsIso`
  returned twelve generic equivalence and fully faithful adjunction results.
  I read `Adjunction.unit_isIso_of_L_fully_faithful`; it assumes the fully
  faithful left adjoint and does not state this construction-specific theorem.
- `msearch.py grep`: `fullyFaithful.*[Ss]heaf|unit_isIso_of_L_fully_faithful`
  returned generic sheaf and adjunction declarations, not this intrinsic unit.
- `msearch.py leansearch`: “Open immersion module sheaves restriction extension
  by zero adjunction unit invertible” returned Internal Server Error. This is
  recorded as unavailable, not as a negative mathematical search result.
- Direct `rg` searches of Mathlib's sites directory, all project `lean/Sheaf`,
  and the upstream `WeilConjectures` tree used both the new declaration names
  and semantic variants involving intrinsic units and fully faithful functors.
  The existing `ProEtale.isIso_openImmersionLowerShriekAdjunction_unit` was
  found and its complete source read. Its binders are a fixed Grothendieck
  abelian coefficient category and an open immersion; its conclusion is
  invertibility of the fixed-category localization unit. It does not mention
  `sfIntrinsicExtensionByZero`, `proEtaleRingModules`, or the canonical
  coefficient realization factors. It is a useful proof ingredient but not an
  exact attachment for the presently recorded intrinsic dependency. No exact
  intrinsic unit theorem or intrinsic adjunction was found elsewhere.

Mismatches found and changes made: none in the Lean or mathematical node
statements. I retained the correct code and dependency repair and appended this
independent reading. Both files have `autoImplicit false`, bound universe u,
source/blueprint docstrings, and no lines over 100 characters. The only new
postponed theorem is `sfIntrinsicOpenUnit_isIso`, matching the item's node and
carrying its proof plan. Validation and delivery checks are recorded below.

Second-reader validation: `scompile.py NG lem-exc-proetale-open-unit` with both
delivered module paths passed in dependency order, including each file's sandbox
and library-form checks, with exit 0 and no errors or warnings. A separate
textual check confirmed that each node's `lean.statement` is verbatim its file's
signature. The required `deliver2.py --no-push` preflight and final delivery are
performed after this report is complete.
