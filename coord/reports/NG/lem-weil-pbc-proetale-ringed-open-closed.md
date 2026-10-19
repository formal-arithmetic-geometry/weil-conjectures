## Worker report

The delivery states `AlgebraicGeometry.Scheme.proEtale_ringed_open_closed` in
`Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`. The only postponed proof is this
one theorem. Its docstring gives the five steps of the DAG proof. There are no
postponed proofs in definitions and no constructed data selected from an existence
statement with `sorry`.

Hypotheses and clauses, in node order:

- Schemes X and Z are `Scheme.{u}`; the closed immersion is `i : Z ⟶ X` with
  `[IsClosedImmersion i]`. The open scheme and its structural map are `U.left` and
  `U.hom` for `U : X.ProEt`, with `[IsOpenImmersion U.hom]` and
  `[QuasiCompact U.hom]`. `hU : Set.range U.hom = (Set.range i)ᶜ` is exactly
  complementarity. Membership in ProEt imposes no additional geometric hypothesis
  on an open immersion: every open immersion is weakly etale.
- The arbitrary sheaf of commutative rings A is
  `Sheaf (ProEt.topology X) CommRingCat.{u + 1}`. Its underlying ring sheaf is
  `proEtaleModuleCoefficients A`, simply Mathlib's `sheafCompose` forgetting
  commutativity. Modules are exactly `SheafOfModules.{u + 1}` (equivalently the
  dependency abbreviation `ringedSiteModules`), with sectionwise module actions.
  No constancy, finiteness, torsion, or flatness assumption on A is imposed.
- On Z, the coefficient sheaf is the actual
  `(proEtaleSheafInverseImage i CommRingCat).obj A`; the module inverse image is
  `proEtaleModuleInverseImage i A`. `proEtaleRingedDirectImage i A` uses
  `SheafOfModules.pushforward` for `proEtaleBaseChange i`, with the ring map
  obtained by forgetting commutativity in the actual ring adjunction unit.
  Thus its sections are H(V times_X Z), its restriction and morphism components
  are those of H, and scalars act through A to i_*i^{-1}A.
- On the open part, the localized ringed site is used as a presentation, rather
  than defining another site or another module action. The theorem explicitly
  supplies an equivalence q from modules over the actual j^{-1}A on
  `U.left.ProEt` to modules over `(proEtaleModuleCoefficients A).over U` on
  `Over U`. Its compatibility is the natural isomorphism
  `proEtaleModuleInverseImage U.hom A ⋙ q.functor ≅ overFunctor ... U`.
  This records the arbitrary-coefficient localization implicit in the node.
  In this presentation, `j^{-1}` is precisely `SheafOfModules.overFunctor`.
- `proEtaleRingedExtensionByZero U A` is the literal composite
  `extensionByZeroPresheaf ... U ⋙ PresheafOfModules.sheafification (𝟙 ...)`.
  The recorded presheaf has direct-sum sections indexed by `V ⟶ U`, with the
  recorded sectionwise ring action and restrictions. Open monomorphy makes the
  index set either empty (zero section module) or a singleton (the given section
  module). Sheafification acts on this module presheaf and its linear morphisms.
  The functor is written in the localized-site presentation; transport back to
  U is q.functor followed by this functor. It has no arbitrary map or chosen data.
- The adjunction `aj` is `j_! ⊣ overFunctor ... U`, exactly the requested
  extension/restriction adjunction. The adjunction `ai` uses the prescribed
  inverse-image functor and the constructed direct image on Z. The theorem
  supplies these adjunctions and asserts its sequence for their actual maps.
- `∀ H, IsIso (ai.counit.app H)` states `i^{-1}i_* ≅ id` with its counit;
  `∀ G, IsIso (aj.unit.app G)` states `id ≅ j^{-1}j_!` with its unit.
  A natural transformation with invertible components is a natural isomorphism.
  The two `IsZero` clauses state `j^{-1}i_*=0` and `i^{-1}j_!=0`, respectively.
  The first uses the equivalent slice presentation of j^{-1} just specified.
- The paired `PreservesFiniteLimits` and `PreservesFiniteColimits` assertions
  give exactness of j_! and i_* in these abelian module categories.
- For every ambient M, the sequence uses exactly `aj.counit.app M` and
  `ai.unit.app M`. `Mono` of the first, `Epi` of the second, and
  `(ComposableArrows.mk₂ ... ...).Exact` are equivalent to exactness of
  `0 → j_!j^{-1}M → M → i_*i^{-1}M → 0`. In particular Exact asserts the
  composite is zero and the image equals the kernel, not just abstract existence
  of a short exact sequence with these objects.
- The last implication adds only `CompactSpace X` and `QuasiSeparatedSpace X`
  for the final clause. For every `I : Type (u + 1)` with `[SmallCategory I]`
  and `[IsFiltered I]`, it states `PreservesColimitsOfShape I` for i_*.
  This is invertibility of the canonical colimit comparison for all such
  diagrams. Filteredness includes nonemptiness. There is no requirement that
  arbitrary non-qc objects have sectionwise filtered colimits.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleBaseChange`,
  `proEtaleSheafInverseImage`, `proEtaleSheafAdjunction`,
  `proEtaleModuleInverseImage`. The actual module inverse-image construction
  transports to AsSmall, uses module pullback through the ring adjunction unit,
  and transports back. It retains site object universe u+1 and Hom universe u.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the abbreviation for Mathlib `SheafOfModules` (used by unfolding the abbreviation).
- `Mathlib.Algebra.Homology.ExactSequence`: `ComposableArrows.Exact`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact` (the
  quasi-compactness part recorded by def-weil-finite-type-morphism).
- `Mathlib.CategoryTheory.Limits.HasLimits`: chosen colimits and their
  canonical comparisons; `Mathlib.CategoryTheory.Filtered.Basic`: `IsFiltered`.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification` with identity ring map.
- `Sheaf.CategoryTheory.ExtensionByZeroPresheaf`:
  `SheafOfModules.extensionByZeroPresheaf`, its section sum and its actual maps.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`:
  `ProEt.weaklyEtale_localization`, including concrete site equivalence and
  monomorphy. Its constant-ring clause alone would not identify arbitrary A;
  the new main theorem therefore includes q and its module inverse-image
  compatibility for arbitrary A.
- The scheme-conventions node is a metatheoretic record: qcqs is expressed by
  `CompactSpace X` and `QuasiSeparatedSpace X`. The size-convention node is
  likewise rendered by the explicit universes, not a fabricated declaration.

All proof-dependency modules with recorded declarations are imported. The remaining
proof dependencies have no recorded modules. No import cycle is introduced: a DAG
reachability check from each recorded proof dependency found no path back to this
item. In particular the generic localized-module exactness theorem is used in the
proof plan after size transport, not by imposing equality of the original site
object and Hom universes. The 51-module framework was inspected through
`coord/pefw-upstream-framework.md` and its actual
`ModuleObject/UpperLowerStar/Defs.lean`: its coefficient ring is pulled back from
a condensed ring at the point, so it does not state this arbitrary-A theorem.

Edge cases checked: U empty and Z=X give zero extension and the identity closed
term; Z empty and U=X give the identity open term and zero closed term. The empty
scheme and zero ring sheaf give zero module categories without extra assumptions.
Non-reduced closed subschemes are permitted. A non-qcqs X is allowed for every
clause except the explicitly conditional filtered-colimit clause. Coefficients
may have infinite section rings. Explicit universe u and section universe u+1
retain the original small pro-etale site and include all diagrams small in the
chosen sheaf universe. Empty filtered diagrams are not erroneously required,
since filtered means nonempty. The presheaf's empty/singleton summands are treated
by the existing construction, not by a new convention for empty schemes.

Searches made (2026-10-15):

- LeanSearch via msearch, query `Closed immersion complementary open immersion
  pro etale ringed topos short exact sequence extension by zero`: unavailable,
  Internal Server Error. No claim about absence is inferred from this failure.
- LeanFinder via msearch, query `For pro etale sheaves of modules a closed
  immersion and complementary quasi compact open give exact extension by zero
  direct image and a short exact sequence`: eight unrelated results, including
  MayerVietorisSquare.shortComplex_shortExact; no match for this statement.
- Loogle via msearch, query `SheafOfModules.pushforward,
  Functor.PreservesFiniteColimits`: unknown second identifier, no result.
  Follow-up `SheafOfModules.pushforward`: 12 results, including the exact generic
  pushforward construction used here, but no pro-etale open-closed theorem.
- Mathlib grep via msearch, query
  `closedImmersion.*exact|extensionByZero.*exact|lowerShriek.*exact`: zero hits.
- rg in upstream WeilConjectures and lean/Sheaf for
  `ringed_open_closed|ringedOpenClosed|proEtaleModuleDirectImage|proEtale.*Adjunction|proEtaleExtensionByZero`:
  the existing inverse-image module, finite-constant-coefficient extension by
  zero and its adjunction, but no arbitrary-ring-sheaf open-closed theorem.
  The finite-constant module cannot be reused as the arbitrary-A construction.
- grep for the exact node id in the upstream WeilConjectures tree: no match.
- DAG inspection found `def-weil-proetale-module-direct-image`, but it is
  expressly constant-coefficient direct image, already constructed as
  `proEtaleConstantModuleDirectImage` in the inverse-image dependency. It is not
  an unstated arbitrary-ring-sheaf prerequisite for this node. The helper here
  instead uses the inverse-image ring and its actual unit for arbitrary A.

No node correction, new independent definition node, or dependency-record repair
was needed. The three helper declarations only expose existing constructions
specialized to the very functors in this node, as permitted by the isolation brief;
they are listed in lean.declarations. No STATEMENT-DISPUTED fault found.

Validation: server-only `scompile.py NG lem-weil-pbc-proetale-ringed-open-closed`
for the delivered module; no local Lean or lake build. Final dry-run result is
recorded below after execution. The independent second reading is left to the
next worker, as required by the brief.

Dry run: `deliver2.py NG lem-weil-pbc-proetale-ringed-open-closed --no-push`
printed `OK (dry run)`: server compilation and preflight passed, with only the
independent second reading deferred to the second reader. Nothing was pushed.


## Second reading by NG

Independent second reader, 2026-10-15. I read the sandbox node and module in full,
the recorded statement-dependency nodes and their declarations, the framework
manifest and ModuleObject/UpperLowerStar/Defs.lean, and the cited Stacks sources.
The statement is faithful; no mathematical or signature repair was needed.

Object/hypothesis/conclusion checklist (node order):

1. Scheme X and closed subscheme Z: `{X Z : Scheme.{u}}`, `(i : Z ⟶ X)` and
   `[IsClosedImmersion i]`. Verdict: exact, including nonreduced Z. I checked
   Mathlib's class extending SurjectiveOnStalks with a closed embedding.
2. Complementary quasi-compact open j: `(U : X.ProEt)`,
   `[IsOpenImmersion U.hom]`, `[QuasiCompact U.hom]`, and
   `hU : Set.range U.hom = (Set.range i)ᶜ`. Verdict: exact. Bundling U as a
   weakly etale object excludes no open immersion; no finite-type assumption is
   substituted for quasi-compactness. The Mathlib open-immersion and
   quasi-compact-morphism signatures have the required meaning.
3. Arbitrary commutative ring sheaf A: `Sheaf (ProEt.topology X)
   CommRingCat.{u + 1}`. Its module category is `SheafOfModules` over
   `proEtaleModuleCoefficients A`. Verdict: exact. That abbreviation forgets
   commutativity via sheafCompose, preserving all section rings and actions;
   `ringedSiteModules` is precisely the same Mathlib category.
4. Closed coefficient ring and inverse image: the actual
   `(proEtaleSheafInverseImage i CommRingCat).obj A` and
   `proEtaleModuleInverseImage i A`. Verdict: exact. I read the dependency's
   AsSmall transports, unit ring map, and module pullback construction. The
   transport enlarges Hom sizes only; it does not change the site or coefficients.
5. Closed direct image: `proEtaleRingedDirectImage i A` is Mathlib pushforward
   along `proEtaleBaseChange i`, with scalar map the actual ring-adjunction unit
   whiskered by the forgetful functor. Verdict: exact, not an arbitrary map.
   Mathlib pushforward uses the original section restrictions and linear maps.
6. Open coefficient ring and site: the domain of q uses actual inverse-image
   coefficients on U.left.ProEt. Its target uses `A.over U` on the slice, and
   the displayed natural isomorphism intertwines actual module inverse image
   with `SheafOfModules.overFunctor`. Verdict: equivalent presentation of the
   specified localization. I read weaklyEtale_localization: its site equivalence
   and monomorphism clauses apply here; its constant-coefficient module clause
   alone would not suffice for A. The added q compatibility supplies exactly
   this arbitrary-A transport, rather than assuming A constant.
7. Extension by zero: `proEtaleRingedExtensionByZero U A` is the recorded
   `extensionByZeroPresheaf` followed by `PresheafOfModules.sheafification`
   along the identity ring map. Verdict: exact. I read the dependency's
   direct-sum section construction, restriction maps, and functorial map on
   summands. Open monomorphy makes each factorization index empty or a
   singleton, recovering the node's two cases. Mathlib sheafification gives
   the associated abelian sheaf with the induced module action.
8. Adjunction: aj has exactly extension by zero as left functor and slice
   restriction as right functor; ai has the prescribed closed functors.
   Verdict: correct adjunctions, with actual unit/counit components used below.
   The quantifiers assert their existence for each i, U, hU, A, with no new
   hypothesis on those objects. Transport through q gives j_! adjoint to the
   original j inverse image as well.
9. Closed counit identity: `∀ H, IsIso (ai.counit.app H)`. Open unit identity:
   `∀ G, IsIso (aj.unit.app G)`. Verdict: precisely the two natural
   isomorphisms in the node; invertibility is componentwise.
10. Vanishing composites: the two `IsZero` clauses give restriction of i_*H
    to U and inverse image of j_!G on Z. Verdict: both specified zero
    composites, for every module, with no condition on its support.
11. Exactness: finite-limit and finite-colimit preservation for each of j_!
    and i_*. Verdict: exactness in these abelian module categories. The extra
    finite-(co)limit formulation is equivalent to exactness here.
12. Short exact sequence for every M: `Mono (aj.counit.app M)`,
    `Epi (ai.unit.app M)` and `ComposableArrows.mk₂ ... ... |>.Exact`.
    Verdict: the arrows and middle object are exactly those requested.
    I checked ComposableArrows.Exact extends IsComplex and requires exactness
    of consecutive triples; mk₂ imposes the sole middle exactness condition.
    Thus the endpoint Mono/Epi clauses complete the stated five-term sequence.
13. Filtered colimits: `CompactSpace X → QuasiSeparatedSpace X →
    ∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I],
    PreservesColimitsOfShape I (proEtaleRingedDirectImage i A)`.
    Verdict: exactly the conditional small-filtered-colimit assertion, using
    the canonical comparison. X is not required qcqs for the earlier clauses.

Source checks: proetale.tex lemma-closed-immersion (09AA) assumes only a
closed immersion. Lemma-closed-immersion-complement-retrocompact-exact (09BM)
requires the retrocompact complement, supplied by QuasiCompact U.hom.
Lemma-open-immersion (09BN), lemma-jshriek-zero (09AG), and
lemma-ses-associated-to-open (09AH) give the identities, disjointness vanishing,
and unit/counit sequence; 09AH explicitly assumes quasi-compact j.
Modules on Sites lemmas extension-by-zero and extension-by-zero-exact
(03DI/03DJ) apply to arbitrary ringed sites, with exactly the direct-sum
presheaf used here. Sites lemma-directed-colimits-sections (0738), clause (4),
is the qcqs covering-section argument used for the last deduction. No global
Noetherian, characteristic, finite-coefficient, or reducedness condition occurs
in these sources or in the Lean. All five DAG proof steps occur in the theorem
docstring; its proof is solely sorry.

Edge cases: U empty permits Z=X and gives zero j_!; Z empty permits U=X
and gives zero i_*; X empty is allowed. Zero ring sheaves give zero module
categories. There is no index, degree, n, or characteristic restriction to
check elsewhere in this statement. Filtered index categories are nonempty
by IsFiltered, so an empty diagram is not accidentally asserted filtered.
The site retains object universe u+1 and Hom universe u; rings, modules and
small diagram categories live in u+1 as required by the dependency and size
convention. There is no imposed equality of site universes. No variable or
universe is unbound.

Independent searches, using different wording from the first reader:

- LeanFinder through msearch: `Recollement for modules on a proetale topos
  with arbitrary ring coefficients closed immersion open complement`.
  Eight results, including Scheme.Etale.forget, Scheme.Modules.pseudofunctor,
  CondensedMod.IsSolid and Scheme.Modules restrictFunctor adjoints. These
  concern other sites/categories or structural functors, not this statement.
- Loogle through msearch: `SheafOfModules.pushforward`. Twelve results;
  read Mathlib pushforward and overFunctor directly. These are the generic
  constructions used in the file, not a duplicate open-closed theorem.
- LeanSearch through msearch: `Closed embedding direct image exact sheaves
  modules proetale recollement`. Service returned Internal Server Error;
  no absence conclusion rests on this failed service.
- rg for `recollement|openClosed|open_closed|closed.*[Ee]xact|[Ee]xact.*closed`
  in upstream and side pro-etale six-functor sources, project algebraic
  geometry, and Mathlib algebraic-geometric sites. Relevant existing
  open-closed sequences are etale/constant-coefficient results; the newly
  imported ModuleObject framework requires coefficients pulled back from a
  condensed ring at the point. I opened its exact upper/lower-star signatures:
  these do not cover an arbitrary ring sheaf A. No matching complete theorem
  or arbitrary-A helper construction was found.

No new definition node, dependency module, statement_change, or citer audit is
needed. No H3--H6 mismatch was found. All three helpers have real data and
source/blueprint docstrings, and are recorded in lean.declarations. The main
signature already agrees verbatim with lean.statement. Changes in this reading:
this independent checklist and search/validation evidence only; the correct Lean
and node were retained.
