## Worker report

The delivery states `AlgebraicGeometry.ProEtale.CondensedRing.closedSupport_bounded_continuity`
in `Sheaf.Paper.ClosedSupportBoundedContinuity`. Its only theorem proof is `sorry`.
One new definition node records the unchanged existing closed-support construction; no Lean definitions, dependency modules, or statement corrections are added.

The node and the full signatures/docstrings of its recorded prerequisites were read.
The source places read were Stacks proetale.tex,
`lemma-closed-immersion-complement-retrocompact-exact` (09BM), the current blueprint
`det-pe-bounded-continuity-direct-image.proof.md`, and Hemo--Richarz--Scholbach,
Constructible sheaves, equations (3.3)--(3.4) and Lemma 3.4 (PDF page numbered 7).
The node expressly presents the filtered-colimit assertion as an agent extraction from
these inputs, rather than a verbatim quotation of 09BM or Bhatt--Scholze.

Hypotheses and clauses, individually:

- Arbitrary commutative condensed ring: `Λ : Sheaf (coherentTopology Profinite.{u})
  Ab.{u + 1}`, `[MonObj Λ] [IsCommMonObj Λ]`. This is exactly the underlying-object
  encoding of `Profinite.CondensedRing`, without a topological presentation or a
  torsion/adic/finite coefficient restriction.
- Schemes `T,Z,U`: `{T Z U : Scheme.{u}}`. Only `T` has
  `[TopologicalSpace.NoetherianSpace T]`; this is noetherianity of the topology,
  not `IsLocallyNoetherian T` or a condition on its structure sheaf.
- Closed immersion: `(i : Z ⟶ T) [IsClosedImmersion i]`.
- Complementary open immersion: `(j : U ⟶ T) [IsOpenImmersion j]` and
  `_hij : Set.range j = (Set.range i)ᶜ`. The orientation agrees with the node.
  Quasi-compactness of j follows from the noetherian topology and is not an extra binder.
- Pulled-back coefficients: `supportModules Λ S` unfolds to
  `Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)`.
  The ring is the existing `p_S^*Λ`, including its transported ring structure.
- Ordinary uncompleted derived categories: every `DerivedCategory` is the ordinary
  localization of cochain complexes at quasi-isomorphisms. There is no completion,
  constructible subcategory, or restricted target.
- Fixed module universe and small filtered diagrams: each continuity conjunct independently
  quantifies `(I : Type (u + 1)) [SmallCategory I] [IsFiltered I]`. The site retains
  its actual distinct object and morphism universes; they were not forced equal.
  The module size and indexing size agree with the published pro-etale convention.
- Each complex diagram is `I ⥤ CochainComplex (supportModules Λ T) ℤ` for N,
  respectively `supportModules Λ U` for V. Morphisms are genuine strict chain maps.
- Uniform *cohomological* lower bound: `(c : ℤ)` and
  `∀ t : I, (DerivedCategory.Q.obj (N.obj t)).IsGE c`, respectively V.
  `DerivedCategory.isGE_iff` identifies this with vanishing of every H^q for q<c.
  No termwise bound or upper bound is required of the input complexes.
- The first displayed map: the first conjunct asserts
  `IsIso (DerivedCategory.Q.map (colimit.post N M))`, with M the composition of
  `CochainComplex.kInjectiveResolutionFunctor.{u + 1} (supportModules Λ T)` and
  `(closedSupport Λ i j).mapHomologicalComplex (ComplexShape.up ℤ)`.
  `closedSupport` is the existing concrete `i^* ker(id → j_*j^*)`; its right derivation
  is the right adjoint of exact closed direct image. It therefore represents precisely
  the recollement Ri!, not a new or arbitrary functor.
- The second displayed map: the second conjunct has the same expression for V and
  the *full* module-object pushforward `lowerStar Λ j`. Restriction of scalars and
  the canonical coefficient action are part of that recorded functor.
- Termwise sheaf colimits and original comparison cocone: `colimit.post D M` is the
  chain map `colimit (D ⋙ M) ⟶ M.obj (colimit D)` induced by `M.mapCocone
  (colimit.cocone D)`. The colimits are formed in complex categories and hence degreewise
  in the module-sheaf categories. Localizing that chain map gives the displayed derived
  comparison. Its legs are the original cocone legs under functorial resolution and F.
  No unproved preservation of categorical colimits in the triangulated derived category
  is assumed. The standard resolution unit and the right-derived unit identify M(K)
  naturally with RF(Q(K)); the source is precisely the stipulated termwise colimit of
  these functorial representatives. Exact filtered colimits preserve quasi-isomorphisms,
  so a different functorial representative model gives the same comparison.
- First bound assertion: the third conjunct is `∀ K : DerivedCategory (supportModules Λ T),
  K.IsGE c → ((closedSupport Λ i j).rightDerivedFunctor.obj K).IsGE c`.
- Second bound assertion: the fourth conjunct is the corresponding assertion for
  `lowerStar Λ j` and `K : DerivedCategory (supportModules Λ U)`.
- All integer c, no local noetherianity, dimension bound, or constructibility: c is an
  unrestricted integer, and no such additional hypotheses occur anywhere in the signature.

Dependency declarations used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing` (transparent
  abbreviation for the ring-object input encoding).
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, and its commutativity instance.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt` and
  `Scheme.ProEt.topology`; `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `colimit.cocone`, `colimit.post`;
  `Mathlib.CategoryTheory.Filtered.Basic`: `IsFiltered`.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`;
  `Mathlib.Algebra.Homology.DerivedCategory.TStructure`: `DerivedCategory.IsGE`, `isGE_iff`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the recorded general
  arbitrary-quasi-isomorphic K-injective interface, publicly reexported by the support module.
  Here ordinary right derivation is the existing universal `Functor.rightDerivedFunctor`
  in `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`:
  `CochainComplex.kInjectiveResolutionFunctor`, with its natural quasi-isomorphism
  `toKInjectiveResolution` and K-injective object instance. The standard derived unit
  computes RF on these representatives, including all transition and cocone maps.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `CondensedRing.lowerStar`; its total right derivation is the same one named by
  `moduleObjectDerivedPushforward` in `Sheaf.Paper.CondensedModuleDerivedPushpull`.
- `Sheaf.Paper.CondensedOpenClosedRecollement`: `condensed_open_closed_recollement`,
  giving the support/right-adjoint identification and the bounded-below recollement.
- Added definition dependency `def-sfb-condensed-closed-support-functor`, with an
  `existing: true` record on `Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction`:
  `supportModules`, `supportModules_grothendieck`, `supportPullback`,
  `supportPullback_additive`, `supportKernel`, `supportKernelι`, `closedSupport`, and
  `closedSupport_additive`. The primary definition is literally
  `supportKernel Λ j ⋙ supportPullback Λ i`, without theorem-selected data.
  This replaces the theorem dependency returned under H2; the recollement node used
  in the existing proof steps supplies the right-adjoint identification.

Every recorded proof dependency with a usable module (including Mathlib matches for
long exact cohomology and the five lemma) is imported without `public` unless already
publicly reexported. The theorem docstring supplies all eight node proof steps, including
the good-truncation reduction and connecting-map naturality.

Edge cases checked: c is arbitrary, including negative c. Input complexes may have
nonzero acyclic tails below c and unlimited cohomology above c. Filtered categories are
nonempty by their definition; the empty indexing category is not a filtered case.
The zero ring, zero diagrams, empty T, empty Z, empty U, and identity closed/open
immersions are not excluded. For Z=T and U empty, Ri! is the identity up to the
canonical comparison and the open functor is zero. For Z empty and U=T the roles reverse.
No special scheme structure is imposed on the closed subset, and no nilpotent invariance
is silently used. No statement dispute or source correction was necessary.

Searches actually run (2026-10-21):

- `msearch.py ... leanfinder`: "Derived closed support and open direct image of condensed
  module sheaves commute with filtered colimits of uniformly bounded below complexes".
  Eight hits: condensed AB4/AB5/colimits/Grothendieck/solid-module infrastructure; no match.
- `msearch.py ... loogle`: `"rightDerivedFunctor", "colimit"`.
  Two hits: `Functor.HasPointwiseRightDerivedFunctorAt.hasColimit` and `hasColimit'`.
  These concern the Kan-extension construction of a derived functor, not continuity.
- `msearch.py ... leansearch`: "Derived closed support and open direct image preserve
  filtered colimits of complexes with a common cohomological lower bound".
  Eight hits: evaluation/complex colimits, exact colimits, general filtered-colimit
  preservation and limit-colimit interchange; no geometric continuity statement.
- `msearch.py ... grep`: `(support|shriek).*(filtered|colimit)|(filtered|colimit).*(support|shriek)`.
  No Mathlib hits.
- `rg` in the exact project `lean/WeilConjectures` and `lean/Sheaf` for
  `closedSupport_bounded_continuity|closedSupport.*continuity|support.*bounded.*continuity|[Cc]losed[Ss]upport.*[Cc]olimit`:
  the existing support adjunction preserves colimits for i_*, not Ri!; no exact match.
- Earlier `rg` searches for bounded continuity and closed support in both source roots found
  `ProEtaleBoundedContinuityDirectImage`, `CondensedQcqsPushforwardContinuity`, and
  `CondensedClosedCostalkDerivedContinuity`. Their full statements were read: the first
  is ring-sheaf direct-image continuity, the others give comparisons on cohomology using
  a good-truncated cocone and a termwise bound. They do not state this four-clause result
  for cohomologically bounded diagrams and termwise complex-representative colimits.
- `grep -rn 'lem-sfb-closed-support-bounded-continuity' lean/WeilConjectures`: no hits.

## Second reading by ND

This is a direct dispatcher delivery; no other agent was started. The maintainer's
independent review remains the second independent reading. As a self-check, I reopened
the node, the full emitted signature, and the exact recorded support functor:
all three schemes, the commutative ring-object data, topological noetherianity, both
immersion classes and the complement equation occur explicitly. The two independent
filtered diagram quantifiers permit arbitrary diagram categories in the module universe.
The bounds use standard derived `IsGE`, rather than a termwise bound. Each comparison
localizes `colimit.post` on actual resolution complexes, and the two remaining conjuncts
quantify over all derived objects with that same bound. I checked especially the direction
of the complement equation, source of the support colimit (on Z), source of the open
colimit (on T), and preservation of arbitrary negative bounds. The support dependency
was added to use its recorded canonical construction rather than repeat it. No statement
mismatch was found. The initial compiler run requested more typeclass search heartbeats
for these module-complex colimits; the signature was unchanged.

Historical validation before this returned-delivery repair: the module passed `scompile.py` in both sandbox and library
modes with no diagnostics (11.4 s and 10.3 s respectively), under the unchanged 60-second
per-file limit. The typeclass budget adjustment is documented inline.


## New nodes

`def-sfb-condensed-closed-support-functor` owns the existing arbitrary-condensed-ring
construction Γ_Z(M)=i^*ker(M→j_*j^*M), including its actual action on morphisms and
natural kernel inclusion. Its source is the opening formula of the current blueprint
`sk-lem-formal-closed-support-adjunction.md`. The Lean definition already exists in
`Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction`, so this is an `existing: true`
record and adds no module. The general construction permits arbitrary i and j; its
closed/open specialization is the intended support functor. The ambient variable is
`Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}` with `[MonObj Λ]`, so no
commutativity is required for this definition. `supportModules` uses exactly Λ_S modules;
`supportPullback` transports the action along the inverse coefficient isomorphism;
`supportKernel` uses the canonical module-adjunction unit; the map is `kernel.map`;
`supportKernelι` is its natural kernel inclusion; and `closedSupport` composes that
kernel functor with pullback along i. Zero rings, zero modules and empty schemes are
allowed. The definition makes sense even when the maps are not immersions. It asserts
no exceptional adjunction or derived triangle.

The three fresh Mathlib searches were LeanSearch (closed-support inverse image of the
unit kernel), LeanFinder (canonical i-pullback of M→j_*j^*M kernel), and grep
`closedSupport|supportKernel|supportModules`. Their full returned summaries are preserved
in the new node's `mathlib_searches`. None gives this construction: the hits concern
ordinary scheme restriction, discrete condensed modules, and locally finite support.
Project rg finds the exact existing definition above. A DAG declaration scan finds it
only as an auxiliary of theorem node `det-lem-formal-closed-support-adjunction`, while
`blueprint_refs.py search 'sections with support'` finds six related nodes, none owning
this general definition. `def-exc-proetale-sections-with-support` concerns finite discrete
coefficients and a different recorded declaration. This is the definition ownership
repair explicitly requested by the independent reviewer.

## Repair of returned delivery b5d521be4a42

H2 repaired: replaced `det-lem-formal-closed-support-adjunction` in `stmt_deps` by the
new definition node above, recorded the eight requested declarations, and updated
`lean.note`. The theorem was not added to `proof_deps`: no proof step cites it, and
recollement is already a proof dependency. All original item fields other than `lean`
and `stmt_deps` agree with the current live node. The existing support module was read
through the construction and additive instance; its source is unchanged. The delivered
Lean statement, imports and complete eight-step proof docstring are byte-identical.
The fresh self-check confirms that only dependency ownership changed and all four
conjuncts, universes and hypotheses remain as reviewed. No other agent was started.

## Current dispatcher repair, 2026-10-21

The H2 repair retains the original Lean statement and construction byte for byte.
The new existing:true definition node owns the eight unchanged support declarations;
the item cites this definition node rather than the adjunction theorem.

Earlier server compilation attempts timed out in the upstream
`WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity` dependency.
The scratch experiments did not yield a validated upstream repair, and none is
included in this delivery. No shared source, launcher tool or timeout was modified.

A fresh prescribed `deliver2.py --no-push` run against the current live library
compiled the retained item and all eight existing-declaration checks cleanly,
reaching server preflight. Preflight then reported only two missing bracketed
citations in the new definition node: its combined dependency citation was not
recognized. These are now written as two separate bracketed citations. The
mathematical definition and every Lean signature remain unchanged.

The final prescribed dry run passed: commit `f73690aa2a7` compiled and passed
server preflight with no warnings. It checked the item and all eight existing
declarations. The successful log is `scratch/repaired-citations-dry-run.log`.
The final push repeats the prescribed checks. No exploratory module is part
of the packet.
