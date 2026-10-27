## Worker report

The module `Sheaf.AlgebraicGeometry.SpacePerfectSourceHomContinuity` states
`AlgebraicGeometry.AlgebraicSpace.perfect_source_hom_continuity`, Stacks 09RI(1)
in Situation 09RH (`literature/stacks-project/spaces-perfect.tex`, lines 5958–6007).
The source and the DAG statement agree. No statement correction, new definition node,
or dependency repair is needed. The mathematical statement and proof are unchanged.
Only the Lean record and additions of already-landed statement dependencies are delivered.

Hypothesis and clause correspondence:

- Universe convention: explicit `universe u w`; `Scheme.{u}` and `I : Type u`, with
  `HasDerivedCategory.{w}` for each stage and the limit, keep the site/module size
  independent of the localization morphism size. No global instance for every
  algebraic space is assumed. `ULift.{u}` puts the Hom sets in `Type (max u w)` so
  the small tail colimit exists at that size. Its up/down equivalence changes no
  mathematical set or map.
- Scheme S and algebraic spaces over S: `{S : Scheme.{u}}` and
  `D : Iᵒᵖ ⥤ AlgebraicSpace S`, using the recorded fppf-sheaf algebraic spaces.
- Small nonempty directed set: `{I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`. A preorder is retained; antisymmetry is not imposed.
- The inverse system and its transition maps are the actual functor D and
  `D.map (homOfLE h).op`. All identity and composition equations come from D.
- Quasi-compact stages: `hqc : ∀ j, CompactSpace (Point (D.obj (op j)).obj.obj)`.
  This is equivalent to the node's quasi-compact surjective etale scheme atlas
  criterion by `points_compactSpace_iff` in AlgebraicSpaceEtaleOpenImage (read its
  signature and proof docstring). It does not assert qc relative to S.
- Quasi-separated stages: `hqs : ∀ j, IsAbsolutelyQuasiSeparated (D.obj (op j))`.
  Its recorded affine-pair test is equivalent to a quasi-compact absolute diagonal;
  no quasi-separatedness or separatedness of S is assumed.
- Affine transitions: `haff : ∀ j k h, MapIsAffine (D.map (homOfLE h).op)`.
  This is exactly the existing affine scheme-test pullback representation criterion.
- The limit X and its projections are `c : Cone D` and `hc : IsLimit c` in the
  category of algebraic spaces. The actual `c.π.app` maps are used, with explicit
  `@id` type annotations only to expose their source to instance synthesis.
- The chosen index is `(i : I)`; `Set.Ici i` is the directed tail j ≥ i.
- The objects P_i and K_i are `(P K : (D.obj (op i)).DerivedModules)`.
  These are the recorded unbounded derived categories on the equivalent small
  affine etale ringed models of the original small etale module categories.
- Perfection is `hP : SheafOfModules.IsPerfectOnRingedSiteOfUniverses
  (D.obj (op i)).smallStructureSheaf P` with explicit universes u,u,u,w.
  Its recorded local bounded finite-free-retract complex definition was read.
  Bounds and ranks may vary with the covering object; no fixed Tor interval is added.
- Quasi-coherent cohomology is `hK : (D.obj (op i)).derivedQCohProperty K`, namely
  every integer cohomology sheaf, transported by the fixed module equivalence,
  satisfies Mathlib `SheafOfModules.IsQuasicoherent`. There is no bound, perfection,
  finite presentation, or finite Tor dimension hypothesis on K.
- P_j and K_j are the objects of `spaceDerivedPullback (D.map ...).obj P/K`;
  P and K at infinity use `spaceDerivedPullback (c.π.app (op i))`.
  The pullback is the recorded universal total left derived tensor pullback,
  computed on flat-term K-flat resolutions. The existing derived-module calculus
  also supplies the canonical K-injective direct image mentioned in the convention;
  no direct-image map is an additional parameter of this statement.
- The transition of a Hom is `spaceLimitHomTransition`: the canonical comparison
  from direct pullback to iterated pullback on P, then the actual functor's map,
  then the inverse comparison on K. The equality of space maps is `D.map_comp`.
- `spaceLimitHomDiagram` has precisely these lifted Hom sets and transitions.
  `spaceLimitHomToLimit` uses the same formula with the cone equation `c.w`.
  `spaceLimitHomCocone` retains all these maps; `spaceLimitHomComparison` is its
  colimit desc. The conclusion `Function.Bijective (spaceLimitHomComparison ...)`
  is exactly the required bijectivity, including its specified canonical map.

The definitions have real data. Three supporting theorem obligations state the
identity/composition laws of this canonical tail diagram and compatibility with
its canonical cocone, with source and natural-language proof docstrings. They are
part of the Hom-system construction in this owning node and are listed in
`lean.declarations`; their proofs, like the main theorem's, are `sorry`.
The main theorem docstring gives all nine proof steps from the DAG, including
unbounded affine models, finite lifting of chain maps and homotopies, natural
Mayer–Vietoris boundaries, the diagram chase, and qcqs induction.

Recorded dependency declarations used (namespace AlgebraicGeometry.AlgebraicSpace
unless qualified):

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicGeometry.AlgebraicSpace`,
  `Modules`, `structureSheaf`, `IsRepresentableWith`, the small etale sites.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations: `moduleTensorPullback`,
  `moduleDirectImage`, `moduleTensorAdjunction`, normalized by compatible chart sections.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: `DerivedCategory`, `HasDerivedCategory`.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule:
  `QCoh` and its original `SheafOfModules.IsQuasicoherent` predicate.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules: `DerivedModules`,
  `derivedQCohProperty`, with the fixed small-module equivalence.
- Sheaf.AlgebraicGeometry.SpaceDerivedPullback: `spaceDerivedPullback`,
  `spaceDerivedPullbackComp`; the actual universal derived counits fix the comparison.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated:
  `IsAbsolutelyQuasiSeparated`.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite: `MapIsAffine`.
- Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology: the recorded `Point` topology.
- Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses:
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses`.

The last six definition nodes, already landed with usable Lean interfaces, are
added to stmt_deps, as permitted by brief-stage2 section 5. This avoids private
copies and makes all extra interfaces explicit. All available recorded proof
modules are imported privately. Unstated proof nodes (etale detection of perfection,
affine-limit stages, affine locality, derived-Hom Mayer–Vietoris, and limit sections)
have no import yet and will be added by maintenance when stated. They do not prevent
stating this theorem, whose statement uses none of them.

Edge cases read against the definitions before writing:
empty algebraic spaces (the zero complex has an empty local cover and all Hom sets
are singletons), P = 0 or K = 0, a singleton index, distinct equivalent indices in a
preorder, an arbitrary chosen i without an initial object, every cohomological shift,
unbounded K, nonflat affine transitions, non-separated S, and independent u and w.
Nothing in the signature excludes these cases. The initial tail object uses the
actual identity pullback and its normalized composition comparison, not a strict
identity assumption on the chosen derived functors.

Searches, 2026-10-24 (msearch group NW, this item):

- LeanFinder: "Hom from a perfect complex commutes with affine inverse limits of
  algebraic spaces": 8 hits, all scheme morphism/section limit results such as
  `Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType`, not derived Hom.
- LeanSearch: "Perfect source derived Hom continuity for affine inverse limits of
  algebraic spaces": 8 hits, scheme compactness, affine limits and unrelated
  continuous algebra morphisms, no matching derived statement.
- Loogle: `DerivedCategory, colimit` returned unknown identifier colimit;
  repeated with quoted `"DerivedCategory", "colimit"`: OK, 0 hits.
- Mathlib grep through msearch: `Perfect.*(colimit|limit)|perfect.*(colimit|limit)`
  in AlgebraicGeometry: OK, 0 hits.
- rg in lean/WeilConjectures and lean/Sheaf for `spaceLimitHom`, the proposed
  declaration name and this blueprint id: no existing matching declaration.
- rg for `perfect.*(colimit|limit)|Perfect.*(colimit|limit)` found the scheme
  `recorded_perfect_hom_continuity`, `affine_perfect_hom_colimit`, and
  `perfect_hom_stage_colimit`. Read their signatures: the first requires a scheme
  over a filtered colimit of rings and both objects perfect; the second also requires
  both complexes bounded finite-projective; the third constructs a scheme Hom
  system but does not assert continuity. None is this algebraic-space result for
  an arbitrary unbounded quasi-coherent target.
- Definition/interface searches in Lean and the DAG found the already-landed six
  definition nodes above; their modules and full relevant declarations/docstrings
  were read and reused, so no new notion was introduced.

Validation: scompile.py compiled the sandbox module and its library path cleanly,
with no errors or warnings, under the prescribed per-file 60-second limit.

## Second reading by NW

An independent second reading by the maintainer review replaces the delivered section,
which was the author's own second pass. It was read against the node, Stacks
spaces-perfect.tex Situation 09RH (situation-descent) and Lemma 09RI(1)
(lemma-descend-homomorphisms), and the live records and modules of every statement
dependency.

Node list → Lean → verdict:
- Size convention, scheme S: `universe u w`, `{S : Scheme.{u}}`, `I : Type u`; the
  Hom size w is kept separate from u. OK.
- Algebraic spaces over S and the inverse system with transitions q_ji:
  `D : Iᵒᵖ ⥤ AlgebraicSpace S`, `D.map (homOfLE h).op : X_k ⟶ X_j`. OK.
- Small nonempty directed I: `[Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]`.
  This is no stronger than the node. OK.
- X_j quasi-compact: `CompactSpace (Point (D.obj (op j)).obj.obj)`. This is equivalent
  to the node's qc étale scheme atlas by `points_compactSpace_iff`
  (AlgebraicSpaceEtaleOpenImage). It is the same form as in the sibling
  `SpacePerfectUniformTor` and `SpaceQcqsDistinguishedSquareInduction`. OK.
- X_j quasi-separated: `IsAbsolutelyQuasiSeparated` (def-sfb-space-absolute-quasi-separated,
  affine-pair test; cited). OK.
- Affine transitions: `MapIsAffine` (def-sfb-space-affine-quasifinite-properties: affine
  pullback of every affine scheme test; cited), for all j ≤ k. OK.
- X = lim X_i with q_i: `c : Cone D`, `hc : IsLimit c` in `AlgebraicSpace S`. OK.
- P_i perfect: `SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u,u,u,w}
  smallStructureSheaf P`. This is the landed local strictly-perfect definition
  (Stacks 08G5), used in the same way by the landed space modules. OK.
- K_i ∈ D_QCoh, with no bound and no Tor condition: `derivedQCohProperty K`
  (def-sfb-space-derived-module-calculus). Every cohomology sheaf is quasi-coherent. OK.
- P_j, K_j, P, K: `spaceDerivedPullback` (def-sfb-space-derived-pullback, the universal
  total left derived tensor pullback) along `D.map` and along `c.π.app (op i)`. OK.
- The transitions use the canonical composition isomorphisms: `spaceLimitDerivedComparison` =
  `eqToIso` ≫ `spaceDerivedPullbackComp`. The latter is fixed by `leftDerivedUnique`
  with the derived counits. Directions checked: f = q_ji, g = q_kj, and h comes from
  `D.map_comp`. The cone map uses g = c.π_j and h = `c.w`. Hom on P → map → inverse on K. OK.
- Conclusion: the colimit over the tail `Set.Ici i` of the lifted Hom sets maps by
  `colimit.desc` of the pullback cocone to Hom(P,K). The theorem states
  `Function.Bijective` of that map. The map is canonical, not a chosen one.
  `ULift.{u}` only raises the size. OK.
- Supporting identity, composition and cocone laws are theorem obligations
  (`sorry`) in the owning node, with proof docstrings. They are true coherences
  of the normalized composition comparison. The functor/cocone data are real. OK.

Edge cases: i is not initial (only the tail Ici i is used); the tail contains i;
the preorder may have equivalent indices; the empty space is covered; K is
unbounded; S is arbitrary.

Searches: rg over lean/Sheaf and lean/WeilConjectures for `HomContinuity`, 09RI, and
`spaceDerivedPullback` together with colimit. Only scheme versions exist
(PerfectOverlapHomContinuity, PerfectHomContinuityUnion,
OpenExtensionRHomContinuity, with no algebraic spaces). There is no duplicate.

Records: all six added stmt_deps are landed definition nodes whose modules are
imported. `lean.statement` is verbatim in the file, and `lean.declarations` lists all ten
declarations. The docstrings carry the source place and `(blueprint: ...)`. The main
docstring gives the nine proof steps.

Changes: none to the Lean or the node. Only this section was rewritten.
