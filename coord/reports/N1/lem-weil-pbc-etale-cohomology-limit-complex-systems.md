## Worker report

Item: lem-weil-pbc-etale-cohomology-limit-complex-systems. Module:
`Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit`, declaration
`AlgebraicGeometry.Etale.nonempty_isColimit_etale_complex_cohomology`.
It states continuity as the colimit universal property of the canonical cohomology
cocone, with its sole proof `sorry`. It defines no new notion and proves nothing.

Source read: https://stacks.math.columbia.edu/tag/0EZM, Lemma 59.52.1,
statement and proof. The local literature/stacks-project/etale-cohomology.tex is
absent on this machine, so the authoritative online tag was opened instead.
The theorem's docstring reproduces the node's three proof steps and the nodes
that supply termwise continuity, spectral-sequence comparison and canonical maps.

Hypothesis and clause correspondence:

- Cofiltered inverse system: `{I : Type u} [SmallCategory I] [IsCofiltered I]`
  and `D : I ⥤ Scheme.{u}`. A morphism `f : j ⟶ i` means the transition
  from stage j to stage i; sheaf/cohomology diagrams are indexed by `Iᵒᵖ`.
  The index universe is the scheme universe as required by brief-stage2.
- Limit scheme and projections: `c : Cone D`, `hc : IsLimit c`, limit `c.pt`
  and projections `c.π.app i`. This allows any chosen limit, not only a
  particular Mathlib limit object.
- Quasi-compact and quasi-separated stages: the instances
  `∀ i, CompactSpace (D.obj i)` and `∀ i, QuasiSeparatedSpace (D.obj i)`.
  These are the scheme-space conditions, not vacuous conditions on identity morphisms.
- Affine transition maps: `∀ (i j) (f : i ⟶ j), IsAffineHom (D.map f)`.
- Complex at every stage: dependent family `F`, taking values in
  `CochainComplex (Sheaf (D.obj i).smallEtaleTopology AddCommGrpCat.{u+1}) ℤ`.
  These are actual complexes of abelian etale sheaves, not arbitrary objects of
  the derived category or complexes of their global sections.
- Maps of complexes: `φ f` has domain the termwise `upperStar` image of `F i`
  and target `F j`. The map is a chain map, so it includes differential compatibility.
- Transition identity: `hidentity` uses `D.map_id`, the corresponding `eqToIso`
  and the recorded `upperStarId`. This is the explicit clarification described below.
- Cocycle law: `hcomposition` says that `φ (g ≫ f)` is the complex map of
  `upperStarComp`, then the pullback of `φ f`, then `φ g`.
  `D.map_comp` supplies precisely the morphism equality required by that comparison.
- One common integer lower bound: `a : ℤ`, `hbelow : ∀ i n, n < a →
  IsZero ((F i).X n)`. There is no upper bound and no bound depending on i.
  A categorical zero object is used rather than equality with a chosen zero.
- The termwise pulled-back system on X: `G` is a diagram of complexes on `c.pt`;
  `eG i` identifies its object with `(c.π.app i)⁻¹ F i`. `hG` prescribes its
  transition map, using `upperStarComp` with the projection equality `(c.w f).symm`.
  The object isomorphisms are arbitrary presentations of the specified objects,
  not an assumption that those objects happen to be isomorphic to unrelated ones.
- The termwise colimit complex: `L : Cocone G` and `hL : IsColimit L`.
  Mathlib's homological-complex colimits are degreewise colimits. Thus `L.pt`
  represents exactly the complex called F^bullet in the node.
- Every integer cohomology degree: `p : ℤ`, not `p : ℕ`.
- Derived-global-sections cohomology: every group in `eH`, `eB` and `P`
  uses the recorded `Etale.cohomology AddCommGrpCat _ p`, evaluated on
  `DerivedCategory.Q.obj` of the actual complex.
- Canonical pullback on complex cohomology: the parameter `P` is fully fixed by
  `hP`. The right side applies `DerivedCategory.homologyFunctor` to (1) derived
  global sections of the derived inverse-image/direct-image adjunction unit,
  (2) the canonical derived global-sections/pushforward comparison, and
  (3) the exact-pullback comparison `mapDerivedCategoryFactors` with the
  termwise pullback complex. The underived global-sections comparison in (2)
  is the composite of `ΓNatIsoSheafSections`, the recorded terminal-section
  pushforward isomorphism, and the inverse target `ΓNatIsoSheafSections`.
  `rightDerivedFunctorCompIso'` derives this comparison. Thus P is neither
  unconstrained nor an arbitrary isomorphism. It is a bound parameter naming
  an explicit expression, not a new definition of cohomology or inverse image.
- The diagram of stage cohomology: `H` and `eH i`, with `hH` forcing its maps
  to be P for the transition followed by cohomology of `φ f`.
- Canonical map to target cohomology: `B : Cocone H`, `eB` identifies its
  vertex with H^p(X,L.pt), and `hB` forces each leg to be projection pullback
  followed by cohomology of the actual colimit coprojection through `eG i`.
- Isomorphism of colimit with target: `Nonempty (IsColimit B)` asserts that
  this prescribed cocone is colimiting. Equivalently, the map from any colimit
  cocone of H to B.pt is an isomorphism; after eB this is exactly the displayed
  canonical isomorphism, not existence of an unspecified isomorphism.

The auxiliary diagram/cocone presentations are ordinary categorical ways of
writing the diagrams and canonical maps in the node. Their equations specify
all objects and maps. They add no exactness, injectivity, constructibility,
torsion, finite coefficients, or continuity assumptions. Any actual coherent
system admits these presentations by inverse-image coherence and the identity
and composition laws for canonical derived pullback. These laws are precisely
the node's recorded proof route. Choosing isomorphic presentations does not
change the universal property. No new definition node or dependency module is
needed: all objects used above are existing Mathlib/source category constructions.

Dependency declarations inspected and used:

- def-weil-pbc-scheme-conventions is a convention record with no module or
  declaration; its note points to Mathlib's `Scheme`, quasi-compact,
  quasi-separated and affine-morphism notions. The theorem uses `Scheme`,
  `CompactSpace`, `QuasiSeparatedSpace` and `IsAffineHom`, also the exact
  hypotheses used in Mathlib.AlgebraicGeometry.AffineTransitionLimit.
- def-weil-pbc-etale-sheaves: the record explicitly identifies its abelian
  category with `CategoryTheory.Sheaf T.smallEtaleTopology AddCommGrpCat.{u+1}`.
  Its Sheaf.AlgebraicGeometry.EtaleSheaves file was read. None of its additional
  set-valued locally-constant/constructible predicates occurs in this node,
  so importing that unused module would be inappropriate; its existing
  `CategoryTheory.Sheaf` declaration is used from the derived functor imports.
- def-weil-pbc-inverse-image:
  WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs,
  `AlgebraicGeometry.Etale.upperStar` and `upperStarLowerStarAdjunction`.
  Used directly as the termwise inverse image and through the recorded
  `mapDerivedUpperStarLowerStarAdjunction` of Derived.UpperLowerStar.
- def-weil-pbc-etale-cohomology:
  WeilConjectures.SixFunctors.Etale.Derived.LowerShriek,
  `AlgebraicGeometry.Etale.cohomology` and `rightDerivedGlobalSections`.
  Their full signatures and docstrings were read; cohomology is RΓ followed
  by derived-category homology, not termwise Γ.
- lem-weil-pbc-inverse-image-composition:
  WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs,
  `AlgebraicGeometry.Etale.upperStarComp` (its full signature and adjoint-uniqueness
  construction read), and UpperLowerStar.Coherence, `upperStarId`.
  Both are lifted to complexes using Mathlib's `NatIso.mapHomologicalComplex`.
  The source `lowerStarComp` signature/docstring was also inspected.

Edge cases checked before writing: cofiltered means nonempty (the empty index
category is not a cofiltered system), but empty schemes and zero sheaves/complexes
remain allowed; a constant singleton system gives the identity colimit; a complex
concentrated in degree a reduces to sheaf continuity shifted by a; arbitrary
negative a and negative p are permitted; no torsion or characteristic restriction
is present. The bounded-below condition is on terms, not merely on cohomology.
The non-unital singleton edge case exposed the ambiguity corrected below.

Searches, all recorded by msearch.py in searches.jsonl:

- LeanSearch, `etale hypercohomology uniformly bounded below complexes continuity
  inverse limits schemes`: unavailable, HTTP Internal Server Error, no verdict.
- LeanFinder, `etale cohomology filtered colimit of bounded below complexes over
  inverse limits of schemes`: eight hits including localCohomology.ofDiagram,
  Condensed colimit facts, and AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone;
  none states complex etale cohomology continuity.
- Loogle, `AlgebraicGeometry.Etale.cohomology`: no hits, identifier unknown to
  Mathlib's service (this is a source-repository declaration).
- msearch grep, `cohomology.*colimit|colimit.*cohomology`, AlgebraicGeometry:
  no Mathlib match.
- rg of project Sheaf and source WeilConjectures for etale complexes,
  hypercohomology, cohomology pullback and continuity: no matching theorem.
  The source cohomologyMap concerns the Ext model of sheaf cohomology;
  it does not state the complex-continuity theorem.
- rg for the item id in source WeilConjectures: no occurrence.
- rg for `nonempty_isColimit_etale_complex_cohomology` in Mathlib,
  WeilConjectures, project Sheaf and dag/lean_names_upstream.json: no occurrence.

Server compile: clean, exit code 0, 8.5 seconds, no warnings. All binders and
universes are explicit. No local notation/instance or private definition appears.

## Statement corrected

The old statement is retained verbatim in the node's
`statement_change.old_statement` (the entire original paragraph). The change is
only to make the transition identity law explicit: self-transitions are the
canonical comparison along the identity scheme morphism. The source is Stacks
0EZM's system of schemes and sheaf complexes, which uses ordinary unital diagrams.
The corrected node's other hypotheses and its conclusion are unchanged.

Why necessary: the written composition law alone permits, for a singleton index,
`φ_ii = 0` on a nonzero degree-zero constant abelian sheaf. It is idempotent,
so satisfies the displayed composition equation, but cannot be the identity map
of an ordinary functor diagram. Stating the identity law explicitly removes this
typing ambiguity, rather than adding a geometric restriction to the source theorem.
The item is a derived auxiliary node, not the blueprint unit's own statement.
No stmt_deps, proof or proof_deps changed.

Every actual dependency citer was found by searching all DAG nodes and checking
membership in stmt_deps/proof_deps, rather than counting incidental text matches:

- sbc-lem-higher-direct-image-limit: holds. Its degree-zero sheaf system is
  unital; pulling it back preserves the identity comparison.
- lem-weil-pbc-derived-etale-cohomology-limit: holds. Its transitions are
  inverse-image composition isomorphisms and are unital by identity coherence.

Neither citer was edited. No unresolved STATEMENT-DISPUTED flag remains.

## Second reading by N1

Independent reading of the corrected node and
`Sheaf/AlgebraicGeometry/EtaleComplexCohomologyLimit.lean`:

- The cofiltered index is rendered by `{I : Type u} [SmallCategory I]
  [IsCofiltered I]`, and the inverse system by `D : I ⥤ Scheme.{u}`.
- The chosen limit and projections are rendered by `c : Cone D`, `hc : IsLimit c`,
  and `c.π.app i`; compactness, quasi-separatedness, and affine transitions are
  exactly the three displayed instance hypotheses.
- The stage complexes are `F i : CochainComplex (Sheaf
  (D.obj i).smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ`; `φ` has precisely the
  inverse-image complex source and stage target required by the node.
- The corrected unital clause is rendered by `hidentity`, using `D.map_id`,
  `eqToIso`, and `upperStarId`; the cocycle clause is rendered by `hcomposition`
  with `upperStarComp`, `D.map_comp`, and the pulled-back transition map.
- The common lower bound is exactly `a : ℤ` and
  `hbelow : ∀ i n, n < a → IsZero ((F i).X n)`, with no extra upper, finiteness,
  characteristic, or constructibility hypothesis.
- The limit-site complex presentation is `G : Iᵒᵖ ⥤ CochainComplex ...`, with
  `eG` identifying each object with the projected inverse image and `hG` fixing
  each transition. The colimit complex is `L : Cocone G` with `hL : IsColimit L`.
- The integer cohomology degree is `p : ℤ`. The canonical pullback map is the
  explicitly constrained parameter `P`, whose equation `hP` expands the derived
  adjunction unit, global-sections comparison, and factorization map; it is not
  an arbitrary map or an additional definition of cohomology.
- The cohomology diagram is `H : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1}` with `eH` and `hH`.
  The target cocone is `B : Cocone H`; `eB` identifies its vertex with the
  derived cohomology of `L.pt`, and `hB` identifies every leg with the canonical
  projection/pushforward map. The conclusion `Nonempty (IsColimit B)` is exactly
  the node's universal-property conclusion.

Edge cases remain covered: `IsCofiltered` supplies the required nonempty indexing
condition; empty schemes, zero sheaves and complexes, arbitrary negative `a` and
`p`, and complexes concentrated in degree `a` are all admitted. The universe of
the index, schemes, sheaves, and coefficient category is shared as required.
I searched Mathlib, `WeilConjectures`, and `lean/Sheaf` for the declaration and
for complex étale-cohomology continuity; no existing declaration matched. The
only mismatch found was the missing identity law in the worker's original node;
the node, Lean signature, and report now consistently include `hidentity`. No
dependency module or definition node was needed. The required compile command
completed successfully with no warnings beyond the permitted `sorry`.
