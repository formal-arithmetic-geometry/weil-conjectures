## Worker report

The theorem `AlgebraicGeometry.neron_lft_of_splitTorus_extension` states the item,
with its entire proof postponed by `sorry`. The module is
`Sheaf.AlgebraicGeometry.SplitTorusExtensionNeronLft`. It imports the existing
`Sheaf.AlgebraicGeometry.NeronLftModel` definition supplied by Q92.
The item's statement and proof plan are unchanged; statement dependencies gain
the already landed Néron-model and split-torus definition nodes.

Hypothesis and clause correspondence:

- `D E : Type u`, `[CommRing D] [IsDedekindDomain D]`, `_hdim : ringKrullDim D = 1`
  give exactly the stipulated Noetherian integrally closed domain of dimension one.
  Mathlib's Dedekind class alone permits fields, so the dimension equation is essential.
  `[Field E] [Algebra D E] [IsFractionRing D E]` specifies the fraction field, and
  `Spec (.of D)` is S. Its generic inclusion is
  `Spec.map (CommRingCat.ofHom (algebraMap D E))` throughout.
- `G H : Grp (Over (Spec (.of E)))` supplies the group operations and diagrams.
  `[IsCommMonObj G.X] [IsCommMonObj H.X]` imposes commutativity.
- `[Smooth G.X.hom] [Smooth H.X.hom]` supplies both smoothness hypotheses.
- The two `[IsClosedImmersion (pullback.diagonal ...)]` binders express precisely
  separatedness as defined in the node.
- The two `[LocallyOfFiniteType ...]` and two `[QuasiCompact ...]` binders express
  finite type, without confusing it with locally finite type.
- `[GeometricallyConnected G.X.hom]` means connected after every field extension:
  Mathlib quantifies over every field-valued point of the base and uses
  `ConnectedSpace` of the base change. ConnectedSpace includes nonemptiness.
- `r : ℕ` allows all nonnegative ranks. `MultiplicativeType.splitTorus E r` is the
  existing finite product of the recorded `StandardGroupSchemes.multiplicative E`,
  including the terminal group in rank zero. The latter is the recorded Laurent
  spectrum with its Hopf group law, not a newly chosen model of G_m.
- `i` and `q` are bundled group homomorphisms. `_hkernel : IsPullback ...` says
  that the square of i, the map to the unit object, q, and the identity section of
  H is cartesian in `Over (Spec (.of E))`. This is exactly the scheme-theoretic
  kernel identification with its specified inclusion.
- `_hlocallySurjective` is `Presheaf.IsLocallySurjective` for `yoneda.map q.hom.hom`
  and `Scheme.fppfTopology.over (Spec (.of E))`. Every section over every test
  scheme therefore lifts on an fppf covering. Together with the kernel square
  this renders the explicitly specified sheaf exactness; it is not a surjectivity
  assertion only on field-valued points.
- `_hcharacters` ranges over every E-scheme morphism from H to the recorded G_m,
  requires `IsMonHom f`, and concludes `f = 1`. Here 1 in the morphism group is
  the trivial homomorphism (the zero homomorphism in additive language).
- `_hmodel` asserts existence of an S-group N, a group-scheme generic-fibre
  isomorphism e to H, and `IsNeronLftModel` for that e. The premise does not
  require a commutative model in advance.
- The conclusion asserts existence of an S-group N, its `IsCommMonObj N.X`, a
  generic-fibre group isomorphism e to the original G, and the same full
  `IsNeronLftModel` predicate. No finite-type or component-group bound is added.
- In the landed predicate, smoothness and closed diagonal are the first two
  conjuncts. Locally finite type follows from smoothness. For every
  `X : Over (Spec (.of D))`, `Smooth X.hom` implies `Function.Bijective` of
  `fun f : X ⟶ N.X ↦ (Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap D E)))).map f ≫ e.hom.hom.hom`.
  These are all scheme morphisms: X need not be a group, affine, connected, or
  quasi-compact. The map is canonical restriction followed by the specified e.
  There is no chosen equivalence or arbitrary map replacing restriction.

Dependency declarations read and used:

- Landed def-sfb-neron-lft-model: `Sheaf.AlgebraicGeometry.NeronLftModel`,
  `AlgebraicGeometry.IsNeronLftModel`, read in full both locally and from
  the current server source during this repair.

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map` (def-pc-scheme and def-weil-affine-spectrum).
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: its recorded convention
  `baseChange_morphism_projections`, explaining `CategoryTheory.Over.pullback`
  and its action on morphisms (def-pc-base-change); actual group scalar extension
  uses `(Over.pullback j).mapGrp`. The landed definition publicly imports this module.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, with
  `QuasiCompact` from its imported morphism module.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `Grp`, `GrpObj`, and the existing
  commutativity and homomorphism structures. The source group-scheme convention
  in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` explicitly identifies
  these with group schemes over a field; the same diagrams work over S.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfTopology`; the slice site is
  `GrothendieckTopology.over` from `Mathlib.CategoryTheory.Sites.Over`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`:
  `StandardGroupSchemes.multiplicative` and `multiplicativeGroup`.
- The mathlib leaf def-weil-connected-scheme has no lean record and needs none:
  its match `ConnectedSpace` is read in `Mathlib.Topology.Connected.Basic`.
  `GeometricallyConnected` in `Mathlib.AlgebraicGeometry.Geometrically.Connected`
  applies precisely that predicate to field base changes.
- Added landed dependency def-sfb-tori-multiplicative-type:
  `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`, `MultiplicativeType.splitTorus`.
- The stated proof dependency lem-sfb-split-torus-character-pushout is imported
  non-publicly as `Sheaf.AlgebraicGeometry.SplitTorusCharacterPushout`;
  its `character_pushout` signature uses exactly the same kernel and local-lifting
  encodings. The remaining six proof dependencies have no recorded Lean modules
  in the read clone; no fictitious import or restatement of their proofs is added.

Edge cases checked before writing:

- Rank zero is included literally in the existing recursive splitTorus definition;
  the kernel is the trivial group and the theorem reduces to transfer along G ≅ H.
- H trivial and G a positive-rank split torus are allowed. The output model may
  have infinitely many components; no QuasiCompact assumption is placed on N.
- The trivial G is allowed. Empty group schemes are excluded by the identity
  section and geometric connectedness, as they must be. The empty smooth test
  scheme is included in the mapping property and has singleton Hom sets.
- Arbitrary characteristic is allowed, without perfection or characteristic-zero
  hypotheses. No henselian, excellent, local, or complete assumption is added to D.
- Fields are excluded as D by the explicit dimension-one condition, following the
  node's own definition of Dedekind domain. D may have any number of closed points.
- Test schemes and field extensions use the same arbitrary universe as the schemes
  in the existing library and its size convention; no independent smaller test
  universe is introduced. The mapping property includes non-finite-type X.

Searches made (all service queries run through msearch.py, in searches.jsonl):

- LeanFinder: "A geometrically connected smooth commutative group which is an
  extension by a split torus has a Neron locally finite type model"; eight hits
  about smooth algebras, approximation, and affine space; no matching theorem.
- Loogle: "IsDedekindDomain, ConnectedSpace"; zero hits for the combined query.
- Mathlib grep: "Neron|Néron|neron|IsDedekindDomain"; Dedekind-domain hits,
  no Néron-model theorem. Exact Néron-only grep under AlgebraicGeometry: zero hits.
- LeanSearch: "Neron locally finite type model smooth separated group scheme
  mapping property"; eight hits concerning finite type, smoothness and properness,
  no model predicate. Loogle `"Neron"`: zero hits.
- `rg -n` for Neron/Néron/neron throughout both project Lean trees: no model
  declaration. Exact searches for `IsNeronLftModel` and
  `neron_lft_of_splitTorus_extension` in Mathlib, both trees and the upstream name
  table: no hits. Searching the item id in WeilConjectures: no hits.
- DAG definition searches found only unrelated Néron desingularization/Néron-Severi
  mentions; `tools/blueprint_refs.py search 'Néron'` returned zero blueprint nodes.
  Searching torus and connectedness found the reused existing declarations above.

Source verification: opened the primary-source BLR PDF linked in the item,
reading 10.1 Definition 1 and Proposition 7, PDF pages 295 and 298–299, and the
mapping property in 1.2 Definition 1, PDF page 18. The printed-page references
are 289, 292–293, and 12. The existing item is the commutative affine-base instance
of that proposition. No statement correction or statement dispute was needed.
The example CompactObject module is currently withdrawn (no declarations), so
module headers follow the live ToriMultiplicativeType/character-pushout modules.

Validation for the repair uses scompile.py on the single delivered theorem module
against the live landed definition. The delivered proof remains exactly `sorry`.

## Repair of returned delivery

The maintainer returned immutable head 4a758fb94fc4 because
`def-sfb-neron-lft-model` had already been created on sheaf-dag by Q92.
I compared the retained delivery files with the current node record and opened
both the locally recorded definition and the current server source using
`scompile.py --source Sheaf.AlgebraicGeometry.NeronLftModel`; they agree.

Removed this delivery's duplicate definition node file and definition module.
The theorem now uses the landed `AlgebraicGeometry.IsNeronLftModel N H e` in
its premise and `AlgebraicGeometry.IsNeronLftModel N G e` in its conclusion.
The landed definition binds D and E implicitly and constructs their canonical
generic map internally; the former delivery passed that map as an explicit
argument to a generalized predicate. The landed predicate omits a separate
locally-finite-type conjunct because its smoothness conjunct implies it.
Its smoothness, separation, specified group isomorphism, all-smooth-test-scheme
quantifier, and actual canonical restriction bijection give exactly the notion
needed by the unchanged item. No dependency repair or new definition is needed.

The item node was refreshed from the current shared read clone, retaining every
field except its lean record and the permitted addition of the two landed
statement dependencies. The final packet contains only the theorem module,
the item's node record and this report; the Q92 definition is imported as-is.
The earlier unsuccessful-search results above describe the original search;
the landed definition discovered on repair is now reused.

## Second reading by Q98

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
