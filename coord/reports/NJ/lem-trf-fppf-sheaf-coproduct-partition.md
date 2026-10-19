## Worker report

The module `Sheaf.AlgebraicGeometry.FppfSheafCoproductPartition` states
`AlgebraicGeometry.Scheme.fppfSheaf_coproduct_partition`, with its entire proof `sorry`.
It also supplies the concrete encoding of its partition data and canonical open-piece
maps. These helpers belong to the notion stated by this item, rather than introducing
an independent mathematical notion. There are no new DAG nodes, dependency repairs,
or statement corrections. Only the item's `lean` field changes.

Sources read: `spaces.tex`, lemma-coproduct-sheaves-open-and-closed (0F15) and
lemma-representable-sheaf-coproduct-sheaves (02WO). The first gives representability
of a summand pullback by a clopen subscheme; the second identifies the resulting
scheme coproduct decomposition. The node's nine proof steps extend that binary
argument to a small set of summands using sheafification (00WI) and its local
sections (00WK). The theorem docstring carries all nine steps, including the
omitted cartesian-square verification and the empty-index argument.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Scheme S | `{S : Scheme.{u}}` |
| Big fppf site over S | `fppfTopology.over S`, on the full category `Over S` |
| Size convention and small I | Explicit universes `u v`; `I : Type (max u v)` and values in `Type (max u v)`; the scheme universe is included, including the ordinary `v = 0` case |
| A family of sheaves of sets | `G : I → Sheaf (fppfTopology.over S) (Type (max u v))` |
| Existence of the coproduct, with coprojections | The first conjunct quantifies `C` and `c : ∀ i, G i ⟶ C`, with `Nonempty (IsColimit (Cofan.mk C c))` |
| Assertions about that coproduct | The second conjunct applies to every `C`, `c`, and `IsColimit (Cofan.mk C c)`, so it does not select a special coproduct |
| Coprojections monic, injective on sections | `∀ i, Mono (c i) ∧ ∀ T, Function.Injective ((c i).hom.app (op T))` |
| Every test object and section | `∀ (T : Over S) (a : C.obj.obj (op T))` |
| Unique partition and unique component sections | `∃! d : FppfCoproductPartition G T, d.MapsTo c a`; equality of the record includes its opens and its dependent component sections; proof fields are irrelevant |
| Open and closed subschemes | `d.opens i : T.left.Opens`, `d.isClosed i`; their schemes are the existing Mathlib `Opens.toScheme`, included by `Opens.ι` |
| Pairwise disjoint, covering T | `d.disjoint : Pairwise ... Disjoint ...`, `d.covers : iSup d.opens = ⊤` |
| Scheme coproduct decomposition | `Nonempty (IsColimit (Cofan.mk T.left (fun i ↦ (d.opens i).ι)))` for every compatible partition |
| Sections on the pieces | `d.sections i : (G i).obj.obj (op (fppfPartitionOpen T (d.opens i)))` |
| The equation c_i(a_i) = a restricted to T_i | `FppfCoproductPartition.MapsTo`, whose body is exactly the component equation with `C.obj.map (fppfPartitionInclusion ...).op` |
| The square with h_Ti, h_T, G_i, C is cartesian | `IsPullback (uliftYoneda.map inclusion) (uliftYonedaEquiv.symm (d.sections i)) (uliftYonedaEquiv.symm a) (c i).hom` |
| Every morphism b : Z → T | `∀ (Z : Over S) (b : Z ⟶ T)` |
| Its partition is the inverse image partition | The resulting compatible `e` has `e.opens i = b.left ⁻¹ᵁ d.opens i` |
| Its sections are restrictions of a_i | `HEq (e.sections i) ((G i).obj.map (fppfPartitionRestriction b (d.opens i)).op (d.sections i))`; heterogeneous equality expresses ordinary equality after transport along the preceding equality of opens |
| Converse gluing to a unique section | `∀ T d, ∃! a : C.obj.obj (op T), d.MapsTo c a` |
| Empty pieces allowed | No nonemptiness condition on any open or component is imposed |
| I empty, T empty: singleton | `IsEmpty I → ... IsEmpty T.left → Nonempty (Unique (C.obj.obj (op T)))` |
| I empty, T nonempty: empty | `IsEmpty I → ... Nonempty T.left → IsEmpty (C.obj.obj (op T))` |

The cartesian square is stated in presheaves, an equivalent formulation of the
square in sheaves: fppf topology is subcanonical, representables are sheaves, and
the inclusion of sheaves creates limits. `uliftYoneda.{v}` is the usual representable
`Z ↦ Mor_S(Z,T)`, with only a universe lift; `uliftYonedaEquiv.symm` sends a section
to the natural map taking a test morphism to its restriction. There is no arbitrary
comparison map. At `v = 0` the representable is equivalent to ordinary Yoneda.

The existence assertion intentionally does not require `HasSheafify` for all
small-valued presheaves on the big category of schemes. It states the coproduct
universal property directly and then all properties for every coproduct cofan.
There are no geometric assumptions such as quasi-compactness, separatedness,
nonempty index, nonempty test scheme, or finite index.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `Scheme.Hom`, read at lines 35–77.
- `def-pc-fppf-site`: `Mathlib.AlgebraicGeometry.Sites.Fpqc`,
  `Scheme.fppfPrecoverage` and `Scheme.fppfTopology`, lines 37–54. Also read the
  recorded `Scheme.overGrothendieckTopology` in `Sites.Small`, lines 103–107.
  The corresponding over-site used here is `GrothendieckTopology.over` from
  `Mathlib.CategoryTheory.Sites.Over`: its objects are `Over S` and its covering
  sieves are precisely those whose underlying sieves cover in `fppfTopology`.
- `def-weil-size-convention` is the recorded metatheoretic convention, rendered
  by explicit universes rather than an additional object or hypothesis.
- `def-weil-pbc-sites-and-cohomology`: import its recorded
  `Sheaf.CategoryTheory.SiteCoveringAxioms`; its note retains Mathlib `Sheaf` for
  sheaves of sets. No special cohomology or continuous-functor component is needed.
  Read `IsSiteForCoverings` and the `Sheaf`/`Presheaf.IsSheaf` documentation.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`, lines 34–39, and the standard `Opens.toScheme`
  and `Opens.ι` in `Restrict`. The pieces are the actual standard open subschemes,
  whose inclusions are open immersions, not private reconstructions.
- `def-weil-pbc-category-colimit`: `Mathlib.CategoryTheory.Limits.HasLimits`,
  `Cocone`, `IsColimit`, and the chosen `colimit` API. We use its general colimit
  universal property on the discrete diagram via `Cofan.mk`.

Proof-only imports retain the modules of the recorded proof dependencies:
`Mathlib.CategoryTheory.Sites.LeftExact` (the concrete sheafification adjunction,
including `plusPlusAdjunction`, read in `ConcreteSheafification`),
`WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`
(`CategoryTheory.sheafification_sections_local`, read with `scompile.py --source`),
`Mathlib.AlgebraicGeometry.Gluing` (`Scheme.Cover.glueMorphisms`,
`ι_glueMorphisms`, and `hom_ext`), and
`Mathlib.AlgebraicGeometry.PullbackCarrier` (surjective base-change instance).
`UniversallyOpen.of_flat` and scheme pullbacks are already exported by the fppf
site imports. The fibre-product API is used by `IsPullback`.

The five auxiliary declarations are all recorded in `lean.declarations`:
`fppfPartitionOpen` forms `Over.mk (U.ι ≫ T.hom)`;
`fppfPartitionInclusion` is `Over.homMk U.ι`;
`fppfPartitionRestriction` is the existing `morphismRestrict`, bundled over S;
`FppfCoproductPartition` is the data record above; and its `MapsTo` predicate is
the displayed equation. All have real data. The restriction map's structural
triangle is discharged by the existing `morphismRestrict_ι`, associativity,
and `Over.w`; no helper theorem is postponed. The only `sorry` is the named main theorem.

Edge cases checked against the statement before writing:

- Empty I forces the union of opens to be bottom; a partition can exist only when
  T is empty. The theorem separately records exactly the corresponding section sets.
- Empty T permits every piece to be empty, with the unique section of each sheaf;
  it imposes no label or nonempty-index choice.
- Singleton I gives the full open T and one component section, including the empty T case.
- Infinite I is allowed: there is neither a finite-cover restriction nor a
  quasi-compactness assumption; disjointness and `iSup = ⊤` encode the full partition.
- An empty summand may contribute an empty piece. No component section over a
  nonempty scheme is asserted unless that section exists.
- Arbitrary non-flat b is permitted. The restriction helper uses inverse images
  of opens and the existing scheme restriction morphism, not fppf membership of b.
- Coefficients include the scheme universe. Test objects run over all `Over S`,
  so their quantification is never vacuous from an undersized independent universe.

Searches actually run with `msearch.py`, group NJ and this item (UTC 2026-10-17):

- LeanFinder: `Sections of coproducts of fppf sheaves give unique clopen partitions of test schemes`.
  Eight results: scheme coproduct structure-sheaf sections, sigma open covers,
  disjoint summand images, and related scheme facts. None is the assertion about
  arbitrary fppf sheaves and their summand pullbacks.
- Loogle: `"Sheaf", "coproduct"`. Twelve results, concerning free-Yoneda coproducts
  of presheaves of modules. None gives this fppf partition theorem.
- Grep: `coproduct.*(sheaf|fppf)|sheaf.*coproduct`, subdirectory `AlgebraicGeometry`.
  Two hits in `Sites/BigZariski.lean`, referring to coproduct sheaf conditions;
  neither is the requested statement.
- LeanSearch: `Coproducts of fppf sheaves have sections given by unique clopen partitions and summand pullbacks represented by the pieces`.
  Eight hits: generic sheaf finite coproduct existence, topological unique gluing,
  scheme and locally ringed space coproducts. The generic existence declaration
  assumes sheafification and does not provide the clopen-partition clauses.
- Direct `rg` of Mathlib, upstream `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` found no occurrences of any proposed full declaration
  name. Direct searches for `coproduct.*fppf|fppf.*coproduct|sheaf.*clopen.*partition`
  in upstream/project sources found no matching statement; the sole unrelated project
  match was an import of `GaloisFiniteInvariantClopenPartition`.
- Direct search for this exact DAG id in upstream `WeilConjectures` found nothing.

Validation: the prescribed `scompile.py` wrapper passed with no errors or warnings,
including the library-path confirmation (16.2 seconds). The final dry run and
delivery use `deliver2.py`. The initial compile caught only
the restriction helper's computability annotation and triangle simplification;
these were repaired without changing the theorem statement.

## Second reading by NJ

Independent maintainer second reading, 2026-10-18, of immutable delivery
852c53f522bfaf6ff18f2cfefc126fcde3c4eb4d. This reading was performed by the
maintainer reviewer, who neither wrote nor previously second-read this delivery.
The original placeholder explicitly said that no second reading had taken place;
it is replaced here with the completed reading (delivery-errors H11).

Read the packet, the immutable item node, all six statement-dependency nodes,
the delivered module and its docstrings, and the Worker report. Compared the three
delivery files byte-for-byte with the immutable commit: all match. The node changes
only in `lean`; its `statement` has not been corrected. No new nodes or dependency
modules are delivered, and no statement-change/citer audit is required.

Clause-by-clause findings (all pass):

- Base and site: `{S : Scheme.{u}}`, `Over S`, and `fppfTopology.over S` give
  schemes over the specified base with all S-morphisms and the generated fppf
  topology. `fppfPrecoverage` is jointly surjective flat, locally finitely presented
  families; `GrothendieckTopology.over` pulls covering sieves back through the
  underlying-sieve equivalence. The Mathlib match of `def-pc-fppf-site` supplies
  this notion even though that dependency has no separate `lean` record.
- Sizes and coefficients: explicit `universe u v`, `I : Type (max u v)`, and
  `Type (max u v)` coefficients give the common universe convention. Scheme and
  over-site objects are not replaced by objects in an independently smaller
  universe. `uliftYoneda.{v}` lifts the S-morphism sets to this same coefficient
  universe. There is no equality imposed between site object and morphism
  universes, no finiteness condition, and no extra sheafification instance.
- Family: `G : I → Sheaf ... (Type (max u v))` uses the existing full category
  of set-valued sheaves; morphisms are natural transformations.
- Existence: the first conjunct supplies `C`, the coprojections `c`, and
  `Nonempty (IsColimit (Cofan.mk C c))`. `Cofan.mk` is a cocone over the discrete
  family, and `IsColimit` is its universal property. The remaining clauses are
  quantified over every such cofan, not just a distinguished choice.
- Monicity: `∀ i, Mono (c i) ∧ ∀ T, Function.Injective ...` asserts both
  categorical monicity and injectivity on all section sets, exactly as requested.
- Partition and component sections: `∃! d, d.MapsTo c a` includes both unique
  opens and unique dependent sections. The record uses actual scheme opens,
  `IsClosed`, pairwise `Disjoint`, and `iSup opens = ⊤`. Its proof fields are
  proof irrelevant. `Opens.toScheme` and `Opens.ι` give the standard open
  subschemes, and the additional scheme `IsColimit` clause supplies the stated
  scheme coproduct decomposition. No nonemptiness is imposed on pieces.
- Component equation: `MapsTo` says precisely that the coprojection of each
  component section equals restriction of `a` along that open inclusion.
- Cartesian square: the four arguments of `IsPullback` are, in order, the
  representable inclusion, the Yoneda map of the component section, the Yoneda
  map of `a`, and `(c i).hom`. `uliftYonedaEquiv.symm` evaluates on a test map
  by restricting the section, so these are the prescribed canonical arrows.
  The assertion in presheaves is equivalent to the sheaf assertion: fppf
  representables are sheaves and sheaf inclusion creates limits.
- Base change: every `b : Z ⟶ T` is allowed. The resulting `e` satisfies
  `MapsTo` for `b`-restriction, has the inverse-image opens, and its sections
  satisfy `HEq` with restrictions along the canonical `morphismRestrict` over S.
  This is equality after transport along the displayed equality of opens.
  The preceding uniqueness clause identifies this `e` with the unique partition.
- Converse: `∀ T d, ∃! a, d.MapsTo c a` gives existence and uniqueness of
  gluing for every partition with its summand sections.
- Empty index: `IsEmpty I` gives `Nonempty (Unique (C(T)))` for empty T, and
  `IsEmpty (C(T))` for nonempty T. These express exactly the two stated cases.

Sources and declarations inspected:

- Stacks `spaces.tex:987` (0F15), including its full binary argument and the
  omitted summand-pullback verification; `spaces.tex:1012` (02WO), including
  scheme coproducts. No separatedness, Noetherian, or finiteness hypothesis is
  present in that context. The node's set-indexed argument is the same local
  labelled-section argument, with unions for each label.
- Stacks `sites.tex:2114` (00WI), sheafification of presheaf colimits, and
  `sites.tex:2156` (00WK), local representatives and their equality condition;
  `topologies.tex:1911` (021L) and `:1998` (021S), fppf covers and big sites.
  Sources were read in `/home/ubuntu/weil-newtargets-NJ/literature/stacks-project`.
- Mathlib `AlgebraicGeometry/Scheme.lean:38,72` (`Scheme`, `Scheme.Hom`),
  `Sites/Fpqc.lean:40,53` (`fppfPrecoverage`, `fppfTopology`),
  `CategoryTheory/Sites/Over.lean:248` (`GrothendieckTopology.over`),
  `CategoryTheory/Sites/Sheaf.lean:78,302` (`Presheaf.IsSheaf`, `Sheaf`),
  `AlgebraicGeometry/OpenImmersion.lean:38` (`IsOpenImmersion`),
  `Restrict.lean:46,52,569,581` (`Opens.toScheme`, `Opens.ι`,
  `morphismRestrict`, `morphismRestrict_ι`),
  `CategoryTheory/Limits/Shapes/Products.lean:56,71` (`Cofan`, `Cofan.mk`),
  `Limits/IsLimit.lean:69` (`IsColimit`),
  `Limits/Shapes/Pullback/IsPullback/Defs.lean:61` (`IsPullback`), and
  `CategoryTheory/Yoneda.lean:65,920` (`uliftYoneda`, `uliftYonedaEquiv`).
  Read in the pinned Mathlib under `/home/ubuntu/weil-src-slopmaster2`.
- Read the recorded `Sheaf.CategoryTheory.SiteCoveringAxioms` module in the
  read-only group clone. Its dependency note retains the existing Mathlib
  sheaf notion, which this theorem uses; no private site/sheaf replacement is
  introduced. The size node is a metatheoretic convention, not missing data.

Edge cases: empty I with empty and nonempty T; empty T with nonempty I;
singleton and infinite I; empty summands/pieces; arbitrary non-flat test maps.
All are included. Neither quasi-compactness nor a finite cover is required.
The canonical empty pieces use the unique sections of a sheaf on the empty
scheme. There is no characteristic, coefficient-ring, or degree parameter.

One-definition-per-notion searches: independently searched pinned Mathlib,
upstream `WeilConjectures`, group `lean/Sheaf`, and `dag/lean_names_upstream.json`
for all six delivered names and for `sheaf.*(clopen|partition)`,
`fppf.*coprod`, `coprod.*fppf`, and partition structures. No existing copy of the
assertion or record was found. Inspected the nearby results in
`Sites/BigZariski.lean` and `CategoryTheory/Sites/Limits.lean`; these concern
scheme coproduct sheaf conditions or generic coproduct existence and do not
state the clopen scheme-test partition theorem. The worker's recorded semantic
and pattern searches are consistent with these results. The helper record
packages this item's data; the other helpers bundle existing canonical maps.

Maintainer gates: all five helpers have real data, not `sorry` or arbitrary
choices. The restriction helper's proof is only the structural over-base
triangle for the existing restriction map. There is exactly one theorem, with
proof exactly `by sorry`. Module and declaration docstrings cite sources and
blueprint id; the theorem docstring follows all nine node proof steps.
All lines are at most 100 characters, all variables/universes are bound, and
`lean.statement` is verbatim equal to the signature before `:= by`.
The current shared route-pivot dropped-node list has no intersection with
`stmt_deps` or `proof_deps`; there is no route-pivot repair note for this item.
No infinity/dg/model-category machinery or pro-etale substitute appears.

Compiler reproduction: ran
`python3 /home/ubuntu/weil-launcher-nt/scompile.py NJ
lem-trf-fppf-sheaf-coproduct-partition
snapshot/lean/Sheaf/AlgebraicGeometry/FppfSheafCoproductPartition.lean`.
The currently installed wrapper performs server side-overlay compilation and
library-path confirmation. It exited 0 with no errors or warnings, reporting
sandbox `Sheaf/Stage2/Sandbox0.lean` [3.7 s] and library
`Sheaf/AlgebraicGeometry/FppfSheafCoproductPartition.lean` [55.8 s].
The initial multiplexing refusal recovered within the wrapper. No direct ssh,
repository edit, Git mutation, lake/global build, or live Lean write was run.

Finding and correction: H11, the delivered second-reading section was an
explicit no-reading placeholder. This full report replacement preserves the
Worker report and supplies the completed independent reading. No mathematical,
Lean-module, dependency, or node-record correction is needed. Verdict: FIX.
