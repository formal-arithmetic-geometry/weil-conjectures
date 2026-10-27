## Worker report

States `AlgebraicGeometry.scheme_infinitesimal_etale_patching` in
`Sheaf.AlgebraicGeometry.SchemeInfinitesimalEtalePatching`, with one postponed theorem
and a six-step source-based proof docstring. The mathematical node statement is unchanged.
The additional definition module constructs the category of triples and its canonical
restriction functor. Definitions contain real data and no sorry.

Hypothesis and clause correspondence:

- Schemes T, T+, S: `{T T' S P : Scheme.{u}}`; `i : T ⟶ T'`, `a : T ⟶ S`.
- Arbitrary thickening: `hi : IsThickening i`, the existing upstream predicate meaning
  closed immersion plus surjectivity. A surjective closed embedding is a homeomorphism.
  No ideal exponent is required.
- Affine T to S: `[IsAffineHom a]`, whose defining property is affineness of inverse
  images of affine opens.
- P is the scheme pushout: `j`, `b`, `hP : IsPushout a i j b`. The existing dependency
  proves existence of such a square; quantifying over any such square retains the
  usual invariance under its unique canonical isomorphism. No cartesian hypothesis is added.
- Etale triples: `EtalePushoutTriples a i` is the full subcategory of
  `Comma (MorphismProperty.Over.pullback @Etale ⊤ a)
  (MorphismProperty.Over.pullback @Etale ⊤ i)` where `IsIso D.hom`.
  Its left and right objects are Mathlib's `S.Etale` and `T'.Etale`.
  The comparison is a morphism over T, so the isomorphism respects the T-projection.
  An invertible morphism determines its unique inverse, so no isomorphism data is lost.
  Comma morphisms are exactly pairs with commuting comparison square; the full subcategory
  changes no morphisms. Identities and composition are the existing componentwise ones.
- The pullback functor is the explicitly defined `etalePushoutRestriction a i j b hP.w`.
  On objects it uses the actual Mathlib base changes along j and b. Its comparison is
  `pullbackComp a j` inverted, followed by `pullbackCongr hP.w`, then `pullbackComp i b`.
  This is the canonical identification via pullback along the equal composites T to P.
  Its morphisms are the two base-change maps, with compatibility from naturality.
- Equivalence and quasi-inverse: the theorem supplies G and `adj : G ⊣ F`, together
  with `IsIso adj.unit` and `IsIso adj.counit`. An adjunction with invertible unit and
  counit is precisely an adjoint equivalence. This retains the functors, naturality and
  coherent inverses; it is stronger data packaging of the same claimed equivalence,
  not an equivalence between some unspecified functors.
- G sends a triple to its scheme pushout: for every D, `IsPushout` on the common
  `pullback D.obj.left.hom a` with maps `pullback.fst` to X and
  `D.obj.hom.left ≫ pullback.fst` to Y, with inclusions `l D`, `r D` into `(G.obj D).left`.
  This is the exact X amalg_(X times_S T) Y square with the given comparison.
- Its induced map to P is specified by both equations
  `l D ≫ (G.obj D).hom = D.obj.left.hom ≫ j` and the analogous equation for r and b.
  The map is etale because G takes values in `P.Etale`.
- Canonical unit: its left/right component projections to the glued scheme equal l/r.
  Their projections to S/T+ are already the structural maps because the components
  are morphisms in the corresponding etale slices. These two properties uniquely
  determine the claimed canonical pullback lifts. Invertibility of the natural unit
  makes both components isomorphisms. Compatibility with phi is precisely the comma
  morphism equation inherent in `adj.unit.app D`; its naturality is inherent in the unit.
- Canonical counit: the last two equations say its restrictions along l and r are
  `pullback.fst W.hom j` and `pullback.fst W.hom b`. Thus pushout uniqueness identifies
  it with the canonical map from the glued pullbacks to W. Its invertibility transfers
  the preceding pushout property to W itself. The common iterated T-pullback is
  canonically W times_P T by the named comparison, retaining exactly the counit clause.
- No quasi-compactness, separatedness, finite-order, nonempty or Noetherian hypotheses
  occur. All schemes have the standard shared universe u and no added size restriction.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `WeilConjectures.AlgebraicGeometry.Thickening`: `IsThickening`, re-exported by
  `Sheaf.AlgebraicGeometry.SchemeAffineThickeningPushout`.
- `Sheaf.AlgebraicGeometry.SchemeAffineThickeningPushout`:
  `exists_scheme_affine_thickening_pushout`, supplies the existence of P; the statement
  accepts an arbitrary witnessing `IsPushout` square rather than making a noncanonical choice.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`, `Scheme.Etale`, its slice category,
  and `Etale.etale_isStableUnderBaseChange` (also the proof dependency's mathlib_match).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `pullback`, `pullback.fst`, `pullback.snd`, and the scheme pullback instances.
- `Mathlib.CategoryTheory.MorphismProperty.OverAdjunction`: `Over.pullback`,
  `Over.pullbackComp`, `Over.pullbackCongr` in namespace `MorphismProperty`.
- `Mathlib.CategoryTheory.Comma.Basic`: `Comma`, `CommaMorphism`;
  `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`: `FullSubcategory`, `homMk`.
- Proof imports include the recorded `scheme_etale_source_target_properties` from
  `Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties`, and Mathlib's open
  immersions (etale instance), affine-open basis, and affine ring-hom criterion.
  The proof dependencies `lem-sfb-infinitesimal-pushout-affine-charts`,
  `lem-sfb-fibre-product-algebra-etale`, `lem-sfb-scheme-pushout-flat-patching` have
  no recorded declarations in the read tree, so there is no module to import for them.
  They are used only in the postponed proof, not to define the statement's objects.

Edge cases checked before writing: empty S forces T and T+ empty and the entire
pushout empty; both categories remain defined. Empty etale schemes and maps are
included. For i an identity the statement reduces to the canonical compatibility
category over S; for a an identity it reduces to etale schemes over T+. Locally
nilpotent defining ideals with no global nilpotence bound are allowed. Arbitrarily
non-quasi-compact and nonseparated etale schemes remain objects. The over-T condition
on the comparison is present, preventing an unrelated scheme isomorphism from
being used as gluing data. The use of a square with the full scheme pushout property
retains the correct universal property against nonaffine targets.

Searches made with msearch.py (real results in searches.jsonl):

- leanfinder: “Etale schemes over an infinitesimal scheme pushout are equivalent to
  compatible etale schemes over its two pieces”: 8 hits on etale base change and
  category instances, no patching equivalence.
- loogle: `"Etale", "pushout"`: 0 hits.
- grep Mathlib: `(pushout|Pushout).*(Etale|etale)|(Etale|etale).*(pushout|Pushout)`: 0 hits.
- leansearch: “Category of triples of schemes over two bases with an isomorphism
  of their base changes”: 8 hits about Scheme.Pullback.Triplet, which are points
  of a scheme pullback, not this category of etale objects.
- leanfinder: “category of compatible etale scheme morphisms with isomorphic
  restrictions over a common scheme”: 8 hits on Scheme.Etale and its forgetful
  functor and pullbacks, no compatible triples.
- grep Mathlib/AlgebraicGeometry:
  `EtalePushoutTriples|etalePushoutRestriction|[Ee]tale.*[Pp]atching|[Ee]tale.*[Tt]riples`:
  0 hits.
- rg on WeilConjectures and Sheaf for patching/triples and the item id: no existing
  declaration of this statement or these specialized compatible triples. EtaleResidueTriples
  and OrientedEtaleTriples refer to different objects. The algebraic-space pushout
  docstring mentions this item only as a proof input.
- DAG search by rg for etale triples, fibre products of categories and iso-comma
  notions: no node of compatible etale triples. Read
  `def-weil-pbc-category-fibre-product`: it is a pullback *in* an arbitrary category
  (IsPullback), not the 2-fibre product category of triples.
- `tools/blueprint_refs.py search 'etale triples'`: 0 blueprint nodes.
  `ancestor` of this item returns None, as its inherited provenance says.
- Checked the proposed declaration names in dag/lean_names_upstream.json and in
  both Lean roots: no clashes.

Sources read: local Stacks more-morphisms.tex, complete 07RV construction and
adjunction, and 07RX(5) with its flat counit. No statement fault or mathematical
correction is needed. Compilation through scompile.py of each module, both sandbox
and final module paths, passed without errors or non-sorry warnings.

## New nodes

`def-sfb-etale-pushout-triples` supplies the missing specialized category of compatible
etale schemes and the canonical restriction functor. Its module
`Sheaf.AlgebraicGeometry.EtalePushoutTriples` defines `EtalePushoutTriples`,
`etalePushoutComparison`, and `etalePushoutRestriction`. The source is Stacks 07RV,
restricted to the etale subcategories as in 07RX(5). The exact three kinds of search
and their results are in the new node; project and DAG searches are above. Existing
Mathlib comma categories and full subcategories are reused, not redeclared; the
specialized etale triple category and its functor were absent. The auxiliary
comparison is the actual composite of existing canonical natural isomorphisms.
No theorem or existential choice supplies any definition's data.

## Second reading by NO

Independent second reading (maintainer review service, 2026-10-24), against the node,
Stacks more-morphisms.tex Tags 07RT, 07RV (lemma-equivalence-categories-schemes-over-pushout)
and 07RX (lemma-equivalence-categories-schemes-over-pushout-flat, item (5) and the flat counit),
and the dependency declarations.

Objects and hypotheses:
- Schemes T, T+, S, P: `{T T' S P : Scheme.{u}}` (def-pc-scheme = Mathlib `Scheme`). Correct.
- Thickening T -> T+: `hi : IsThickening i` = `IsClosedImmersion i ∧ Surjective i`
  (WeilConjectures.AlgebraicGeometry.Thickening, owner def-sbc-first-order-thickening, Tag 04EX(1));
  a surjective closed embedding is a homeomorphism. No nilpotence order. Correct, not stronger.
- T -> S affine: `[IsAffineHom a]`. Correct.
- P = S ⊔_T T+: arbitrary square `hP : IsPushout a i j b` (w : a ≫ j = i ≫ b); existence is
  the dependency theorem; no cartesian or thickening hypothesis on j added. Correct.
- Etale triples: `EtalePushoutTriples a i`, full subcategory of the comma category of the
  two base-change functors `S.Etale ⥤ T.Etale`, `T'.Etale ⥤ T.Etale` on `IsIso D.hom`.
  D.obj.hom.left : pullback X.hom a ⟶ pullback Y.hom i, i.e. φ : X ×_S T ≅ Y ×_{T+} T over T,
  as in the 2-fibre product of 07RV. Comma morphisms = pairs over S, T+ commuting with φ.
  Real data (Mathlib comma/full subcategory), no sorry. Correct.
- Pullback functor F: `etalePushoutRestriction a i j b hP.w`, base change along j and b,
  comparison = pullbackComp⁻¹ ≫ pullbackCongr w ≫ pullbackComp (canonical). Correct.

Conclusion clauses:
- Equivalence: G, adj : G ⊣ F, IsIso adj.unit, IsIso adj.counit (adjoint equivalence). Correct.
- Quasi-inverse is the pushout X ⊔_{X ×_S T} Y: IsPushout (pullback.fst X.hom a)
  (φ ≫ pullback.fst Y.hom i) (l D) (r D) in Scheme; induced map to P pinned by
  l ≫ G.hom = X.hom ≫ j, r ≫ G.hom = Y.hom ≫ b; etale since G lands in P.Etale. Correct.
- Unit: components' first projections equal l, r; second projections are the structural maps
  (Over-morphisms); invertibility from IsIso adj.unit; compatibility with φ is the comma
  equation of adj.unit.app D. Pinned and canonical. Correct.
- Counit: restrictions along l, r of counit.app W are pullback.fst W.hom j / b, so W is the
  pushout of W ×_P S and W ×_P T+ along the (canonically identified) W ×_P T. Correct.
- No qc / separated / finite-order hypotheses; single universe u as in the node.

Edge cases: empty schemes (all categories defined, empty objects allowed); i = 𝟙, a = 𝟙;
locally but not globally nilpotent ideals; non-quasi-compact etale W. All covered.

Records: item statement unchanged from base; added stmt_dep def-sfb-etale-pushout-triples is
the new definition node of this delivery (Tag 07RV source, three search kinds, real
declarations). lean.statement fields verbatim with the files. Docstrings carry source place
and blueprint ids; the theorem docstring carries the six proof steps; the only proof is `sorry`.
Searches (Mathlib grep `EtalePushout|etale.*patching`, live clone grep for the declaration names):
no existing declaration or parallel landing.

Advisory: the node's stmt_deps (base, stage 1) cite def-weil-closed-immersion and the
theorem node for the thickening notion; the Lean predicate's owner is def-sbc-first-order-thickening.
Not a fault of this delivery.

Change made by the reviewer: this section replaces the dispatcher-wording placeholder.
