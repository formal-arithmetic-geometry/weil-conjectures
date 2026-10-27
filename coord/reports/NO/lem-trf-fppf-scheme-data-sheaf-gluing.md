## Worker report

Item: lem-trf-fppf-scheme-data-sheaf-gluing. Group NO, stage 2, 2026-10-22.

The delivery adds `Sheaf.AlgebraicGeometry.FppfSchemeDataSheafGluing`, declaring
`AlgebraicGeometry.fppfSchemeDataSheafGluing` with a `sorry` proof. It introduces no
new definition, no dependency module, and no statement correction. Only `lean`
changes in the node copy. The existing `reviewed` record is the stage-1 review of
the split; `lean` and `reviewed_lean` were absent when this stage-2 work started.
The previous attempt left no module, node copy, or report in this item's sandbox.

Sources read: Stacks `descent.tex`, lemma-descent-data-sheaves (Tag 02W5), including
both constructions, the omitted quasi-inverse verification, and the following
remark-what-product-means; the recorded set-sheaf gluing interface for Sites Tags
04TR and 04TQ; and the complete statement and eight proof steps of this item.

Hypotheses and clauses, in the order of the node:

1. The base scheme is `T : Scheme.{u}`; the covering members are
   `U : I → Scheme.{u}`, with `f : ∀ i, U i ⟶ T`. The set index is
   `I : Type (u + 1)`. `hcov : Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage T`
   is exactly joint surjectivity, flatness, and local finite presentation.
   This is a precoverage membership, not just an arbitrary map or cover assumption
   added to a vacuous hypothesis.
2. The size convention is explicit: scheme carriers have level `u`, the site,
   indexing sets, and section sets fit level `u+1`. This is the existing
   dependency's universe convention; smaller set indices lift into this level.
   No nonempty, finite, affine, separated, or Noetherian hypothesis is imposed.
3. The big site is `Scheme.fppfTopology.over T`. The representable `h_Z` is
   encoded by `RepresentableBy` on `Over T`; `uliftYoneda.{u+1}` moves the
   scheme Hom sets into the section universe without changing their elements.
   `Limits.prod` is the product of presheaves, whose projections are used in the
   formula. Products of these sheaves are sheaves, by sectionwise limits.
4. The category L is exactly `(IsLocallyRepresentableFppfSheaf f).FullSubcategory`.
   Its existing definition uses representability of the slice restrictions,
   equivalent to product representability by the remark after 02W5. The theorem
   additionally supplies actual product representations by the specified X_i.
5. The category D is `SchemeCoverDescent f`. Its objects retain the local schemes
   `D.localScheme i`, the actual representing bijections `D.representation i`,
   and `D.data` with all transitions and cocycles. Its induced-category morphisms
   are compatible local sheaf morphisms, hence exactly the local scheme morphisms
   by those bijections and Yoneda. No private copy of descent data is used.
6. `G` is the asserted functor D → L. The natural isomorphism `e` has type
   `G ⋙ L.ι ⋙ toDescentData f ≅ schemeCoverDescentForget f`.
   Its component at D, then at i, is `G(D)|_{U_i} ≅ D.data.obj i`; composing
   with `D.representation i` identifies the latter with the node's F_{D,i}.
   The restriction is `overMapPullback`, which precomposes by `Over.map (f i)`
   and is sectionwise, rather than a sheafification or different restriction.
7. The overlap equation `e_j = θ_ij e_i` is the `DescentData.Hom.comm` equation
   for `e.hom.app D`. `D.data.hom p a b ha hb` is exactly θ on an arbitrary
   overlap test object, with the two prescribed base maps. It is conjugated by
   `D.representation i/j` to the scheme transition retained by the dependency's
   Yoneda encoding. This also includes i=j. The canonical transitions of
   `toDescentData` are the sectionwise identifications on double slices.
8. For a morphism D → D', the naturality equation of `e.hom`, evaluated at i,
   says `G(f)|_{U_i} ≫ e_{D',i} = e_{D,i} ≫ h_{f_i}` in Lean's composition
   order. This is exactly the displayed morphism equation in the node; it is
   part of the stated natural isomorphism, not an unstated extra theorem.
9. `β D i` is a natural `RepresentableBy` witness for
   `h_{U_i} × G(D)` represented by `(Over.map (f i)).obj (D.localScheme i)`.
   On `W : Over (U i)` and `x : W ⟶ D.localScheme i`, the first equation says
   that its first projection is `ULift.up (Over.homMk W.hom)`. Thus it is over
   the prescribed member U_i, not merely an abstract product representation.
   The second equation says that its second projection is
   `((e.inv.app D).hom i).hom.app (op W) ((D.representation i).homEquiv x)`.
   This is exactly the node's inverse slice bijection formula.
   These formulas cover all maps of T-schemes: for a map V → X_i over T,
   endow V with its composite to U_i, making it such a W. The resulting global
   object is canonically isomorphic to the original V/T by the identity map
   of schemes; naturality of RepresentableBy transports the equation along it.
10. The requirement that the product overlap comparison is the original φ_ij is
    encoded jointly by the preceding formula and the descent-morphism equation
    of e, rather than by adding an unrelated existence of an overlap isomorphism.
    Indeed, evaluate on a test scheme with coordinates (a_i,s,a_j). The inverse
    β formula gives `e_i(s)` on one side and `e_j(s)` on the other. The equation
    `e_j(s)=θ_ij(e_i(s))` gives exactly the prescribed φ_ij including both base
    coordinates. Natural RepresentableBy witnesses and Yoneda identify the full
    scheme maps, not only points over a field. Conversely the node's e and β
    plainly satisfy these two equations.
11. The universal final clause quantifies over `R : L ⥤ D` and
    `r : R ⋙ schemeCoverDescentForget f ≅ L.ι ⋙ toDescentData f`.
    This r is the exact sectionwise encoding of being defined by chosen product
    representations with coordinate-preserving overlaps and morphisms id × v.
    For the node's chosen α_i, take the fibre over each W → U_i; composing that
    fibre representation with `R(H).representation i` gives r. Its compatibility
    with transitions expresses preservation of the H coordinate; naturality
    expresses the specified action on morphisms. Conversely, any such R,r gives
    those chosen product representations by separating maps according to their
    base coordinate, exactly as for β. Thus this does not replace a canonical
    construction by an arbitrary functor or require an extra property of it.
12. `ε : G ⋙ R ≅ 𝟭 (SchemeCoverDescent f)` has the orientation R∘G ≅ id.
    The final equality specifies its components after the fully faithful forgetful
    functor: `(forget.map (ε.hom.app D)).hom i =
    (r.hom.app (G.obj D)).hom i ≫ (e.hom.app D).hom i`.
    Applying the local representing bijections says precisely that ε_i is the
    unique map induced by β_i^{-1} α_i; these are the comparisons in the node.
    Naturality is part of ε, so the conclusion retains the final naturality clause.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `Scheme.Hom`, through the public descent-datum import.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology`, `Scheme.fpqcPrecoverage`, and the subcanonical instance
  for `fpqcTopology` (and its fppf specialization). This also supplies the
  recorded fpqc-covering and representable-morphism-descent proof interfaces.
- `def-weil-size-convention` is metatheoretic; its recorded convention has no
  declaration. The explicit universe `u` and levels above implement it.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.lift`; the geometric overlaps are
  encoded by the existing descent-data interface, with all test base maps.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings` is publicly available through
  the datum module. The existing sheaf categories and Grothendieck topologies
  implement the relevant sheaf part of this dependency; no alternative site.
- `Sheaf.AlgebraicGeometry.SchemeCoverDescentDatum`:
  `AlgebraicGeometry.SchemeCoverDescentDatum`, `SchemeCoverDescent`,
  `schemeCoverDescentForget`, `IsLocallyRepresentableFppfSheaf`, and the fields
  `data`, `localScheme`, `representation`.
- `Mathlib.CategoryTheory.Sites.Over`: `GrothendieckTopology.over`,
  `overMapPullback` and `Sheaf.over`. The recorded
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous` is imported
  too; the present theorem needs only the set-sheaf portion of that node.
- The stated proof dependencies are imported without `public`:
  `Sheaf.AlgebraicGeometry.FppfAffineRefinement`, declaration
  `AlgebraicGeometry.Scheme.exists_finite_fppf_affine_open_refinement`, and
  `Sheaf.CategoryTheory.SetSheafCoverDescent`, declaration
  `CategoryTheory.setSheafCoverDescent`. Their complete statements/docstrings
  were read. Yoneda and representable uniqueness use the recorded Mathlib
  `Functor.RepresentableBy`, `yoneda`, `Yoneda.fullyFaithful`, and
  `Functor.FullyFaithful.isoEquiv`; these are already exported by the imports.

Edge cases checked before writing: an empty index set (then a covering forces
T empty), empty local schemes and empty overlaps, repeated indices, the identity
cover, and infinite covering families. There is no inhabitance or finiteness
requirement. In the empty-cover case the big site over the empty base has only
empty test schemes up to isomorphism and the empty-cover axiom forces singleton
sections. All quantified comparisons are then empty families, and the datum
category has a unique compatible morphism, as required. The identity cover gives
the usual represented sheaf and β's inverse-slice formula. Repeated indices use
the dependency's diagonal normalization, which follows from the invertible
cocycle and adds no hypothesis. No claim of geometric effectivity is introduced:
the global object here is a sheaf and need not be represented by a scheme.

Searches made in this run (via msearch.py where indicated):

- LeanFinder: "Gluing scheme descent data over an fppf covering into locally
  representable sheaves functorially with local comparison isomorphisms".
  Eight hits: RelativeGluingData.functor/natTrans, GlueData.sheafValGluedMk,
  LocalRepresentability.glueData and its related Zariski constructions.
  These require open immersions or Zariski scheme-gluing; none gives this node.
- Loogle: "CategoryTheory.Pseudofunctor.DescentData,
  CategoryTheory.Functor.RepresentableBy". Successful query, zero hits.
- LeanSearch: "Scheme descent data glue to a locally representable sheaf on the
  big fppf site with natural local representation comparisons". Eight hits:
  Scheme.GlueData, Zariski LocalRepresentability.glueData and related fields,
  Pseudofunctor.DescentData/ofObj/mk. These define raw descent data or glue open
  schemes; none states this theorem.
- Mathlib grep via msearch: "[Dd]escent|[Rr]epresent" in
  AlgebraicGeometry/Sites/Representability.lean. Five header hits. Read the
  actual hypotheses there: Zariski topology and open immersions, not this case.
- rg in the project's WeilConjectures and Sheaf trees:
  `SchemeCoverDescent|IsLocallyRepresentableFppf|fppf_scheme_data|scheme.*[Gg]lui|[Gg]lui.*scheme`.
  Found the dependency, its current consumers and the parent
  FppfSheafRepresentabilityDescentData.lean; read the latter in full. Its existing
  statement gives an equivalence, an unnormalized product representation, and
  an effectivity criterion. It does not specify the β equations or the
  comparison for every representative-choosing R, so it is not an exact match.
- rg for the item id and proposed declaration/module names in WeilConjectures,
  Sheaf and dag/lean_names_upstream.json returned no conflicting declaration.
  No existing match was redefined.

Validation: prescribed scompile.py compiled both the sandbox and library module
paths cleanly (2.7 s and 2.5 s respectively). The first compile diagnosed only a
syntax/API mistake: `prod.fst`/`snd` take their object arguments implicitly.
Those were changed to named arguments before the successful compile. Every
variable/universe is explicitly bound and `autoImplicit` is false. The module
contains one theorem with exactly `by sorry`; there are no definitions, hidden
sorry data, probes or extra axioms. No line exceeds 100 characters.
No node fault or STATEMENT-DISPUTED issue was found.

## Second reading by NO

A second pass in this single-worker session reread the complete node, the compiled
module, and the dependency's Yoneda encoding. No separate agent was started,
as required by the dispatcher brief; the maintainer's independent review remains
separate from this self-check.

The main checks were that e is an isomorphism of *descent data*, not just local
objects; that the two β projections fix its normalization; and that the final ε
is tied to r and e by the stated equation. Checked the composition direction:
Lean's `G ⋙ R` is the node's R∘G, and `r_i ≫ e_i` means e_i after r_i. Checked
that `β.homEquiv` maps scheme morphisms to product sections, while e.inv maps
represented local sections to global sections, so neither inverse is reversed.
Checked that r's transition and naturality conditions express exactly the chosen
representation functor in the node. Checked the passage from arbitrary T-test
maps to W over U_i by composition with the structure map and naturality along
the canonical identity-underlying scheme isomorphism. This loses no test schemes
or base coordinates. The edge cases above remain included. No mathematical
mismatch was found in this pass; the only implementation repair was the implicit
product-projection arguments reported above. No node text was changed.
