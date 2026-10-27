## Worker report

The delivery states `AlgebraicGeometry.Scheme.fppf_generator_sheafification_comparison`
in `Sheaf.AlgebraicGeometry.FppfGeneratorSheafificationComparison`. Its only postponed
proof is this theorem, whose docstring contains the node's six-step natural-language
proof with the named ingredients. No definition, helper theorem, or dependency node
is added. The mathematical statement and dependency lists are unchanged.

### Hypotheses and objects

- The base scheme is `{S : Scheme.{u}}`. The big fppf site is `Over S` with
  `fppfTopology.over S`, precisely the recorded fppf-site interface. Its objects
  have universe `u+1` and its morphisms have universe `u`. The coefficient universe
  is `max (u+1) v`; the free `v` allows every larger value universe.
- The objects `U,U'` are `{U U' : Over S}` and the S-morphism is `g : U' ⟶ U`.
  Its etaleness is `[Etale g.left]`. No surjectivity is assumed initially.
- The representables are `uliftYoneda.{max (u+1) v}.obj U` and its U' counterpart.
  Their sections are `ULift (T ⟶ U)` and `ULift (T ⟶ U')`; this is the canonical
  universe lift of the actual S-morphism sets. Restrictions are precomposition,
  and `uliftYoneda.map g` is postcomposition by g. No representable is redefined.
- `P P' : (Over S)ᵒᵖ ⥤ Type (max (u+1) v)` are the two presheaves.
  `vmap : P' ⟶ P` is their natural transformation, and `hv` says precisely
  `∀ T, Function.Injective (vmap.app (op T))`.
- `q` and `q'` have the specified representable domains; `hq` and `hq'` assert
  sectionwise surjectivity for every object of `Over S`.
- The compatibility `v q' = q h_g` is
  `hcompat : q' ≫ vmap = uliftYoneda.map g ≫ q`.
- The chosen sheafifications are arbitrary sheaves `F,F'` for the stated topology
  with units `η : P ⟶ F.obj` and `η' : P' ⟶ F'.obj`. Their hypotheses `hη,hη'`
  are exactly the universal property of def-weil-pbc-sheafification: for every
  sheaf G and presheaf map θ there exists a unique sheaf map φ with `η ≫ φ.hom = θ`
  (respectively η'). This includes arbitrary choices of sheafification and their
  units, without identifying them definitionally with Mathlib's adjunction choice.

### Conclusions, clause by clause

- `∃ α : F' ⟶ F` supplies the actual sheaf morphism. The first conjunct is
  `η' ≫ α.hom = vmap ≫ η`; the next quantifies over every other sheaf map α'
  satisfying this equation and concludes `α' = α`.
- `∀ T, Function.Injective (α.hom.app (op T))` is sectionwise injectivity;
  this conjunct is outside the `Surjective g.left` implication.
- `Surjective g.left → ...` introduces exactly surjectivity on underlying points
  for the remainder. For each `T,z`, the first existential gives an index type I,
  objects `V i`, arrows `f i : V i ⟶ T` and `a i : V i ⟶ U`. Membership of the
  underlying `Presieve.ofArrows` in `fppfPrecoverage T.left` says precisely that
  the f_i are flat, locally finitely presented and jointly surjective. The next
  equation is `F.obj.map (f i).op z = η.app ... (q.app ... (ULift.up (a i)))`,
  the specified local representative formula.
- The next universal quantifier considers EVERY such cover and EVERY choice
  of representatives, rather than only the existentially selected ones. The
  pullback `pullback (a i) g` is the actual fibre product in `Over S`. Its
  projections `pullback.fst (a i) g` and `pullback.snd (a i) g` are p_i and b_i.
  Their underlying scheme square is the same scheme fibre product over U.
- For each i the statement asserts `Etale ...left`, `Surjective ...left`, and
  `Presieve.singleton ...left ∈ fppfPrecoverage (V i).left`. These render all
  three claims about p_i (etale, surjective, singleton fppf covering).
- Membership of `Presieve.ofArrows (fun i ↦ (pullback (a i) g).left)` with
  arrows `((pullback.fst (a i) g) ≫ f i).left` in `fppfPrecoverage T.left`
  states that the composites f_i p_i are an fppf covering of T.
- The next equation applies `α.hom.app` to
  `η'.app ... (q'.app ... (ULift.up (pullback.snd (a i) g)))` and equates this
  with restriction of z along `pullback.fst (a i) g ≫ f i`. This is exactly
  `α(η'(q'(b_i))) = z|_{W_i}`.
- Pairwise overlap compatibility is written for all test objects Z and arrows
  `r : Z ⟶ W_i`, `s : Z ⟶ W_j` with equal composites to T. It equates the
  two restricted displayed sections. Taking Z to be the pairwise fibre product
  gives the node's overlap statement; conversely that statement implies this
  formulation by pulling back along the unique map to the fibre product.
- `∃! x : F'.obj.obj (op T)` gives the unique glued section, with its restriction
  along every `p_i ≫ f_i` equal to the specified lifted section, and its image
  under α equal to z. Since F' is a sheaf and the composite family is covering,
  uniqueness here also applies to any glued section without first assuming
  its image equation.
- `∃ β : F ⟶ F'` gives a natural transformation as the inverse assignment.
  `β ≫ α = 𝟙 F` and `α ≫ β = 𝟙 F'` are the two inverse identities.
  The further equation `α_T(x)=z → β_T(z)=x`, for every T,z,x, makes independence
  of the covering and representatives explicit: each glued x from any of the
  universally quantified local presentations is exactly β_T(z). Naturality is
  part of β being a sheaf morphism. The final conjunct is `IsIso α`.

### Dependency declarations read and used

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology`; `Mathlib.CategoryTheory.Sites.Over`:
  `GrothendieckTopology.over`. This is the existing slice-site interface from
  the fppf dependency's lean.note; no specialization repair is needed.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale` and
  `Etale.etale_isStableUnderBaseChange` (the latter is part of the proof plan).
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`. This dependency explicitly
  retains Mathlib's `Sheaf` and presheaf functors for the remaining components;
  the theorem uses those retained interfaces and imports its recorded module.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`,
  `toSheafify`, `sheafificationAdjunction` specify the universal property
  rendered by hη,hη'. No private sheafification notion is introduced.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; the pullbacks in the slice exist by the
  imported scheme pullbacks and Mathlib's Over construction.
- Proof imports: `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`
  (`CategoryTheory.sheafification_sections_local`) and
  `WeilConjectures.CategoryTheory.SiteCoveringsCommonRefinement`
  (`CategoryTheory.Precoverage.siteCoverings_common_refinement` and
  `siteCoverings_finite_common_refinement`). Their source signatures and
  docstrings were read. They retain the local-representative and refinement
  steps of the node's proof plan; no new hypothesis from these APIs is imposed
  on this statement.
- `lem-weil-pbc-etale-covering-base-change` has a Mathlib match rather than a
  lean record. Its matched `Mathlib.AlgebraicGeometry.Sites.MorphismProperty`
  base-change instance was read and imported as a proof dependency.

### Edge cases and scope

The empty base and empty test scheme are allowed. An empty indexing family
can cover the empty scheme; there is no Nonempty I assumption. Sheaf uniqueness
on that cover is included. U' may be empty while U is not: the unconditional
comparison and injectivity still apply, and the surjective branch is not
asserted in that case. If U is empty and g is surjective the same pullback and
empty-cover arguments apply. Identity g is included. No reducedness, finiteness,
separation, or affineness assumption is added. The representable and coefficient
universes include the entire big site, with an arbitrary further enlargement.
The arbitrary chosen units are handled by the universal property rather than
an extra isomorphism or a chosen arbitrary comparison map.

### Searches actually run

All msearch queries used group Q21 and this item id.

- LeanFinder: `Sectionwise injective presheaf map with compatible representable
  generators related by a surjective etale map yields sheafification isomorphism
  by pullback covers and unique natural gluing`. Eight hits, including
  `Presheaf.isLocallyInjective_presheafToSheaf_map_iff` and
  `Presheaf.isLocallyInjective_toSheafify`. These give generic subclaims, not
  the representable pullback-cover/gluing statement.
- Loogle: `"presheafToSheaf", "Mono"`. Three monoidal-functor hits, none matching.
- msearch grep in CategoryTheory/Sites:
  `IsSheafification|isLocallyInjective_presheafToSheaf|isLocallySurjective_presheafToSheaf`.
  Five hits, pointing to the generic local-bijection API. Read the two relevant
  declarations in LocallyBijective.lean; they do not state this node's conclusion.
- LeanSearch: `Compatible representable surjections of presheaves along an etale
  surjection induce a sheafification isomorphism with inverse by local lifting
  and gluing`. Eight hits: generic isoSheafify/unit local-surjectivity declarations,
  not an exact match.
- Project searches: `rg` for `generator.*sheafification|Generator.*Sheafification`
  in both lean/WeilConjectures and lean/Sheaf, and the item's id in
  lean/WeilConjectures. The former returned unrelated tensor/module generator
  constructions; the latter returned no match. Additional searches for
  `IsSheafification`, `uliftYoneda`, and chosen universal sheafification interfaces
  located the existing Mathlib Yoneda interface and the related quotient modules.
  None states the full comparison theorem.

The Stacks source `literature/stacks-project/groupoids.tex`, label
`lemma-quotient-pre-equivalence-relation-restrict` (Tag 045Z), was read in full.
The node explicitly abstracts that argument to the given compatible presheaf
surjections; no source correction is necessary. No STATEMENT-DISPUTED finding.

### Validation

The single delivered module compiled cleanly with the prescribed scompile.py
against the live server library. `set_option autoImplicit false` also enforces
explicit binding of all variables and universes. The dry run and final delivery
are performed by deliver2.py. Independent review is the maintainer's review as
specified by this dispatch; no independent reviewer is claimed here.

## Second reading by Q21

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
