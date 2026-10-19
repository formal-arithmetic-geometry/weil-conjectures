## Worker report

The module `Sheaf.CategoryTheory.SimplicialToposAugmentation` states
`CategoryTheory.CoherentSitePseudofunctor.ToposAugmentation.augmentation_morphism`.
The proof is exactly `sorry`; its docstring gives all five proof steps of the node.
The input and output structures are specification helpers for this same augmentation
statement, not replacements for the dependency's notions. No additional node is needed.
All helper definitions have real data, and no object is chosen from a postponed theorem.

Hypotheses and conclusions, clause by clause:

- The coherent simplicial site diagram is `D : CoherentSitePseudofunctor
  SimplexCategoryᵒᵖ F`, where `F : LocallyDiscrete (SimplexCategoryᵒᵖ)ᵒᵖ ⥤ᵖ Cat.{w,w}`.
  It carries the actual unitors, compositors, coverages, continuity and covering
  pullbacks required by the total-site dependency. The total site is exactly
  `D.totalTopology` on the dependency's CoGrothendieck category.
- The assumption that the transition functors are inverse images of geometric
  morphisms is `h : ∀ i j α, PreservesFiniteLimits (D.inverseImage α)`;
  the adjunctions are already `D.imageAdjunction α`. This is exactly the hypothesis
  of `totalSite_sheaf_systems`, not an extra exactness or descent assumption.
- The base category is `E : Type u`, `[Category.{v} E]`, with
  `hE : IsGrothendieckTopos.{w} E`. Universe `w` is the chosen larger set universe,
  shared with the site and its sheaf values; `u` and `v` remain independent.
- The component inverse-image functors, their right adjoints, adjunctions and finite
  limit preservation are `A.component i : GeometricMorphism (D.fibreSheaves i) E`.
  This unpacks the term “inverse-image functors” in the node.
- The coherent identifications are `A.comparison α`, with `comparison_id` and
  `comparison_comp` inserting exactly `D.inverseImageId` and `D.inverseImageComp`.
  For `α : i ⟶ j` in `Δᵒᵖ`, they identify `f_α⁻¹ a_j⁻¹` with `a_i⁻¹`.
  For the order map `[p] → [q]`, this is the corrected `f_α⁻¹ a_p⁻¹ ≅ a_q⁻¹`.
- The given total-systems equivalence is used as
  `P : D.SheafSystemPresentation`. It exists by the recorded systems theorem under
  `h`; it has actual fibre restriction and a bijection onto every compatible Hom
  family, as well as essential surjectivity onto all systems. None of its interfaces
  is copied or replaced.
- `A.system G` has components `(A.component i).inverse.obj G` and transitions
  `(A.comparison α).hom.app G`. Its identity and cocycle proofs are exactly the two
  input coherence fields. `A.systemMap f` gives the component functor maps; its
  compatibility is the existing naturality equation of the comparison.
- The theorem concludes `Nonempty (A.Result P)`. The result contains the geometric
  morphism itself, including its adjunction and finite-limit preservation.
  `fibreIso`, `fibreIso_naturality` and `fibreIso_transition` fix its inverse image
  to the canonical system on objects, arrows and every transition. Thus this is
  existence of the specified canonical construction up to its natural coherent
  identifications, not an arbitrary geometric morphism or an unspecified isomorphism.
- `A.pushTransition S α` constructs the canonical arrow
  `a_j* S_j → a_i* S_i`: transpose under the component-i adjunction the comparison
  inverse, the inverse image of the component-j counit, and `S.transition α`.
  The triangle identities identify this with the unit-of-`f_α` formula in Tag 0D70.
  The two equalizer arrows specialize this construction to
  `(SimplexCategory.δ (0 : Fin 2)).op` and `(SimplexCategory.δ (1 : Fin 2)).op`.
  These are exactly the two order maps `[0] → [1]`, viewed in `Δᵒᵖ`.
- `equalizerι_eq` fixes the equalizer embedding to the transpose of the degree-zero
  component of the total counit. `equalizer_condition` is its equalizing equation,
  and `equalizer_isLimit` is the universal property of that actual fork with point
  `morphism.direct.obj X`. This specifies the right adjoint as the equalizer including
  its canonical embedding, not just as an isomorphic object.
- `familyEquiv G X` is a bijection from maps into this equalizer to
  `D.SheafSystemHom (A.system G) (P.system X)`. These Hom objects are precisely
  compatible component families, without invertibility of transitions.
  `familyEquiv_app` fixes each component as fibre restriction of the adjoint map
  `morphism.inverse.map f ≫ morphism.adj.counit.app X`, using `fibreIso`.
  It specifies the canonical bijection, and hence its naturality in both variables.
  All systems are covered because `P` is essentially surjective, not merely systems
  with invertible transitions. Identity and cocycle laws use the dependency's
  `SheafSystem` and `SheafSystemHom` laws throughout.

Dependencies read and used:

- `Sheaf.CategoryTheory.TotalSitePseudofunctor`:
  `CategoryTheory.CoherentSitePseudofunctor`, `totalTopology`, and the actual
  CoGrothendieck total category. This is publicly imported through the systems module.
- `Sheaf.CategoryTheory.TotalSiteSheafSystems`:
  `fibreSheaves`, `inverseImage`, `imageAdjunction`, `inverseImageId`,
  `inverseImageComp`, `SheafSystem`, `SheafSystemHom`, `SheafSystemPresentation`,
  and the theorem `totalSite_sheaf_systems` whose presentation the hypothesis uses.
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`:
  `CategoryTheory.GeometricMorphism` with its `inverse`, `direct`, `adj`, `leftExact`.
- `Sheaf.CategoryTheory.Sites.GrothendieckTopos`:
  `CategoryTheory.IsGrothendieckTopos`; available through the preceding public import.
- `def-weil-size-convention` is the recorded metatheoretic convention, implemented
  by the explicit universes, not by a new declaration.

Edge cases checked before and after writing: no nonemptiness assumption on fibres,
no terminal object in the index beyond the actual simplex category, no hypercover,
properness or surjectivity assumption, and no Cartesian/invertible transition
restriction. Degree zero and both degree-one vertices occur explicitly; all degrees
and all simplicial operators occur in the coherence fields and family Hom. Empty
covering families are retained in `D`, and degenerate geometric topoi are allowed.
The two equalizer arrows can coincide (constant diagrams), with the ordinary fork
universal property still valid. The original index formula was ill-typed for unequal
fibres and is repaired below. No unresolved statement dispute remains.

Searches for an existing statement:

- `msearch.py`, LeanFinder, query “equalizer right adjoint augmentation simplicial
  topos”: eight hits, including `SimplicialObject.cechNerveAdjunction`,
  `CosimplicialObject.cechConerveAdjunction` and `SimplicialObject.augment`; these
  concern simplicial objects or Čech nerves in a single category, not the claimed
  coherent diagram of varying sheaf topoi. No exact match.
- `msearch.py`, Loogle, query `CategoryTheory.Limits.Fork.IsLimit.homIso`:
  six hits, including the generic fork Hom bijection and its naturality lemmas.
  These provide only the equalizer universal property, not the augmentation theorem.
- `msearch.py`, grep, query `augmentation.*site|equalizer.*simplicial` in
  `CategoryTheory`: no hits.
- `msearch.py`, LeanSearch, query “equalizer right adjoint for a coherent augmentation
  of a simplicial diagram of topoi”: unavailable, rate limit exceeded, recorded as such.
- `rg` in upstream `WeilConjectures/` and the project's `lean/Sheaf`, searching
  augmentation names and the node id: no upstream exact match. The existing
  `SliceSiteSimplicialAugmentation` is the specialized slice-site construction, not
  this generic augmented diagram with its equalizer and compatible-family formula.
  `TotalSiteSheafSystems` supplies the systems equivalence and is used directly.
- Name-collision searches for `ToposAugmentation`, `pushTransition` and
  `augmentation_morphism` across Mathlib, upstream and project sources found no
  preexisting declaration. The upstream declaration inventory was also consulted.

Validation: the prescribed `scompile.py` compiled the sandbox and actual module
individually, cleanly with no warnings or errors (approximately 2–3 seconds each).
The only postponed theorem is `ToposAugmentation.augmentation_morphism`.

## Statement corrected

Old statement (verbatim, also in `statement_change.old_statement`):

> Let $(\mathcal E_n,f_\alpha^{-1})$ be a coherent simplicial diagram of sites/topoi indexed by $\Delta^{op}$ [def-weil-pbc-topos] [def-weil-size-convention], with total site $\mathcal E_{\mathrm{tot}}$ constructed by [lem-trf-slice-site-total-pseudofunctor]. Let $\mathcal D$ be a topos [def-weil-pbc-topos] with inverse-image functors $a_n^{-1}:\mathcal D\to\mathrm{Sh}(\mathcal E_n)$ and coherent identifications $f_\alpha^{-1}a_q^{-1}\cong a_p^{-1}$ for every $\alpha:[p]\to[q]$. Use the equivalence of $\mathrm{Sh}(\mathcal E_{\mathrm{tot}})$ with compatible systems $(F_n,t_\alpha)$ (with arbitrary transition maps) supplied by [lem-trf-slice-site-total-systems]. Then $G\mapsto(a_n^{-1}G)_n$, with its canonical transitions, defines a geometric morphism [def-trf-geometric-morphism] from $\mathrm{Sh}(\mathcal E_{\mathrm{tot}})$ to $\mathcal D$. Its right adjoint sends a compatible system $(F_n,t_\alpha)$ to the equalizer in $\mathcal D$ of the two maps $a_{0,*}F_0\rightrightarrows a_{1,*}F_1$ associated to the two maps $[0]\to[1]$. The equalizer is characterized by the fact that a map into it is exactly a compatible family of maps $a_n^{-1}G\to F_n$; the identity and cocycle laws follow from the coherence data.

Its only incorrect formula was
`f_α^{-1} a_q^{-1} ≅ a_p^{-1}` for `α:[p]→[q]`.
For a diagram indexed by `Δᵒᵖ`, that operator gives
`f_α : Sh(E_q) → Sh(E_p)`, so its inverse image takes sheaves in degree `p`,
not degree `q`. For unequal fibres the original composite is not typed. It would
also reverse the propagation from vertices used to obtain the equalizer formula.

Stacks `spaces-simplicial.tex`, Tag 0D70, lemma-augmentation-site, clause (1)
and the displayed inverse-image formula in the proof explicitly give
`f_φ^{-1} a_m^{-1} G = a_n^{-1} G` for `φ:[m]→[n]`.
The correction changes the comparison to `f_α^{-1} a_p^{-1} ≅ a_q^{-1}`
and states the direction of `f_α`. No hypothesis or conclusion is otherwise changed;
the statement dependencies, proof and proof dependencies remain verbatim.
This is a subsidiary lemma, not the blueprint unit's own statement.

Citer audit: a full search of the DAG finds exactly one citing node,
`lem-trf-slice-site-simplicial-augmentation` (in `proof_deps` and its proof).
It **holds**: its operators `U_q → U_p` induce inverse images from degree `p`
to degree `q`, exactly the corrected comparison. Its component base-change
identifications already have this direction. No citer is edited.

## Second reading by Q41

The delivered section was a stub: no second worker was started. This section is the
maintainer reviewer's independent reading (cc review service, 2026-10-18), supplied
as the reviewer's fix. The module and node record are unchanged.

Node clauses against the Lean (verdict: all hold):

- Coherent simplicial diagram of sites indexed by Δᵒᵖ: `D : CoherentSitePseudofunctor
  SimplexCategoryᵒᵖ F`, `F : LocallyDiscrete (SimplexCategoryᵒᵖ)ᵒᵖ ⥤ᵖ Cat.{w, w}`. This is
  the recorded total-pseudofunctor interface. The total site is `D.totalTopology`. OK.
- The f_α are component geometric morphisms: `h : ∀ i j α, PreservesFiniteLimits
  (D.inverseImage α)`, with adjunction `D.imageAdjunction α`. This is exactly the hypothesis
  of `totalSite_sheaf_systems`, and nothing stronger. OK.
- 𝒟 is a topos: `E : Type u`, `[Category.{v} E]`, `hE : IsGrothendieckTopos.{w} E`. The
  definition is an equivalence with `Sheaf J (Type w)` for a small site in `Type w`, and `u`
  and `v` are free. There is no universe restriction beyond the size convention. OK.
- a_n⁻¹ are inverse images: `A.component i : GeometricMorphism (D.fibreSheaves i) E`. OK.
- f_α⁻¹ a_p⁻¹ ≅ a_q⁻¹ for α:[p]→[q] (the corrected statement): `A.comparison α :
  (component j).inverse ⋙ D.inverseImage α ≅ (component i).inverse` for `α : i ⟶ j` in Δᵒᵖ.
  Here `D.inverseImage α` sends fibre j to fibre i, as `SheafSystem.transition` shows, so
  with j = [p] and i = [q] this is the corrected formula. The unit and cocycle laws insert
  `inverseImageId` and `inverseImageComp`, in the same form as `SheafSystem`'s laws. OK.
- The systems equivalence: `P : D.SheafSystemPresentation`. It exists under `h` by
  `totalSite_sheaf_systems`. Its restriction and transition formulas pin it down, so an
  arbitrary `P` is the dependency's equivalence. Transitions are arbitrary, not invertible. OK.
- G ↦ (a_n⁻¹G)_n with its canonical transitions: `A.system`, `A.systemMap`. In `Result`,
  `fibreIso`, `fibreIso_naturality` and `fibreIso_transition` identify `morphism.inverse`
  with this system on objects, arrows and transitions. The directions typecheck and match
  Stacks. OK.
- It is a geometric morphism: `Result.morphism` with adjunction and `leftExact`. OK.
- The right adjoint is the equalizer of a_{0,*}F_0 ⇉ a_{1,*}F_1 for the two maps
  [0]→[1]: `pushTransition` at `(δ 0).op`, `(δ 1).op : op ⦋1⦌ ⟶ op ⦋0⦌`. That gives the
  arrows a_{0*}S_0 → a_{1*}S_1. Their transpose (comparison inverse, f_α⁻¹ of the counit,
  then the transition) agrees by the triangle identities with Stacks' formula, which goes
  through the unit 1 → f_{φ,*}f_φ⁻¹ and then F(φ). The embedding `equalizerι` is fixed as
  the transpose of the degree-0 counit, and `equalizer_isLimit` is the fork's universal
  property. OK.
- Maps into the equalizer are exactly compatible families a_n⁻¹G → F_n: `familyEquiv` into
  `D.SheafSystemHom (A.system G) (P.system X)`, with `familyEquiv_app` fixing the
  components. The bijection is therefore canonical and natural. OK.

Edge cases: degree 0 and both edges [0]→[1] occur explicitly. The two edge maps may
coincide, and the fork property still holds. Empty fibres and coverings and degenerate topoi
are allowed. There are no Cartesian, invertibility, properness or hypercover assumptions.
Universes: the index is in `Type 0`, the fibres are `Cat.{w,w}`, the sheaf values are
`Type w`, and `E` is in arbitrary `u v`. No variable or universe is left unbound.

Statement correction: checked against `spaces-simplicial.tex` lines 924–997. Clause (1),
"a_m ∘ f_φ = a_n for φ:[m]→[n]", and the displayed f_φ⁻¹ a_m⁻¹ G = a_n⁻¹ G confirm the
corrected direction. The old formula was ill-typed for unequal fibres. The single citer,
`lem-trf-slice-site-simplicial-augmentation`, holds: its base change W ↦ W×_{U_p}U_q for
α:[p]→[q] goes from degree p to degree q. `grep` of dag/nodes finds no other citer.

Remaining slip, for the lead (a stage-2 fix cannot edit the item's `proof`): proof step 1
of the node still reads "f_α⁻¹a_q⁻¹G ≅ a_p⁻¹G". Under the corrected statement's convention
α:[p]→[q], this should read "f_α⁻¹a_p⁻¹G ≅ a_q⁻¹G". The statement, the Lean and the Lean
proof docstring are correct; only this prose formula in the DAG proof is stale.

One definition per notion: Mathlib (`cechNerveAdjunction`, `Fork.IsLimit.homIso`), the
project's `lean/Sheaf` (`SliceSiteSimplicialAugmentation` is the specialized slice-site
node) and upstream `WeilConjectures` contain no generic augmentation theorem. The helper
structures have real data. The only `sorry` is the theorem's proof.

Compile: `nt_compile.py --json` against the side overlay gave rc 0 with no error or
warning. `TotalSitePseudofunctor` took 4.2 s, `TotalSiteSheafSystems` 4.3 s and the item
3.5 s.
