## Worker report

The item is stated in `lean/Sheaf/AlgebraicGeometry/AlgebraicSpaceAffineCohomology.lean`
as `AlgebraicGeometry.AlgebraicSpace.affine_cohomology_edge_isIso`. Its proof is `sorry`.
The original statement, proof and proof dependencies are unchanged. Only `lean` and the
addition of the new canonical-map definition to `stmt_deps` change on the item.

Clause-by-clause reading of the item:

- The scheme S is `{S : Scheme.{u}}`; there is no assumption on its characteristic,
  finiteness, separation, or Noetherianity.
- The two spaces are `{X Y : AlgebraicSpace S}` and their actual morphism is `f : Y ⟶ X`.
  This is the recorded fppf-sheaf algebraic-space category, not a scheme specialization.
- Affineness is `hf : MapIsAffine f`, the landed affine-scheme base-change predicate.
  The supporting `affine_relativelyRepresentable f hf` supplies exactly the representability
  implied by that predicate, without a new hypothesis in the item.
- The coefficient is `F : Y.Modules` with `hF : F.IsQuasicoherent`. Modules use the recorded
  small-etale structure sheaf and Mathlib's local-presentation quasi-coherence predicate.
- Every nonnegative degree is `q : ℕ`, including zero.
- Direct image is the recorded `moduleDirectImage f`, specified by compatible sections
  on charts of the actual fibre product. Its underlying additive direct image is identified
  with the recorded representable precomposition direct image, by its normalized projection
  to the representing scheme chart, not by an arbitrary isomorphism.
- Cohomology is `Sheaf.H` of the underlying additive sheaf. `liftedAdditive` applies the
  standard exact fully faithful `AddCommGrpCat.uliftFunctor.{u+1,u}` to that sheaf. This keeps
  every original section, addition and restriction, and uses the coefficient universe of
  the recorded `representableAbelianDirectImage`; it imposes no size equality or restriction
  on S, X, Y, F. On the small affine-etale basis this coefficient lift preserves the
  injective-resolution/Ext cohomology calculation. The resulting group is the same
  cohomology of the underlying additive sheaf, with its canonical universe transport.
- The specified map is `representableCohomologyEdge`: the direct-image coefficient
  comparison, followed by exact inverse-image transport of Ext using the actual constant
  integer comparison, followed by cohomology of the actual adjunction counit. This is
  precisely the canonical Leray bottom edge. In degree zero the adjunction triangle gives
  the defining global-section identification. The conclusion is `IsIso` of this very
  additive homomorphism, packaged using `AddCommGrpCat.ofHom`.
- Neither X nor Y is treated as a terminal scheme object of its small scheme-valued site.
  Ext from the constant integer sheaf computes global topos cohomology without that error.

Declarations and modules read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its Hom category.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`,
  `EtaleSite`, `etaleTopology`, `structureSheaf`, `Modules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and its underlying
  Mathlib `SheafOfModules.IsQuasicoherent`; the two existing slice-instance theorems.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`; its public
  sheaf-cohomology import supplies the recorded `Sheaf.H` convention. This module is
  publicly imported through the existing algebraic-space module.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite`: `MapIsAffine`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `ModuleChart`,
  `ModuleDirectImageModel`, `moduleDirectImageModel`, `moduleDirectImage` and its actual
  projections. The full signature and its section-limit uniqueness were read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbelianDirectImage`:
  `RepresentableEtaleBaseChange`, `representableEtaleBaseChange`,
  `representableAbelianDirectImage`, including the square, projection and continuity fields.
- Mathlib: `Functor.sheafPullback`, `Functor.sheafAdjunctionContinuous`,
  `sheafificationAdjunction`, `toSheafify`, `AddCommGrpCat.uliftFunctor`, `Sheaf.H.map`.
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`: `Sheaf.H.mapFunctor`.
- Proof imports: `WeilConjectures.AlgebraicGeometry.Cohomology.Leray` (its public abstract
  Grothendieck spectral sequence and exact-adjunction acyclicity declarations), and
  `Sheaf.CategoryTheory.FirstQuadrantRowCollapse`, `first_quadrant_row_collapse`.
  `lem-sfb-space-affine-higher-direct-image-vanishing` has no Lean record or source module
  on the inspected base, so there is no module to import for this proof-only dependency.

Sources read: Stacks spaces-cohomology.tex, lemma-relative-affine-cohomology (0D2U)
with preceding affine higher-image vanishing (073H); sites-cohomology.tex,
lemma-apply-Leray (0733); spaces-properties.tex, lemma-functoriality-etale-site (03G2),
including the representable clause (4). The current blueprint direct-images stability
proof (3) was read in literature/blueprint/latest. No unit statement or target changes.

Edge cases checked mathematically: q=0 is the adjunction global-section identification;
f=id gives the ordinary identity via its representing squares and counit; F=0 gives zero
groups and an invertible zero-object map; empty Y and the empty algebraic space are allowed;
empty scheme base and zero section rings are allowed. Infinite local-presentation index
sets, arbitrary characteristic, non-Noetherian spaces and non-separated spaces are not
excluded. An affine base change by a nonaffine chart is representable by open gluing,
which is why representability is derived from the affine-chart predicate rather than
added to the item. No statement dispute or source correction was needed.

Searches performed before writing:

- msearch leanfinder: "An affine morphism of algebraic spaces identifies cohomology of quasi
  coherent modules with cohomology of direct image". Returned scheme-only results; no match.
- msearch loogle: `"rightDerived", "cohomology"`: no exact algebraic-space affine edge theorem.
- msearch grep: `affine.*cohomology|cohomology.*affine` in AlgebraicGeometry: 0 hits.
- msearch leansearch: "canonical direct image abelian sheaves algebraic space small etale
  cohomology comparison": scheme pushforward and general sheaf infrastructure only.
- New-node searches, with complete tool output retained in its `mathlib_searches`:
  leanfinder for canonical Leray edge on representable algebraic spaces; leansearch for
  canonical direct-image cohomology comparison; grep for
  `representableAbelianInverseImage|representableCohomologyEdge|AlgebraicSpace.*cohomology`.
  These returned general Mayer-Vietoris/sheaf and scheme declarations, no such construction.
- rg in lean/WeilConjectures found scheme-only affine-cohomology results; grep for this item
  id there found no declaration. rg in lean/Sheaf found existing base-change and module
  direct-image models, reused above; no canonical algebraic-space cohomology edge.
- rg for the proposed declaration names in both source roots: no collisions.
- DAG concept search for canonical cohomology edges: schemes, topological sites, torsors
  and hypercohomology only. The existing algebraic-space abelian-direct-image definition
  gives only base change and precomposition, so it is reused without redeclaration.
  `tools/blueprint_refs.py search 'abelian etale direct image'` returned 0 blueprint nodes;
  its ancestor command reports the inherited null blueprint ancestor for this item.

Validation: both delivered modules compiled separately in dependency order using scompile.py.
The construction took approximately 11 seconds and the item approximately 2 seconds, with
no errors or warnings other than expected sorry diagnostics. A final compile and the required
server preflight/delivery checks follow the completed docstrings and JSON records.

## New nodes

`def-sfb-space-representable-cohomology-edge` supplies the actual missing canonical edge,
not an additional vanishing or invertibility theorem. Its module is
`Sheaf.AlgebraicGeometry.AlgebraicSpaceCohomologyEdge`. It reuses the base-change and module
functors, defines their normalized comparison and the actual inverse-image/counit formula
for the edge, and supplies the supporting standard interface properties. The source is
Stacks Tags 03G2(4), 03LR, 03G8, 0732 and 0733, with affine representability from 03WF.
The DAG and Mathlib/project searches above show that the canonical edge was not already
carried by a node or declaration. The item gains this definition as a statement dependency.

The definition-node clauses match its declarations as follows: original coefficient
transport = `liftedAdditive`; small Ext groups = `etaleAdditiveHasExt`; affine
representability = `affine_relativelyRepresentable`; the recorded base-change continuity
is exposed by `baseChangeContinuous`; actual inverse image and its adjunction =
`representableAbelianInverseImage` and `representableAbelianAdjunction`; its additive and
exact properties are the three named instance theorems; the sheafified local-integer unit,
its adjoint transpose and invertibility = `representableConstantUnit`,
`representableConstantComparison` and `representableConstantComparison_isIso`; actual
representing chart = `representableModuleChart`; uniquely section-normalized comparison =
`representableModuleDirectImageComparison_existsUnique` and its selected comparison;
finally the three-step cohomology map = `representableCohomologyEdge`. Every definition
has real data, and the only choice uses existence AND uniqueness fixing all sections.
Seven supporting theorem proofs are postponed, each with its source, complete proof
explanation, and matching clause in this new definition node. There is no arbitrary map,
unnormalized natural isomorphism, or additional assumption in the affine statement.

## Second reading by Q103

A second in-thread reading was performed with both node statements and both completed
modules open. No separate worker was started, as required by the dispatcher brief;
the maintainer's independent reading remains the review of this delivery.

Checked all item binders and the precise `IsIso` conclusion against the original TeX:
S; both algebraic spaces; direction Y to X; MapIsAffine; original small-etale module;
quasi-coherence; every q including zero; canonical edge in the direction X to Y.
No hypothesis or clause differs. The extra definition is needed to name that map.
The ULift is coefficient transport, preserving the original groups, not a restriction
on the spaces or coefficients. There are no new assumptions for sheafification, Ext,
exactness or representability in the item.

Checked the new-node normalization against each definition: `square.w.symm` has exactly
the chart-triangle direction required by ModuleChart; the constant comparison is the
transpose of the explicit constant-presheaf unit, and its inverse (not its hom) is used
as the constant-source comparison for H.mapFunctor; the counit has source L_f R_f F
and target F; the module/direct-image isomorphism is fixed on every section by the
recorded cone projection. These checks found no mismatch needing a statement correction.
Initial scratch #check/#synth commands were removed. The initial exploratory HasExt
instance search was replaced by a named small-Ext interface theorem with the standard
small-affine-basis/enough-injectives proof plan, so instance search cannot stall elaboration.
The final module mode and public/proof import visibility match the brief.
