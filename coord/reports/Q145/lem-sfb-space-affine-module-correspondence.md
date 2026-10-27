## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceAffineModuleCorrespondence` states
`AlgebraicGeometry.AlgebraicSpace.space_affine_module_correspondence` with a single
`sorry`. Its `AffineModuleCorrespondence` structure packages the conclusions of the
lemma, not extra hypotheses. All helper definitions have real data, using existing
Mathlib module sheaves, restriction of scalars, full subcategories and continuous-site
restriction. There are no new independent notions requiring definition nodes.

Sources read: `literature/stacks-project/spaces-morphisms.tex`,
`lemma-affine-equivalence-modules` (08AI), whose proof is omitted, and the neighboring
relative-spectrum correspondence (081V). The node's nine proof steps supply the full
chart/descent proof, reproduced in the theorem docstring. The upstream scheme result
`WeilConjectures.AlgebraicGeometry.AffineModuleCorrespondence` was also read: its
Zariski scheme sites and scheme morphisms do not state this algebraic-space result.

Hypotheses and clauses, matched against the node:

- An arbitrary scheme S is the binder `S : Scheme.{u}`; Y and X range over
  `AlgebraicSpace S`. An affine p is exactly
  `IsRepresentableWith (fun _ _ a ↦ IsAffineHom a.left) p.hom.hom`, meaning affine
  scheme base changes. No Noetherian, finiteness, separation or surjectivity is added.
- The small-etale structure sheaf, site and module category are the existing
  `structureSheaf`, `EtaleSite`, `Modules`. `CommAlgebraSheaf.moduleRing` only forgets
  commutativity from the existing algebra sheaf; `Modules` is `SheafOfModules.{u}`.
- A = p_* O_Y is `AffineModuleCorrespondence.algebra : StructureAlgebraModel p`.
  Its existing `underlying`, `projection` and `projection_structure` identify it with
  the prescribed direct image of the structure module and its ring operations.
  `algebra_quasiCoherent` states quasi-coherence of its underlying O_X-module.
- For EVERY A-module M, `quasiCoherent_iff M` is precisely Mathlib's local-presentation
  `M.IsQuasicoherent ↔ (A.moduleForget.obj M).IsQuasicoherent`. Arbitrary small local
  generators and relations are retained. The categories have Mathlib's A-linear maps.
- `equivalence : Y.QCoh ≌ A.QCModules` is the equivalence, and `additive` is additivity
  of its forward functor. `directImageIso` recovers the dependency's specified
  `moduleDirectImage p`, naturally in F. `action_projection` pins its A-action to
  multiplication after EACH compatible-chart projection. Thus neither the functor
  nor its action can be an unrelated equivalence.
- The `chart` field quantifies every affine etale V and every scheme presentation q
  of its full fibre product. `hq` is the cartesian square defining Y_U, not an extra
  restriction on p. Its e identifies that scheme with Spec(A(V)), with the ring map
  given by the existing regular-function projection. Affineness ensures these q exist.
- The natural isomorphism in `chart` identifies the inverse functor restricted to q
  with evaluation M(V), followed by `tilde.functor` and pullback along e. This is
  the associated module on Spec C. Its naturality in ALL A-linear maps says precisely
  that their corresponding chart maps are the C-linear section maps. Zariski
  restriction here is the recorded scheme/etale identification, not a new notion of
  quasi-coherence on Y. Quasi-coherent etale modules are determined by this restriction.
- `finiteFree n` is the free module clause in ambient module categories:
  F is O_Y^(n), and its corresponding algebra module is A^(n). Mathlib's `free` is
  the coproduct of the unit module. `ULift.{u} (Fin n)` is the same finite index set
  in the section universe, permitting every u and n=0 without a universe equation.
- The theorem chooses the correspondence for all affine morphisms simultaneously.
  For an arbitrary etale g:X'→X and arbitrary cartesian square it supplies the etale
  h and the quasi-coherence proof needed to form restriction on the full subcategories.
  The hp' binder merely records affineness of the base-changed map, which follows
  from hp; it excludes no base change. The ring iso e identifies A' with restricted A;
  its projection equation makes it the identity on compatible regular functions.
  `affineAlgebraRestriction` is Mathlib continuous-site restriction using e, with real
  data. `beta` is the commuting-square natural isomorphism for the equivalences;
  its final equation specifies the identity on every compatible chart section.
  Full faithfulness determines the corresponding inverse comparison and compatibility
  of the units/counits. These section identities force comparisons for successive
  base changes to compose, and include identity and non-scheme base changes.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`,
  `EtaleSite`, `structureSheaf`, `Modules`, `etaleMap`, `pullback`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  it transparently uses Mathlib `SheafOfModules`, not a second category.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and its
  slice sheafification instances. Quasi-coherence itself is Mathlib
  `SheafOfModules.IsQuasicoherent` / `isQuasicoherent` (local presentations).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `ModuleDirectImageModel`,
  `moduleDirectImageModel`, `moduleDirectImage`, `ModuleChart`, `moduleChartDiagram`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativeSpecCorrespondence`:
  `StructureAlgebraModel`, particularly its full underlying-module and projection
  normalization; the already stated proof dependency is imported.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentAlgebra`:
  `CommAlgebraSheaf`, `toModule`, `commStructureSheaf` (reused via the existing modules).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceCommAlgebraSheaf`: the full-site sheafification
  instances needed by Mathlib free modules. No auxiliary site is introduced.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`: `schemeRestriction`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction`:
  `etaleRingRestriction`, `moduleChartBaseChange`, and the proof comparison theorem.
- `Mathlib.AlgebraicGeometry.Modules.Tilde`: `tilde.functor` and the unit/counit
  declarations recorded by `lem-weil-pbc-affine-tilde-gamma-adjunction`; imported publicly
  because the chart statement uses tilde. The other stated proof dependencies are
  imported without public visibility: affine chart calculus, affine etale cover,
  fibre products, scheme Zariski/etale equivalence, affine pullback sections and the
  Mathlib left-adjoint-colimit instance. The groupoid-equivalence and kernels/colimits
  nodes have no Lean record in the read repository, so there is no module to import
  for them; they are proof dependencies, not missing statement notions.

Edge cases checked before writing: the empty scheme/space and empty charts; zero
algebra (empty inverse image), zero modules, arbitrary infinite generator/relation
sets, finite rank zero; identity p and arbitrary etale g including identities and
non-surjective maps; non-affine overlap schemes; non-Noetherian/non-separated spaces.
No nonzero-ring, Nonempty, positive-rank or finite-presentation assumption is present.
All universes and variables are explicit (`set_option autoImplicit false`). The site
object universe u+1 and section universe u remain those of the recorded dependencies.

Searches actually run:

- `msearch.py ... leanfinder "Affine morphism of algebraic spaces equivalence quasi
  coherent modules over direct image structure algebra"`: eight hits about affine
  scheme properties (including `instHasAffinePropertyIsAffineHomIsAffine`, `affineAnd`,
  `sourceAffineLocally`), no algebraic-space module equivalence.
- `msearch.py ... loogle "SheafOfModules.IsQuasicoherent,
  SheafOfModules.restrictScalars"`: zero hits.
- `msearch.py ... grep "affine.*[Mm]odule|[Mm]odule.*[Ee]quivalence"
  AlgebraicGeometry`: one hit, `Scheme.Modules.exists_affineOpenCover_presentation`
  in Mathlib's Tilde module; not the requested statement.
- `rg` over project Sheaf and upstream WeilConjectures for affine-module equivalence,
  `StructureAlgebraModel`, proposed helper names and correspondence names: existing
  scheme affine-module theorem and the algebraic-space relative Spec interfaces,
  but no statement of the requested theorem. The scheme theorem was read in full.
- Literal search for the item id in upstream WeilConjectures: no hit. Sheaf's
  `SpaceGradedCohomologyFinite.lean` names this item only in its proof docstring.
- Direct reads of Mathlib Sheaf.ChangeOfRings, Sheaf.Quasicoherent, Sheaf.Free,
  Sheaf.PushforwardContinuous and Modules.Tilde confirm that their existing
  definitions and linear natural maps are used, not privately copied.

No statement correction, dependency repair, new node, or STATEMENT-DISPUTED flag.
Compilation: scompile.py, final sandbox and library-name probes both clean (11.7 s
and 12.0 s respectively), with the single expected theorem sorry warning suppressed
by the wrapper. The initial pass exposed a scalar-carrier elaboration issue, fixed
with a typed `@id`, and Fin's index universe, fixed with ULift; no statement changed.

## Second reading by Q145

I reread the complete node, source lemma and completed module clause by clause after
compilation. The source's two assertions are the equivalence and the unrestricted
quasi-coherence iff. The node additionally spells out etale compatibility, affine
charts, maps and finite frees; each appears in the structure fields or final theorem
as mapped above. The algebra is fixed by regular-function projections, and the action
and etale comparison by their section formulas. The chart natural isomorphism covers
morphisms as well as objects. The rank-zero case uses an empty lifted Fin type.
No mathematical mismatch or node fault was found. This is the dispatch worker's
second pass; no second agent was started, in accordance with the explicit brief.
The maintainer's independent review remains the delivery's independent reading.
