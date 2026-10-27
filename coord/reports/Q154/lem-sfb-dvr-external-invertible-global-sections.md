## Worker report

The delivery states `lem-sfb-dvr-external-invertible-global-sections` in
`Sheaf.AlgebraicGeometry.DvrExternalInvertibleGlobalSections`, with three named theorems
and `sorry` as every proof. It adds one definition node,
`def-sfb-relative-external-sections`, in `Sheaf.AlgebraicGeometry.RelativeExternalSections`.
All definitions have real data. No existing node statement was changed and no dependency
record was replaced. The item changes only in `lean` and by adding the new definition to
`stmt_deps`.

The source read is `literature/stacks-project/varieties.tex`, `lemma-kunneth`, especially the
maps preceding `equation-kunneth-on-cech` and its finite-affine-cover proof (lines 5442ff).
The source explicitly assumes a field. The node explicitly supplies its integral extension:
the two degree-zero equalizers work over a DVR because the section modules used for tensoring
are torsion-free, hence flat by Tag 0539. This is not a claim that 0BED itself proves the
integral version. I also read the recorded flat-invertible torsion-free theorem and
`Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`, the exact 0539 Mathlib match.

All names below are in `AlgebraicGeometry.RelativeExternalSections` unless qualified.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| A is a discrete valuation ring, including the domain/nonfield conditions | `(R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]`; Mathlib's DVR class extends local PID and asserts nonzero maximal ideal. Bundling R changes no ring. |
| X and Y are schemes over Spec A | `(X Y : Over (Spec R))`; their structure maps are `X.hom`, `Y.hom`. |
| X,Y quasi-compact | `[CompactSpace X.left] [CompactSpace Y.left]`, equivalent to quasi-compactness of their entire underlying spaces. No nonemptiness is assumed. |
| Structure maps separated and flat | `[IsSeparated X.hom] [IsSeparated Y.hom] [Flat X.hom] [Flat Y.hom]`. In particular there is no properness or finite-type hypothesis. |
| F,G invertible module sheaves | `(F : X.left.Modules) (G : Y.left.Modules) [F.IsInvertible] [G.IsInvertible]`. The upstream rank-one local-triviality definition implies quasi-coherence. |
| P and its projections | `(X ⊗ Y).left` in the existing cartesian monoidal structure on `Over (Spec R)` is definitionally `pullback X.hom Y.hom`. `fst` and `snd` have the existing pullback projections as `.left`. |
| Global sections with the A-module structure | `sections R X F` uses `ModuleCat.restrictScalars` along `((Scheme.ΓSpecIso R).inv ≫ X.hom.appTop).hom`. Its underlying group is exactly `Γ(F, ⊤)`. |
| External coefficient sheaf | `coefficients F G` is the existing `tensorPullback` of the two factors along the projections, tensored in the existing monoidal category of module sheaves. |
| The actual canonical external map | `dvr_external_invertible_global_sections` gives a linear equivalence `K`, and requires `K (s ⊗ₜ[R] t) = pure F G s t` for every s,t. `pure` is literally `tmulSection` of the two `pullSection` values. The formula determines K uniquely because pure tensors generate; no arbitrary isomorphism or arbitrary comparison is allowed. |
| Isomorphism | `K : (sections R X F ⊗[R] sections R Y G) ≃ₗ[R] sections R (X ⊗ Y) (coefficients F G)`. |
| Naturality for pullback of sections | `dvr_external_sections_naturality` quantifies over all over-scheme maps `a : X' ⟶ X`, `b : Y' ⟶ Y`, constructs the unique pure-tensor-normalized linear map K' for the pulled-back sheaves, and states the actual equality after `pullSection (a ⊗ₘ b).left` and the canonical `pullCoefficients` comparison. No hypotheses on X',Y' are added. |
| Naturality for scheme and sheaf isomorphisms | The same theorem allows arbitrary isomorphisms `eF : a^*F ≅ F'`, `eG : b^*G ≅ G'`; its equation includes their actual pullbacks along the new projections. Taking a,b to be scheme isomorphisms covers the stated scheme-isomorphism case. Taking identity a,b covers arbitrary isomorphisms of F,G. Taking identity eF,eG gives ordinary pullback naturality. |
| H is a flat affine A-group scheme | In `dvr_external_sections_coaction`, `H : Over (Spec R)`, `[GrpObj H] [IsAffine H.left] [Flat H.hom]`. These are genuine group objects over the specified ring; no field, connectedness, smoothness or finite-type condition is present. |
| H acts on X,Y | `[ModObj H X] [ModObj H Y]`, the existing cartesian-category action objects with unit and multiplication diagrams. |
| Linearizations with identity and cocycle | `DX`, `DY` are the existing `ActionGroupoidModel` presentations; M,N are the existing `Scheme.GroupoidModule` objects for these presentations, with `[M.moduleObj.IsInvertible]`, `[N.moduleObj.IsInvertible]`. The beta isomorphism has direction a^*F -> pr^*F; its inverse is the theta in the node. `descent` merely exposes this beta through the existing tensor-pullback interface. No coherence or finite-generation condition is imposed. |
| C=A[H] and rational coactions | C is literally `Γ(H.left, ⊤)`. `IsRational` reuses `BorelDistributions.IsCoordinateCoaction` with `H.hom` as the over structure, which in turn uses the existing canonical coordinate Hopf algebra. It asserts both counitality and coassociativity with the actual associator and counit identifications. |
| Coactions induced by the linearizations, whenever defined | `hM`, `hN`, `hQ` are `IsInduced` for the actual M,N descent and `externalDescent` respectively. Besides the rational coaction laws, `IsInduced` says for every finite tensor presentation that the coaction's section after base change is exactly beta applied to action pullback. It does not assume a base-change comparison is bijective, or substitute arbitrary coactions. |
| Diagonal action and tensor coaction | `diagonalAction` is the product lift of the two given action maps with the same H-variable. `externalDescent` is the tensor of the two given descents along that variable, using the section-normalized composition and tensor identifications. The final equality is `ρQ (K (s ⊗ t)) = ∑ i, ∑ j, K (si i ⊗ tj j) ⊗ (ci i * dj j)` for every finite presentation of ρM(s),ρN(t). This is exactly diagonal coaction compatibility. Every coaction value has such a finite presentation; linearity and generation by pure tensors give the full coaction square. |
| Empty schemes and no higher-cohomology/base-change hypotheses | No `Nonempty` instance occurs. No positive cohomology, vanishing, properness, finiteness of sections, or section-base-change isomorphism occurs in any theorem. Fin n and Fin m may be empty. |

The only sorry declarations are the three named theorem clauses, all recorded in the
item's `lean.declarations`. Their docstrings give the node's eight proof steps: affine
covers/rectangles, affine tensor calculation, torsion-free/flat sections, first and second
equalizers, pure-tensor naturality, injectivity of the group base-change comparison and the
diagonal coefficient calculation, and the empty cases. No theorem is hidden inside a
definition.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Spec`, `Spec.map`, `Scheme.ΓSpecIso`.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing` with the
  explicit additional `[IsDomain R]` required by its signature.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, equivalent to
  stalkwise flatness by `Flat.iff_flat_stalkMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.Separated` and `.QuasiCompact`: `IsSeparated` and
  quasi-compact morphism/topological conventions. `CompactSpace` renders the statement's
  quasi-compact schemes directly.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` and the module tensor category.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, the recorded general-site tensor dependency;
  the concrete scheme tensor is the already existing specialization, not a second tensor.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`; linear maps/equivalences and
  pure tensors use the existing tensor construction and universal property.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `.fst`, `.snd`.
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Over` realizes the same chosen pullback in Over.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSection`, `tensorPullbackSectionComp`.
- `WeilConjectures.AlgebraicGeometry.Modules.TensorSection`: `tmulSection` (actual
  sheafification section), using the existing sheaf tensor.
- `WeilConjectures.AlgebraicGeometry.ModulePullbackTensor`: `module_pullback_tensor`, whose
  comparison is natural and fixed on ALL local pure tensor sections; `pullTensor` selects
  that normalized comparison and does not choose a bare Nonempty isomorphism.
- `Sheaf.AlgebraicGeometry.HopfCoactionLinearization`:
  `HopfAction.affineCoordinateHopfAlgebra`, which is the canonical Mathlib instance;
  its unbundled `coordinateHopfAlgebra` specialization requires a field and is not used here.
- `Sheaf.AlgebraicGeometry.EquivariantCoherentGZero`: `source`, `target`, `identityArrow`,
  `inverseArrow`, `ActionGroupoidModel`, and `pullbackIso`. Only the general action-groupoid
  presentation is used; neither `Coherent` nor any Grothendieck group is used.
- `Sheaf.AlgebraicGeometry.SchemeGroupoidModule`: `Scheme.GroupoidModule`, with its actual
  identity/cocycle predicates and quasi-coherent underlying module.
- `Sheaf.AlgebraicGeometry.GroupScheme.AffineGroupDistributionCalculus`:
  `BorelDistributions.IsCoordinateCoaction`; its signature is over a commutative base ring,
  despite the field-specialized introductory examples in its node.

All stated proof dependencies are imported, publicly when part of the statement and with
plain `import` otherwise. The Mathlib finite cover, affine intersection and affine product
matches are supplied by `.Morphisms.QuasiCompact`, `.Morphisms.Affine`, and `.Pullbacks`
(the last is publicly available through the groupoid/action modules). Affine sections,
quasi-coherent pullback, quasi-coherent tensor sections, flat-invertible torsion-free sections,
flat tensor exactness, tensor finite products and invertible pullback/tensor comparisons have
their recorded modules imported explicitly. The general sheaf-of-modules category is reused
through `Sheaf.CategoryTheory.RingedSiteModules` and the actual scheme Modules specialization.

Edge cases checked mathematically: X or Y empty makes its sections and the product's sections
zero, and the normalized map is 0 -> 0. Empty affine intersections give zero equalizer terms.
X=Y=Spec R with trivial line bundles gives R tensor_R R -> R by multiplication. Taking one
factor Spec Frac(R) gives the localization comparison; no finite module condition is imposed.
Nontrivial positive coherent cohomology is allowed because the proof uses only flat-tensored
sheaf equalizers. Zero tensor presentations (n=0 or m=0) are allowed; counitality then forces
the corresponding section to be zero. Trivial actions and the trivial group require no
special exclusions. Scheme, ring, and module universe u is explicit throughout; any given
pair of schemes and base ring can be placed in a common universe, as in the project's scheme
module convention. No auto-bound variable is used.

Searches performed, with their actual outcomes:

- msearch leanfinder: “Over a discrete valuation ring global sections of external tensor
  products of invertible sheaves on flat quasi compact separated schemes are tensor
  products”: 8 hits about residue-field tensor products/Picard modules, no theorem here.
- msearch loogle: `"globalSections", "tensor"`: OK 0 hits.
- msearch grep: `external.*[sS]ection|[Kk]unneth`: OK 0 Mathlib hits.
- msearch leansearch: “Definitions of global sections of a sheaf of modules over a scheme
  over a commutative ring as modules over the base ring and external tensor sections”:
  OK 8 hits, ordinary sheaf sections, GammaSpecIso, tilde and module-sheaf constructions;
  no relative external-section map. Exact returned output is in the new node.
- msearch loogle: `ModuleCat.restrictScalars, TensorProduct`: OK 6 hits on scalar-extension
  identities, no relative external sections. Exact output is in the new node.
- msearch grep: `externalGlobalSections|relativeGlobalSections|IsCoordinateCoaction`:
  OK 0 Mathlib hits. Exact output is in the new node.
- msearch leanfinder: “Rational coaction on global sections induced by a group scheme
  linearization and external product of sections over a commutative ring”: 8 hits about
  ordinary group representations, not this geometric interface.
- msearch grep `linearization|IsCoordinateCoaction|external.*section` in AlgebraicGeometry:
  OK 0 hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for external sections, Kunneth,
  `externalGlobalSectionsTensor`, `Linearization`, and `IsCoordinateCoaction`: found and read
  the field-only `ScalarGlobalSectionsComparison`, its `FieldLinearModuleCohomologyOperations`
  prerequisite, and `ExternalGlobalSectionsTensorBijective`; they cannot be specialized to a
  DVR. Found and reused the general tensor-pullback, action-groupoid, and ring-base coaction
  interfaces listed above. No item-id hit in WeilConjectures.
- DAG searches and `blueprint_refs.py search external sections`, `search linearization`,
  `search relative external`, `search global sections ring`: no node for this general
  ring-base relative section/induced-coaction interface. Existing field external-section
  nodes and unrelated derived/etale sections were inspected. `blueprint_refs.py ancestor`
  reports ancestor None for the item; the new node preserves this inherited ancestry and
  prepends this item to its via chain.

Server validation: scompile.py compiled BOTH delivered modules independently in dependency
order, including sandbox and library-module modes. No errors or warnings were emitted by
either module; the three sorry declarations are expected in stage 2.

## New nodes

`def-sfb-relative-external-sections` defines the missing ring-base external-section interface:
scalar restriction of actual global sections, actual normalized pullback sections and their
external product, normalized square/tensor/external comparisons, the actual diagonal action
and external descent, and the predicate that an existing rational coaction is induced by that
descent. Source: the degree-zero formulas of Stacks 0BED and groupoid modules in 03LF. The
three required search kinds ran through msearch; exact outputs are in `mathlib_searches`.
DAG/blueprint/project searches found only the field-specific API and the more general
component notions that this definition reuses. The node cites each of those component
notions. Its primary declaration is `sections`; all owning helper declarations are listed
in `lean.declarations`. It asserts no new theorem, constructs no arbitrary map, and adds
no proof or data sorry. The already recorded `IsCoordinateCoaction` and `GroupoidModule`
definitions are USED, not redeclared. Its `import_flags` is [] as required for this reached
stage-2 definition.

## Second reading by Q154

Reopened the original node, the final Lean files and the dependency signatures for a second
clause-by-clause pass. This pass is by the assigned delivery worker; the independent
maintainer review follows delivery, as the dispatch brief specifies. No additional agent
was started.

The base really is a DVR, not a field; the original field-only external API is not silently
reused. Both actual structure maps have the separated and flat classes. No nonempty case
was introduced. Invertibility uses the upstream rank-one notion. The target is the actual
chosen product and actual sheaf tensor. The equivalence's pure-tensor equation pins the
canonical map uniquely. Naturality includes sheaf isomorphisms and arbitrary pullbacks,
with a target linear map whose normalization is asserted, so the pullback assertion is
not a conditional claim about a possibly nonexistent target map. Equivariance uses a group
object over R with actual action laws, the existing descent identity and cocycle, canonical
coordinate algebra, and coactions induced by precisely those descent isomorphisms. Its
finite double sum uses ci*dj, hence the diagonal coaction. The definition does not replace
these induced coactions by arbitrary maps or by a base-change bijectivity assumption.

The first compile found inference errors in the diagonal-action expression and the
orientation of two composition squares. Explicit action-object arguments and the correct
orientation repaired them without changing the mathematics. The final two-module compile
is clean. The only new DAG node packages the missing ring-base definitions; the item's
natural-language statement, accepted split, source, proof and proof dependencies are
unchanged. No STATEMENT-DISPUTED flag or statement correction is needed.
