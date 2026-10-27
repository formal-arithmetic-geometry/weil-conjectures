## Worker report

Item: lem-sfb-space-completion-internal-hom. Module:
`Sheaf.AlgebraicGeometry.SpaceCompletionInternalHom`, main declaration
`AlgebraicGeometry.AlgebraicSpace.space_completion_internal_hom`.
The only postponed proof is the theorem of this node, whose docstring carries its
seven proof steps. Every helper has real data; no new independent notion or node
is introduced. No statement correction or disputed statement is needed.

Hypotheses and clauses, checked against the node and Stacks spaces-more-morphisms.tex,
lemma-completion-internal-hom (08B6), and the coherence/support paragraphs in
lemma-fully-faithful (08B9):

- The base scheme is the explicitly bound `S : Scheme.{u}`; the space is
  `X : AlgebraicSpace S`. All modules are the recorded `X.Modules` on its original
  small etale site, with section carriers in u and site objects in u+1. No universe
  equality or extra smallness assumption is introduced.
- Locally Noetherian is `hln : ∀ T : X.EtaleSite,
  IsLocallyNoetherian (X.etaleForget.obj T)`. Quasi-compactness is
  `hqc : CompactSpace (Point X.obj.obj)`; absolute quasi-separatedness is
  `hqs : IsAbsolutelyQuasiSeparated X`, the recorded affine-test condition for
  the quasi-compact absolute diagonal. These are exactly the Noetherian conditions
  accepted by the dependency's `CoherentAdicSystem` and completion functor.
- The quasi-coherent ideal is `J : QuasiCoherentIdeal X`, the existing quasi-coherent
  subobject of the unit structure module. No arbitrary ideal map is substituted.
- Coherence of each input is the explicit conjunction of `.IsQuasicoherent` and
  `∀ T, RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
  ((X.schemeRestriction T).obj M)`. In the first conjunct this is spelled out as
  implications for F and G; in the equivalence family it is the property defining
  their full subcategory. Morphisms in this full subcategory are all module maps.
- H is `completionInternalHom F G`. Its data are exactly the recorded
  `SheafOfModules.homObj` on restrictions of F,G to the existing equivalent small
  affine etale site, transported back by `X.smallModuleEquivalence.inverse`.
  The large-site `homObj` would land in universe u+1 and could not be passed to
  the recorded u-module quotient functor. This equivalent-site expression preserves
  the local module Hom notion without changing the site in the assertion or adding
  a smallness hypothesis. It is a helper transport of an existing definition,
  not an independently redefined internal Hom.
- The first conclusion says H is quasi-coherent and chartwise coherent, and
  `moduleSupport H ⊆ moduleSupport F ∩ moduleSupport G`. The recorded support is
  the geometric nonzero-germ locus, including points outside any given chart.
- `completedModuleSections J H` is the subtype of compatible families of global
  sections of the fixed `coherentAdicCompletionDiagram J` of H. It uses Mathlib's
  functor sections, hence expresses the inverse limit over ALL transition arrows.
  The index `op n` means exponent n+1, so only positive levels are present.
  Module `.sections` means compatible sections on all scheme chart objects; no
  terminal chart is assumed to exist.
- The existential maps `e F G n` are from H/J^(n+1)H to the internal Hom between
  F/J^(n+1)F and G/J^(n+1)G. The factorization equation identifies them with
  postcomposition by the quotient of G, after precomposition by the quotient of F.
  The quotient universal property makes these maps unique; this is the node's
  canonical local quotient construction, not an unspecified equivalence.
- `Φ F G` is an actual equivalence to the Hom type between the two objects of
  `coherentAdicCompletion J hln hqc hqs`, whose codomain is the recorded Coh(X,J).
  Its component equation evaluates e on the corresponding global section and
  interprets that Hom section as a module map. Thus bijectivity concerns precisely
  the canonical quotient map described in the node's proof.
- Naturality in both F and G is the displayed equality for `a : F' ⟶ F` and
  `b : G ⟶ G'`. On the left, `completedModuleSectionsMap` applies the existing
  quotient functor to `completionInternalHomMap a.hom b.hom`; the right composes
  with the two completion maps. This states the whole naturality square.
- The last equation takes a global Hom section s and any compatible family t whose
  components are its quotient sections, and identifies `Φ F G t` with the completion
  functor applied to its corresponding global morphism. Such t is determined by its
  components and exists by `AdicQuotientModel.transition`, so this is exactly the
  stated normalization. No global sections-to-Hom identification is assumed as an
  additional hypothesis: `completionInternalHomSection` restricts the section to
  the affine basis, applies the equivalence counit and upstream Hom-sections
  equivalence, then takes the fully faithful restriction functor's preimage.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- Mathlib.AlgebraicGeometry.Noetherian: `AlgebraicGeometry.IsLocallyNoetherian`.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicSpace`, `EtaleSite`,
  `etaleForget`, `structureSheaf`, `Modules`.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: `QCoh`, built from
  Mathlib `SheafOfModules.IsQuasicoherent` and its slice instances.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations: the canonical
  `ModuleDirectImageModel`, `moduleDirectImage`, `moduleTensorPullback`, and
  `moduleTensorAdjunction`; imported publicly through the adic-system interface.
- Sheaf.AlgebraicGeometry.CoherentFiniteType: publicly exposes the exact
  `RingedSpace.IsCoherent`, `SheafOfModules.IsQuasicoherent` and `IsFiniteType`.
- Sheaf.AlgebraicGeometry.SpaceCoherentAdicSystem: `AdicQuotientModel`,
  `adicQuotientModel`, `coherentAdicCompletionDiagram`, `coherentAdicCompletion`.
  Their full signatures and projection-normalized universal properties were read.
- WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom:
  `SheafOfModules.homObj`, `homObjMap`, `homObjSectionsEquiv`.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel:
  `smallModuleRestriction`, `smallModuleEquivalence`, `smallEtaleInclusion`,
  `smallStructureSheaf`. This existing node was added to stmt_deps for transport.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport: `moduleSupport`.
  Its existing node was added to stmt_deps for the support conclusion.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal: `QuasiCoherentIdeal`.
  Its existing node was added to stmt_deps for the ideal binder.
- The metatheoretic size-convention dependency has no declaration: its record says
  to express sizes directly. The module declares universe u and every binder.

All already recorded proof-dependency modules are imported as plain imports:
SchemeZariskiEtaleQuasiCoherentEquivalence, CoherentLocalFinitePresentation,
CoherentSheafHom, StalkInternalHomFinitePresentation, AlgebraicSpaceEtaleChartSupport,
CompletionInternalHom, QuasiCoherentTensorProductAffineSections,
Modules.QuasiCoherentCokernelImage and AlgebraicSpaceRepresentableEtaleSchemeTests.
Modules used publicly are not repeated as proof imports. The two comparison proof
nodes lem-sfb-scheme-etale-tensor-hom-comparison and
lem-sfb-scheme-etale-module-exact-finiteness-comparison currently have no usable Lean
record, so there is no module of theirs to import; they remain in the seven-step
proof docstring. They are not statement prerequisites for this node.

Edge cases checked before the statement: empty X; F=0; G=0; J=0 (constant quotient
system and ordinary global Hom); J=O_X (all positive quotients zero, singleton Hom
and section limits); nilpotent J (eventually constant system); n=0 means exponent
one; no surjectivity assumed for individual test charts; no Noetherian assumption
on arbitrary overlap schemes (refine overlaps by Noetherian affine opens).
The transport preserves the zero and empty cases as an equivalence. No finite-type
or properness condition on X over S, or condition on J's support, is imposed.

Searches for an existing statement:

- msearch.py leanfinder: “Hom of coherent adic completions is the inverse limit of
  global sections of completed internal Hom on an algebraic space”. Eight hits,
  condensed Hom and scheme Gamma/Spec formulas; no adic algebraic-space theorem.
- msearch.py leansearch: “Internal Hom of coherent completions as inverse limit of
  global sections of sheaf Hom”. Eight hits: sheafHom, sheaf Hom types, global-section
  universal properties and condensed closed structure; none states the node.
- msearch.py loogle: `SheafOfModules.homObj, AdicCompletion`. Zero hits; homObj is
  unknown to the Mathlib index because it is upstream, not Mathlib.
- msearch.py grep: `completion.*[Hh]om|[Hh]om.*completion` in
  RingTheory/AdicCompletion. Sixteen ring-completion map hits; no sheaf theorem.
- rg on Mathlib, lean/WeilConjectures and lean/Sheaf for completion/Hom, small-Hom
  transport and the chosen declaration names. Found the scheme theorem
  `AlgebraicGeometry.completion_internal_hom_bijective`, which assumes a scheme and
  uses that scheme's ideal and formal-module system. It cannot state this result
  for general algebraic spaces. Found and reused the small-site equivalence and
  support API. No existing space-completion internal-Hom statement was found.
- grep -rn of the item id in lean/WeilConjectures: no occurrence. rg of the item
  id in literature/blueprint/latest/blueprint: no occurrence (this is an auxiliary
  node sourced directly to Stacks). No duplicate chosen names in the DAG upstream
  name index, Mathlib, project or upstream source.

Validation: scompile.py compiled the complete file in both sandbox and library
module mode, with no errors or warnings, under the default per-file 60 second
limit. No global build, direct Git command or shared-source edit was performed.

## Second reading by NF

The dispatcher explicitly prohibited starting other agents; this is a separate
self-reading, not a claimed independent worker review. The maintainer's independent
review remains the next review. Reopened the node, its source, dependency definitions
and final module and checked each clause against the list above. The first compile
exposed only elaboration issues: functor sections needed an explicit type/coefficient
ring, and naturality binders needed their full subcategory type. Those were repaired.
The normalization uses a component-specified compatible family rather than introducing
an extra helper theorem. No mathematical hypothesis or conclusion was changed.
Checked the orientation: Hom is F to G, the factorization precomposes by q_F and
postcomposes by q_G, and naturality sends v to b v a. Checked the exact ordinary
adic system rather than any derived or pro-object completion. Every existential
map is normalized by the quotient/component equations. No mismatch found.
