## Worker report

This is a stage-2 statement delivery, not a re-split. The current item has no Lean record
and occurs in coord/queue.tsv at stage 2. Q05's accepted 2026-10-23 split is preserved in
full: statement, eight proof steps, proof dependencies and every other field remain
unchanged. Only lean is attached and the definition node below is added to stmt_deps.
The inherited unchanged-item rejection concerned the previous stage-1 attempt and does
not prohibit this stage-2 handoff (brief-stage2 §0). No repair note was present.

The main module is Sheaf.AlgebraicGeometry.FinitePresentationAffineLimitChartModels.
Its primary theorem is
AlgebraicGeometry.exists_finitePresentation_affine_limit_chart_models.
The helpers fpLimitChartProjection and HasFpLimitChartModel only package the restricted
projection and clause (3) of this same node; they contain real data/formulas, no sorry.
The only sorry is the primary theorem, with the complete accepted eight-step proof
in its docstring. All variables/universes are explicit; autoImplicit is false.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Small nonempty directed set: I : Type u, Preorder I, Nonempty I,
  IsDirected I (· ≤ ·). A preorder avoids imposing antisymmetry; Fin K.size is
  just a numbering of the finite labelled collection, with no restriction on its size.
- Inverse system of schemes: D : Iᵒᵖ ⥤ Scheme.{u}; its maps are exactly p_ji.
  The indexed IsAffineHom instance states affineness of every transition.
- Every stage quasi-compact and quasi-separated: indexed CompactSpace and
  QuasiSeparatedSpace instances. The latter is Mathlib's absolute scheme notion,
  equivalent to QuasiSeparated (terminal.from _); no separatedness is assumed.
- Scheme limit and universal projections: c : Cone D, hc : IsLimit c; S is c.pt
  and p_i is c.π.app (op i). This accepts any supplied limiting cone.
- Prescribed initial stage: i₀ : I and the conclusion's i₀ ≤ i.
- F a finitely presented O_S-module: F : c.pt.Modules, hF : F.IsFinitePresentation.
  The module category is Mathlib SheafOfModules on the ringed scheme, and its
  IsFinitePresentation means local finite generators and relations. Quasi-coherence
  of F is not added as a hypothesis; it follows from finite presentation.
- Choice and existence of the finite affine collection: first conjunct
  ∃ K C, K.Valid C asserts existence. The second conjunct quantifies over every
  K, C and proof of K.Valid C, so this does not merely choose one convenient cover.
  The shape includes main, pair, overlap, triple, subordinate and incidence labels.
  Valid includes affineness, all four covering equations, three containing pair
  charts for each triple chart, and every explicitly recorded inclusion.
- Clause (1): existential Ci gives all C_d,i simultaneously; K.Valid Ci asserts
  exactly the same affine/covers/subordination/incidence equations at stage i.
  Each h : p_i ⁻¹ᵁ Ci d = C d is the actual open equality, not an abstract iso.
- Clause (2): opensDiagram D (op i) (Ci d) is Mathlib's actual restricted diagram
  indexed by Over (op i). For a preorder this is the directed tail j ≥ i with its
  unique structural arrow, so no stages/maps are omitted or changed. The indexed
  IsAffine clause says every C_d,j is affine. IsLimit (opensCone ...) gives its
  limit with actual restricted projections. The cone vertex is the inverse image
  p_i ⁻¹ᵁ Ci d, equal to C d by h. Scheme.Γ.mapCocone (opensCone ...).op applies
  global sections contravariantly to those same maps, and its IsColimit asserts
  exactly the canonical coordinate-ring colimit, not an arbitrary ring isomorphism.
- Clause (3): HasFpLimitChartModel f U V h F unfolds to a module N on V.toScheme,
  N.IsFinitePresentation and N.IsQuasicoherent, and an isomorphism e from the actual
  tensorPullback of N along f.resLE V U h.ge to F.restrict U.ι.
  The restriction of F uses Mathlib's open-immersion restriction, not another
  pullback functor. The restricted arrow is the canonical q_d.
  θ is a Γ(U.toScheme, ⊤)-linear ModuleCat isomorphism with source extendScalars
  q_d.appTop.hom applied to the global sections of N. This is precisely
  Γ(C_d,O) tensor over Γ(C_d,i,O) Γ(C_d,i,N). Its target is Γ(F|C_d,top),
  canonically the sections Γ(C_d,F) by Mathlib's restrictAppIso.
  The equation for all b and s fixes θ(b tensor s) to Γ(e)(b • pullbackSection(s)).
  tensorPullbackSection is the actual section 1 tensor s, so this specifies the
  canonical tensor-pullback sections comparison followed by Γ(e). An @id supplies
  its global-sections type, since the inverse image of top is definitionally top.
  Thus θ is not an unrelated choice of scalar-extension isomorphism. No maps or
  gluing conditions between distinct N_d,i are asserted.

Dependency declarations read and used:

- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme, AlgebraicGeometry.Scheme and
  Scheme.Hom (the universal Scheme category and morphisms).
- pqf-def-affine-morphism: Mathlib.AlgebraicGeometry.Morphisms.Affine,
  AlgebraicGeometry.IsAffineHom (affine inverse images of all affine opens).
- def-weil-pbc-quasi-compact-scheme: Mathlib.Topology.Defs.Filter, CompactSpace.
- def-weil-quasi-separated-morphism:
  Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated, AlgebraicGeometry.QuasiSeparated;
  its absolute realization is QuasiSeparatedSpace, as the recorded mathlib_match says.
- def-weil-sheaf-of-modules-category: Sheaf.CategoryTheory.RingedSiteModules,
  CategoryTheory.ringedSiteModules, the transparent abbreviation of SheafOfModules.
  Scheme.Modules is the exact scheme specialization of that same Mathlib category.
- def-pc-module-pullback: Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction,
  AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction,
  tensorPullbackSection, tensorPullbackSectionComp; tensorPullback itself is the
  existing functor in WeilConjectures.AlgebraicGeometry.TensorPullback, publicly
  imported by the recorded module. No second pullback construction is made.
- pqf-def-coherent: Sheaf.AlgebraicGeometry.CoherentFiniteType,
  AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType, transparently a conjunction
  of Mathlib IsQuasicoherent and IsFiniteType. This item requires finite presentation
  and quasi-coherence separately; the theorem uses those Mathlib constituents, without
  confusing coherent with finitely presented or imposing finite type instead.
- New definition: Sheaf.AlgebraicGeometry.FiniteAffineRefinementCollection,
  AlgebraicGeometry.FiniteAffineRefinementShape and its Valid predicate.

All available proof-dependency modules are imported, without public when only used by
the future proof. Mathlib geometric leaves use AffineTransitionLimit and its imports.
The non-Mathlib inputs are LimitAffineTransition, QuasiCompactOpenIntersection,
QuasicoherentFiniteTypeAffine, FinitePresentationColimit,
FinitePresentationAffineSectionsRealization, TensorPullbackFinitePresentation,
and ModulePullbackAffineSections. The last is public because the clause-(3)
sections comparison and change-of-scalars language is part of the public interface.

Edge cases checked before writing: singleton I; directed preorders with equivalent
indices; empty schemes and empty finite collections (K.size = 0); empty pair, overlap
and triple intersections; empty affine charts/zero coordinate rings; the zero module;
repeated labelled opens; non-separated qcqs schemes (overlaps are not assumed affine);
non-flat and non-injective transitions. Empty covers are finite suprema over empty
finsets, so equality with bottom is exactly enforced. The theorem asserts eventual
stage cover equations even when the limit is empty; it does not infer covers merely
from their inverse images. Every supplied finite collection can be numbered, and
unused labels are allowed. The total subordinate function has no obligation outside
triple labels and is empty when there are no labels. No hypothesis requires flatness,
Noetherianity, an affine base, or a prechosen global model. No statement correction
or STATEMENT-DISPUTED issue was necessary.

Searches actually made with msearch.py: LeanFinder for simultaneous finite affine
chart/module descent returned affine-open descent, affine-limit cover and scheme-map
factorization lemmas, not this result. Loogle for AlgebraicGeometry.Scheme,
IsAffineOpen, IsLimit returned no hits (unknown unqualified IsAffineOpen). LeanSearch
for finite affine covers with pair, overlap and subordinate triple refinements returned
ordinary affineOpenCover/AffineOpenCover and the qs affine-cover criterion. LeanFinder
for finite affine covers with overlap and subordinate triple refinements returned
OpenCover.affineRefinement and ordinary covers, not this package. Mathlib grep for
exists.*chart.*model|chart.*collection|finite.*affine.*refinement in AlgebraicGeometry
returned zero hits. The successful required three kinds are recorded in the new node.
Direct rg of WeilConjectures and Sheaf found no tag/name match for this item and no
FiniteAffineRefinementShape. Existing FinitePresentationAffineChartSectionsModel,
FinitePresentationAffineChartModels and FinitePresentationLocalOverlapModels concern
a fixed affine-base setting and do not assert simultaneous arbitrary chart/cover
stabilization. AffineLimitChartDiagrams assumes charts already at a fixed stage and
specific ring maps; it does not define our chosen finite refinement collection.
DAG search for finite affine collections/pair-triple refinements found this item,
its parent and overlap-cocycle consumer, with no existing definition node.
blueprint_refs.py search 'finite affine refinement' returned zero; ancestor returned
lem-trf-local-term-locality. The current latest blueprint ancestor statement/proof and
sk-i-curve-zero unit were read. This is a generic inherited supporting limit tool;
it changes none of the trace-formula unit statements or proof route.

Validation: both delivered files compiled separately in dependency order using
scompile.py, in both sandbox and library module modes, with no errors or non-sorry
warnings. Initial elaboration errors (resLE argument order and the global-section type
of tensorPullbackSection) were repaired before this clean result.

## New nodes

The definition node def-trf-finite-affine-refinement-collection packages the exact
finite labelled affine chart choices, all four levels of covering equations, triple
subordination and specified inclusions in the item's first two paragraphs. Its two
real structures are FiniteAffineRefinementShape and FiniteAffineRefinementShape.Valid;
there is no existence or descent theorem in this definition node. Source: Stacks 01ZR
first proof's Zariski gluing preparation, with finite affine refinements from 01IT/01KO.
Mathlib already supplies individual affine covers and refinements, which are reused
as opens and affineness, but supplies no single finite labelled collection with these
pair, overlap, subordinate-triple and incidence equations. The searches and specific
DAG/blueprint/library checks above justify this definition. It is directly cited in
the item's stmt_deps; its only notion dependency is def-pc-scheme. No dependency-module
repair is required, and no existing definition is replaced.

## Second reading by Q125

No second worker was started: the dispatcher explicitly forbids it. The maintainer's
independent review reads this delivery. I reread both source modules against the node:
all hypotheses and clauses are matched above, including existence of the collection,
subordinate triple charts, canonical ring maps, θ's pure-tensor formula, and empty
covers. The initial compile errors were fixed without changing the natural-language
statement, its split, or its proof dependencies.

Dry-run metadata repair: the live server has a longer ancestry via than the read clone.
The new definition uses the complete live ancestry printed by preflight. Preflight also
requires import_flags on a new node; an empty list was supplied as requested.
