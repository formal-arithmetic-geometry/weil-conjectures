## Worker report

Stage 2 repair, Q31, lem-sfb-ringed-site-picard-h1-natural, following the independent
review of returned head 6b5baa38cf48. The accepted item statement, theorem signature,
and mathematical definitions are preserved. The saved packet passed its initial dry
run, but still contained the duplicate interface identified by the independent review;
this repair removes that duplication and the forbidden landed-record rebind.

The theorem is CategoryTheory.RingedSitePicard.picard_h1_natural in
Sheaf.CategoryTheory.Sites.RingedSitePicardH1Natural. Its only proof is sorry. All helper
definitions contain real data; structures specify normalized presentations, and their
existence is part of this theorem, never an additional hypothesis. In particular no
object is chosen from a bare Nonempty theorem and no arbitrary map replaces pullback.

Source read: literature/stacks-project/sites-cohomology.tex, lemma-h1-invertible (040E),
lines 521 onward, and lemma-torsors-h1 (03AJ), lines 291 onward. The latter describes
the extension whose fibre over 1 is the torsor and whose boundary is its class. The
former describes frames by sections inducing an isomorphism on the slice. Its raw
quotient need not be a module before sheafification; the accepted split's repair of
that issue is retained verbatim in the proof docstring. No change to a blueprint unit
or the item's statement is made.

Clause-by-clause correspondence:

- Sites C,D small relative to the sheaf universe: independent uC,vC,uD,vD,w, Category
  instances and EssentiallySmall.{w}. J,K are their Grothendieck topologies. Neither
  has a terminal-object assumption. HasSheafify, the slice weak-sheafification and
  locally-bijective instances, and HasExt.{h} make explicit the existing categorical
  constructions; these are available for sites small relative to w and a sufficiently
  large Ext universe. They impose no geometric conditions or coefficient flatness.
- A,B commutative unital ring sheaves: Sheaf J/K CommRingCat.{w}. ring A/B is exactly
  their image under forget₂ CommRingCat RingCat, so ringedSiteModules uses the recorded
  general-site module category without a copied module notion.
- A line is locally isomorphic to the ring sheaf: Line A is the subtype of actual
  module sheaves satisfying the existing SheafOfModules.IsInvertible, defined in
  WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree. I read its
  full definition and IsInvertibleData: local generating families are Unique and
  the maps from the rank-one free sheaves are isomorphisms. No locally-ringed
  assumption is used.
- Pic(A) consists of isomorphism classes: lineSetoid relates two actual lines exactly
  when their module objects are isomorphic; Pic is its root Quotient and lineClass
  is Quotient.mk. Comparison.group is an abelian group structure on that exact
  quotient. IsComparison specifies zero by the unit module and addition by the
  existing sheafified tensor, including existence of line representatives for
  tensor products. The additive notation represents the tensor group law.
- A^× is U↦A(U)^×: units is sheafCompose of the existing
  CommRingCat.unitsAddCommGrp. Its underlying values are Additive of actual units;
  unitValues is their actual inclusion into the ring sheaf. Units preserve limits.
- Cohomology is derived global sections: Sheaf.H is Mathlib Ext from integers J,
  the sheafified constant ULift ℤ. Hom from these integers is global sections, or
  Hom from the final set sheaf, without a final site object. If a site object is
  final this agrees with evaluation by the existing constantSheafAdj/H.equiv₀.
- Canonical group isomorphisms c_A,c_B: Comparison.comparison is an AddEquiv on the
  actual quotient to Sheaf.H (units A/B) 1. IsComparison additionally requires
  GeneratorTorsor and GeneratorExtension for every line and fixes its image by
  E.exact.extClass for every such extension. This is the boundary of the identity
  section 1, not merely an unspecified group isomorphism.
- The sheaf of generators Isom_A(A,L): Frame M U consists of sections s such that
  r↦r·s|V is bijective for every V→U. These are exactly linear isomorphisms on the
  slice, by evaluation at 1. GeneratorTorsor gives natural equivalences with these
  frames and specifies the action by actual unit multiplication. The reused
  Sheaf.Torsor records the group action, local inhabitation and sectionwise simple
  transitivity, equivalently G×T→T×T is invertible.
- Arbitrary ringed-topos morphism f: the universally quantified landed interface
  has inverse, direct, their adjunction, finite-limit preservation, structural ring
  map and all ring identities, plus the induced module direct image normalized by
  the displayed generalized-element scalar equation. The A/B order is reversed in
  its arguments because its first argument is the source ring (B).
- f*L = B tensor_{inverse A} inverse L: the conclusion supplies a functor F, its
  adjunction to f.modules, a transported ring AI, an existing AlgebraicInverseImage
  I and c:AI→B whose underlying map is f.ringMap, and an isomorphism of every F(M)
  with changeOfRingsOfUniverses c (I.modules.obj M). The latter is explicitly the
  sheafification of the sectionwise ModuleCat.extendScalars tensor, with independent
  site universes. The specialized AlgebraicInverseImage is publicly available from
  the recorded AlgebraicInverseImageOfUniverses module and is used only at equal
  ring/module coefficient universes w; this does not equate any site universe.
- f*L is a line: for every M:Line A, a N:Line B is supplied with N.val ≅ F.obj M.val.
  Because the quotient identifies precisely module isomorphisms, this is independent
  of the chosen representative N.
- rho is induced by the structural ring map: IsStructuralUnitsMap is equality of
  actual underlying-sheaf maps from inverse A^× to B, via unitValues and f.ringMap.
- The inner H1 pullback uses the specified resolutions and is independent of choices:
  CohomologyTransport supplies the normalized abelian inverse image, its exactness,
  and its integer-sheaf comparison preserving the global 1. pullback is the actual
  Ext.mapExactFunctor followed by precomposition with that comparison.
  ComputesByResolutions P (units A) quantifies every injective resolution I,T,
  asserts existence of beta under inverse A^×, and for every such beta and every
  global degree-one cocycle a:Z→I¹ requires the resulting class to be that of
  Z→inverse Z→inverse I¹→T¹. This is exactly the adjunction-unit/global-section
  adjunction/beta composite: under Hom(Z,-), inverse-image transport of a section
  is the adjoint of its unit followed by direct image, and P.one fixes 1.
- Naturality equation: cB.comparison (lineClass N) = Sheaf.H.map rho 1
  (pullback P 1 (cA.comparison (lineClass M))). This is the node's displayed equation
  in its stated order. No flatness assumption occurs anywhere.

Dependency declarations used (full signatures and docstrings were opened):

- def-weil-size-convention: metatheoretic lean.convention; universes and
  EssentiallySmall are explicit.
- def-weil-pbc-sites-and-cohomology: Sheaf.CategoryTheory.SiteCoveringAxioms,
  CategoryTheory.Precoverage.IsSiteForCoverings; Mathlib Sheaf.H and H.map for the
  topology-dependent sheaf/cohomology components retained by its record.
- def-weil-sheaf-of-modules-category: Sheaf.CategoryTheory.RingedSiteModules,
  CategoryTheory.ringedSiteModules (transparent SheafOfModules abbreviation).
- def-weil-pbc-ringed-topos-morphism: its landed record remains unchanged.
- def-pur-ringed-topos-morphism-of-universes: Sheaf.Paper.SequenceSiteCompletionProjection,
  CategoryTheory.RingedToposMorphismOfUniverses. Its full fields agree with the former
  duplicate interface; this owning node is now cited by the Picard-data definition.
- def-pur-sheaf-tensor-product: Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses,
  SheafOfModules.cochainModulesMonoidal, and publicly imported
  SheafOfModules.changeOfRingsOfUniverses from TensorProductOfUniverses.
- def-trf-abelian-inverse-image-presentation: its recorded AbelianInverseImagePresentation.
- def-weil-pbc-algebraic-inverse-image: its recorded AlgebraicInverseImageOfUniverses module
  publicly retains AlgebraicInverseImage, the same coefficient-universe specialization.
- Existing general-site torsor: WeilConjectures.CategoryTheory.Sites.Torsor,
  CategoryTheory.Sheaf.Torsor. Its classH1 classifier is NOT used because it requires
  a final site object; the item's proof still cites its unstated arbitrary-site
  classification prerequisite lem-sfb-site-abelian-torsor-h1.

Proof-only imports retain every stated proof prerequisite: geometric inverse image
exactness, inverse-image local families, geometric module construction, the sectionwise
sheafification criterion, Mathlib adjoint-colimit preservation and sheafification
(already imported by the data module). The two genuine proof prerequisites
lem-sfb-site-abelian-torsor-h1 and lem-sfb-topos-cohomology-pullback-delta have no Lean
record, so there is no module to import yet. They are not extra assumptions or chosen
maps: the theorem states its own full comparison and resolution formula and its proof
is postponed. Stage 3 can use them when their modules are recorded.

Edge cases checked mathematically before writing: zero ring (its unique module is still
rank one locally, units and Pic are trivial); empty site and empty covers; sites without
any final object (integers/final sheaf used throughout); identity morphism (usual
comparison and scalar tensor); nonflat ring maps such as Z→Z/2 (rank-one pullback remains
free); independent object/Hom universes and the essentially small-site presentation.
A generator presheaf can have empty values; no module operations are assigned to it.
The normalization requires extensions for every line, so it is not vacuous.

Searches actually run: msearch.py LeanFinder, Loogle, Mathlib grep and LeanSearch. Exact
queries and result lists are in the new node's mathlib_searches. LeanFinder returned ring
Picard groups, Loogle only PresheafOfModules.instIsNormalEpiCategory, Mathlib Sites grep
returned no hit, and LeanSearch returned ring Picard and SheafOfModules.unit. Project
rg found GmPicard/UnitsTorsor (schemes only), general IsInvertible and the existing torsor.
rg for the item id in WeilConjectures and Sheaf returned no match. DAG grep and
blueprint_refs.py search found no definition node for the new presentation. No exact
existing theorem covers this item. No STATEMENT-DISPUTED flag or source-based correction
is needed.

Validation: both retained files are compiled separately via scompile.py, with supplied
modules in dependency order. An initial expensive transparent tensor abbreviation
caused kernel checking of the large Comparison structure to exceed the limit; tensor
is now an ordinary definition, and the normalization predicate is defined separately.
The 60-second limit is unchanged. Only the theorem has sorry; no diagnostic #check,
profiler option, local notation or private helper remains.

## New nodes

`def-sfb-ringed-site-picard-data` owns RingedSitePicardData.lean. It packages the actual
line quotient, frames, generator-extension normalization, tensor group and cohomology
transport predicates needed to state the item. It asserts no existence theorem; the
item asserts existence. Sources are 040E, 03AJ, 00YV and 03D2/03EK. Search results above
exclude an existing general-site composite, while existing IsInvertible, Torsor, tensor,
Ext and algebraic inverse-image notions are reused. The arbitrary-site torsor-classifier
and cohomology-pullback lemma are proof results, not replacements for these definitions.

## Returned-review repair

H13/H9/H4, returned immutable head 6b5baa38cf48: removed the delivered module
Sheaf.CategoryTheory.RingedToposMorphismOfUniverses and removed the sandbox copy of
def-weil-pbc-ringed-topos-morphism.json. The established record continues to point at
CategoryTheory.RingedToposMorphism in Sheaf.CategoryTheory.RingedToposMorphism; its
consumers require no adaptation. RingedSitePicardData now publicly imports
Sheaf.Paper.SequenceSiteCompletionProjection and reuses its existing
CategoryTheory.RingedToposMorphismOfUniverses. I read the landed structure and its
owning def-pur-ringed-topos-morphism-of-universes node: it retains the same fields,
independent site universes, structural ring identities, induced module direct image,
and generalized-element scalar identity. The new Picard-data node cites that owner
in its statement and stmt_deps. No dependency module or dependency-record rebind is
included in this repaired delivery. The independent reviewer accepted the item
mathematics clause by clause; the theorem signature and its only sorry are unchanged.

The imported semilinear-system `hasDerived` instance is disabled locally in the data
module, as authorized in the return, to avoid irrelevant derived-module instance
search when elaborating abelian sheaf cohomology. This imposes no additional hypothesis. The module also opens the landed
CategoryTheory scope, selecting its existing high-priority sheaf-composition instances
instead of repeated searches for generic limit-preservation instances. Compilation with that instance enabled first
timed out at the unchanged 60-second limit, including server confirmation.

## Self-check by Q31

Read the current landed interface and owner node, both retained Lean files, and the
item and new definition node together. The only interface change is reuse of the
existing declaration through its owning module. All Picard quotient, tensor-law,
generator-torsor/extension, integer normalization, resolution formula, structural
units map and module-adjunction clauses are unchanged. The item node differs from
current main only in lean and the added data definition in stmt_deps. The new data
node cites every definition id named in its statement, including the landed universe
generalization. Both Lean files bind their universes explicitly, disable autoImplicit,
and stay within 100 columns. Exactly one sorry remains, the item's named theorem.
This is the author's self-check; the maintainer supplies the independent review.

Final server compilation succeeded for both retained modules (56.1 seconds for
RingedSitePicardData and 23.2 seconds for RingedSitePicardH1Natural), at the unchanged
60-second limit. Standard constructor-generation options are disabled in the data
module, following the imported interface module, to avoid generating unused helpers.
Temporary profiling and diagnostic options have been removed. The final declaration
signatures match both lean.statement records exactly.

## Second reading by Q31

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
