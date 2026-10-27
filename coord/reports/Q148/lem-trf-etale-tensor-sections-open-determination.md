## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleTensorSectionsOpenDetermination` states
`AlgebraicGeometry.Scheme.Modules.etaleTensorSections_open_determination`, with `sorry`.
It states the accepted stage-1 node without changing its mathematical statement or proof.
The earlier dispatch ending concerned a stage-1 unchanged-split gate; the current node has
no Lean record and is in the stage-2 queue. The current brief's stage-handoff paragraph
explicitly permits this statement delivery. There is no repair note for the item.

The source was read at `literature/stacks-project/descent.tex:2300-2366`: Stacks 070S,
lemma-compare-sites, gives tensor sections for arbitrary modules and omits proof (2).
The six-step uniqueness argument is the accepted agent-supplied intermediate argument,
not a proof claimed to be printed in Stacks. Its whole argument is in the theorem docstring.

Hypothesis and clause correspondence:

- A scheme T is `(T : Scheme.{u})`; all etale test objects are `T.Etale`, equipped with
  `T.smallEtaleTopology`. No test-object universe is made smaller than T's universe.
- The ring presheaf is written using existing functors:
  `(Scheme.Etale.forget T ⋙ Over.forget T).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat`.
  Its value at `op V` is exactly the ring `Γ(V.left, ⊤)`; its restriction along g is
  pullback of regular functions by `g.left`. This is the usual etale structure ring,
  without replacing its section rings by an abstract ring or another topology.
- An arbitrary Zariski O_T-module M is `(M : T.Modules)`. The ordinary Zariski site is
  the opens-site used by this existing definition. No quasicoherence instance is present.
- An arbitrary sheaf G of modules on the small etale site is unpacked as a presheaf
  `G : PresheafOfModules.{v} (...)` and `hG : Presheaf.IsSheaf T.smallEtaleTopology
  G.presheaf`. These are exactly the two fields `val` and `isSheaf` of Mathlib's
  `SheafOfModules`; no extra assumption is being imposed. The module universe v is
  independent of u. Its abelian groups, scalar actions and semilinear restrictions
  are the actual Mathlib module-presheaf data.
- P_M has section group `Γ((tensorPullback V.hom).obj M, ⊤)` and the specified
  `etaleTensorSectionsRestriction M g`. The recorded `etaleTensorSectionsPresheaf`
  has precisely these objects and maps. No independently chosen pullback or map is used.
- The two module-presheaf morphisms are unpacked as `θ θ' : ∀ V : T.Etale,
  Γ((tensorPullback V.hom).obj M, ⊤) →ₗ[Γ(V.left, ⊤)] G.obj (op V)` with naturality
  `hθ` and `hθ'`. Their component additivity and linearity are provided by `LinearMap`.
  Each naturality equation quantifies over ALL site morphisms `g : V ⟶ U` and ALL
  source sections, so this is exactly a compatible linear family, not arbitrary maps.
  This unpacking avoids a new copy of the tensor module presheaf and permits the
  independent target-module universe.
- The auxiliary notation G_u(A) in the node is G evaluated on the composed open
  etale object over T. It introduces no extra datum or theorem conclusion; the
  construction and use of this Zariski sheaf appear in proof steps 1 and 3 of the docstring.
  Likewise G_T(W) is `G.obj (op (Scheme.Etale.mk W.ι))`.
- For EVERY open W, including the empty and whole opens, `h_open` quantifies over
  every `m : Γ(M, W)` and compares the two images of
  `(tensorOpenSectionIso T M W).inv m` at `Scheme.Etale.mk W.ι`.
  This is exactly the displayed node hypothesis after evaluation at m. The existing
  comparison is the inverse of the section map of the unit-normalized tensor-to-
  restriction comparison, followed by the standard restriction section isomorphism
  and `W.ι_image_top`. Thus its inverse is the node's Γ(kappa_W) with the canonical
  identification of restricted global sections with M(W). It is not an arbitrary iso.
- The conclusion is equality `θ = θ'` of the entire dependent linear families.
  Equality of presheaf morphisms is equality of those families: their naturality
  properties are propositions, so no arrow data remain to compare. This is exactly
  equality on every object and arrow asserted by the node.
- No separation, nonemptiness, characteristic, affine, finite-type or quasi-coherence
  assumptions occur. The theorem is the sole new declaration; there are no definitions
  with postponed data and no additional helper theorem.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, with objects
  `Scheme.Etale` and their arrows from `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf`: `PresheafOfModules`, its linear
  `Hom.app` and naturality interface. `Mathlib.Algebra.Category.ModuleCat.Sheaf`:
  `SheafOfModules` (fields `val`, `isSheaf`). The recorded
  `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`, is
  a transparent abbreviation of this same `SheafOfModules`; its source was read.
- `Mathlib.CategoryTheory.Sites.Spaces`: `TopologicalSpace.Opens.grothendieckTopology`;
  Zariski modules use this topology. The recorded module-sheafification declaration
  `PresheafOfModules.sheafification` and its adjunction in
  `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` were inspected; no
  sheafification is needed to formulate the uniqueness lemma.
- `WeilConjectures.AlgebraicGeometry.EtaleTensorSections`:
  `tensorSectionsComp`, `tensorSectionsUnit`, `etaleTensorSectionsRestriction`,
  its semilinearity/identity/composition theorems, `etaleTensorSectionsPresheaf`.
  These use the canonical adjunction of
  `WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction`,
  `exists_tensorPullbackAdjunction` (also a proof dependency).
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `tensorPullbackSectionAdjunction`, retaining the upstream explicit `tensorPullback`
  while fixing its unit to actual `1 tensor m`. This recorded dependency is imported.
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`: `restrictFunctorIsoPullback`,
  `restrictAdjunction_unit_app_app`; `Mathlib.CategoryTheory.Adjunction.Unique`:
  `Adjunction.unit_leftAdjointUniq_hom_app`. These are the recorded Mathlib matches
  for the unit-compatible open comparison. The tensor specialization is implemented
  by the already published declaration in the next bullet, not copied here.
- `WeilConjectures.AlgebraicGeometry.EtaleTensorOpenSectionsNaturality`:
  `tensorOpenSectionIso`, `etaleTensorOpenSectionIso`,
  `etaleTensorOpenSectionIso_naturality`. Their signatures and definitions were read.
  The owning already-landed node `new-etale-tensor-open-section-iso` is added to
  `stmt_deps`, because its canonical comparison now occurs in the signature;
  it was already a proof dependency. No cycle or fresh notion is introduced.
- `Mathlib.CategoryTheory.Adjunction.CompositionIso`:
  `Adjunction.leftAdjointCompIso_assoc`, the recorded proof-dependency match.
  Proof dependency modules are imported even though this stage supplies only `sorry`.

Edge cases checked by reading the binders and the actual constructions: empty T, empty
etale V, W empty, W all of T, M zero, G zero, arbitrary module sizes v, identity arrows,
and non-open etale maps. All are admitted by the universal quantifiers and canonical
pullback comparison. The naturality hypotheses include arbitrary etale-object arrows,
not just inclusions of base opens. h_open is neither tautological nor the conclusion:
for a non-open etale V there is no hypothesis directly equating its components.

Searches actually run with msearch.py:

- LeanFinder: "Natural module maps from tensor pullback section presheaves on the
  small etale site are determined on Zariski opens". Eight hits, headed by ordinary
  scheme-module `hom_ext_iff` and `hom_ext`; none determines a map on all etale
  objects from its values only on base opens.
- Loogle: `"PresheafOfModules", "ext"`. Eleven hits, including
  `PresheafOfModules.hom_ext` and `Hom.ext`; these require all site components,
  so do not match this node.
- grep: `hom_ext|pullback_obj_obj_ext` in `Algebra/Category/ModuleCat`. Twenty-five
  hits; no matching theorem. Read the ordinary presheaf `hom_ext` signature at
  Presheaf.lean:113 and scheme-module `hom_ext` at Modules/Sheaf.lean:136.
- LeanSearch: "Maps from tensor pullback section presheaves to etale modules are
  determined by their components on Zariski opens". Eight hits, including stalk
  pullback, module pullback and sheafification comparison; no exact match.
- Direct rg in both `lean/WeilConjectures` and `lean/Sheaf` for
  `etaleTensorSections`, `OpenDetermination|open_determination|open.*determined|determined.*open`,
  plus the node id in `WeilConjectures` and upstream names. No declaration states
  this result. The existing tensor-section comparison modules were read and reused.

Validation: scompile.py compiled this file in sandbox and library modes, cleanly
(3.3 seconds and 3.0 seconds in the first check). The final import-complete file is
compiled again by scompile.py and the prescribed delivery preflight. No source or
live repository files were directly written and no git command was run there.
No mathematical node fault or STATEMENT-DISPUTED issue was found.

## Second reading by Q148

A separate rereading of the completed node and signature was performed by the dispatched
worker; the human brief prohibits starting other agents and delegates independent review
to the maintainer. In this rereading I checked each binder against the node: T and all
etale test objects use the scheme universe u, M is arbitrary, and the target G's separate
v is unrestricted. G with hG exactly unfolds a module sheaf. The source of each linear
map is the specified tensor pullback, its scalars are the functions on V, and both
naturality hypotheses include every site morphism. The open hypothesis uses the inverse
of the *fixed* tensorOpenSectionIso, not a choice of comparison and not just an equality
on the whole base. Dependent-family equality in the conclusion equals presheaf-morphism
equality because naturality is propositional. I reopened the existing comparison's
source and checked its leftAdjointUniq direction: it maps tensor pullback to restriction,
so its inverse is precisely the node's kappa on sections. No mathematical statement
changed. I added the owning landed node to stmt_deps and made the proof imports explicit.
