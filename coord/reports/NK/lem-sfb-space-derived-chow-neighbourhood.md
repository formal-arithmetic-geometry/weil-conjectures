## Worker report

Stage 2, not a stage-1 repair. The live item is stage-1 split and reviewed by Q45,
has no Lean attachment, and appears with stage 2 in coord/queue.tsv. There is no
released repair note. The inherited unchanged-item rejection concerned the earlier
stage; this delivery adds its actual Lean statement and uses deliver2.py.

The module Sheaf.AlgebraicGeometry.SpaceDerivedChowNeighbourhood states
AlgebraicGeometry.AlgebraicSpace.exists_derivedChow_neighbourhood. Its sole theorem
has proof sorry. The projective space, its open, and its inclusion are imported from
Sheaf.AlgebraicGeometry.SpaceDerivedChowTransformRestriction. The module declares
only the neighbourhood theorem and contains no local helper definitions. No statement correction or dependency interface replacement is needed. The return at
77ce51cfd39a requires a new definition node for these three existing definitions;
that ownership repair is described below. Additional already-landed definition nodes are
cited directly in stmt_deps for the point, support, morphism, and derived interfaces.

Read source: spaces-more-morphisms.tex, lemma-derived-chow (Tag 0CTR), the full
proof, and lemma-compute-Fourier-Mukai-for-derived-chow (Tag 0CTS), including its
finite-presentation argument. Read the item's eight proof steps and every statement
dependency's statement and recorded interface. The original CompactObject example
is now a withdrawn module with no declarations; its node is an existing Mathlib
attachment. This module uses the current module/public-import conventions.

Hypothesis and clause correspondence:

- Ring A: A : CommRingCat.{u}, including the zero ring. Base is Spec A, and
  X : AlgebraicSpace (Spec A) retains arbitrary spaces, rather than schemes only.
- Universe convention: explicit u and w, and a family of HasDerivedCategory.{w}
  choices for spaces over Spec A. This supplies localization models for the spaces
  quantified in the conclusion, not any mathematical finiteness or exactness
  assumption. SmallModules is the published equivalent small ringed model, with
  the same coefficient universe u; no identification of different site universes.
- Separated: hsep tests the relative diagonal, here the diagonal into the product
  of presheaves on schemes over Spec A, by closed scheme immersions.
- Finite presentation: hqc is quasi-compactness of X over the affine base;
  hqs is quasi-compactness of that diagonal; hlfp is local finite presentation
  of every representable etale scheme chart over Spec A. Together these are
  exactly the qc, qs, and etale-local finite-presentation hypothesis stated.
- Point: x : Point X.obj.obj uses the field-valued point classes.
- n >= 0: n : Nat. chowProjectiveSpace A n uses homogeneous coordinates
  ULift (Fin (n+1)), so it is projective n-space, not projective (n-1)-space.
- T = X times_A P with projections p,q: the first conjunct is
  Nonempty (IsLimit (BinaryFan.mk p.hom.hom q.hom.hom)). Presheaves here are
  on Over (Spec A), so this product is precisely the relative product over A.
  It quantifies a representative with its universal property, equivalent to the
  chosen product, with no extra geometry. It does not replace the product by
  an arbitrary ambient space.
- Closed finitely presented h : Z -> T: IsRepresentableWith tests every scheme
  base change for IsClosedImmersion and LocallyOfFinitePresentation. A closed
  immersion is automatically qc and qs, so local finite presentation is exactly
  finite presentation here, as in the published closed-structure theorem.
- V open in P: V : (chowProjectiveSpace A n).left.Opens. Its underlying scheme
  and inclusion are chowProjectiveOpen A n V and chowProjectiveOpenInclusion A n V.
- T_v = X times_A V: the first IsPullback specifies r : T_v -> T as the
  inverse image of V under q. Thus the final isomorphism lives over the ENTIRE
  product open, rather than over W alone.
- W = c^{-1}(V), c = q after h: the second IsPullback uses (h >> q).hom.hom
  and the same inclusion, with maps k : schemeSpace W -> Z and yoneda.map j.
  W : Over (Spec A) is an actual scheme. Giving this scheme representative is
  equivalent to saying the inverse image is a scheme.
- j : W -> V closed and finitely presented: IsClosedImmersion j.left and
  LocallyOfFinitePresentation j.left, again using automatic qc and qs for a
  closed immersion, without requiring V itself to be quasi-compact.
- b restricted to W etale: IsEtale (k >> h >> p).hom.hom.
- z in W: a scheme point w_0 : W.left and
  schemePointMap k.hom.hom w_0 = z. This is exactly membership in the open
  subspace's image on points. No chosen unique point or residue-field equality.
- b(z)=x: mapPoint (h >> p).hom.hom z = x.
- E in D(O_T): E : T.DerivedModules, the published equivalent small-site category.
- E pseudo-coherent: T.IsPseudoCoherent E, exactly the recorded etale-local
  bounded-above finite-free-complex definition; no competing m-wise definition.
- Every cohomology sheaf vanishes off h(Z): for every integer i, moduleSupport
  of the i-th homology object transported by T.smallModuleEquivalence.inverse
  is contained in pointImage h.hom.hom. This is genuine geometric stalk support.
- Kernel isomorphism: Nonempty of the categorical isomorphism between
  (spaceDerivedPullback r).obj E and the pullback of
  (DerivedCategory.singleFunctor T.SmallModules 0).obj applied to
  (smallModuleDirectImage h).obj (SheafOfModules.unit Z.smallStructureRings).
  Thus the second object is the ORDINARY h_* O_Z in degree zero and both
  objects are restricted to T_v. Derived pullback along this open is restriction.
  The ordinary direct image is the existing compatible-chart functor conjugated
  by the specified small-model equivalences; it is not an arbitrary chosen map.

Dependency declarations actually used (all in their recorded public modules):

- Mathlib.AlgebraicGeometry.Scheme: Scheme, Scheme.Hom, Opens and its open scheme.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicSpace, IsRepresentableWith,
  IsEtale, EtaleSite, structureSheaf and Modules.
- Sheaf.CategoryTheory.RingedSiteModules: ringedSiteModules (underlying module API).
- Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory,
  HasDerivedCategory, singleFunctor, homologyFunctor.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: QCoh and its
  IsQuasicoherent predicate, through the recorded small-model interface.
- Sheaf.AlgebraicGeometry.AlgebraicSpacePseudoCoherentComplex: IsPseudoCoherent.
- Sheaf.AlgebraicGeometry.SpaceDerivedChowTransformRestriction: the existing
  chowProjectiveSpace, chowProjectiveOpen, and chowProjectiveOpenInclusion,
  built from ProjectiveSpace and its canonical morphism to the base. The latter
  is an algebraic-space arrow; its .hom.hom is used in both presheaf pullbacks.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel: SmallModules,
  smallModuleEquivalence, smallStructureRings.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules: DerivedModules,
  smallModuleDirectImage.
- Sheaf.AlgebraicGeometry.SpaceDerivedPullback: spaceDerivedPullback.
- Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses: Point, schemePointMap.
- Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology: pointImage, pointTopologicalSpace.
- Sheaf.AlgebraicGeometry.ProperCurveModuli: mapPoint, MapIsQuasiCompact.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport: moduleSupport.
- Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite: schemeSpace.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties imports the existing
  point/quasi-compactness calculus and scheme morphism properties. No private copies.

The public imports expose these dependencies. Plain proof imports include every
currently stated proof dependency's recorded module, including the Mathlib leaves.
The unstated space-approximation, partial-section, qcqs, and relative-flat-kernel
nodes have no module to import; no proof is attempted here. The theorem docstring
carries all eight accepted proof steps with their node names, including the finite
free resolution argument added by the stage-1 reviewer.

Edge cases checked before writing: n=0 has one homogeneous coordinate; no empty
coordinate set is introduced. The zero ring and empty X are allowed; an empty X
has no x to supply, so no false existence assertion results. Empty V and W are
not excluded syntactically, but the two point equalities force W to contain the
specified point for this conclusion. V need not be quasi-compact. Rank zero,
zero complexes, variable local upper bounds, and arbitrary negative cohomological
degrees remain those of the existing IsPseudoCoherent definition. Nonreduced rings
and all characteristics are retained. No Noetherian hypothesis was added. Lifts
of x need not be unique, in agreement with the reviewed source-proof correction.

Searches actually run:

- msearch.py leanfinder: "Derived Chow etale neighbourhood for a separated finitely
  presented algebraic space with a pseudo-coherent closed graph kernel".
  Eight related etale/scheme-property results, no derived Chow theorem.
- msearch.py leansearch: "Derived Chow lemma for separated algebraic spaces of
  finite presentation". Eight scheme-separated/proper results, no matching theorem.
- msearch.py loogle: "AlgebraicGeometry.ProjectiveSpace,
  AlgebraicGeometry.IsClosedImmersion". Zero hits; unknown identifier
  AlgebraicGeometry.ProjectiveSpace in the service index (the project declaration
  is present and was read locally).
- msearch.py grep: "derived.?[Cc]how|[Cc]how.*[Nn]eighbour", AlgebraicGeometry:
  zero Mathlib matches.
- rg in both WeilConjectures and Sheaf for DerivedChow, derivedChow,
  chow_neigh, ChowNeighbour, chowNeighbour and the item id: no existing theorem.
- grep -rn for the item id in WeilConjectures: no match.
- rg for derived.?[Cc]how|[Cc]how.*[Nn]eigh in WeilConjectures and Sheaf:
  no match. That initial search predated the landed transform-restriction module; the repair
  search below finds and reuses all three helper names.
- Read the recorded dependency modules and searched the project for Point,
  moduleSupport, schemeSpace, derived pullback, and finite-presentation APIs;
  reused the existing declarations listed above.

Validation: scompile.py compiled this file in both its sandbox and its actual
library module position successfully, with no errors or non-sorry warnings.
No STATEMENT-DISPUTED issue remains; the source proof's point-uniqueness slip was
already corrected in the reviewed DAG, and this statement only requires existence.


## Repair of return L (immutable head f78246072bf7)

The initial saved-packet dry run passed at 4b7ec43f84f, but the independent return
identified a collision not detected by that check. Read the existing helper
signatures, bodies and docstrings in SpaceDerivedChowTransformRestriction, both
locally and via scompile.py --source, and compared them with the retained packet.
Removed chowProjectiveSpace, chowProjectiveOpen and chowProjectiveOpenInclusion
from this module, and publicly imported their owning module. No renaming or
replacement definition is introduced. The projective space and open have the
same data. The existing open and inclusion take explicit A and n; the existing
inclusion is an algebraic-space arrow rather than an Over arrow, whose underlying
presheaf map .hom.hom is exactly the former yoneda.map inclusion. Both pullback
squares now use that existing map. Updated lean.declarations to list only the
neighbourhood theorem, and regenerated lean.statement verbatim. Added the landed
helper-owning node to stmt_deps; it does not depend on this neighbourhood node.
The saved node was compared with current main: its earlier differences were
only lean and the previously added statement dependencies, which are retained.
The delivery wrapper refreshes the base and rebases the packet itself.

Repair search: rg for chowProjectiveSpace, chowProjectiveOpen and
chowProjectiveOpenInclusion in lean/Sheaf/AlgebraicGeometry found the three
existing declarations at lines 52, 58 and 65 of SpaceDerivedChowTransformRestriction.
The live-server source confirms their signatures and actual scheme/Yoneda data.

## Second reading by NK

Self-check of the repair with the node and revised module open (no separate
worker was started, as this dispatcher brief prohibits other agents): the
hypotheses remain A, X, the common derived localization models, separatedness,
quasi-compactness, quasi-separatedness, chartwise local finite presentation, and
x. The existential n, T, Z, product projections, finitely presented closed h,
open V, the entire product open, scheme W, closed finitely presented j, etaleness,
point conditions, pseudo-coherent E, all cohomology supports, and derived kernel
isomorphism are still rendered by the clauses described above. The mismatch
in the earlier returned packet was duplicate ownership of the three helper definitions.
Reusing their existing data changes neither geometric objects nor hypotheses.
The existing .hom.hom inclusion denotes the same presheaf arrow in each square.
No mathematical statement correction or new definition node was needed.

Repair validation: scompile.py compiled the revised module in sandbox and library
positions in 1.9 s and 1.8 s, with no errors or warnings. The revised file declares
only exists_derivedChow_neighbourhood; all three collided names are imported.


## Repair of return L (immutable head 77ce51cfd39a)

The required initial saved-packet dry run passed at 846290f3468. This does not
resolve the independent H2/H3 finding: the neighbourhood's stmt_deps named the
transform-restriction theorem merely to obtain three ordinary definitions from
its module. Added def-sfb-chow-projective-space-open as their definition owner,
with existing: true and the same published module and three declaration names.
Replaced only that theorem entry in the item's stmt_deps by this new definition
entry. The theorem is not selected, chosen from, or otherwise needed by any of
the three bodies. No dependency-node file is changed. The delivery wrapper
refreshes and rebases the packet on the current published branch.

The item Lean remains byte-identical to the retained return packet, SHA-256
1dcb70455d22c3477fe61a7a2a48d4d3729b8e73e71ada030127befd8a6967f1.
The advice to use MapIsSeparated and MapIsLocallyOfFinitePresentation is advisory;
the explicit equivalent hypotheses are retained to honor the byte-identity repair.
The earlier statement that no new definition node was needed is superseded by
this ownership repair. No mathematical notion or statement is changed.

## New nodes

**def-sfb-chow-projective-space-open** owns the three existing definitions
AlgebraicGeometry.AlgebraicSpace.chowProjectiveSpace, chowProjectiveOpen, and
chowProjectiveOpenInclusion in Sheaf.AlgebraicGeometry.SpaceDerivedChowTransformRestriction.
The source is Tag 0CTR (projective space and V) and Tag 0CTS (the same open inclusion).
This is an existing:true attachment, with no new module or duplicate definition.
For A : CommRingCat.{u} and n : Nat, the first definition is Over.mk of the
canonical projection of ProjectiveSpace (ULift.{u} (Fin (n+1))) (Spec A).
For every V : (chowProjectiveSpace A n).left.Opens, the second is Over.mk of
V.ι followed by that projection. The third is ObjectProperty.homMk of yoneda.map
(Over.homMk V.ι), a morphism between the corresponding schemeSpace objects.
All three are genuine constructions, with no theorem choice and no sorry data.
The new node cites the existing size, scheme, projective-space and scheme-space
definition nodes. Its primary lean.statement is the first definition's verbatim
signature; lean.declarations records all three constituent definitions.

Searches for the new node (recorded exactly in mathlib_searches): LeanSearch query
"Projective space over Spec A as a scheme over the base and its open subscheme inclusion as an algebraic space morphism"
returned eight related declarations including Scheme.Opens.ι and Proj; LeanFinder
query "Projective space over Spec A with n+1 homogeneous coordinates, open subscheme and Yoneda open inclusion"
returned eight Proj-related declarations. Neither gives the three packaged helpers.
msearch grep for chowProjectiveSpace|chowProjectiveOpen|chowProjectiveOpenInclusion
in Mathlib AlgebraicGeometry returned zero hits. The same rg in WeilConjectures
returned none, and in Sheaf found exactly the three existing declarations and
their uses in SpaceDerivedChowTransformRestriction. In dag/nodes these names occur
only in the transform-restriction theorem node; no definition node owns them.
blueprint_refs.py search chowProjective returned zero blueprint matches, and
blueprint_refs.py ancestor returned None, matching the item's null from.node.
The new node retains the item's blueprint trail with the item prepended.
The live source was re-read with scompile.py --source and agrees with the local
three definitions. Edge cases n=0, zero ring, empty or full V, and arbitrary u
are retained: no nonemptiness, finiteness or characteristic hypothesis is added.

## Second reading by NK (ownership repair)

Re-read the item node and the entire unchanged Lean file, and the new node against
all three existing signatures and bodies. The new node's P is the Over scheme
with n+1 coordinates; its arbitrary open V carries exactly the composite structure
map; its algebraic-space inclusion is the actual Yoneda arrow. No theorem result
is used. The item continues to quantify A, X, explicit u and w, derived-category
models, separatedness, qc, qs, chartwise local finite presentation, and x. Its
conclusion still provides n,T,Z,Tᵥ,p,q,h,V,r,qᵥ,W,k,j,z,w₀,E, the product and two
pullback properties, both finitely presented closed immersions, etaleness, both
point conditions, pseudo-coherence, all-degree support, and the isomorphism on
the entire product open. The detailed clause correspondence above is unchanged.
The only repaired mismatch is ownership in stmt_deps; no declaration, hypothesis,
conclusion, definition body, or theorem proof has changed. This self-reading
uses no other agent, as explicitly required by the dispatcher.


Repair validation: scompile.py compiled the byte-identical item in the sandbox
and actual module positions in 1.9 s and 1.8 s, with no errors or warnings.
The first repaired-packet dry run required the schema field import_flags on the
new node; added the empty list, matching existing definition-node records.
The item signature matches lean.statement verbatim. Comparing the item with
the live read clone shows changes only in lean and added stmt_deps; none of
the original dependencies is removed.

The repaired packet passed deliver2.py --no-push at dbc8fc42f53, including
server preflight and compilation. Final self-check confirms the new definition
node lists exactly the three existing helpers and the item cites that node
instead of the transform-restriction theorem; the Lean SHA-256 is unchanged.
