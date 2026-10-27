## Worker report

The module Sheaf.AlgebraicGeometry.SpaceReducedGenericFlatFinitePresentation states
AlgebraicGeometry.AlgebraicSpace.exists_dense_open_flat_locallyOfFinitePresentation_of_reduced.
Its single theorem has proof `sorry`; no definition or helper theorem is introduced.
The node statement is unchanged. Two already-landed definition nodes are added to stmt_deps:
def-sfb-reduced-algebraic-space and def-sfb-space-morphism-properties. Their existing
definitions are used rather than copied. The presentation criterion remains only in
proof_deps; its theorem module is no longer directly imported.

Hypothesis and clause correspondence:

- The arbitrary scheme S is `{S : Scheme.{u}}`. Explicit `universe u` is the existing
  algebraic-space size convention: test schemes and their ring values use the same u.
  No separate smaller test universe is introduced.
- The spaces over S and their morphism are `{X Y : AlgebraicSpace S} (f : X ⟶ Y)`.
  These are the recorded full subcategory of fppf sheaves and its natural transformations.
- Reducedness of every etale chart of Y is `hred : IsReduced Y`. The existing space
  predicate quantifies over every object of Y.EtaleSite and uses Mathlib scheme
  IsReduced, equivalent to reducedness of all local rings. It does not choose an atlas.
- Finite type is `hft : MapIsFiniteType f`. Unfolding the recorded predicate gives
  `MapIsQuasiCompact f.hom.hom ∧ MapIsLocally (@LocallyOfFiniteType) f`.
  The first is the existing affine-scheme/topological quasi-compactness test, also reused
  by def-sfb-stack-qcqs-morphism; its source records the equivalence with all
  quasi-compact algebraic-space base changes. The second tests all compatible etale
  source-and-target scheme charts. Thus neither quasi-separatedness nor a finite atlas
  is an extra hypothesis.
- An open subspace is `∃ D : OpenSubspace Y`. This is exactly the recorded subtype of
  Subfunctor Y.obj.obj whose inclusion D.val.ι is representable by open immersions.
- Its underlying set is `pointImage D.val.ι`, and density is
  `Dense (pointImage D.val.ι)` in the existing pointTopologicalSpace atlas topology.
- The restricted morphism is the canonical projection
  `Limits.pullback.snd f.hom.hom D.val.ι`. This is a pullback of presheaves, hence
  evaluates to pairs of matching sections. For the sheaves X, Y, and the open
  subfunctor D, it is the underlying presheaf of the sheaf fibre product X ×_Y D:
  compatible pairs glue componentwise. There is no arbitrary comparison map or
  additional existence assumption. The subfunctor need not first be bundled as a
  chosen algebraic-space object to test its canonical projection.
- The universal binders `(U V : Over S)`,
  `(a : yoneda.obj U ⟶ Limits.pullback f.hom.hom D.val.ι)`,
  `(b : yoneda.obj V ⟶ D.val.toFunctor)`, and `(h : U ⟶ V)` give every compatible
  pair of scheme charts and horizontal scheme map. `IsEtale a → IsEtale b →`
  and the equation
  `a ≫ Limits.pullback.snd f.hom.hom D.val.ι = yoneda.map h ≫ b →`
  specify exactly the two etale charts and their commuting diagram. There is no
  surjectivity requirement on either chart.
- `Flat h.left ∧ LocallyOfFinitePresentation h.left` gives both required properties
  for the same horizontal scheme map, using the recorded Mathlib predicates.
  This is the MapIsLocally-style chart test written inline for the canonical projection;
  no presentation structure or theorem conclusion is used in the signature.
- There are no hypotheses of Noetherianity, irreducibility, quasi-separatedness,
  quasi-compactness of Y, or nonemptiness.

Declarations and source signatures read:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicGeometry.AlgebraicSpace,
  IsRepresentableWith, IsEtale, IsSurjective, IsAlgebraicSpace, EtaleSite, etaleForget.
- Sheaf.AlgebraicGeometry.StackQcqsMorphism: AlgebraicSpace.IsQuasiCompact and
  MapIsQuasiSeparated, with its documented reuse of MapIsQuasiCompact.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: QuasiCompact.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace: OpenSubspace.
- Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology: pointImage and
  pointTopologicalSpace (Point and representatives come from AlgebraicSpacePointClasses).
- Mathlib.AlgebraicGeometry.Morphisms.Flat: Flat;
  Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation: LocallyOfFinitePresentation.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers:
  fibreProduct_isAlgebraicSpace, etaleCover_pullback, etale_fibreProduct_isScheme.
- Sheaf.AlgebraicGeometry.ReducedAlgebraicSpace: AlgebraicSpace.IsReduced.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties: MapIsLocally and
  MapIsFiniteType (and the Flat/LocallyOfFinitePresentation specializations).
- Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion was read to expand
  its EtalePresentation fields exactly; none of its declarations is used by the
  repaired signature. Its theorem remains a proof dependency of the node.

Stated proof dependencies are imported non-publicly: the affine etale cover, scheme-test
representability, sheaf fibre products, etale scheme open image and open-subspace
correspondence modules, the qcqs module, and the Mathlib affine/quasi-separated/etale
modules. The three proof dependencies with no current Lean or Mathlib declaration
(the qc finite affine atlas refinement, scheme source-and-target locality, and reduced
affine generic flatness) have no module to import; their exact roles remain in the
step-by-step theorem docstring. They are proof prerequisites, not missing statement notions.

Edge cases checked against the statement and Tag 06QS: for empty Y choose the whole
empty open, which is dense in the empty point space; its scheme-chart conditions are
vacuous on empty sources. For empty X over arbitrary reduced Y, choose D = Y; the
source of each etale presentation is empty and both scheme properties hold there.
No nonempty index type, irreducible component count or compactness of Y is assumed.
The universal presentation condition includes empty diagrams and imposes no chart
surjectivity condition. All test schemes are in the recorded universe u.

Searches for an exact existing declaration (2026-10-24):

- msearch.py leanfinder: "A finite type morphism of algebraic spaces to a reduced space
  is flat and locally of finite presentation over a dense open subspace". Eight hits,
  including scheme Flat, LocallyOfFinitePresentation, smoothness and universal openness;
  no algebraic-space generic-flatness statement.
- msearch.py loogle: "AlgebraicGeometry.Flat, AlgebraicGeometry.LocallyOfFinitePresentation".
  Twelve scheme-level hits (openness, etaleness, descent, flat monomorphisms); no match.
- msearch.py leansearch: "Generic flatness over a reduced algebraic space without
  noetherianity". Eight ring/module flatness and scheme affine-local hits; no match.
- msearch.py grep: "generic.*flat|flat.*generic|GenericFlat" in AlgebraicGeometry.
  No Mathlib hit.
- rg in lean/WeilConjectures and lean/Sheaf for the same regular expression and the
  exact proposed declaration name; search for the item id in WeilConjectures. The id
  and proposed name have no existing declaration. Existing generic-flatness modules
  concern schemes, integral bases or other specialization/flatification conclusions.
  Read WeilConjectures.AlgebraicGeometry.GenericFlatFinitePresentation: its
  exists_nonempty_open_flat_finitePresentation_restrict assumes IsIntegral and concerns
  schemes, so it does not state this reduced algebraic-space result.
- rg for Reduced, MapIsLocally, OpenSubspace and MapIsFiniteType located the already
  landed notions used here. No private copy was introduced.

Source checked directly: literature/stacks-project/spaces-morphisms.tex,
proposition-generic-flatness-reduced (Tag 06QS), including its whole proof. Its
structure-sheaf specialization gives exactly the two morphism clauses requested by
this node. The theorem docstring follows the node's expanded descent and density proof.
No statement correction or STATEMENT-DISPUTED issue was found.

Validation: the repaired module is compiled with scompile.py, then checked by
both the deliver2.py dry run and final delivery preflight and per-file compile.

## Second reading by Q127

A second direct pass compared the node and module clause by clause: S, X, Y and f have
exactly their recorded types; hred uses every etale chart, and hft is the quasi-compact
plus locally finite type condition. D uses the existing open-subfunctor subtype, and
its pointImage is dense in the existing atlas topology. The projection is literally
pullback.snd, with the correct target D; the inline universally quantified U, V, a, b,
h have exactly the two compatible etale charts and commuting square. Both Flat and
LocallyOfFinitePresentation apply to the same scheme map h.left. In particular the
conclusion is local finite presentation, not finite presentation, and no
quasi-separatedness or nonemptiness is introduced. No mismatch or corrective edit was
found in this pass. This was a self-review; the dispatcher forbids starting another
agent, and the maintainer's independent review reads the delivery.

## Repair of H2 (returned head d374997996f3)

The independent reviewer found that stmt_deps incorrectly cited the theorem node
lem-sfb-space-etale-presentation-property-criterion for its plain EtalePresentation
structure. Applied correction (b): removed that theorem from stmt_deps and removed its
direct import; expanded its structure fields inline in the conclusion, using the
MapIsLocally-style universal chart test. The node retains the theorem in proof_deps.
The repaired signature has no EtalePresentation reference. No new node is needed.

Compared the retained delivery with the returned signature and current shared node:
current main still has no lean record and its original statement/dependencies are
unchanged. Rebuilt the sandbox node from that current node, adding only the two
landed definition dependencies and the updated lean record. All other fields,
including the statement and proof_deps, are preserved from current main. The delivery
wrapper rebases the repaired files onto the current server branch.

The second pass over the repaired conclusion checked each former structure field:
U, V, a, b and h are universal binders, source_etale and target_etale are the two
IsEtale antecedents, and comm is the displayed equation for pullback.snd. The
consequent is the unchanged conjunction on h.left. This expansion preserves every
chart, including empty charts, and adds no surjectivity or finiteness assumption.
