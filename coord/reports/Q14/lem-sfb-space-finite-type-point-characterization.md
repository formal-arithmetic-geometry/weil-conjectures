## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceFiniteTypePointCharacterization` states
`AlgebraicGeometry.AlgebraicSpace.closed_etale_lift_iff_locallyOfFiniteType_representative`.
Its sole theorem has proof `sorry`; there are no new definitions or auxiliary theorems.
I read Stacks `spaces-morphisms.tex`, lemma-point-finite-type (06EF) and
lemma-identify-finite-type-points (06EH). The node's (i) is 06EF(2) and its (ii) is 06EF(1).
The statement is unchanged. The item adds the landed point-class definition and the
new existing-declaration definition node for the presentation structure to stmt_deps.

Hypothesis and clause correspondence:

- The arbitrary base scheme is `{S : Scheme.{u}}`.
- The algebraic space over S is `(X : AlgebraicSpace S)`, the dependency's full
  subcategory of fppf sheaves with representable diagonal and an étale surjective atlas.
- The point is `(x : Point X.obj.obj)`. `Point` is the existing quotient of
  field-valued representatives by common-field-extension equality, rather than a chosen
  chart point or an arbitrary set standing in for the underlying points.
- The scheme W over S and its point w in (i) are the existential binders
  `(W : Over S) (w : W.left)`. A map to X determines its composite to S, so this
  packaging adds no condition to the source's formulation.
- The map e is `(e : yoneda.obj W ⟶ X.obj.obj)`. The predicate `IsEtale e` includes
  representability, and tests étaleness on every scheme base change, exactly as in
  `def-trf-algebraic-space`.
- Closedness of w in all of W is `IsClosed ({w} : Set W.left)`. In particular it is
  not merely closedness in a neighbourhood. The equality e(w)=x is
  `schemePointMap e w = x`, using the canonical residue-field representative.
- The field K, its field structure, its map to S, and its field-valued map a in (ii)
  are the data of `p : PointRepresentative X.obj.obj`: `p.K`, the existing instance
  `p.field`, `p.base : Spec (CommRingCat.of p.K) ⟶ S`, and `p.value`.
  Yoneda identifies the associated map a with `yonedaEquiv.symm p.value`.
- Representing x is `Quot.mk _ p = x`. This permits changing representatives by
  field extension; it does not demand equality with a fixed representative.
- Local finite type of a is
  `∀ D : EtalePresentation (yonedaEquiv.symm p.value), LocallyOfFiniteType D.h.left`.
  The existing structure D includes both schemes over S, the two representable étale
  charts and the commuting map h. Thus this quantifies over every compatible pair of
  charts, with no surjectivity restriction. `D.h.left` is precisely the scheme map
  whose local finite type is required. This is the universal presentation condition
  of the already landed presentation-property node and the node's explicit chart test.
- The equivalence of the two full conditions is `↔`. There are no Noetherian,
  Jacobson, quasi-compactness or separation hypotheses and no extra conclusion.

Recorded dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicSpace.IsEtale` (the latter includes scheme-test representability).
- Mathlib's `Field` (`Mathlib.Algebra.Field.Defs`), in `PointRepresentative.field`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, used by
  the recorded representable-étale and presentation definitions.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`: `Point`, `PointRepresentative`,
  `PointRepresentative.Rel`, `schemePointMap`; its owner is the landed node
  `def-a1-algebraic-space-point-classes`, added to stmt_deps.
- `Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion`: `EtalePresentation`;
  its owner is the new definition node `def-sfb-space-etale-presentation`,
  added to stmt_deps with an existing:true record on the unchanged structure. I read its complete structure and both scheme/space criterion
  declarations. Reusing it avoids constructing a second chart-test notion or needing
  an additional chosen scheme-as-space object.
- `Mathlib.CategoryTheory.Yoneda`: `CategoryTheory.yonedaEquiv`, whose inverse sends a
  presheaf section to its canonical Yoneda natural transformation.

The published proof dependencies are imported without `public`:
`SpaceLocalPropertiesChartTest`, `StackChartwiseSmoothEtaleCalculus`,
`AlgebraicSpaceFibreProductsEtaleCovers`, `Mathlib.AlgebraicGeometry.ResidueField`,
`Mathlib.AlgebraicGeometry.Morphisms.Etale`, and `Mathlib.RingTheory.Ideal.Maximal`.
They supply respectively the chart comparison, composition/base-change calculus,
fibre products and cover permanence, residue-field factorization, open-immersion
étaleness, and maximal ideal existence. The scheme criterion node
`lem-sfb-finite-type-field-point-characterization` has no recorded declaration or
Mathlib match on the read base and is only a proof dependency: no import is fabricated.
Its eventual proof import belongs to the maintainer after that node is stated.

Edge cases checked before writing:

- Empty X has no x, rather than requiring an extra nonemptiness assumption. Empty S
  likewise causes no spurious field point. W cannot be empty when its witness w exists.
- W need not be affine, quasi-compact or separated. Closedness is in W itself.
  The converse proof shrinks an atlas to get such a W, as the source does.
- No Jacobson assumption is smuggled in by using Mathlib's Jacobson closed-point
  criterion: that criterion is not used in the statement.
- The representative field need not be algebraically closed, perfect, finite over
  the base, or of any fixed characteristic. Its extension equivalence is the shared
  quotient, including the identity-extension case.
- Both chart schemes in a presentation may be empty or nonsurjective. The universal
  test retains all of them; it does not replace local finite type by finite type.
- Universes are explicitly bound by `universe u`. Schemes, test schemes and fields
  use the same size convention as `AlgebraicSpace` and `PointRepresentative`;
  points themselves lie in `Type (u + 1)`. No independent smaller test universe occurs.

Searches (2026-10-24):

- msearch LeanFinder: "A point of an algebraic space is represented by a locally
  finite type morphism from a field if and only if it lifts to a closed point in an
  etale scheme chart". Eight hits, including the Jacobson scheme criterion,
  `Scheme.Etale`, the closed immersion criterion and residue-field maps; none states
  the arbitrary algebraic-space equivalence.
- msearch Loogle: `"LocallyOfFiniteType", "IsClosed"`. Two hits:
  `instLocallyOfFiniteTypeOfIsClosedImmersion` and
  `isClosed_singleton_iff_locallyOfFiniteType` (the latter assumes JacobsonSpace).
- msearch grep, AlgebraicGeometry: `finiteTypePoint|finite_type_point|AlgebraicSpace`.
  Zero Mathlib hits.
- msearch LeanSearch: "A point of an algebraic space has a locally finite type field
  representative if and only if it is the image of a closed point of an etale scheme".
  Eight hits on scheme local finite type, Jacobson closed points and residue-field
  maps. No match for the algebraic-space theorem.
- rg over `lean/WeilConjectures` and `lean/Sheaf` for
  `finiteTypePoint|finite_type_point|finite_type.*iff.*closed|finiteType.*[Pp]oint|06EF|06EH`:
  no equivalent theorem. The nearby `ArtinVersalFieldLifting` result concerns versal
  lifting, not this characterization.
- rg over the same sources and `dag/lean_names_upstream.json` for the proposed full
  theorem component and module name: no collision. Searching the item id in
  `lean/WeilConjectures` returned no declarations.
- Targeted declaration searches found the shared `AlgebraicSpacePointClasses` and
  `SpaceEtalePresentationPropertyCriterion` interfaces, which are reused directly.

Validation: scompile.py compiled this exact delivered file separately in sandbox
and library modes, in 3.1 s and 2.9 s respectively, with no diagnostics.
The H2 return identified a dependency ownership fault, repaired below. No mathematical
statement dispute was found.

## Second reading by Q14

This is the author's second reading, not a claim of an independent review; the
maintainer's independent review follows delivery, as required by the dispatcher brief.
I reread the node, the delivered signature, the point-class definition, the complete
EtalePresentation fields and Stacks 06EF. The existential W,w,e exactly gives (i):
closedness is global in W, IsEtale includes representability, and schemePointMap
uses κ(w). On the other side the existential p supplies a genuine field and base
map, the quotient equality gives its point class, and the universal presentation
condition gives local finite type of the same canonical field-valued map obtained
from p.value by Yoneda. In particular the presentation contains no local finite type
assumption itself, no surjectivity requirement on the target chart, and no arbitrary
map replacing the canonical field map. No clause or hypothesis was changed in this
reading. The additions to stmt_deps name the landed point-class owner and the new definition
node owning the existing presentation structure. The theorem node is not a statement
dependency: neither its conclusion nor a choice from that conclusion is used. The proof docstring follows all four node proof steps, including the
nonempty affine open/maximal ideal selection and the residue-field/common-extension
identification in the final step. The single sorry is the theorem's whole proof.


## New nodes

`def-sfb-space-etale-presentation` owns the unchanged plain structure
`AlgebraicGeometry.AlgebraicSpace.EtalePresentation` in
`Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion` via `existing: true`.
Its source is Stacks 03MJ, the displayed commuting scheme-chart diagram. The exact
structure is parametrized by a presheaf map, so the node records that existing generality,
including the representable-source case needed here. Its fields correspond to U,V,
a,b,h, representable etaleness of each chart, and commutativity. Neither surjectivity
nor any property P of h belongs to this definition. The statement dependencies are
def-pc-scheme, def-trf-algebraic-space and def-weil-etale-morphism.

LeanSearch returned eight hits on etaleness, ring presentations and schemes, but no
matching diagram structure. Loogle EtalePresentation returned zero hits (unknown
identifier). Mathlib grep returned zero hits. Upstream grep found ring standard-etale
presentations and unrelated uses only. Project grep found the exact existing structure
at SpaceEtalePresentationPropertyCriterion.lean:54. DAG searches found no definition
node owning it, and blueprint_refs.py found no blueprint match; its ancestor is the
inherited null ancestor. Full queries and results are in mathlib_searches. The new
node therefore adds ownership metadata, with no module or duplicate declaration.

## Repair of returned delivery

H2, immutable returned head 674abf9cc874: the item cited the theorem node
lem-sfb-space-etale-presentation-property-criterion only to access its plain structure.
I compared the retained sandbox with current main: the item's only differences were
lean and stmt_deps. I rebuilt its copy from current main, preserving the delivered
Lean record, then replaced that theorem dependency with
def-sfb-space-etale-presentation. No other definition owner had landed on current main.
The new node binds the existing declaration with its verbatim structure signature.
The item's Lean source is byte-identical to the returned version; no statement, proof
or existing dependency source is edited. I read the current server source using
scompile.py --source and checked all eight fields against the new node.

Second-reading check of this repair: the new node says schemes over S for U,V, Yoneda
chart maps for a,b, an over-S map for h, the exact IsEtale predicates for both charts,
and the equality a ≫ f = yoneda.map h ≫ b for commutativity. These are precisely the
structure's fields. Its presheaf-level scope permits the field-spectrum source without
requiring an additional chosen algebraic-space object. No theorem existence conclusion
or .choose is used. The new node is directly cited by the item and introduces no
Lean declaration. This addresses the sole numbered return point.
