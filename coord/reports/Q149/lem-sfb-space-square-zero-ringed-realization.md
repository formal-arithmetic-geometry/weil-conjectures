## Worker report

The delivery states `AlgebraicGeometry.AlgebraicSpace.space_square_zero_ringed_realization`
in `Sheaf.AlgebraicGeometry.SpaceSquareZeroRingedRealization`. There is one named theorem,
with the whole proof `sorry`, and a separate module of explicit structures and predicates.
There are no definitions selected from existence theorems and no postponed proof inside
any definition. The original statement, split and proof dependencies are unchanged;
`stmt_deps` gains only the new definition node listed below.

The inherited BLOCKED ending confused stages: Q159's report and `reviewed` record are
for the stage-1 split. The current node has no `lean` or `reviewed_lean` record, and
coord/queue.tsv lists it at stage 2. Thus this is its initial stage-2 statement, not a
re-splitting or a push of a returned stage-1 branch. No repair note exists for the item.

Sources read: spaces-more-morphisms.tex, complete statements and proofs of
lemma-thickening-equivalence (05ZS), lemma-first-order-thickening (05ZT), and
lemma-first-order-thickening-maps (05ZN). Also spaces-properties.tex,
definition-f-map, lemma-f-map (03G4), definition-structure-sheaf (03G7), and
lemma-morphism-ringed-topoi (03G8), including the proof's explicit chart formula.
The current blueprint unit and its direct-images proof (3) were read under
literature/blueprint/latest, together with the item's inherited supporting chain.
No change to that unit's statement or proof route is proposed.

Hypothesis and clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; every space in every clause has type
  `AlgebraicSpace S`. All morphisms are morphisms in the existing full subcategory
  of fppf sheaves, hence over S. `B` is an arbitrary algebraic space, not a scheme.
- A first-order thickening is `IsSpaceFirstOrderThickening i`, defined using the
  existing `IsRepresentableWith` and scheme `IsFirstOrderThickening p.left` on
  every scheme test. The latter is precisely closed immersion plus square-zero
  ideal. Such scheme maps are homeomorphisms: a square-zero ideal lies in every
  prime, and a closed immersion is a closed embedding. This is equivalent to the
  node's chartwise closed immersion with square-zero kernel and unchanged point
  space; it does not impose any extra finiteness or separation condition.
- The first conjunct supplies `ThickeningOverModel f i q` for EVERY thickening
  with `i ≫ q = f`. Its equivalence identifies the two small étale categories;
  `reduction` and `cartesian` normalize its inverse by actual scheme pullbacks.
  Continuity in both directions identifies the sheaf topoi. Its `quotient_app`
  fixes the ring map as pullback of regular functions along reduction.
  `base_normalization` fixes the base action on every base-chart square by an
  actual lifted scheme map. These normalized objects are conclusions, not
  extra assumptions on the given thickening.
- The second conjunct binds `(G : X.QCoh)`, using the existing full subcategory
  for `SheafOfModules.IsQuasicoherent`; it never copies quasi-coherence.
  `SpaceSquareZeroExtension f G.obj` is precisely the input sequence and algebra
  data: `algebra` is a sheaf of rings, `commutative` supplies commutativity on
  each section ring, and `quotient` is a natural unital ring map.
- `inclusion` is an additive map on every chart, with `inclusion_naturality`.
  `injective` says it is a monomorphism of sheaves. `kernel` identifies its image
  with the sectionwise kernel; `locally_surjective` is sheaf surjectivity, on
  a covering sieve for each quotient section. Surjectivity on global sections
  is deliberately not assumed.
- `square_zero` kills products of kernel sections. `scalar` says
  `inclusion (p(a) • m) = a * inclusion m`, so the image is an ideal and its
  quotient O_X-action is the prescribed module action. The `base` chart map is
  exactly an `f^{-1}O_B`-algebra structure, and `base_quotient` says p is an
  algebra map to the given O_X, with canonical f-sharp.
- The realization is `∃ X' i q, IsSpaceFirstOrderThickening i ∧ i ≫ q = f ∧ ...`.
  The isomorphism `γ` identifies the ENTIRE transported étale structure sheaf
  with A. `γ.hom ≫ A.quotient = T.quotient` is compatibility with p, and the
  final chartwise equation is compatibility with the base algebra action.
  Compatibility with the specified injection requires no arbitrary additional
  marking: its induced inclusion in O_X' is exactly γ.inv after A.inclusion.
  Injectivity and the kernel equation then identify G with the geometric kernel,
  and the scalar equation gives its specified O_X-action. No choice of an
  unrelated kernel identification is permitted or needed.
- The third conjunct independently quantifies over X, Y, X', Y', their two
  thickenings and their maps to B, `(g : X ⟶ Y)` and `g ≫ h = f`. No identity
  restriction on g and no quasi-coherence hypothesis on these kernels is made.
  `α : ChartRingMap g W.rings T.rings` is a map of ring sheaves from the inverse
  image. `Reduces` is exactly the reduction square; `OverBase` is precisely
  compatibility with the two B-algebra structures on composable chart triples.
  `∃! g'` states uniqueness as an ACTUAL space morphism, with `i ≫ g' = g ≫ j`
  and `g' ≫ r = q`. `InducedBy` states that its map on regular functions agrees
  with α on every lifted chart square, including the existence of those lifts.
- The fourth conjunct quantifies over two thickenings of the same X and a
  SPECIFIED ring isomorphism θ, preserving the quotient and base actions. It
  gives `∃! e : X' ≅ Y'` over B, commuting with the reduction inclusions and
  inducing precisely θ on every lifted chart. In particular this applies to
  any specified isomorphism of extensions, including its specified map on G.
  This is the marked uniqueness assertion, also a consequence of the general
  maps assertion and its application to θ inverse. It asserts no uniqueness
  of an isomorphism when the isomorphism of extensions has not been fixed.

The chart-map encoding is exactly the f-map definition preceding Stacks 03G4:
`ChartRingMap.app` ranges over ALL commuting squares of scheme charts, and its
single naturality field is the commuting restriction square for BOTH charts.
By 03G4 this is equivalently a map from the inverse image, and by 03G8 the
canonical map is the ordinary pullback of regular functions on each square.
All site arrows between étale scheme objects are themselves étale. This use of
f-maps is necessary because for general g the pullback of a scheme chart need
only be an algebraic space; no representability hypothesis on g is added.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicSpace`, `IsRepresentableWith`,
  `EtaleSite`, `etaleTopology`, `structurePresheaf`, `structureSheaf`, `Modules`.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: `QCoh`, with
  Mathlib's `SheafOfModules.IsQuasicoherent` and `QuasicoherentData` read.
- Sheaf.CategoryTheory.RingedSiteModules: `CategoryTheory.ringedSiteModules`,
  transparently the existing Mathlib `SheafOfModules` category.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`;
  WeilConjectures.AlgebraicGeometry.Thickening: `IsFirstOrderThickening`.
- The stated proof inputs are imported by regular imports:
  `AlgebraicSpace.etale_relation_quotient` from EtaleRelationQuotient and
  `FormallyUnramified.hom_ext` from Mathlib's FormallyUnramified module.
  The general site and étale definitions are already imported by AlgebraicSpace.
  The other proof-only DAG nodes have no Lean record or Mathlib match, so no
  invented import was added. They remain the eight-step docstring's proof plan.

Edge cases: zero kernel gives the identity extension and identity thickening.
Empty spaces and their empty covering sieves are allowed; local surjectivity
then has its usual vacuous sheaf meaning. No atlas is required to be nonempty,
finite or affine. The maps clause includes identity thickenings, nonidentity g,
and non-quasi-coherent square-zero ideals. Split extensions with derivations
can have automorphisms; specifying θ avoids the false unmarked uniqueness.
The square-zero inverse calculation works in characteristic 2 as well. The
universe is the existing `AlgebraicSpace S` convention: schemes and section
rings in u and site objects in u+1; no new universe equality is imposed.

Searches actually run with msearch.py (full service records in searches.jsonl):
LeanFinder `algebraic space square zero ring sheaf extension realization thickening`
returned eight ring/scheme results (Algebra.Extension.infinitesimal,
Scheme.IdealSheafData.glueDataObj, and derivation lifts among them), none giving
this algebraic-space assertion or data. Loogle
`AlgebraicGeometry.AlgebraicSpace, Sheaf` returned zero hits and reported the
project name unknown; this is not treated as evidence that Mathlib knows that
name. Mathlib grep `AlgebraicSpace|squareZeroExtension|SquareZeroExtension`
in AlgebraicGeometry returned zero hits. LeanSearch
`Square zero extensions of ring sheaves on algebraic space etale sites and compatible morphisms on charts`
returned eight TrivSqZeroExt/Algebra.Extension ring results, no sheaf extension
or normalized chart datum. Direct rg in WeilConjectures and Sheaf found the
existing scheme thickenings, generic module direct-image operations and
square-zero action lemmas, none with this interface. The prescribed item-id
search in WeilConjectures and Sheaf returned no hit. Whole-DAG and blueprint
searches by tags and square-zero extension found no definition for this datum;
blueprint_refs.py search reported zero matching blueprint nodes, and ancestor
reported None, agreeing with the item's recorded ancestor. The new node keeps
that ancestor and prepends the item to its inherited via list.

No STATEMENT-DISPUTED flag, source error, statement correction, or unusable
recorded statement dependency was found. No dependency module is delivered.

## New nodes

`def-sfb-space-square-zero-extension-data` defines the explicit extension datum,
chart ring maps, scheme-tested first-order thickening predicate, normalized site
and base models, and reduction/base/induced-map predicates needed by this item.
It is a definition-only node in the item's chapter and unit, with its own module
`Sheaf.AlgebraicGeometry.SpaceSquareZeroExtensionData`. Its source is the input
data and formulas of 05ZS/05ZT/05ZN, together with the f-map definition and 03G4,
03G7 and 03G8. It asserts no existence of a model, ringed realization or lift.
Its structures contain actual functors, natural transformations, maps and their
explicit normalization equations; its predicates have fully written bodies.
The three search kinds above are recorded from the service log in the new node.
Existing scheme first-order thickenings are reused, not redefined, and existing
module sheaves and algebraic-space sites are reused without a private variant.

## Second reading by Q149

A second in-session pass opened both modules and matched the four conjunctions
against the unchanged statement and the three Stacks lemmas. The dispatcher
explicitly prohibits starting another agent; this pass does not claim to be a
separate worker's review. The maintainer's independent review remains required.

Checks made in that pass: the extension kernel is sectionwise exact while its
quotient is only locally surjective; the kernel action is the specified one;
B remains an arbitrary space; every chart action is normalized by an actual
scheme map; both g and its lift range over arbitrary space morphisms; maps have
no added quasi-coherence assumption; and the specified θ is retained in the
isomorphism uniqueness clause. The site equivalence is normalized by pullback
squares and continuity in both directions, rather than an unnormalized Nonempty
choice. No Lean theorem was proved. Imports were narrowed so the definition
module imports AlgebraicSpace directly, while the main module imports the
existing quasi-coherent specialization it actually uses.

Validation before delivery: both delivered modules compiled separately through
scompile.py on the server (definition module about 8.3 seconds, main module about
1.6 seconds), with no errors or unexpected warnings. The final imports and
records will be checked again by the prescribed delivery dry run.
