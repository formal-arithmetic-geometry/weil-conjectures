## Worker report

The delivery states lem-per-generically-reduced-strict-transform-geometry in three named
sorry-only theorems of Sheaf.AlgebraicGeometry.GenericallyReducedStrictTransformGeometry.
Their common DAG node is the assigned node; each docstring gives its relevant numbered
proof steps and source. The item statement is unchanged. The sole new statement dependency
is the definition def-per-finite-embedded-blowup-diagram. No dependency record is changed.

Clause mapping, read against the complete item statement:

- `X : Scheme.{u}` and `[IsLocallyNoetherian X]` are the locally Noetherian scheme.
  The `hX` predicate quantifies over every `C ∈ irreducibleComponents X`, every point η,
  and `IsGenericPoint η C`, and assumes `_root_.IsReduced (X.presheaf.stalk η)`.
  It does not assume `IsReduced X` or any condition at nongeneric points.
- The first conjunct of `genericallyReduced_blowup_geometry` gives `IsField` and
  `IsRegularLocalRing` for precisely those generic stalks.
- Its second conjunct universally binds the quasi-coherent `J : X.IdealSheafData`,
  finite type `J.ofFiniteType`, and `interior (J.support : Set X) = ∅`.
  `IdealSheafData` is Mathlib's actual quasi-coherent ideal sheaf, and support is V(J).
  The conclusions use the published `J.blowup` and `J.blowupMap`, giving local
  Noetherianity and reducedness of every component generic stalk upstairs.
- The `Dense` assertion is in the subtype of each component C. Its set is the preimage
  of the center complement under the blowup map and subtype inclusion, so it asserts
  exactly density in each component, rather than merely density in the whole space.
- For every upstairs component generic point, the next conjunct gives membership in
  the inverse image complement, a downstairs component with its generic point, and
  `IsIso (J.blowupMap.stalkMap ξ)`. The following `∃! ξ` gives one and only one component
  generic point over every downstairs generic point. Together these are the stated
  generic-point bijection and canonical identification of local rings.
- The last conjunct quantifies over all ambient P, all closed immersions i, and all
  finite-type ambient ideals I with `I.comap i = J`. Its iso to `I.strictTransform i`
  commutes with the intrinsic map and the map through the ambient blowup. The published
  strict transform is the scheme-theoretic image of the open, retaining nilpotents.
  No ambient or center regularity, ambient local Noetherianity, or global reducedness
  has been added.
- `genericallyReduced_smooth_geometry` binds arbitrary `v : Y ⟶ X` with `[Smooth v]`.
  It gives local Noetherianity of Y, generic reducedness of its actual stalks, and
  preservation of component generic points. It also records the empty interior of
  extended nowhere dense finite-type centers and `IsIso (J.blowupFlatBaseChange v)`;
  this is the canonical published Rees/Proj comparison, not an unspecified iso.
- `genericallyReduced_strictTransform_smooth_diagrams` binds any finite diagram D.
  The local Noetherian and generic reducedness assumptions apply only to the intrinsic
  initial scheme, as in the item. An arbitrary smooth map W → P₀ yields a new diagram
  E with a Comparison and a specified initial ambient isomorphism to W over P₀.
  The Comparison has cartesian intrinsic squares at every level, cartesian ambient
  squares at every step, extended center equalities, and an equation identifying its
  next ambient map with the actual `blowupFlatBaseChange` followed by projection.
  Consequently its intrinsic closed images are the corresponding scheme-theoretic
  strict transforms; this is a statement about schemes and ideal sheaves, not supports.
- For every earlier stage j and every level k ≥ j, two displayed ideal equalities retain
  the earlier ambient ideal and its restriction to the intrinsic scheme. In particular
  neither equality discards the intrinsic ideal when the intrinsic blowup is an iso.
- If `(E.center j).support = ⊥`, both transition morphisms are `IsIso`. Their actual
  source and target schemes may differ as chosen models of an identity stage.
- The uniqueness conjunct says comparisons with the same initial ambient and intrinsic
  maps have equal entire natural transformations. The identity conjunct normalizes
  them to the identity transformations. The composition conjunct gives a Comparison
  whose transformations are exactly the composites, so further smooth pullback is
  compatible, rather than just isomorphic by an unspecified choice.
- The final conjunct spells out the iterated first assertion: up to every stage whose
  preceding intrinsic centers have empty interior, the pulled-back intrinsic scheme
  remains locally Noetherian and generically reduced. It requires no ambient regularity.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Noetherian: `AlgebraicGeometry.IsLocallyNoetherian`, with
  its every-affine-open definition and local finite-type ascent.
- Mathlib.AlgebraicGeometry.Properties: `AlgebraicGeometry.IsReduced`; reducedness at
  a particular generic stalk uses its underlying ring predicate `_root_.IsReduced`.
- Mathlib.Topology.Sober: `IsGenericPoint` (closure of the singleton).
- Mathlib.Topology.Irreducible: `irreducibleComponents` (maximal irreducible subsets).
- Sheaf.AlgebraicGeometry.IsRegularScheme: `AlgebraicGeometry.IsRegularScheme` is
  local Noetherianity together with the upstream stalkwise IsRegular predicate. The
  ring clause used here is Mathlib's `IsRegularLocalRing` from RegularLocalRing.Defs,
  exactly the ring clause of the same recorded dependency.
- Sheaf.AlgebraicGeometry.CoherentFiniteType: `Scheme.Modules.IsQuasiCoherentFiniteType`
  and its public standard module predicates. For ideals, the actual existing finite-type
  predicate is `Scheme.IdealSheafData.ofFiniteType` in
  WeilConjectures.Compactification.FiniteTypeExtension (FG on every affine open).
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth`, allowing variable relative dimension.
- WeilConjectures.Blowup.Gluing: `Scheme.IdealSheafData.blowup` and `blowupMap`.
- WeilConjectures.Compactification.StrictTransform: `strictTransform`,
  `Scheme.IdealSheafData.strictTransform`, `strictTransformMap`, `strictTransformToSource`.
- Mathlib.AlgebraicGeometry.IdealSheaf.Functorial: `Scheme.IdealSheafData.comap`,
  `comap_comp`, and `comapIso` (the kernel of the pulled-back closed immersion).
- WeilConjectures.Blowup.FlatBaseChange: `blowupFlatBaseChange` and
  `blowupFlatBaseChangeIso`. The dependency has no lean record, but its closed upstream
  audit names this module and declaration. Its actual factor order is Bl ×_X Y;
  this harmless chosen pullback model is used consistently in the canonical equation.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback` and its projections.

All recorded proof-dependency modules that exist are imported, using plain imports for
proof-only modules. The chart-restrictions proof node currently has neither a Lean record
nor an upstream audit and supplies no import. Its coefficientwise calculation remains
explicit in the theorem proof docstring. The closed upstream flat-base-change theorem is
already supplied by the public FlatBaseChange import. Mathlib leaf APIs are supplied by
their corresponding imported modules, including minimal primes, Krull dimension zero,
going down and regular local rings. No proofs were written in this delivery.

Edge cases checked before writing: empty X (all generic-point assertions vacuous); empty Y
for a nonsurjective smooth map; multiple irreducible components; embedded nilpotents away
from the generic points (no global reducedness assumption); unit center J (support empty,
identity blowup); zero ideal on an empty scheme (allowed); zero ideal on a nonempty scheme
(fails nowhere-dense hypothesis, as it should); nonregular center and ambient scheme;
principal invertible non-unit center with identity intrinsic blowup (earlier ideals retained);
zero-length diagrams (Fin 0 has no centers); arbitrary finite lengths; further identity
and composite pullbacks; variable relative dimension. One explicit universe u controls
all schemes and test schemes. Both autoImplicit options are false.

Searches made with msearch.py, Q123 and this item:

1. LeanFinder: "A blowup of a locally Noetherian generically reduced scheme is generically
   reduced and smooth pullback preserves this property" — eight results for normalization,
   ordinary reducedness and smoothness, none the statement.
2. Loogle: `"blowup", "baseChange"` — zero hits.
3. Mathlib grep: `genericallyReduced|generically_reduced|strictTransform`, AlgebraicGeometry
   — zero hits. Direct rg of the project and upstream for generic-reducedness and the item
   id — no existing item declaration. The published Blowup.FlatBaseChange and
   Compactification.StrictTransformBlowup were found by direct source searches and reused.
4. LeanSearch and LeanFinder searches for finite ambient diagrams, and direct rg of existing
   tower structures, are recorded in the new node. OrdinaryBlowupTower is intrinsic only;
   LabeledEmbeddedResolutionTower/History require rational smooth/reduced inputs and
   regular centers. They cannot encode the present unrestricted diagram.
5. `tools/blueprint_refs.py search 'finite blowup strict transform diagram'` — zero matches;
   ancestor query gives lem-per-artin-gabber-affine-curve. Proposed declaration names were
   absent from Mathlib, WeilConjectures, Sheaf, DAG records and dag/lean_names_upstream.json.

Validation: scompile.py compiled each module independently, in dependency order, against
published live sources. Both sandbox and library-path compilations succeeded, with no
errors or unexpected warnings. The only postponed proofs are the three named theorems.

## New nodes

`def-per-finite-embedded-blowup-diagram` supplies the missing finite uncontracted diagram
and canonical smooth Comparison. Its two real-data structures use the existing blowup,
scheme-theoretic strict transform, ideal extension and pullback constructions; no data or
proof field is filled by sorry. Source: Stacks 080E and 0805 iterated, with 081I for the
closed subscheme squares, precisely item proof steps 7--9. The new node records the
LeanSearch, LeanFinder and grep results and why the more restrictive existing resolution
towers cannot serve. It imposes no regularity, reducedness or center nonemptiness. The
item cites it directly. There is no new generically-reduced predicate: that condition is
written directly from the recorded generic-point, component and reduced-ring notions.

## Second reading by Q123

The dispatcher explicitly prohibits starting another agent; this is a separate rereading
pass by the worker, not an independent-person review. The maintainer's independent review
still reads the delivery. I reread the item and both complete modules together. In the
first pass I noticed that an existence-of-isomorphism statement alone would fail to
normalize flat comparisons and would not retain the earlier intrinsic ideals; the final
Comparison.canonical equation and the second earlier-ideal equality address these. I also
added the explicit identity-comparison clause and the intrinsic canonical flat-comparison
isomorphism clause. Rechecked density in the component subtype rather than the whole
scheme, the uniqueness quantifier over actual generic points, and IsIso on the canonical
stalk map. The final sources contain no extra regularity, reducedness or characteristic
hypotheses. The new data structure has all transition maps as functors, so length-zero,
composition and naturality are meaningful without hidden file-local notation or instances.
No item statement correction, disputed statement, or dependency-interface repair is needed.
