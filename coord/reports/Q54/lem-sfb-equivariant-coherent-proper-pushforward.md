## Worker report

Repair of immutable returned head 69ec64e940d2, H4. The required initial dry run
of the saved packet passed mechanically (ee8d761fb6b), but the independent return
correctly identified its duplicate mathematical notions. This delivery repairs
that defect rather than treating the dry run as mathematical approval.

The theorem `AlgebraicGeometry.EquivariantCoherent.equivariant_coherent_proper_pushforward`
states `Nonempty (ProperPushforwardSystem k)`. Its witnesses are the constructions
asserted by the node, not additional hypotheses. The original mathematical
statement, twelve-step proof and proof dependencies are unchanged. The only
postponed proof is this theorem, whose docstring gives those twelve steps.

The coherent and rational interfaces are now Q60's exact landed declarations:
`Sheaf.AlgebraicGeometry.EquivariantCoherentGZero` supplies
`ActionGroupoidModel`, `Coherent`, `underlying`, `underlyingMap`, `linearization`,
`GZero`, `classOf`, `IsTensor`; `Sheaf.AlgebraicGeometry.RationalRepresentationGZero`
supplies `RationalModule`, `Representation`, `coordinateHopf`,
`RepresentationGZero`, `representationClass`, `IsRepresentationRing`,
`IsAssociated`, and `IsRepresentationAction`. Both owning DAG nodes are direct
statement dependencies. Their full source, signatures, predicates and docstrings
were read. No copy of their category, coactions, quotient relations, ring,
associated bundle or representation-action definition remains.

The smaller new module retains only geometric bundles and missing operation
interfaces, in the disjoint namespace
`AlgebraicGeometry.EquivariantCoherent.ProperPushforwardData`. Thus it declares
none of Q60's colliding full names `Coherent`, `relations`, `coordinateHopf`, or
`representationClass`. The point comparison uses Q60's `IsAssociated`; it defines
no second associated bundle. `actionIso` is only the folded inverse of Q60's
`linearization`, with no new action data.

| Node hypothesis or clause | Exact Lean rendering |
| --- | --- |
| Base field F | Explicit `(k : Type u) [Field k]` and explicit `universe u`; autoImplicit and relaxedAutoImplicit are false. |
| Affine finite-type G | `ProperPushforwardData.Group`: actual `Over (Spec (.of k))`, `GrpObj`, `IsAffine`, `LocallyOfFiniteType` and `QuasiCompact`. |
| Arbitrary scheme Y with action | `Space` has only its original Over scheme and `ModObj`; no finiteness is imposed. |
| Coherent module with identity and cocycle | Q60 `Coherent (model G X)` is the coherent full subcategory of actual `Scheme.GroupoidModule`. `model` witnesses the genuine action groupoid whose composition is pinned on every scheme-valued test. `linearization` has the node's a* to p* direction; `actionIso` is its inverse, the fibre direction y to gy. |
| Isomorphism classes and every equivariant short exact sequence | Q60 `GZero` is its free abelian quotient by exactly those relations, `classOf` its generator. Morphisms are the actual descent-intertwining morphisms, not a test on geometric points. |
| Finite-dimensional rational coactions and R(G) | Q60 `Representation k G.scheme` is `RationalModule` with finite `space`, counital coassociative coaction for the canonical coordinate Hopf algebra. `RepresentationGZero` is its SES quotient. `representationRing_spec` is Q60 `IsRepresentationRing`, pinning multiplication and unit to its tensor and trivial coactions and retaining the quotient additive group. |
| Tensoring gives an R(G)-module for every action scheme | `moduleAction` is an actual Module on these same quotient groups for every `Space`. `tensor_class` identifies its generator action with the finite direct sum of M indexed by a basis of V; the action matrix is extracted from V.coaction and pulled back along pr1, composed with the inverse of Q60's existing linearization. This is the trivial-bundle tensor action, including dimension zero. |
| Same associated-bundle action on finite-type schemes | `moduleAction_spec` is precisely Q60 `IsRepresentationAction` on `FiniteSpace`. Such schemes are Noetherian. Q60's predicate also requires the associated bundle itself to be coherent and every coherent tensor representative to exist; imposing that on an arbitrary noncoherent scheme would be an extra hypothesis. The finite-direct-sum formula above gives the stated action on arbitrary schemes without that strengthening. No new action predicate is defined. |
| X,Y separated finite type | `FiniteSpace.finiteSeparated` is IsSeparated, LocallyOfFiniteType and QuasiCompact on their structure maps. |
| Proper equivariant f | `ProperMap` retains the actual Over map, `IsModHom`, and `IsProper` on its underlying scheme map. |
| Coherent natural higher images | `image`, `imageComparison` identify a Q60 coherent equivariant object with the existing `schemeModuleHigherDirectImage` in degree q. `naturality` lifts every Q60 equivariant map to the actual transported higher-image map. |
| Canonical linearization in every q | `imageAction` requires `IsHigherPushforward` in all degrees, with exactly the accepted exchange equation. Q60 `linearization.inv` replaces the former custom all-test lift. `pullbackExact` supplies projection/action exactness, ensuring the universal equation is nonvacuous. |
| Ordinary action in degree zero | `ordinary` identifies the image with actual module pushforward, and `ordinaryAction` retains the accepted ordinary base-change equation. |
| Vanishing q sufficiently large | `vanishing`: a natural bound and IsZero of the underlying image for every greater q. |
| Alternating homomorphism | `push` is an additive homomorphism on Q60's GZero. `euler` specifies its value on every classOf M using any valid finite cutoff and (-1 : Z)^q. |
| R(G)-linearity | `linearity` uses the same actual `moduleAction` on both quotient groups, for every virtual representation and every element. |
| Composition | `composition` quantifies every composable proper equivariant f,g and proper equivariant h whose actual map is f then g. |
| Closed-subgroup restriction | `ClosedSubgroup` is a closed group-scheme homomorphism. `RestrictedSpace.compatibility` pins its action on the same scheme to h followed by H to G. `IsRestriction` identifies the same underlying module with the pullback of Q60's actual descent isomorphism along H times X to G times X, with section-normalized compositors. `restrict_class` pins its homomorphism to those objects, `restrictedMap_eq` retains f exactly, and `restriction_push` is the required commutative square. No flatness of H to G is assumed. |
| Spec F identification | `point` is Spec k with trivial action. `pointEquivalence` is an additive equivalence between Q60's existing GZero and RepresentationGZero, and `point_class` is normalized on every Q60 associated bundle. Existence of associated bundles follows from moduleAction_spec at finitePoint; no arbitrary equivalence can satisfy an unrelated character twist. |
| Finite-dimensional rational cohomology and alternating class | `cohomology` supplies Q60 rational Vq whose spaces are isomorphic to the existing Zariski `Scheme.Modules.H`, and requires `IsAssociated k (V q)` of the very higher-image object. It states eventual zero and the alternating representation-class formula under the same pointEquivalence. |
| Closed immersion: extension by zero | `closedImmersion` is the degree-zero class formula; `ordinary` and `ordinaryAction` identify this with ordinary direct image with its canonical action. Ordinary direct image for a closed immersion is extension by zero. |

The previously accepted H3/H2 repair is retained. `higherBaseChange` is the
normalized exact-pullback cohomology comparison, cohomology of the inverse
`exactPullbackComparison`, cohomology of the actual `schemeDerivedBaseChangeMap`
on M[0], and cohomology of direct image of the normalized single comparison.
`exactPullbackComparison` is left-derived uniqueness for the same counit chosen
in `exists_derivedPullbackComposition` and used by schemeDerivedBaseChangeMap.
The composition theorem is genuinely used in both helpers, hence its public
import and statement dependency remain. The exact-cohomology definition node is
still existing:true on `Functor.mapDerivedCategoryHomologyFunctorIso`, read
verbatim in its upstream module; direction F(H^n K) to H^n(D(F)K), normalization
and independent category/localization universes agree with Stacks 015F.
No dependency record is replaced, and pqf-def-coherent is not in the packet.

Other recorded dependency declarations read: `GrpObj` (Mathlib monoidal Grp),
`Scheme` and Scheme.Hom, `IsProper`/`IsSeparated` (Mathlib morphisms),
`LocallyOfFiniteType`/`QuasiCompact`, `RingedSpace.IsCoherent` (upstream Coherent,
publicly exposed by Q24 CoherentFiniteType), `tensorPullback` and its
section-normalized adjunction/compositors (TensorPullbackSectionAdjunction),
`schemeModuleHigherDirectImage` (upstream SchemeDerivedDirectImage),
`moduleBaseChangeMap` (upstream ModuleBaseChangeMapOpenRestriction), and
`schemeDerivedBaseChangeMap`. Proof dependency imports are preserved. The two
proof nodes without available recorded modules in the read snapshot are
`lem-pod-texact-truncation-triangle-comparison` and
`lem-sfb-linearized-qcoherent-cohomology-coaction`; the theorem docstring names
them, and no statement depends on their missing theorem interfaces.

Edge cases: zero coherent module, zero-dimensional representation (empty sum),
empty schemes, identity proper maps, trivial groups, all characteristics,
nonreduced affine groups and closed subgroups (alpha_p/mu_p), nonflat subgroup
inclusions, every higher degree including zero and vanishing degrees, and any
valid vanishing cutoff. The restriction equation is on scheme products and
uses no flatness of the subgroup map. The action equation is the accepted
all-degree normalization, not merely naturality; higher-degree character twists
therefore fail it. All scheme and module universes remain u, with the standard
shared derived localization at u+1. Definitions have real data and no sorry.

Searches: the original packet's msearch search evidence is preserved in the new
node, explicitly labelled historical and superseded where Q60 now provides a
match. Repair searches used LeanFinder for restriction of a group-scheme
linearized coherent sheaf to a closed subgroup and equivariant proper higher
direct images (ordinary restriction and abstract-group Rep adjunction hits);
Loogle `"pushforward", "coherent"` (five ordinary quasicoherent pushforward
hits); LeanSearch for proper equivariant morphisms with higher direct images
and subgroup restriction (ordinary IsProper and topological proper-action
hits); Mathlib grep `IsRestriction|ProperPushforwardSystem|IsPointEquivalence`
in AlgebraicGeometry (zero hits). `rg` in dag/nodes, lean/WeilConjectures and
lean/Sheaf found Q60's landed notions, now reused, and no missing-interface
match. Blueprint search for proper pushforward was also read. Actual queries
and results are preserved in searches.jsonl and the definition node.

Source reading: current blueprint latest main-20261024, ef6f9619, and the
inherited supporting-node chain; Stacks coherent.tex 02O5 (proper coherent
higher images), 02O6 (finite cohomology), 02KH (flat base change) and Q60's
03LF-normalized associated action. The node honestly identifies this as an
agent-supplied supporting prerequisite; it does not pretend Milne 22.50 proves
it. No mathematical statement correction or STATEMENT-DISPUTED fault arises.

## Second reading by Q54

The dispatcher forbids spawning agents, so this is a separate self-audit and
not a claimed independent review. With the node and both current modules open,
I checked the above table against each hypothesis and clause. The H4 return was
correct: the saved groups module duplicated Q60's objects and quotients. I
removed those declarations entirely, used Q60's category and both quotients,
and moved the remaining interfaces into ProperPushforwardData. The old
AssociatedRepresentation, SheafTensor and RepresentationRing structures are
gone. Q60's IsAssociated, IsRepresentationRing and IsRepresentationAction now
pin the corresponding witnesses directly.

I checked the action orientation: Q60 beta is a* to p*, hence beta inverse is
the former theta p* to a*. Both ordinary and higher exchange equations keep
their original orientation. The subgroup comparison pulls beta itself back,
with the inverses of the section-normalized composition isomorphisms pointing
from iterated to composite pullbacks. Its square gives exactly the original
restricted action. I also caught the arbitrary-scheme coherence issue above:
moduleAction_spec is on finite-type schemes, while tensor_class retains the
full arbitrary-scheme tensor action, without requiring coherent O_X. The
Spec-k normalization uses exactly Q60's existing associated bundle and not a
second tilde/coaction definition. All-degree exchange, exactness nonvacuity and
the chosen counit are preserved. No original node statement or dependency
record is edited.

## New nodes

`def-sfb-equivariant-coherent-groups` is reduced to geometric and missing
operation interfaces: affine finite-type group/action bundles, finite separated
spaces, actual proper equivariant maps, existing higher images, closed subgroup
restriction and point equivalence normalization. It reuses and cites both Q60
nodes, the tensor-pullback node, properness, finite type and derived direct image.
Every declaration is in ProperPushforwardData and has its source/blueprint
docstring. Its source is the same proper-pushforward prerequisite with Stacks
03LF, 01T0, 02O5/02O6. The repair searches and their now-existing matches are
recorded; this node no longer claims to introduce coherent/rational quotients,
associated bundles or representation actions.

`def-sfb-exact-derived-cohomology-comparison` remains the accepted existing:true
record of `CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso` in
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, verbatim.
Its actual localization-lift construction and representative normalization were
reread. It owns that canonical comparison, not its coherence theorem. It has
no new module or duplicate definition.

## Dependency modules

None. Q60's nodes and modules and Q24's coherence record remain unchanged.

During compiler self-check, I fixed a genuine name-resolution issue caused by
opening the nested namespace: the group bundle is explicitly qualified as
`ProperPushforwardData.Group`, avoiding the unrelated root algebraic Group
class. I also normalized the action/projection square maps to Q60's actual
`target` and `source`, rather than asking Lean to identify the universal
point-expression `fst • snd` definitionally with the action morphism. This is
the same mathematical square. Finally, the point additive equivalence and its
normalization are bound before representationRing, fixing their additive
instances to the canonical quotient structures; IsRepresentationRing then
requires the ring's additive structure to equal precisely that structure.

Validation: the prescribed scompile.py compiled both current delivered modules
with exit 0 and no Lean errors or unexpected warnings. The final proper
pushforward library compile reports 44.6 seconds. The wrapper's cumulative
cached/slot-acquisition timing is not a raised per-file limit: every file still
uses its unchanged 60-second compiler limit. Diagnostic probe modules and all
#check commands are removed. The packet contains exactly two Lean modules,
three node records (two new definitions and the item), and this report. JSON
layout, verbatim signatures, citation lists, 100-character lines, explicit
universes and variables, no definition sorry and the single named theorem sorry
were checked. The item's only changed fields against the current read clone are
lean and stmt_deps; all original statement dependencies are retained. The new
module's declaration list has empty intersection with both Q60 declaration
lists. Both Q60 owning nodes are cited directly and through the reduced
interface node. The accepted exact-cohomology record remains unchanged.
