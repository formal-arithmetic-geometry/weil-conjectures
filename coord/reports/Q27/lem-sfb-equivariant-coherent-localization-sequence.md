## Worker report

The module `Sheaf.AlgebraicGeometry.EquivariantCoherentLocalizationSequence`
states `AlgebraicGeometry.EquivariantCoherent.equivariant_coherent_localization_sequence`
with `sorry`. It introduces no definitions, no axiom and no additional theorem.
The node's natural-language statement, proof, and proof dependencies are unchanged.
Its statement dependencies gain the two already-landed owning definition nodes
`def-sfb-equivariant-coherent-gzero` and `def-sfb-rational-representation-gzero`.
There are no new nodes or dependency repairs.

I read the item and all nine original statement dependencies (including their
recorded declarations and docstrings), the two added definition nodes and their
modules, and the proper-pushforward module, including `ProperPushforwardSystem`.
I also read the action-groupoid module's actual identity and cocycle equations.
The example CompactObject module is now withdrawn; its node records the identical
upstream declaration, so the delivery follows the required module/public-section
format and current public-import conventions.

Source checked: Milne iAG2017, Section 22d, Theorem 22.50, printed p.480
(`pdftotext -layout`, matching 22.50). Its proof invokes Nielsen/Iversen's fixed
point theorem; it does not assert this localization lemma. This is accurately
labelled an agent-formulated supporting statement, as in the DAG. I read the
actual local Stacks sources: groupoids.tex `lemma-pushforward` (09VH),
`lemma-abelian` (077S), `lemma-colimit-coherent` (07TU), and coherent.tex
`lemma-power-ideal-kills-sheaf` (01Y9) and `lemma-i-star-equivalence` (087T).
The declaration docstring carries all seven accepted proof steps in full,
including extension, graph comparison, lifted exact relations, ideal-power
filtration, descent from the unreduced closed subscheme and tensor linearity.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Field F | `(F : Type u) [Field F]` |
| F-schemes G,Y,W,U | `G Y W U : Over (Spec (.of F))` |
| G group scheme | `[GrpObj G]`, the recorded internal-group definition |
| Affine finite-type G | `[IsAffine G.left] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]` |
| Actions on each scheme | `[ModObj G Y] [ModObj G W] [ModObj G U]` |
| Y separated finite type | `[IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]` |
| Equivariant closed immersion i | `(i : W ⟶ Y) [IsModHom G i] [IsClosedImmersion i.left]` |
| Invariant open complement j | `(j : U ⟶ Y) [IsModHom G j] [IsOpenImmersion j.left]`, with `hU : Set.range j.left = (Set.range i.left)ᶜ` |
| Linearization a* M ≅ p* M with identity/cocycle | `Coherent DY`, `Coherent DW`, `Coherent DU` use `Scheme.GroupoidModule`, its actual pullback identity/cocycle laws, and `RingedSpace.IsCoherent` |
| Fibre action y to gy | The shared `linearization` is a* to p*, and its inverse is the geometric fibre-action direction; `ActionGroupoidModel` pins composition to `(g,h,y) ↦ (gh,y)` |
| Integral groups on isomorphism classes, exact relations | Existing `GZero` is the free abelian group quotient by `relations`, including both isomorphism and equivariant short exact sequence relations; `classOf` is its generator map |
| Rational finite-dimensional representations | Existing `RationalModule` has `Module.Finite`, coaction, counit and coassociativity, with the canonical `coordinateHopf F G` |
| R(G), tensor multiplication | Existing `RepresentationGZero F Γ(G.left, ⊤)`; existential `r` with `IsRepresentationRing r` fixes its additive structure, multiplication on tensor representatives and unit |
| R(G)-action by tensoring associated bundles | `mY`, `mW`, `mU` and `IsRepresentationAction` on each model; `IsAssociated` fixes the trivial bundle and the coaction formula, and `IsTensor` fixes its tensor linearization |
| Ordinary closed pushforward | `push : GZero DW →+ GZero DY`, existence of `IsPushforward i N M` for every N, and its value `push (classOf N) = classOf M` for every such representative |
| Restriction | `restrict : GZero DY →+ GZero DU`, existence of `IsPullback j M N` for every M, and its value on every such representative |
| R(G)-linearity of both maps | The two displayed `push (mW.smul a z)` and `restrict (mY.smul a z)` equations, for every scalar and group element |
| Surjectivity of j* | `Function.Surjective restrict` |
| ker(j*) = im(i*) | `AddMonoidHom.range push = AddMonoidHom.ker restrict` (equality is symmetric) |
| No regularity, W nonreduced or empty | No regularity, reducedness, smoothness, nonempty or closed-subscheme-reduction binder occurs |

Existential models only present the canonical action groupoid on chosen
pullbacks. Ring/module witnesses satisfy the shared normalization predicates;
they are not arbitrary operations. The maps are not unconstrained existential
homomorphisms: they are pinned on *every* generator to ordinary operations,
with existence of those representatives. `IsPushforward` uses the actual
`tensorPullbackSectionAdjunction` and an equivariant counit with invertible
adjoint, so its underlying object is the ordinary `Scheme.Modules.pushforward`.
This is precisely the closed-immersion convention of the proper-pushforward
node. Its formula on all classes uniquely fixes the same group map; no new
higher-image or derived construction is substituted.

Dependency declarations used:

- `Mathlib.Algebra.Field.Defs`: `Field` (read lines 170–180).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` (lines 41–48),
  with the scheme specialization documented in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `Scheme.Hom`; `Over` retains the exact structure map to Spec F.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: the recorded public coherence
  interface. Its public `WeilConjectures.AlgebraicGeometry.Coherent` supplies
  `AlgebraicGeometry.RingedSpace.IsCoherent`, the finite-type/kernel condition,
  which the shared `Coherent` category actually uses. No quasi-coherent/finite-
  type conjunction is substituted for coherence.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsSeparated`
  (defined in Morphisms.Separated). Properness itself is not an extra
  hypothesis: the stated closed immersion already implies it.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` and
  `QuasiCompact` (the latter defined in Morphisms.QuasiCompact).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Sheaf.AlgebraicGeometry.EquivariantCoherentProperPushforward`:
  `equivariant_coherent_proper_pushforward`, `ProperPushforwardSystem`,
  `IsOrdinaryPushforward`; public import retains the stipulated dependency.
  Its closed-immersion convention agrees with the canonical ordinary
  operation specified by the shared `IsPushforward` above.
- `Sheaf.AlgebraicGeometry.EquivariantCoherentGZero`:
  `ActionGroupoidModel`, `Coherent`, `GZero`, `classOf`, `IsPushforward`,
  `IsPullback`, `IsPullbackMap`, `IsTensor`. These supply all actual quotient
  groups and canonical operation predicates; none is defined again.
- `Sheaf.AlgebraicGeometry.RationalRepresentationGZero`:
  `RepresentationGZero`, `coordinateHopf`, `IsRepresentationRing`,
  `IsRepresentationAction`, `RationalModule`, `IsAssociated`.

All recorded proof-dependency modules are imported privately (and the stated
proper-pushforward dependency publicly). The mathlib proof leaves are exposed by
Morphisms.Flat, Morphisms.Affine, Noetherian, Morphisms.QuasiCompact and the
public separated/closed-immersion imports. At the read base,
`lem-sfb-cartesian-groupoid-pushforward-adjunction` and
`lem-sfb-equivariant-coherent-submodule-extension` have no Lean record, so no
nonexistent module import was invented. They are proof-only prerequisites,
not missing notions needed to type this statement. Other private proof imports
are EulerChar, GroupoidModuleLimitsColimits, ClosedImmersionCoherentEquivalence,
CoherentKernelCokernelLocallyNoetherian, CoherentSupportPowerIdealKills,
FlatModulePullbackExact, Modules.QuasiCoherentCokernelImage, and
QuasiCoherentTensorProductAffineSections, under their recorded module roots.

Edge cases checked before writing: trivial group (ordinary coherent G-zero
localization), W empty (restriction to Y), U empty (nilpotent-ideal devissage,
without assuming W = Y scheme-theoretically), Y empty (all groups zero),
W nonreduced (e.g. the closed subscheme t² = 0 in A¹ with trivial group),
n = 0 in the ideal-power argument (the coherent module is zero), arbitrary
field characteristic and nonsmooth/nonreduced G. There is no reductivity or
regular-immersion hypothesis. All universes and variables are explicitly bound;
no independent small test-object universe, arbitrary comparison map, or hidden
`let` occurs in the statement. No statement fault or dispute was found.

Searches actually run, recorded by msearch in searches.jsonl:

- LeanFinder: "Localization exact sequence for equivariant coherent Grothendieck
  groups for a closed subscheme and its invariant open complement". Eight hits,
  headed by `Scheme.IdealSheafData.isLocalization_away`; these are ordinary
  localization/Proj statements, not this equivariant G-zero sequence.
- Loogle: `"Grothendieck", "exact"`. Four hits on topology points and
  Mayer–Vietoris exactness; no equivariant coherent Grothendieck group theorem.
- msearch grep: `equivariant.*(coherent|Grothendieck)|GZero.*(exact|localization)`.
  Zero Mathlib hits.
- LeanSearch: "The sequence of equivariant coherent Grothendieck groups of an
  invariant closed subscheme, ambient scheme, and open complement is right
  exact". Eight hits including `Rep.coinvariantsShortComplex_shortExact`,
  ordinary Ext and group-cohomology exact sequences, and opens restrictions;
  none is the required statement.
- Direct rg of Mathlib AlgebraicGeometry and CategoryTheory for localization
  with Grothendieck/equivariant coherence: no matching theorem.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` by the exact item id,
  localization/GZero, and equivariant coherent/Grothendieck concepts: the Q60
  definitions, Q54 proper-pushforward interface, self-intersection and Tor
  constructions exist and are reused; no existing localization statement.
- Direct rg of `dag/lean_names_upstream.json` and both Lean roots for the new
  declaration name and module name: no prior declaration collision.

Validation: scompile.py compiled the module against the live server library
cleanly (sandbox 2.1 s and library 2.0 s). Only the required wrapper is used;
no local compiler, git mutation, global build or direct preflight was run.

## Second reading by Q27

This is a second source-to-signature pass by this dispatcher-started worker,
not a claim of independent agent review; the brief forbids starting agents,
and the maintainer supplies the independent delivery review.
I reopened the node, the completed Lean file and the operation predicates.
The three scheme actions, equivariance of i and j, and the complement equation
are all separate binders. In particular a merely invariant set without an
open immersion would not satisfy this signature. The group finite-type and
Y separated finite-type conditions have their correct distinct structure
morphisms. Finite type includes quasi-compactness in both places.
The conclusion uses actual integral quotients, not a freely chosen additive
group, and fixes the representation-ring additive structure before its module
actions. The associated-bundle convention uses inverse linearization for the
geometric action, matching the node's y to gy direction.
I checked existence as well as universal normalization of representatives for
both maps, so neither map can be chosen as zero merely to force exactness.
The last two conjuncts are precisely surjectivity and range = kernel; there
is no injectivity assertion at the first term. The scheme W remains the given
closed subscheme, not its reduction. No mismatch or statement correction was
needed. During this pass I made the Mathlib affine/Noetherian/quasi-compact
proof-leaf imports explicit; the theorem signature did not change.
