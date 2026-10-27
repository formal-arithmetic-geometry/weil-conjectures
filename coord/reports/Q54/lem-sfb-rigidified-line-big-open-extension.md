## Worker report

The module `Sheaf.AlgebraicGeometry.RigidifiedLineBigOpenExtension` states
`AlgebraicGeometry.exists_rigidified_line_big_open_extension`, with one `sorry` proof
and no new definitions. Its declaration docstring carries all ten accepted DAG proof
steps, including boundary isolation, descent of the specified comparison, rank-one
normalization, and gluing of both the line and its rigidification.

The inherited BLOCKED ending concerned the stage-1 delivery already merged from Q24.
The current node has no Lean record and `coord/queue.tsv` lists it at stage 2. The
2026-10-22 stage handoff in `coord/brief-stage2.md` §0 explicitly permits this work;
Q24's accepted split is preserved. The current returned-delivery repair is recorded below.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The normal integral locally Noetherian base is `(S : Scheme.{u})`, `[IsIntegral S]`,
  `[IsLocallyNoetherian S]`, and `hnormal : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
  IsIntegrallyClosed (S.presheaf.stalk s)`. This is exactly the node's explicit local
  normal-domain convention, with no assumption of global Noetherianity or regularity.
- A group scheme over S is `(G : Over S) [GrpObj G] [IsCommMonObj G]`. Its total scheme
  is `G.left` and p is `G.hom`. The multiplication, inverse, identity and all group
  identities are precisely the existing categorical group-object structure. The
  identity is `η[G].left`; `by simp` supplies its section identity for `sectionBaseChange`.
- Smooth, separated, finite presentation are `[Smooth G.hom]`, `[IsSeparated G.hom]`,
  `[LocallyOfFinitePresentation G.hom]` and `[QuasiCompact G.hom]`. Separatedness supplies
  the quasi-separatedness part of finite presentation, so no finiteness hypothesis is
  missing. `IsSeparated` is the closed-diagonal condition stated in the node.
- Connected geometric fibres are `[GeometricallyConnected G.hom]`: Mathlib defines this
  by connectedness after every field-valued base change. This agrees with connected
  geometric fibres (connectedness descends under field extension). The identity section
  guarantees nonempty fibres, so ConnectedSpace adds no extra nonemptiness restriction.
- The dense open subscheme is `(U : S.Opens) (hU : Dense (U : Set S))`; its inclusion is
  `U.ι`, and G_U is exactly `pullback G.hom U.ι`.
- The given line is `N : (pullback G.hom U.ι).Modules` with `[N.IsInvertible]`, using the
  recorded scheme invertibility predicate, not a new notion or an arbitrary sheaf.
- The given rigidification `r` is an actual isomorphism from tensor inverse image of N
  along the canonical base-changed identity `sectionBaseChange ... (Over.mk U.ι)` to
  `SheafOfModules.unit U.toScheme.ringCatSheaf`. All displayed module inverse images
  use `Scheme.Modules.tensorPullback`, never the unrelated chosen abstract pullback.
- The enlarged open is `∃ (V : S.Opens) (hUV : U ≤ V)`. It contains every s with
  `ringKrullDim (S.presheaf.stalk s) ≤ 1`. Dimension is Mathlib's WithBot ℕ∞ value,
  including infinity. The equivalent complement-dimension-at-least-two clause follows
  because the local rings of a locally Noetherian integral scheme have nonnegative
  integer or infinite Krull dimension. No extra tautological conjunct is added.
- The extension is `∃ N_V : (pullback G.hom V.ι).Modules, N_V.IsInvertible ∧ ...`, and
  `r_V` is an actual identity tensor-pullback isomorphism to the structure module on V.
- The comparison `α` is an actual isomorphism from tensor pullback of N_V along
  `baseChangeMap G.hom (Over.homMk (S.homOfLE hUV) ...)` to N. The two over-objects
  are explicitly U and V; its map is the canonical G_U → G_V.
- Rigidification preservation is the final equality. Its left side pulls α back along
  e_U and then applies r. Its right side passes from e_U-star i-star N_V through
  pullback of the common composite to (U→V)-star e_V-star N_V, applies pulled-back r_V,
  and finally the canonical map from the pullback of O_V to O_U. The commuting square
  is exactly `sectionBaseChange_comp_baseChangeMap`; the two comparison isomorphisms
  are `tensorPullbackCompositionIso`. No arbitrary comparison or unit normalization
  is quantified over. The final structure-module map is the canonical definition; its invertibility theorem
  is not used in this statement.
- There is no assertion that S's entire regular locus is open.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, together
  with `IsDomain`; the local form is exactly def-weil-pbc-normal-ring's normal domain.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`; quasi-compactness is included explicitly.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`, as
  supplied by the canonical inclusions of the opens U and V.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`, the upstream real tensor functor
  publicly imported by the recorded dependency's repaired interface.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor` was read. No module stalk functor is needed in
  the statement: the only stalks used are Mathlib's existing structure-ring stalks
  `S.presheaf.stalk s`. There is no duplicate stalk construction.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`:
  the dependency's fibre-product convention `pullback`, `baseChangeMap`,
  `sectionBaseChange`, and `sectionBaseChange_comp_baseChangeMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, used through `IsSeparated`'s closed diagonal.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackCompositionIso`.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackObjUnitToUnit`, owned by the live
  `existing: true` node `def-sfb-tensor-pullback-structure-sheaf-map`. This is the plain
  canonical definition; `tensorPullbackObjUnitToUnit_isIso` is not used.

The already-landed definition nodes `def-pc-tensor-pullback-composition-iso` and
`def-sfb-tensor-pullback-structure-sheaf-map` are added to stmt_deps to record the
canonical comparisons used in the compatibility clause; neither statement nor proof
is changed.
There are no new nodes or dependency replacements. All recorded Lean proof-dependency
modules are imported privately unless also used in the statement. The unstated
`lem-trf-fp-module-limit-isomorphism-descent` remains in the proof docstring and DAG;
it is not needed to type the statement, so no substitute theorem is invented.

Edge cases checked: U=S permits V=S and identity comparisons; a field base forces U=S;
a DVR with the generic-point open permits the trait line extension with its exact
rigidification; in dimension one all of S must be retained. For a normal surface,
intersections of distinct boundary divisors may be omitted, but their generic points
must be retained. For a locally Noetherian non-quasi-compact base there is no global
finiteness assumption or finite cover imposed. Infinite local dimension is permitted
in the omitted complement. The empty base is excluded by the node's integrality
hypothesis; the empty open is excluded by density on that nonempty base. The trivial
relative group and relative dimension zero remain included. All universes and variables
are explicitly bound; there are no file-local instances, notations or private copies.

Searches (UTC date 2026-10-23; through the prescribed msearch wrapper and source reads):

- LeanFinder: “A rigidified invertible module on a smooth connected commutative group
  over a dense open of a normal locally Noetherian base extends over an open containing
  all codimension one points”. Eight hits: ModuleCat.Tilde local-fraction results,
  free-locus openness and StructureSheaf.normalize_finite_fraction_representation;
  none states this extension theorem.
- Loogle: `AlgebraicGeometry.Scheme.Modules.IsInvertible,
  AlgebraicGeometry.IsCommGroupScheme`. Zero hits, unknown project identifier; the
  direct source search found the existing invertibility and group-object encodings.
- Mathlib grep: `rigidif|Rigidif|invertible.*extension` under AlgebraicGeometry: zero hits.
- LeanSearch: “rigidified line bundle extension open normal scheme codimension two”.
  Eight hits on FormallyUnramified recursors and scheme normalization; no match.
- rg on WeilConjectures and Sheaf: `Rigidification|rigidification|Rigidified|rigidified`,
  the exact node id, and `big.open.*(extension|rigidif)|rigidif.*big.open|rigidified.*extend|
  extend.*rigidified`. No copy of the requested statement. Found the regular-base
  algebraic-space extension and its rigidified-space line category; these require a
  regular base and use the algebraic-space module site, so are not this normal-base
  scheme-module statement. Their modules were read, not privately redefined.

Source status: the node and Q24's report explicitly mark the original Moret-Bailly
II 3.2.2--3.2.3 text WANTED. This delivery preserves that honest provenance. The local
Stacks source statements at Tags 00PD, 0BD9, 01ZR, 0B8W and 04TR were opened; they are
exactly the DVR, invertible-extension, object/map descent and sheaf-gluing ingredients
of the accepted ten-step assembly. No new attribution or statement correction is made.
No STATEMENT-DISPUTED fault found.

Validation: scompile.py compiled both the sandbox module and its intended library
module cleanly (2.6 and 2.7 seconds). An initial inference timeout at the comparison
isomorphism was repaired by explicitly specifying both Over objects in Over.homMk;
no timeout or heartbeat limit was increased. The single theorem proof is exactly `by sorry`.
The delivery dry run passed preflight and compiled at de85fd1dad3; nothing was pushed.

## Second reading by Q54

This is a second self-reading, not a claim of an independent agent review: the dispatcher
forbids starting other agents and the maintainer independently reviews the delivery.
I reopened the full node and the final signature. The checks above cover each binder
and clause. In particular I rechecked the direction of α, both tensor composition
isomorphisms, and the common target O_U of the rigidity equation. The canonical square
has e_U followed by G_U→G_V equal to U→V followed by e_V, matching the two inverse-image
paths exactly. The inverse comparison is used first, then the forward comparison.
Finite presentation is locally finite presentation plus quasi-compactness and the
quasi-separatedness already supplied by separatedness. All connectedness, normality,
commutativity and density assumptions were retained although the existence proof can
use less. No strengthening to a regular, Noetherian, proper or quasi-compact base was
introduced. Only the explicit Over endpoints changed during elaboration repair.

## Returned delivery repair (H2)

The independent review of immutable head `dd1e87b31afe` requested replacing
`lem-weil-pbc-module-pullback-structure-sheaf` in stmt_deps with the landed definition
node `def-sfb-tensor-pullback-structure-sheaf-map` (Q73, 2026-10-23). This replacement
is made. I read the live definition node and its recorded upstream declaration in
`WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`. The declaration
`AlgebraicGeometry.Scheme.Modules.tensorPullbackObjUnitToUnit` defines the canonical
morphism using the inverse adjunction bijection applied to the structure-sheaf map.
The rigidity equation uses this plain definition; it does not choose data from the
isomorphism theorem or use `tensorPullbackObjUnitToUnit_isIso`.

The saved packet was retained. Its initial required dry run passed at `e307066bbbe`.
Comparison with the live node showed differences only in lean and the two added
stmt_deps; all inherited node fields match current main. The Lean source is unchanged
by this repair, as the reviewer requested. The lean record date is refreshed to UTC.
There are no new nodes, dependency modules, or changes to the mathematical statement.

The second self-reading for H2 checked the final equation against the definition's
domain and codomain: the map takes the tensor pullback of the structure module on V
to the structure module on U, exactly the target required after pulling back r_V.
Thus definition ownership suffices. The independent maintainer's substantive review
remains applicable to the unchanged signature and docstrings.

Repair validation: scompile.py compiled the delivered file cleanly in both sandbox
and intended library contexts (2.6 s and 2.7 s). The signature record is verbatim,
all Lean lines have at most 100 characters, the sole theorem remains postponed,
and comparison with current main confirms only lean and the two intended definition
stmt_deps differ. The H2 theorem dependency is absent from the repaired stmt_deps.
