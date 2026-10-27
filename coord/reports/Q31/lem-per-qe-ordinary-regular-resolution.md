## Worker report

The theorem `AlgebraicGeometry.exists_regular_functorial_qe_ordinary_resolution` in
`Sheaf.AlgebraicGeometry.QEOrdinaryRegularResolution` states exactly the existence of
one rule on all reduced Noetherian quasi-excellent rational schemes. Its only proof is
`sorry`. Its docstring gives all six steps of the accepted split, including Noetherian
stabilization using pointwise finite prime height rather than finite global dimension.
The separate definition module has actual structure/predicate data and no sorry.

The previous worker's stage-1 supersession diagnosis does not block this stage-2 task:
`coord/brief-stage2.md` section 0 explicitly says that an accepted split without a usable
Lean record is ready to state. The live item has no Lean record, the current queue marks
it stage 2, and no released repair note exists. I preserve Q21's entire accepted split,
statement, proof and proof dependencies. Only `lean` and the addition of the new
interface definition to `stmt_deps` change.

I read the original seven statement-dependency records and their source declarations,
the new interface's reused tower/comparison and scheme-quasi-excellence definitions,
and ILO VIII printed pp.91--94 directly in the archived PDF. I also read the latest
blueprint ancestor `lem-per-artin-gabber-affine-curve` and its proof; the assigned item is
a supporting input, not the blueprint unit's own statement. No statement correction or
mathematical dispute is needed.

Clause-by-clause rendering (all names below are in namespace `AlgebraicGeometry`):

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| One rule simultaneously on the entire category | `Nonempty (RegularFunctorialQEOrdinaryResolution.{u})`, with one `tower` function quantified over every `QERationalResolutionInput.{u}` |
| Schemes over Q | `QERationalResolutionInput.scheme : Scheme.{u}` and `structureMap : scheme ⟶ Spec (.of (ULift.{u} ℚ))`; the lift only matches the size of the rational field to the scheme universe |
| Reduced | `QERationalResolutionInput.reduced : IsReduced scheme` |
| Noetherian, admitting a finite affine Noetherian cover | `QERationalResolutionInput.noetherian : IsNoetherian scheme`; Mathlib's class is local Noetherianity plus quasi-compactness, equivalent to the stated finite-cover convention |
| Quasi-excellent affine coordinate rings | `QERationalResolutionInput.quasiExcellent : GabberModification.QuasiExcellent scheme`, literally `∀ U : scheme.affineOpens, IsQuasiExcellent Γ(scheme,U)` |
| Finite disjoint unions included | There is no connectedness/integrality/separation condition on the input, and no finite-type or dimension bound. Every such finite disjoint union is another input of the same function |
| Finite ordinary blowup tower with initial X | Existing `OrdinaryBlowupTower`, with natural-number `length`, `Fin (length+1)` levels, initial isomorphism, coherent transition maps, `center`, `blowupIso`, and `blowup_fac`; these use the actual ordinary `IdealSheafData.blowup` and `blowupMap` |
| Coherent ideal centers I_i | `coherent_centers` asserts `RingedSpace.IsCoherent` of each actual center's `toModules`; this is the full finite-type/finite-type-kernel definition. `resolves` also retains the existing tower predicate's finite-type clause, equivalent here since all intermediate schemes are Noetherian |
| Nonempty V(I_i) | `resolves` and `OrdinaryBlowupTower.IsRegularResolution` give `Set.Nonempty ((center i).support : Set _)`; support here is V(I), not the ideal module's support |
| Nowhere dense V(I_i) | Same predicate gives `IsNowhereDense ((center i).support : Set _)` |
| Regular V(I_i) | Same predicate gives `IsRegularScheme (center i).subscheme` |
| Regular X_n | Same predicate gives `IsRegularScheme` of the level indexed by the tower's length |
| Every regular morphism f:Y→X between inputs | `comparison S T h over hr`, where `over` is the equality of Q-structure maps and `hr : IsResolutionRegular h`; there is no smoothness or finite-type binder |
| Regular means flat with geometrically regular fibres | `IsResolutionRegular` is `Flat h` and regularity of `pullback h (Spec.map (algebraMap κ(x) K) ≫ X.fromSpecResidueField x)` for every x and every finite field extension K/κ(x). Thus it tests exactly finite residue-field extensions, including the identity extension |
| F(Y) is contraction of scheme-theoretic pullback | Existing `OrdinaryResolutionComparison`: `cartesian` is an `IsPullback` at every original level; `count`, `count_zero`, `count_last` and `deleted_level` record all repetitions and contractions |
| Precisely the unit-ideal centers deleted | `OrdinaryResolutionComparison.deleted_iff_unit`, using actual `IdealSheafData.comap` (extended ideals) and `⊤` (the unit ideal) |
| All remaining actual ideals retained in order | `retainedStage : Fin B.length ↪o Fin A.length`, `count_before`, `count_after` and `retained_ideal`; the last clause identifies the source ideal, after the indicated equality transport, with the extended target ideal |
| Identity compatibility | `identity_count` and `identity_map` give identity counts and identity actual level maps, with the necessary transport between equal level indices |
| Composition compatibility | `composition_count` and `composition_map` give the composite counts and the composites of the actual level maps after the same index transport |
| No deletion for surjective f | `surjective_no_deletion` quantifies over `[Surjective h]` and makes the ordered embedding `retainedStage` surjective |
| Empty input | `empty_input : ∀ S, IsEmpty S.scheme → (tower S).length = 0` |

Identity and composition fields quantify over proofs that the identity and composite
morphisms are regular. These are proof arguments of the laws, not additional hypotheses
on inputs or an assumption on the existence theorem. Identities and composites are
regular in the stated category. Quantifying over these proofs avoids choosing closure
proofs in a data definition. Proof irrelevance makes the comparisons independent of the
particular regularity and over-map witnesses. The cartesian squares, initial tower
isomorphisms and naturality fix the level maps over the blowup towers; they are not
unconstrained comparison arrows. No towers are chosen from a postponed existence proof.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Properties`: `IsReduced` (all open sections reduced).
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian` and `IsNoetherian`
  (the latter extends the former and `CompactSpace`).
- `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent` (Noetherian, G-ring, J-2),
  through `Sheaf.AlgebraicGeometry.GabberModificationData`:
  `GabberModification.QuasiExcellent`, the existing affine-local scheme predicate.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup` and `blowupMap`,
  through `Sheaf.AlgebraicGeometry.OrdinaryResolutionRule`:
  `OrdinaryBlowupTower`, `OrdinaryBlowupTower.toBase`,
  `OrdinaryBlowupTower.IsRegularResolution`, `OrdinaryResolutionComparison`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`, literally
  `IsLocallyNoetherian X ∧ IsRegular X`; no stalkwise-only substitute.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` exposes the original upstream
  `WeilConjectures.AlgebraicGeometry.Coherent` definition `RingedSpace.IsCoherent`.
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module` supplies the actual
  ideal module `Scheme.IdealSheafData.toModules` as a kernel.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`, with its documented stalkwise
  equivalence `Flat.iff_flat_stalkMap`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.fromSpecResidueField`; `Mathlib.AlgebraicGeometry.Fiber` supplies the
  same scheme-theoretic fibre convention via pullback, used here after a finite field
  extension. The canonical map is `Spec.map (CommRingCat.ofHom (algebraMap _ _))`.

Proof-plan imports are `Mathlib.Topology.NoetherianSpace` (minimal closed subsets),
`Mathlib.RingTheory.Ideal.KrullsHeightTheorem` (finite prime height),
`Mathlib.AlgebraicGeometry.PullbackCarrier` (surjective base change),
`WeilConjectures.Blowup.FlatBaseChange` (`blowupFlatBaseChange` and
`blowupFlatBaseChangeIso`) and `WeilConjectures.Blowup.InvertibleCenter`
(`isIso_blowupMap_of_isInvertible`). Flat base change is already publicly visible
through the definition module's flatness import. The two accepted codimension-induction
proof prerequisites currently have no Lean module, so there is no module to import for
them; their full roles remain in the theorem's proof docstring. They are not prerequisites
to typing this existence statement.

Edge cases checked:

- Empty schemes and length-zero towers are admitted; `empty_input` forces exactly zero.
  The general tower and comparison types use `Fin 0` for the empty list of centers.
- Disconnected, mixed-dimensional and non-separated Noetherian schemes are admitted.
- Regular inputs are not excluded. No new requirement about centers lying in the singular
  locus is added; it is not a clause of this node.
- Open regular immersions may delete centers; surjective regular maps may not.
- A nonempty Cartier center is retained even when its blowup is an isomorphism:
  deletion uses the unit ideal, not an `IsIso` test.
- Geometric regularity tests finite field extensions and uses the same universe as the
  residue field; the identity extension is included. Testing all infinite extensions
  with a Noetherian regularity predicate would impose an unwarranted condition here.
- Identity and composite maps retain actual map coherence, not just equality of lengths.
- The input has no global finite-dimensionality bound; the proof docstring uses finite
  height point by point.

Searches made:

- `msearch.py` LeanFinder query: "Ordinary desingularization of reduced Noetherian quasi
  excellent schemes over Q functorial under regular morphisms": eight hits about
  normalization, reducedness and smooth charts; no resolution theorem or matching rule.
- `msearch.py` LeanSearch query: "A regular functorial ordinary resolution rule on reduced
  Noetherian quasi excellent schemes over Q with ordered unit-center contractions":
  eight hits about categorical resolutions and reduced schemes; no match.
- `msearch.py` Loogle query `"desingularization"`: zero hits.
- `msearch.py` Mathlib grep `desingular|BlowupTower|GeometricallyRegular`: zero hits.
- `msearch.py` Mathlib/AlgebraicGeometry grep
  `IsResolutionRegular|QERationalResolutionInput|RegularFunctorialQEOrdinaryResolution|quasi.excellent|desingularization`:
  zero hits. The raw four-kind search records are preserved in the new node.
- Local `rg` in `lean/WeilConjectures`, `lean/Sheaf` and `dag/nodes` found none of
  `IsResolutionRegular`, `QERationalResolutionInput`,
  `RegularFunctorialQEOrdinaryResolution`; item-id search in both source roots found no
  declaration for the item. Concept searches found and reused the ordinary tower and
  comparison, coherent predicate, scheme regularity and `GabberModification.QuasiExcellent`.
- `tools/blueprint_refs.py search 'ordinary resolution'` and
  `search 'regular functorial'` each returned zero blueprint matches. `ancestor` returned
  `lem-per-artin-gabber-affine-curve`; the new node records that ancestor and the full via.
- The existing `RationalResolutionInput` imposes finite type, and
  `SmoothFunctorialOrdinaryResolution` treats only smooth maps. Its existence theorem
  therefore is not this node's statement. Log, fan and normalized towers also do not match.

Validation: both delivered files compile separately through `scompile.py`, including
sandbox and actual-library-module checks, with no warnings or errors. The definition
file took 2.3--2.5 seconds and theorem file 1.7 seconds. No global/local Lake build was run.
A read-only graph traversal found no dependency path from the reused
`def-per-gabber-modification-data` node back to this item, so the added interface does
not introduce a cycle through that broad predicate-owning node.

## New nodes

`def-per-qe-ordinary-resolution-rule` owns `Sheaf.AlgebraicGeometry.QEOrdinaryResolutionRule`:
`QERationalResolutionInput`, `IsResolutionRegular` and
`RegularFunctorialQEOrdinaryResolution`. It packages the full Noetherian quasi-excellent
rational domain, finite-extension fibre criterion, ordered pullback laws, coherence,
surjectivity and empty-input convention of ILO VIII 2.1.12, 2.3.1, 2.3.4--2.3.5(i),
2.3.10 (printed pp.88,91--93). The four search kinds above show no existing full-domain
rule. All component notions already available are reused. In particular, the generic
ordinary towers and comparisons of `def-trf-ordinary-resolution-rule` work without the
finite-type input restriction of that node's separate smooth-functorial rule. This is a
new definition node rather than a repair to that correct finite-type/smooth interface.
No dependency modules or node-statement corrections are supplied.

## Second reading by Q31

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
