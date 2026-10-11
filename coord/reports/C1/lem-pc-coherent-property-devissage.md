## Worker report

The module states `AlgebraicGeometry.coherent_property_devissage` for a locally Noetherian,
quasi-compact scheme (`CompactSpace`), a property on `X.Modules`, zero objects, short exact
sequences, and integral closed immersions. Coherence is `RingedSpace.IsCoherent`; support is
rendered as the non-subsingleton stalk locus; annihilation uses `IsLocalRing.maximalIdeal` and
`PresheafOfModules.stalkObj`; the one-dimensional residue-field condition is represented by an
explicit residue-field module structure and `Module.finrank = 1`.

The proof is `sorry`, with the five Noetherian-induction/filtration steps from the node's proof
and the cited irreducible-support lemma recorded in the declaration docstring.

Dependencies used: `Sheaf.AlgebraicGeometry.Coherent` (`AlgebraicGeometry.RingedSpace.IsCoherent`),
`Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase` (support convention),
`Sheaf.Topology.PresheafModuleStalkFunctor` (`PresheafOfModules.stalkObj`), and Mathlib
`AlgebraicGeometry.Scheme`, `AlgebraicGeometry.IsLocallyNoetherian`,
`AlgebraicGeometry.IsIntegral`, `AlgebraicGeometry.IsClosedImmersion`, and
`CategoryTheory.ShortComplex.ShortExact`.

Edge cases checked: zero coherent module via `IsZero`; empty scheme is allowed by `CompactSpace`;
zero-dimensional stalks are excluded by `finrank = 1`; arbitrary universe `u` is shared by schemes,
modules, and the integral subscheme.

Searches: `msearch.py leanfinder` (coherent sheaf property devissage: no match), `msearch.py loogle`
(Noetherian/support devissage: no match), grep of Mathlib and `WeilConjectures` for coherent property
and devissage (no declaration). Existing project declarations above were read and reused.

## Earlier second reading (a previous round; superseded)

The statement was checked against Tag 01YI clause by clause: Noetherian hypotheses, (0) zero-object
property, (1) two-out-of-three for coherent short exact sequences, (2a) support equality for every
integral closed immersion, (2b) maximal-ideal annihilation, (2c) residue-field dimension one, and
(2d) property of the witness, followed by the universal coherent-module conclusion.

## Second reading by C1

I read the node statement and `CoherentPropertyDevissage.lean` independently against
Stacks Tag 01YI (Lemma 30.12.6). The objects and hypotheses render as follows: `X` is
`Scheme.{u}` with `[IsLocallyNoetherian X]` and `[CompactSpace X]`, matching a Noetherian
scheme (local Noetherian plus quasi-compact); `P : X.Modules → Prop` is the property on
module sheaves; `hP_zero` is clause (0) for every zero object; `hP_seq` takes a
`ShortComplex`, `ShortExact`, coherence of all three terms, and each of the three
two-out-of-three disjunctions, and returns the property for all three terms; and
`hP_integral` quantifies an integral scheme `Z`, a closed immersion `i`, and a point
`ξ : Z`, then supplies coherent `G`. Its four conjuncts render support as
`(¬ Subsingleton (G.presheaf.stalk x)) ↔ x ∈ Set.range i.base`, maximal-ideal
annihilation on `PresheafOfModules.stalkObj`, residue-field module structure with
`@Module.finrank _ _ _ _ hκ = 1`, and `P G`. The conclusion is exactly the universal
coherent-module implication.

The only mismatch found was a stage-2 statement-form issue: the worker used a `let`
inside the residue-field finrank clause. The standing brief forbids `let` binders because
they elaborate to hidden `have`s that stage 3 cannot unfold. I replaced it by the explicit
instance application `@Module.finrank _ _ _ _ hκ`; this has identical mathematical
content and compiles. I expanded the theorem docstring to record all five proof steps
from the node (isomorphism/filtration induction, coherent filtration and support
containment, minimal bad support, application of the irreducible-support lemma, and final
filtration induction). No hypotheses or conclusion clauses were added or removed.

Edge cases checked: `CompactSpace` permits the empty scheme; `hP_zero` covers the zero
module and empty filtration; an empty index is not present; the universe `u` is shared by
`X`, `Z`, and module sheaves; and `finrank = 1` excludes a zero-dimensional witness stalk.
The characteristic is unrestricted, as in 01YI.

Searches were reread: LeanFinder and Loogle searches for coherent-property devissage,
grep of Mathlib and `WeilConjectures/` for the theorem, and project searches for support,
stalk, coherence, and residue-field declarations found no existing theorem or duplicate.
The reused declarations are `AlgebraicGeometry.RingedSpace.IsCoherent`,
`PresheafOfModules.stalkObj`, and the inline support convention from the recorded
dependency modules.
