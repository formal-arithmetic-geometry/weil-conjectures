## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceExtendAdmissibleBlowup` states
`AlgebraicGeometry.AlgebraicSpace.exists_blowupPresentation_extend_admissible`.
Its sole theorem has proof `sorry`; there are no new definitions, helper theorems,
or dependency repairs. Read Stacks `spaces-divisors.tex`, definition-admissible-blowup
(Tag 086B) and lemma-extend-admissible-blowups (Tag 086D), including the proof.
The natural-language node statement and its four proof steps remain unchanged.

Hypotheses and conclusion, clause by clause:

| Node clause | Lean rendering |
| --- | --- |
| Scheme S, algebraic spaces over S, size convention | Explicit `universe u`, `{S : Scheme.{u}}`, `(T V : AlgebraicSpace S)`; scheme tests `A : Over S` are in the same scheme universe. |
| T quasi-compact | `hTqc` supplies an etale surjective atlas `a : yoneda.obj A ⟶ T.obj.obj` with `CompactSpace A.left`. |
| T quasi-separated, absolutely rather than relative to S | `hTqs : IsAbsolutelyQuasiSeparated T`, using the existing affine-test criterion for the absolute diagonal. |
| U an open subspace of T | `U : OpenSubspace T`, the existing subfunctor with representable open-immersion inclusion `U.val.ι`. |
| U quasi-compact | `hUqc` supplies a quasi-compact scheme atlas for `U.val.toFunctor`, with `IsEtale a ∧ IsSurjective a`. |
| V an open subspace of T | `v : V ⟶ T` and `hv : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) v.hom.hom`. Giving an open immersion with source V is the same as specifying the open subspace, up to its unique isomorphism. |
| V quasi-compact | `hVqc`, exactly the same atlas condition for V. |
| J a quasi-coherent ideal on the small etale site of V | `J : QuasiCoherentIdeal V`, a subobject of the module `SheafOfModules.unit V.structureSheaf` with the Mathlib quasi-coherence predicate. |
| J finite type | `hJ : (J.val : V.Modules).IsFiniteType`, the existing locally-finitely-generated sheaf predicate. |
| J is unit on U intersect V | `hJU : IdealIsUnitAbove J v U`, testing the unit ideal on every etale chart whose composite to T factors through U. |
| The specified blowup of J | `C : BlowupPresentation J`. This is a model of precisely the descended scheme blowups, not an arbitrary morphism or an extra geometric hypothesis. The theorem applies to every representative C of that blowup. |
| Existence of a finite-type quasi-coherent ideal I on T | `∃ (I : QuasiCoherentIdeal T), (I.val : T.Modules).IsFiniteType ∧ ...`. |
| I restricts to the unit ideal on U | `IdealIsUnitAbove I (𝟙 T) U`. |
| Blowup of I | `B : BlowupPresentation I`, inside the existential conclusion. No object is chosen from a merely asserted existence theorem. |
| Isomorphism of the restriction of B over V with C over V | `h : C.space ⟶ B.space` and `IsPullback C.projection h v B.projection`. A cartesian square is equivalent to an isomorphism `C.space ≅ V ×_T B.space` over V. It retains the actual comparison morphism rather than only a bare nonempty isomorphism. |
| C is an open subspace of B | `IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) h.hom.hom`. This is the requested in-particular clause, not an extra assumption. |
| Canonical identifications over U intersect V | The presheaf `Limits.pullback U.val.ι v.hom.hom` is the intersection. `s` maps it to C and `t` to B. The two `IsPullback` squares have identity as their left vertical arrow, and lower arrows the intersection's projections to V and T. Thus the *whole* inverse images of the intersection are identified with it. |
| The isomorphism restricts to identity | `s ≫ h.hom.hom = t`. The cartesian squares uniquely characterize s and t as the inverse projection maps over the intersection, so this is identity in the canonical blowup coordinates. |
| No containment between U and V | There is no containment, density, or nonemptiness hypothesis. |

The cartesian-square formulation does not strengthen the requested conclusion:
from its isomorphism over V, take the composite of its inverse with the projection
to B to obtain h and the square. Conversely a square yields the isomorphism over V.
The inverse projection maps on the intersection are unique, so s and t introduce
no choices or conditions beyond the canonical identity clause.

Dependency declarations read and reused (namespace `AlgebraicGeometry.AlgebraicSpace`
unless stated otherwise):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `IsSurjective`, `EtaleSite`, `structureSheaf`,
  `Modules`. Full signatures and documentation were read in the source module.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, the scheme-test convention named by the
  statement's setup. Imported as the recorded statement dependency.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: recorded `MapIsLocally`
  and its property definitions, including `MapIsSeparated`, read with their chart tests.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and the slice
  sheafification instances; ideals use its exact Mathlib predicate, read at
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`, `SheafOfModules.IsQuasicoherent`.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup` and `blowupMap`,
  used by the chart condition of the existing `BlowupPresentation`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceBlowupPresentation`: `BlowupPresentation`,
  `blowupChartIdeal`, `IdealIsUnitAbove`, reusing its real scheme-chart specification.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal`: `QuasiCoherentIdeal`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated` (absolute, even for a non-quasi-separated S).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`.
- The metatheoretic `def-weil-size-convention` has no module/declaration; explicit
  universe polymorphism implements it, as its existing record instructs.
- Proof-only import `Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteTypeSubmoduleExtension`:
  `exists_finiteType_submodule_extension`, whose complete signature and proof docstring
  were read. It extends a specified monic submodule with inclusion compatibility.
  `lem-sfb-space-blowup-chart-properties` has no Lean record on the read base, so
  there is no module for that proof dependency to import yet; the proof docstring
  preserves both uses (restriction and the complement isomorphism). The statement
  requires none of its still-unstated conclusions as an input.

Four already-landed definition nodes were added to `stmt_deps` so the reused
interfaces have explicit owners: `def-sfb-space-blowup-presentation`,
`def-sfb-space-quasi-coherent-ideal`, `def-sfb-space-absolute-quasi-separated`,
`def-a1-space-open-subspace`. Their statements and full recorded declarations
were read; no node or definition is duplicated. This is the landed-node addition
permitted by brief-stage2 section 5. No new nodes are needed.

Edge cases checked mathematically before finalizing the statement: U empty makes
both unit-above conditions vacuous; the intersection is empty and its identity
clause automatic. V empty gives the empty blowup embedding; no nonempty atlas is
required. U=T forces J unit on V and I can be unit, with the identity blowup on T.
V=T permits I=J, since J is already unit on U. U and V disjoint imposes no
restriction on J. Unit ideals give identity blowups; zero or nilpotent ideals give
empty blowups, which are allowed by the chart-based presentation and by the
conclusions. No reducedness, Noetherian condition, characteristic assumption, or
quasi-separatedness of the base is imposed.

Searches actually run, via the launcher's msearch wrapper (logged in this sandbox):

- LeanFinder: `Extend an admissible blowup from an open algebraic subspace to a quasi compact quasi separated algebraic space`.
  Eight hits on scheme normalization/quasi-separatedness, no space blowup extension.
- Loogle: `"blowup"`. No hits.
- Mathlib grep: `blowup|Blowup|admissible`, subdirectory `AlgebraicGeometry`.
  Five hits on admissible changes of Weierstrass variables; no matching theorem.
- LeanSearch: `An admissible blowup of a quasi compact open subspace of a quasi compact quasi separated algebraic space extends to an admissible blowup of the whole space`.
  Eight scheme quasi-compactness/quasi-separatedness hits; no matching theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `extend.*[Aa]dmissible|extend.*[Bb]lowup`, and `086D`.
  The analogous `IsAdmissible.exists_extend_of_disjoint` in upstream
  `WeilConjectures.Blowup.Extension` is scheme-only (signature and docstring read),
  so is not this statement. Existing algebraic-space common/composite blowup
  statements use this item in their proof plans, but do not state it.
- `rg` through algebraic-space modules for `blowup|Blowup|Blowing|blowing` and
  `IsAbsolutelyQuasiSeparated|Ideal|QuasiCompact`, then DAG lookup of the exact
  owner ids, located the existing interfaces above.

Validation: `scompile.py Q21 lem-sfb-space-extend-admissible-blowup <file>` passed
both sandbox and library-name compiles cleanly (1.6 s and 1.7 s). Initial elaboration
resolved bare `pullback` to the algebraic-space module-restriction functor; explicitly
qualifying the intersection as `Limits.pullback` repaired it. No timeout setting
was changed. All binders and the single universe are explicit; `autoImplicit` is false.
No mathematical node fault or disputed statement was found.

## Second reading by Q21

This is a separate rereading by the same worker, not a claim of a second agent's
review: the dispatcher explicitly forbids starting other agents, and the maintainer
provides the independent review. Reopened the node and the completed Lean module.
Checked hTqc and hTqs against qcqs, hUqc/hVqc against the two quasi-compact opens,
J and hJ against the finite-type quasi-coherent ideal, and hJU against precisely
unit on the intersection (not unit everywhere on V). Checked the output existential
binds I and B, requires finite type and unit on U, and compares the given C via a
cartesian square over T, which gives exactly the isomorphism over V. Checked the
open-immersion conclusion uses that same h. Finally checked s and t have the same
intersection as source, the lower arrows land in V and T respectively, both squares
make the entire inverse images identities, and `s ≫ h.hom.hom = t` expresses the
canonical identity rather than just commutativity over T. No stronger equality
I restricted to V = J was added to the conclusion, although the proof constructs it.
No assumptions on containment, density, emptiness, or the base were added. All four
added stmt_deps are existing definition owners with usable records; no dependency
was repaired. The only implementation change during reading was qualification of
`Limits.pullback`; no mathematical statement correction was needed.
