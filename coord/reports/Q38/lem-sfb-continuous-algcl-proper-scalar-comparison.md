## Worker report

The module `Sheaf.Paper.ContinuousAlgClProperScalarComparison` states
`AlgebraicGeometry.ProEtale.CondensedRing.continuousAlgClProperScalarComparison_isIso`.
Its sole proof is `by sorry`. It introduces no new definition or replacement canonical map.
The blueprint source and all six DAG proof steps are in its docstrings.

The node is rendered clause by clause as follows.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Prime ell | `(ℓ p : ℕ) [Fact ℓ.Prime]` |
| A field k of characteristic p > 0, p different from ell | `(k : Type u) [Field k] [CharP k p] (_hp : 0 < p) (_hpℓ : p ≠ ℓ)` |
| Algebraic closure Omega with extended ell-adic norm | The existing `PadicAlgCl ℓ` normed algebraic closure, used by the imported mate definition |
| Finite intermediate extension Q_ell contained in E contained in Omega | `(E : PadicAlgCl.FiniteIntermediateField ℓ)`; this is a finite-dimensional intermediate field, not an arbitrary finite-type ring |
| Both schemes over k | `{Z T : Scheme.{u}} [Z.Over (Spec (.of k))] [T.Over (Spec (.of k))]` |
| Both schemes separated, finite type over k | For each structure map: `[LocallyOfFiniteType ...] [QuasiCompact ...] [IsSeparated ...]` |
| f a k-morphism | `(f : Z ⟶ T) [f.IsOver (Spec (.of k))]` |
| f proper | `[IsProper f]` |
| A_E(S) = all continuous maps S to E | `Profinite.continuousMapRingObj E.1` |
| B(S) = all continuous maps S to Omega | The mate's `Profinite.continuousMapRingObj (PadicAlgCl ℓ)`; not `Profinite.padicAlgClRingObj ℓ` |
| Pull these coefficients back from the point | `condensedRingObj` in the type of K and in the imported mate |
| Coefficient map induced by continuous inclusion | `tameBoundaryScalarMap ℓ E`, postcomposition with `E.1.subtype` and `continuous_subtype_val` |
| Internal module objects | `Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) ...` |
| Ordinary unbounded derived module categories | `DerivedCategory (Mod ...)`, both for K and for both endpoints of the mate |
| K bounded constructible, using finite constant local models | `_hK : constantModelBoundedConstructible (Profinite.continuousMapRingObj E.1) Z K`; this is boundedness and constant-model constructible homology in every integer degree |
| Derived extension T_W = B_W tensor^L over A_E,W | `tameBoundaryScalarExtension ℓ E W`, the existing `Mod.extendScalars (coefficientMap ... W)` followed by the generic `leftDerivedFunctor` |
| Specified canonical pullback/tensor comparison | `tameBoundaryScalarPullIso ℓ E f`, uniquely characterized by `TameBoundaryScalarPullNormalized` on K-flat representatives |
| beta the adjunct of that comparison followed by T_Z of the counit | `tameBoundaryScalarComparison ℓ E f K`; its definition applies the geometric derived adjunction's `homEquiv` to precisely this composite |
| beta is an isomorphism for every such K | `IsIso (tameBoundaryScalarComparison ℓ E f K)` |
| No constructibility requirement on T_Z K or either image; no flatness requirement | The only complex-property hypothesis is `_hK`; no output-property or coefficient-flatness binder occurs |
| No completion or filtered-union interpretation | Neither is used in the conclusion's map or its coefficient rings; the finite-subextension-valued ring occurs only in the natural-language proof plan |

The already landed node `def-sfb-all-continuous-scalar-mate` was added to `stmt_deps`,
as authorized for existing landed nodes in brief-stage2 section 5. Its module and its
full source were read. It defines this exact map for every morphism, not only tame
boundaries, and its existence/uniqueness theorem determines the pullback isomorphism.
There is no new node and no dependency repair. The statement, proof, and other
mathematical fields of the item remain unchanged.

Dependency declarations used (the recorded sources and their docstrings/signatures were read):

- `sk-def-sfb-dc-setting`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` and the documented
  setting. The setting is spelled out by the structure-map and characteristic binders;
  a compactification is not needed to define this proper direct-image map.
- `def-sfb-continuous-map-condensed-ring`: `Sheaf.Topology.ContinuousMapCondensedRing`,
  `Profinite.continuousMapRingSheafOfUniverse` and `continuousMapRingObjOfUniverse`.
  At coefficient universe zero these specialize definitionally to the published
  `Profinite.continuousMapRingSheaf` and `continuousMapRingObj`, used by the existing mate.
  `PadicAlgCl ℓ` and its intermediate fields live in `Type`, independently of scheme u.
- `sk-def-sfb-pulled-back-coefficients`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.coefficientRing` and `condensedRingObj`.
  The latter is exactly `(upperStarFromPoint X).obj Λ`, with transported ring structure.
- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`, `CategoryTheory.Mod`;
  the action/unit/associativity and compatible morphisms are the existing module objects.
- `sk-def-sfb-module-derived-pushpull`: `Sheaf.Paper.CondensedModuleDerivedPushpull`,
  `moduleObjectDerivedPushforward`, the actual `lowerStar` total right derived functor,
  together with the published `derivedUpperStarLowerStarAdjunction` used in beta.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`,
  `HasFiniteConstantLocalModel`, `IsConstantModelConstructible`, and
  `constantModelBoundedConstructible`; the finite-stratification, affine-local, and
  bounded-homology definitions are used unchanged.
- `def-sfb-continuous-map-condensed-ring-map`: `Sheaf.Topology.ContinuousMapCondensedRingMap`,
  `Profinite.continuousMapRingSheafMapOfUniverse` and `continuousMapRingObjMapOfUniverse`;
  their coefficient-universe-zero versions are exactly the postcomposition in the mate.
- `sk-def-sfb-derived-extension-of-scalars`:
  `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`,
  `CategoryTheory.Mod.derivedExtendMapDerivedCategoryAdjunction`; the left functor is
  precisely the generic `leftDerivedFunctor` of `Mod.extendScalars` used in T_W.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`:
  `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
  Its canonical K-flat representative normalization supplies the compatibility concept;
  the already landed all-continuous mate specializes it to the present coefficient maps.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`. Universally closed implies quasi-compact, so its
  locally-finite-type field gives the node's finite-type condition.
- Added landed `def-sfb-all-continuous-scalar-mate`: `Sheaf.Paper.AllContinuousScalarMate`,
  `tameBoundaryScalarMap`, `tameBoundaryScalarExtension`, `tameBoundaryScalarPullIso`,
  `tameBoundaryScalarComparison`, in namespace `AlgebraicGeometry.ProEtale.CondensedRing`.

All recorded proof-dependency modules are imported for stage 3, including the
finite-subextension two-colimit, coefficient cocycle, rational proper comparison,
constructible topology comparison, all-continuous proper finiteness and finite-Tor
statements, and K-flat normalization. The finite-type-over-Noetherian Mathlib match
is imported through `Mathlib.AlgebraicGeometry.Noetherian`. The module docstring
explains why the finite-subextension ring is only an intermediate proof coefficient.

Edge cases checked before writing: the zero complex and empty source or target scheme
are not excluded; no nonempty or positive-rank binder occurs. Identity proper maps
and E = Q_ell are included. Positive characteristic 2 is included whenever ell differs
from 2. Complexes may have negative cohomological degrees: boundedness is the derived
t-structure predicate, not a nonnegative-complex restriction. The universe u is explicit;
site morphisms retain universe u and site objects/coefficients the required u+1 size.
There is no equality imposed between those two site universes. Choosing the existing
normed algebraic closure follows the same coordinate model as the landed mate and
open-comparison nodes and does not introduce an extra assumption on Omega.

Searches for an existing exact statement:

- `msearch.py ... leanfinder`: “Proper derived direct image commutes with extension from
  finite l adic field coefficients to all continuous maps into the algebraic closure”.
  Eight results, concerning BDeRhamPlus, adic completions and valuations; no match.
- `msearch.py ... loogle`: `"Condensed", "rightDerived"`. Zero results.
- `msearch.py ... leansearch`: “Proper derived direct image coefficient change condensed
  all continuous algebraic closure l adic coefficients”. Eight results, including
  `CondensedMod.isDiscrete_tfae`, condensed limits/adjunctions and proper base-change
  stability; no exact derived coefficient-change statement.
- `msearch.py ... grep`: `(Condensed|PadicAlgCl).*(proper|rightDerived)|(proper|rightDerived).*(Condensed|PadicAlgCl)`.
  Four incidental Mathlib hits in condensed solid modules, internal projectives and
  CompHausLike documentation; no match.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id and proper scalar
  comparison names: no existing exact theorem. Found integral/rational comparisons
  for other coefficient rings, the open comparison and the existing canonical mate.
- `rg` of `dag/lean_names_upstream.json` for the proposed theorem name and
  `tameBoundaryScalarComparison`: no entries. `rg` of `dag/nodes` found the existing
  `def-sfb-all-continuous-scalar-mate` binding, reused rather than duplicated.

The example `CompactObject.lean` under Sheaf is withdrawn; its node now points to
`WeilConjectures.CategoryTheory.CompactObject`, which was read for the current header,
public-section and docstring conventions. There is no repair-note file for this item.
No statement dispute or correction was needed.

Validation: `scompile.py Q38 lem-sfb-continuous-algcl-proper-scalar-comparison <file>`
compiled both sandbox and library module modes cleanly (4.1 s and 4.0 s). No local/global
build, direct Git command, or write to the shared repository was used.

## Second reading by Q38

The dispatcher explicitly prohibits starting another agent. This is a separate rereading
by the same worker, not a claim of an independent reviewer; the maintainer independently
reviews the delivery. Reopened the node and the complete Lean file after compilation.
The signature contains exactly positive characteristic, p different from ell, a finite
intermediate field, both separated finite-type k-schemes, a proper k-morphism and a
bounded constant-model constructible input. In particular it has no flatness or
constructibility-of-output assumption. The conclusion applies IsIso to the actual
`tameBoundaryScalarComparison`, whose source, target, homEquiv and normalized pullback
comparison were checked against the displayed beta definition in the node. The
all-continuous coefficient is not the finite-subextension ring or its completion.
The six proof steps retain the distinction between C and B, establish the two endpoint
memberships before testing Hom, and explicitly identify the resulting inverse with the
canonical mate via the coefficient cocycle. No mismatch was found and no statement
change was made during rereading.
