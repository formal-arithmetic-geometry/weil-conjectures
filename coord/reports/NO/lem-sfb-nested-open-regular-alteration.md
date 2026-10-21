## Worker report

The module states `AlgebraicGeometry.exists_nestedOpen_regular_alteration`, with its sole proof `sorry`. No definitions, helper axioms, dependency repairs or new nodes are introduced. The node changes only in `lean`. The theorem's docstring contains all seven proof steps and their cited nodes.

Source read: ILO, *Travaux de Gabber*, Exposé X, Theorem 2.1, printed page 149 (PDF page 155), including its definition of a relative strict normal crossings divisor. This is the global projective alteration theorem; IX 1.1 is not substituted for it. The prescribed-cover and nested-boundary conclusions follow the node's seven-step assembly, rather than claiming that Theorem 2.1 literally states those extra conclusions.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Any field of characteristic p > 0 | `k : Type u`, `[Field k]`, `p : ℕ`, `[CharP k p]`, `hp : 0 < p`; primality follows for a field. |
| Nonempty integral T | `[IsIntegral T]`, whose first field is `Nonempty T`. |
| Separated finite-type k-scheme | `[T.Over (Spec (.of k))]`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` on `T ↘ Spec (.of k)`. |
| Dense open S ⊆ Tcirc ⊆ T | `S Tcirc : T.Opens`, `hST : S ≤ Tcirc`, `hS`, `hTcirc` as `Dense`; opens denote their canonical open subschemes. |
| Nonempty connected finite étale surjection H → S | `H`, `[ConnectedSpace H]`, `c : H ⟶ S.toScheme`, `[IsFinite c]`, `[Etale c]`, `[Surjective c]`. `ConnectedSpace` includes nonemptiness. No integrality of H is assumed. |
| Regular integral separated finite-type Y over k | Existential `Y : Over (Spec (.of k))`, existential `IsIntegral Y.left`, then `IsRegularScheme Y.left`, `IsSeparated Y.hom`, `LocallyOfFiniteType Y.hom`, `QuasiCompact Y.hom`. The explicit existential integral instance scopes generic-point and function-field types. |
| Proper dominant h over k | Existential `h : Y.left ⟶ T`, `IsProper h`, `IsDominant h`, and `h ≫ (T ↘ Spec (.of k)) = Y.hom`. |
| k(Y)/k(T) finite | Existential equality `hη` of the generic points, then `RingHom.Finite` on `(T.presheaf.stalkSpecializes (specializes_of_eq hη) ≫ h.stalkMap (genericPoint Y.left)).hom`. These stalks are definitionally `T.functionField` and `Y.left.functionField`. This is the induced generic stalk map, not an arbitrary field embedding or algebra instance. The generic-point equality follows from dominance and adds no restriction. |
| Reduced SNC boundary D with finite components | `D : Y.left.IdealSheafData`, `IsStrictNormalCrossingsBoundary D`. This existing predicate includes an effective Cartier radical ideal and the finite regular-intersection component criterion. `n : ℕ` and `C : Fin n ≃ {Z // Z ∈ irreducibleComponents (D.support : Set Y.left)}` enumerate exactly its reduced irreducible components. On the regular Noetherian source these are exactly the integral closed subschemes in the boundary definition; taking their supports introduces no extra condition. |
| W = h⁻¹(S) = Y \ D | `(h ⁻¹ᵁ S : Set Y.left) = (D.support : Set Y.left)ᶜ`; its canonical open scheme is the source of `h ∣_ S`. |
| V = h⁻¹(Tcirc) = Y \ union Aout | `Aout : Finset (Fin n)` and the second set equality, with `Subtype.val '' (C a).val` embedding a boundary component's support into Y. The total union of all components is D by their definition as irreducible components. |
| Proper surjection r:W → S | `IsProper (h ∣_ S) ∧ Surjective (h ∣_ S)` using the actual canonical restriction. |
| r factors through c | `∃ b : (h ⁻¹ᵁ S).toScheme ⟶ H, b ≫ c = h ∣_ S`. |
| Nonempty dense open S0 ⊆ S | `S0 : S.toScheme.Opens`, `Nonempty S0 ∧ Dense (S0 : Set S.toScheme)`. |
| W0 = W ×S S0; r0 finite | `pullback (h ∣_ S) S0.ι`, with `IsFinite (pullback.snd (h ∣_ S) S0.ι)`. |
| W0 → T0 → S0 factorization | Existential schemes/maps `T0`, `u`, `e`, and `u ≫ e = pullback.snd (h ∣_ S) S0.ι`. |
| u finite universal homeomorphism | `IsFinite u ∧ (topologically IsHomeomorph).universally u`, exactly the recorded dependency's universal-base-change formulation. |
| e finite étale surjective of constant degree d ≥ 1 | `IsFinite e ∧ Etale e ∧ Surjective e ∧ 1 ≤ d ∧ ∀ s, e.finrank s = d`. Mathlib's finite-flat rank is the degree of this finite étale map. |
| No SNC assertion after shrinking, no separability assertion | There is no boundary predicate for the complement of W0 and no separability conjunct. |

Dependency declarations read and used:

- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`; also `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.IsOpenImmersion`
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale`
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite`; also `AlgebraicGeometry.IsFinite`, `AlgebraicGeometry.IsIntegralHom`
- `def-weil-surjective-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`, `AlgebraicGeometry.Surjective`
- `def-weil-regular-scheme`: `Sheaf.AlgebraicGeometry.IsRegularScheme`, `AlgebraicGeometry.IsRegularScheme`
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`; also `AlgebraicGeometry.IsProper`, `AlgebraicGeometry.IsSeparated`, `AlgebraicGeometry.UniversallyClosed`
- `def-trf-strict-normal-crossings-boundary`: `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`, `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`
- `def-sc-function-field`: `WeilConjectures.AlgebraicGeometry.FunctionField`, `AlgebraicGeometry.Scheme.functionFieldOfComponents`
- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra`
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `CategoryTheory.Limits.pullback`; also `CategoryTheory.Limits.pullback`, `CategoryTheory.Limits.pullback.fst`, `CategoryTheory.Limits.pullback.snd`
- `def-weil-universal-homeomorphism`: `Mathlib.CategoryTheory.MorphismProperty.Limits`, `CategoryTheory.MorphismProperty.universally`; also `CategoryTheory.MorphismProperty.universally`, `AlgebraicGeometry.topologically`, `IsHomeomorph`

The integral clause of def-sc-function-field explicitly uses Mathlib `Scheme.functionField`, not the component-product definition for nonintegral curves. `IsRegularScheme` is the recorded locally-Noetherian/stalkwise-regular conjunction. The SNC predicate's full signature and docstring were read, including its empty-family convention. `morphismRestrict` was read: it is the second pullback projection transported along the canonical open-subscheme isomorphism. Constant degree uses Mathlib `Scheme.Hom.finrank` from `Mathlib.AlgebraicGeometry.Morphisms.FlatRank` (its full definition and docstring were read). No second function-field-map definition was added: the signature directly writes the canonical stalk-map composite, the same composite used by upstream `Scheme.Hom.functionFieldMap`.

All presently recorded proof-dependency modules are imported without `public` unless already public for the statement. `lem-sfb-gabber-global-snc-alteration` has neither a Lean record nor a Mathlib match in the read tree, so it has no module to import yet; this is a proof prerequisite, not a missing notion needed to state this item. The remaining Mathlib proof dependencies are imported from their recorded files. No dependency is restated.

Edge cases checked: S = Tcirc = T allows D empty, n = 0 and Aout empty; the irreducible-component type of the empty support is empty, so the enumeration is valid. S = Tcirc and Aout all components are allowed. Aout empty allows Tcirc = T. The zero-dimensional integral case has no nontrivial boundary. Empty T is excluded by the node's integral hypothesis; empty H by ConnectedSpace; empty S by density in nonempty T. d = 1 and identity factors are included. Purely inseparable finite extensions are allowed, and no perfectness or algebraic closedness of k is imposed. The single universe u uniformly ranges over all sizes and can be enlarged for any particular finite diagram; there are no independent smaller universes making a test quantifier vacuous.

Searches actually run using msearch.py:

- grep: `alteration|strictNormalCrossing|strict_normal_crossing`: 0 hits. .
- loogle: `IsProper, IsRegular, IsFinite`: 0 hits. loogle: unknown identifier 'IsProper'.
- leanfinder: `A proper generically finite regular alteration adapted to nested dense opens and a prescribed finite etale cover, with strict normal crossings boundary`: 8 hits. AlgebraicGeometry.Scheme.Etale, AlgebraicGeometry.IsSmooth.exists_isStandardSmooth, AlgebraicGeometry.IsSmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension, AlgebraicGeometry.Scheme.Hom.normalizationOpenCover, AlgebraicGeometry.IsEtale, AlgebraicGeometry.IsSmoothOfRelativeDimension, AlgebraicGeometry.Scheme.Hom.normalization, AlgebraicGeometry.Scheme.Hom.toNormalization.
- leansearch: `A proper generically finite alteration with regular source and strict normal crossings boundary adapted to two nested dense opens and a finite etale cover`: 8 hits. AlgebraicGeometry.instIsProperOfIsFinite, AlgebraicGeometry.IsProper.instOfIsFinite, AlgebraicGeometry.IsProper.instMorphismRestrict, AlgebraicGeometry.Scheme.Etale, AlgebraicGeometry.IsFinite.instMorphismRestrict, AlgebraicGeometry.IsEtale.instIsStableUnderBaseChangeScheme, AlgebraicGeometry.instLocallyQuasiFiniteOfIsImmersion, AlgebraicGeometry.IsEtale.instFormallyUnramified.

LeanFinder and LeanSearch returned étale/normalization/smoothness or finite/proper facts, none asserting this alteration assembly. Loogle's query could not resolve its unqualified `IsProper` identifier, so its zero count is not treated as absence evidence. The other searches establish no exact match. Direct rg searches in Mathlib, WeilConjectures and Sheaf for alteration/strict-normal-crossings and nested-open alteration names found only the existing boundary predicate and unrelated nested-open comparisons. Searches for the item id in upstream sources found no declaration. The chosen declaration name was also searched in all three source trees and `dag/lean_names_upstream.json`: no collision.

Validation: the server's sandbox and library single-file passes completed cleanly (2.5 s and 2.2 s before the final import completion). The initial import of a nonexistent standalone Dominant module was removed: IsDominant is supplied by the recorded UnderlyingMap module. The final delivery preflight recompiles the completed imports. No statement correction or STATEMENT-DISPUTED issue was necessary. Independent review is performed by the maintainer as specified in this worker's brief; no second-reader claim is made here.

## Second reading by NO

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
