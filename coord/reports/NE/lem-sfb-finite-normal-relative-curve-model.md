## Worker report

Item: `lem-sfb-finite-normal-relative-curve-model`, group NE, stage 2, 2026-10-22.
Module: `Sheaf.AlgebraicGeometry.FiniteNormalRelativeCurveModel`.

The module states every clause of the item in five named theorems. Each proof is exactly
`by sorry`. Its only definition is the actual pullback lift
`FiniteNormalRelativeCurveModel.genericLift`, built with `pullback.lift`; its data and its
commutativity proof contain no sorry. All six declarations are listed in `lean.declarations`.
The node copy changes only `lean`; there are no new nodes or dependency repairs, and the
natural-language statement, dependency lists, and proof are unchanged.

Source read: de Jong, *Families of curves and alterations* (1997), §§3.2, 3.5, printed
pp.605,607--608, publisher scan
https://www.numdam.org/article/AIF_1997__47_2_599_0.pdf . Section 3.2 supplies the
constant extension and compatible group diagram; §3.5 normalizes in the covering field
and obtains finite maps to intermediate normal coverings. The item's eleven-step proof
supplies the detailed integral-closure and dimension argument, reproduced by clause in
the theorem docstrings, using Stacks 0307, 0F32, 02FZ, and 02FY. The scan's §2.9 also
explicitly constructs both normalizations, the structural map, and the lifted action.

### Hypotheses and the named generic curve

Write K = `S.functionField`, F = `X.functionField`,
T = `S.normalizationIn E`, Y = `X.normalizationIn L`, and
X_K = `pullback f S.fromSpecFunctionField`. These are explanatory names only, not
file-local Lean notation. In the main theorem, the following are the exact renderings.

| Node hypothesis | Lean |
| --- | --- |
| k is a field | `(k : Type u) [Field k]` |
| S and X are integral | `(S X : Scheme.{u}) [IsIntegral S] [IsIntegral X]` |
| S is a k-scheme, projective of finite type | `(p : S ⟶ Spec (.of k)) [IsHProjective p] [LocallyOfFiniteType p] [QuasiCompact p]` |
| S is normal | `hS : ∀ s, IsDomain (S.presheaf.stalk s) ∧ IsIntegrallyClosed (S.presheaf.stalk s)` |
| f is H-projective | `(f : X ⟶ S) [IsHProjective f]` |
| X is of finite type over k | `[LocallyOfFiniteType (f ≫ p)] [QuasiCompact (f ≫ p)]` |
| Every geometric fibre is pure of dimension one | `hpure : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S), (pullback f s).IsPureDimension 1` |
| Generic fibre is smooth and geometrically integral | `[Smooth (pullback.snd f S.fromSpecFunctionField)] [GeometricallyIntegral (pullback.snd f S.fromSpecFunctionField)]` |
| L/F is finite separable | `[Algebra X.functionField L] [FiniteDimensional X.functionField L] [Algebra.IsSeparable X.functionField L]` |
| E/K is finite separable | `[Algebra S.functionField E] [FiniteDimensional S.functionField E] [Algebra.IsSeparable S.functionField E]` |
| E is a subextension in L/K | `[Algebra S.functionField L] [Algebra E L] [IsScalarTower S.functionField E L]` |
| K and F use f's actual generic maps | `h : X.fromSpecOfAlgebraFunctionField L ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S.functionField L)) ≫ S.fromSpecFunctionField` |
| Normalization C of X_K in L | `(genericLift f L h).normalization`, Mathlib relative normalization of the specified generic map `Spec L ⟶ X_K` |
| Induced E-structure on C | `(c : (genericLift f L h).normalization ⟶ Spec (.of E))` and `hc : (genericLift f L h).toNormalization ≫ c = Spec.map (CommRingCat.ofHom (algebraMap E L))` |
| C is smooth projective geometrically integral of dimension one | `[Smooth c] [IsHProjective c] [GeometricallyIntegral c]` and `hcurve : (genericLift f L h).normalization.IsPureDimension 1` |

The extra displayed equations h and hc specify the structures the node already calls
induced. They do not posit an arbitrary curve or an arbitrary E-structure. The source map
for the relative normalization has its two components explicitly built with `pullback.lift`.
An E-structure satisfying hc is unique: the normal curve is integral, the generic map is
dominant, and `Spec E` is separated. There is no chosen field of the wrong generic scheme.
For the isomorphism, action, and intermediate-model clauses the same original context is
repeated explicitly (the normality hypothesis is renamed `hnormal`). Thus these clauses
retain the original hypotheses even where the integral-closure proof alone needs fewer.

### Conclusions, clause by clause

| Node conclusion | Lean rendering |
| --- | --- |
| T is normal and integral | The first local-stalk conjunction and `IsIntegral (S.normalizationIn E)` |
| T is projective of finite type over k | `IsHProjective (S.fromNormalizationIn E ≫ p)`, followed by `LocallyOfFiniteType` and `QuasiCompact` for that map |
| k(T) = E | `∃ e : Spec (.of E) ≅ Spec (S.normalizationIn E).functionField`, with `e.hom ≫ ...fromSpecFunctionField = (S.fromSpecOfAlgebraFunctionField E).toNormalization` |
| T → S is finite surjective | `IsFinite (S.fromNormalizationIn E) ∧ Surjective (S.fromNormalizationIn E)` |
| Y is normal and integral of finite type over k | The local-stalk conjunction on `X.normalizationIn L`, its `IsIntegral` clause, and `LocallyOfFiniteType`/`QuasiCompact` of `X.fromNormalizationIn L ≫ f ≫ p` |
| k(Y) = L | The analogous spectrum isomorphism characterized by the canonical map from `Spec L` |
| Y → X is finite | `IsFinite (X.fromNormalizationIn L)` |
| The structural factorization is canonical | `∃! g`, its equality `g ≫ S.fromNormalizationIn E = X.fromNormalizationIn L ≫ f`, and its specified equality on `Spec L` |
| Y → X ×_S T is finite surjective | `∃ m`, its equations with BOTH `pullback.fst` and `pullback.snd`, and `IsFinite m ∧ Surjective m` |
| Y → T is H-projective | `IsHProjective g` |
| Every geometric fibre over T is pure dimension one | `∀ Ω [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S.normalizationIn E), (pullback g t).IsPureDimension 1` |
| Generic fibre over T is C with its E-structure | `∃ e : pullback g (S.fromSpecOfAlgebraFunctionField E).toNormalization ≅ (genericLift f L h).normalization` and the projection equations over E and X, together with preservation of the specified map from `Spec L` |
| Constant-extension tensor product is a field | The first conjunct `IsField (TensorProduct S.functionField X.functionField E)` of `finite_normal_relative_curve_model_constant_extension` |
| L = F tensor_K E is finite separable over F | In the same theorem, for any field presentation `eL` satisfying the displayed pure-tensor multiplication formula: `FiniteDimensional X.functionField L ∧ Algebra.IsSeparable X.functionField L` |
| In this case C = X_K ×_K E | The same theorem gives c, its generic characterization, all four curve properties, and an isomorphism of the generic normalization with the literal iterated pullback; both projection equations are included |
| Functorial for compatible isomorphisms, including semilinear ones | `finite_normal_relative_curve_model_isomorphisms`: unique pair of isomorphisms of Y and T, commuting with both normalization maps, both specified generic maps, and g |
| Compatible actions extend uniquely | `finite_normal_relative_curve_model_actions`: `∃! ρ : (G →* Aut Y) × (G →* Aut T)` with the five equivariance clauses |
| Every intermediate finite normal model receives a unique finite map | `finite_normal_relative_curve_model_intermediate`: the canonical generic map restricts to t, and `∃! m : Y_U ⟶ Z` with `m ≫ q = ν_U`, `t ≫ m = Spec.map i ≫ Z.fromSpecFunctionField`, and `IsFinite m` |

The function-field isomorphisms are not arbitrary abstract ring equivalences: their equations
identify the canonical generic points and hence the inclusions into E and L. The generic
fibre is pulled back along the actual generic map `Spec E ⟶ T`, identified with T's generic
point by the preceding spectrum isomorphism. The comparison with C also retains its map
to X and explicitly preserves the canonical generic map from Spec L via its inverse. The factor map to the full fibre product is forced by both projections; it is not a
map to just its reduction or a selected component.

In the constant-extension theorem, `hKF` identifies the K-algebra on F with the actual
morphism f. `IsField` refers to the EXISTING commutative-ring operations of the tensor
product. After that assertion the universal statement over a field presentation L applies,
in particular, to the tensor ring equipped with the field structure obtained from IsField.
The presentation is characterized on pure tensors and the two scalar towers ensure the
specified K-, F-, and E-structures agree. This avoids an existential Field instance with
unrelated multiplication. No additional existence assumption replaces the assertion that
the tensor product is a field.

For functoriality, `aX`, `aS`, `aL`, `aE` are isomorphisms of the original scheme and field
spectra and `hf`, `hX`, `hS`, `hE` are their compatibility equations. The ground field
is also part of the datum: `ak : Spec k ≅ Spec k'`, `p' : S' ⟶ Spec k'`, and
`hk : aS.hom ≫ p' = p ≫ ak.hom` specify its compatible transport. `hgf` and `hgf'`
assert that g and g' are the relative structural maps, and `hg`, `hg'` characterize them
on the specified generic fields. Unique lifting gives the identity and composition laws:
the identity lifts the identity data and a composite of lifts lifts the composite data.
There is no condition that the ground-field isomorphism be the identity. An action on a field by automorphisms σ becomes the
action on its spectrum `a ↦ Spec.map (σ(a⁻¹))`; conversely field-spectrum automorphisms
recover the field action because Spec is fully faithful. The action theorem explicitly supplies `ρk` and
`hk : ∀ a, (ρS a).hom ≫ p = p ≫ (ρk a).hom`. It therefore includes all the nonfaithful semilinear actions in the node, with G in an independent
universe v and without a finiteness assumption.

For the intermediate clause `q : Z ⟶ (f ⁻¹ᵁ U).toScheme` is finite dominant, `hZ` is local
normality, and `i : Z.functionField →+* L` is the field embedding (injectivity follows
from the field domain). `hi` is exactly its F-compatibility. The equality specifying t
asserts that the canonical generic map to Y actually lands in Y_U, preventing an empty
or unrelated generic restriction. Its equation with m fixes the field map, rather than
merely asking for some finite factorization.

### Dependency declarations read and reused

The statement dependencies were read in the DAG and their recorded signatures/docstrings
were opened in the local read-only Lean source, including the integral-scheme clause of
the function-field node.

| Dependency | Module and declaration used |
| --- | --- |
| def-weil-field | `Mathlib.Algebra.Field.Defs`: `Field` |
| def-pc-integral-scheme | `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral` |
| def-weil-finite-type-morphism | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`: `LocallyOfFiniteType`, `QuasiCompact` |
| def-weil-finite-integral-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite` |
| def-sbc-smooth-morphisms | `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth` |
| def-pc-geometrically-irreducible | `Mathlib.AlgebraicGeometry.Geometrically.Integral`: `GeometricallyIntegral` |
| def-kun-projective | `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective` |
| def-sc-function-field | `WeilConjectures.AlgebraicGeometry.FunctionField`, importing Mathlib's `Scheme.functionField`, the recorded node's arbitrary-integral-scheme clause; the component-product definition is unnecessary for integral X and S |
| def-pc-field-extension | `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `algebraMap` |
| def-fin-normalization-extension | `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`: `Scheme.normalizationIn`, `Scheme.fromNormalizationIn`, `Scheme.fromSpecOfAlgebraFunctionField` |
| def-pc-fibre-product | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift` |
| def-weil-pure-dimension | `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension` |

The five proofs import the recorded available proof-dependency modules privately, including
normalization finiteness, H-projective composition, projective properness, finite over
projective, projective-space base change, both local dimension theorems, fibre dimension
base change, smooth normality, and the affine integral-closure and primitive-element tools.
`lem-sfb-finite-dominant-normal-base-universally-open` has no recorded Lean declaration
in the read DAG; its future proof-module import is left to the maintainer under the
stage rule. Its fact is used only in the natural-language proof, not assumed in a statement
or replaced by a stronger hypothesis. No downstream theorem is imported.

### Searches and results

* `msearch.py ... leanfinder "normalization finite extension function field projective relative curve pure dimension fibres"`:
  eight results include Mathlib `Scheme.Hom.normalization`, `normalizationDesc`,
  `toNormalization`, `fromNormalization`, and its integral/dominant instances. These
  supply the construction but not the finite relative-curve theorem or its other clauses.
* `msearch.py ... loogle "AlgebraicGeometry.Scheme.normalizationIn, AlgebraicGeometry.Scheme.Hom.normalizationMap"`:
  zero hits; service does not know the upstream name `normalizationIn`.
* `msearch.py ... grep "normalizationIn|normalizationDesc" AlgebraicGeometry`:
  five Mathlib hits, giving the relative-normalization descent API and its generic equation.
* `msearch.py ... leansearch "normalization in finite field extension relative curves pure one dimensional fibres semilinear group action"`:
  eight hits, including `toNormalization`, its dominance instance, and unrelated algebraic
  norm/separability statements; no matching relative-curve model statement.
* `rg -n` over `lean/WeilConjectures` and `lean/Sheaf` for normalization constructions,
  normal relative curve models, the item id, and the proposed declaration names: found
  upstream finite normalization and affine-curve results, plus the consumers
  `HighGenusEquivariantCover` and `EquivariantFlatCurvePreparation`. None states the item.
  `NormalizationExtendsCover` concerns extending finite etale covers, not this theorem.
* `grep -rn "lem-sfb-finite-normal-relative-curve-model" lean/WeilConjectures`:
  no existing upstream statement for this item.
* `dag/lean_names_upstream.json`: no binding for the item or proposed theorem names.
  The separate residue-field-normalization theorem does not give relative curve models.

All needed notions already have usable dependency records. No duplicate definition node,
private normalization, new pure-dimension predicate, or arbitrary replacement map is used.

### Edge cases and validation

* An integral source/base cannot be empty, exactly as in the node. Empty geometric fibres
  remain permitted by `IsPureDimension` (no irreducible components). No surjectivity of f
  or flatness is assumed as an extra hypothesis.
* A zero-dimensional base S is included. Taking E = K or L = F gives the identity
  extension and ordinary normalization cases; no positive field degree is imposed.
* All characteristics are allowed. Separability is `Algebra.IsSeparable`; neither
  characteristic zero nor a perfect-field assumption is introduced.
* If U is empty no integral Z can map dominantly to X_U, so the final implication is
  vacuous as it should be. U = S and all nonempty intermediate finite normal models are
  included, without an added nonemptiness assumption on U.
* The group can be trivial, infinite, or act with a kernel. Its universe is independent
  of the scheme universe. Isomorphisms and actions are never required to fix k.
* Geometric test fields are in the scheme universe u, matching the published scheme
  base-change convention; no smaller independent test-field universe is introduced.
* Source normalization is retained even when the original X is not normal, and the finite
  map targets the full, possibly nonreduced fibre product.
* `set_option autoImplicit false` enforces explicitly bound variables and universes.
  There are no local notations, private definitions, local instances, hidden lets in
  statements, `#check` commands, data sorries, or non-sorry theorem proofs.

Server validation uses only the prescribed `scompile.py`; no local/global lake build or
read-clone edits were performed. The model theorem first compiled cleanly, and then the
complete five-theorem module compiled cleanly, including after restoring the original
source context on each companion clause. Final wrapper/preflight results are recorded below.

No STATEMENT-DISPUTED issue, source correction, new node, or dependency-module repair.

## Second reading by NE

The dispatcher forbids starting other agents and assigns the independent delivery reading
to the maintainer. This section records the author's separate second pass, not an invented
independent reviewer.

Reopened the item and the complete module and compared the hypotheses and every clause
using the tables above. Found and repaired two issues before delivery: a redundant
normalization-composition conjunct was removed; and the isomorphism/action clauses now
require g (and g') to commute with the maps to the original base, in addition to their
generic-field equations. Without the former compatibility, nonseparated bases in a
generalized auxiliary statement could defeat the intended uniqueness argument. Also
repeated the full original curve context on all three structural companion clauses so
that no unrequested generalization drops source hypotheses.

The final pass specifically checked both projections for the full fibre-product map,
the E-projection and X-projection for the generic-fibre isomorphism, the canonical-field
rather than abstract-field meaning of the spectrum isomorphisms, the pure-tensor formula,
and the chosen embedding in the intermediate-map equation. A final pass added explicit semilinear ground-field compatibility (`ak`/`hk` and
`ρk`/`hk`) and required the generic-fibre comparison to preserve the canonical Spec L
map. No remaining mismatch found.
The sole helper constructs a pullback lift using the supplied equality. Every theorem
retains a sorry proof and carries its source and natural-language proof in its docstring.

Final validation: `deliver2.py NE lem-sfb-finite-normal-relative-curve-model --no-push`
reported `OK (dry run): commit 13d30f986ad passes the preflight and compiles; nothing pushed`.
The final source compiled without errors or unpermitted warnings. The delivery wrapper
repeats compilation and preflight when pushing the packet.
