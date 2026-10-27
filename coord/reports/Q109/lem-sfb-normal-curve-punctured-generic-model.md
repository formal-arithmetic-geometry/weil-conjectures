## Worker report

The module `Sheaf.AlgebraicGeometry.NormalCurvePuncturedGenericModel` states
`AlgebraicGeometry.exists_normal_curve_punctured_generic_model`. Its only proof is `sorry`.
There are no definitions, helper axioms, additional nodes, dependency repairs or statement
corrections. The node copy changes only `lean`.

Read Stacks Project `limits.tex`, Tag 0GWV, lines 4238–4363, in particular the final
normalization-and-shrinking paragraph. The node is the explicitly affine curve version of
that construction. Also read the signatures and docstrings for the statement dependencies,
the normalization interfaces and the spreading lemma. The source does not require
separability of the generic extension or separatedness of either target scheme.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Field k | `{k : Type u} [Field k]` |
| Integral affine k-scheme T | `T : Scheme.{u}`, `[IsAffine T]`, `[IsIntegral T]`, structure map `t : T ⟶ Spec (CommRingCat.of k)` |
| T finite type over k | `[LocallyOfFiniteType t] [QuasiCompact t]`, the recorded finite-type convention |
| Generic point eta | `η : T`, `hη : IsGenericPoint η Set.univ` |
| Closed point y | `y : T`, `hy : IsClosed ({y} : Set T)` |
| Local dimension at y is one | `hdy : ringKrullDim (T.presheaf.stalk y) = 1` |
| K is kappa(eta) | The type `T.residueField η` is used directly, rather than introducing an independently chosen K |
| Any finite field extension L/K | `L : Type u`, `[Field L]`, `[Algebra (T.residueField η) L]`, `[FiniteDimensional (T.residueField η) L]` |
| Y and W locally finite type over k | Structure maps `s`, `w`, and `[LocallyOfFiniteType s] [LocallyOfFiniteType w]` |
| k-morphisms i and f | `i : T ⟶ Y`, `f : W ⟶ Y`, `hi : i ≫ s = t`, `hf : f ≫ s = w` |
| k-morphism u from Spec L | `uL : Spec (CommRingCat.of L) ⟶ W`; `huL` identifies its composite with `w` with the k-structure induced through K and T |
| fu is the specified generic composite | `hfu : uL ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (T.residueField η) L)) ≫ T.fromSpecResidueField η ≫ i` |
| Integral finite type k-scheme C | Existential `C`, structure map `q`, and `IsIntegral C ∧ LocallyOfFiniteType q ∧ QuasiCompact q` |
| k-morphism p to T | Existential `p : C ⟶ T` and `p ≫ t = q` |
| Closed point c | Existential `c : C` and `IsClosed ({c} : Set C)` |
| All local rings are integrally closed domains | `∀ x : C, IsDomain (C.presheaf.stalk x) ∧ IsIntegrallyClosed (C.presheaf.stalk x)` |
| c lies over y | `p c = y` |
| Local dimension at c is one | `ringKrullDim (C.presheaf.stalk c) = 1` |
| Punctured scheme C minus c | `U : C.Opens` with `(U : Set C) = ({c} : Set C)ᶜ`; this specifies the actual open subscheme, not a smaller unspecified open |
| k-morphism a from the puncture to W | `a : U.toScheme ⟶ W` and `a ≫ w = U.ι ≫ q` |
| fa equals ip on the puncture | `a ≫ f = U.ι ≫ p ≫ i` |
| Generic point of C | Existential `ηC : C` with `IsGenericPoint ηC Set.univ` |
| Identification kappa(eta_C) = L | `e : C.residueField ηC ≅ CommRingCat.of L`, a ring/field isomorphism |
| Canonical generic restriction into the puncture | `g : Spec (CommRingCat.of L) ⟶ U.toScheme` with `g ≫ U.ι = Spec.map e.hom ≫ C.fromSpecResidueField ηC` |
| Generic restriction of p is the specified map, respecting K | `(Spec.map e.hom ≫ C.fromSpecResidueField ηC) ≫ p = Spec.map (CommRingCat.ofHom (algebraMap (T.residueField η) L)) ≫ T.fromSpecResidueField η` |
| Generic restriction of a is exactly u | `g ≫ a = uL` |
| No separability, separatedness or characteristic restriction | None appears among the binders |

The generic compatibility equation also forces `p ηC = η`, and, by naturality and
faithfulness of Spec, identifies the induced embedding of K in kappa(eta_C) with the
specified algebra map into L under `e`. Thus the field isomorphism is not an arbitrary
abstract identification. Similarly `g` is fixed by its composite with the open immersion
`U.ι`; it is the canonical generic factorization, not an arbitrary auxiliary map.
There are no inline `let`, `show`, proof casts, or file-local definitions in the statement.
One explicit universe `u` is shared by the schemes, their residue fields and both field
spectra, as required by Mathlib's category of schemes; every variable and universe is bound.

Statement dependencies used (no private copies):

- `def-weil-field`: `Field` from `Mathlib.Algebra.Field.Defs` (publicly available through the imported scheme/field hierarchy).
- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, its morphisms and opens from `Mathlib.AlgebraicGeometry.Scheme`; the affine predicate is Mathlib `AlgebraicGeometry.IsAffine`.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`, `Mathlib.AlgebraicGeometry.Properties`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`, `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and `AlgebraicGeometry.QuasiCompact`, `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-weil-pbc-krull-dimension-ring`: `ringKrullDim`, `Mathlib.RingTheory.KrullDimension.Basic`.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField`, `Mathlib.AlgebraicGeometry.ResidueField`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`, `Mathlib.AlgebraicGeometry.Scheme`.
- `def-pc-scheme-fibre`: its recorded `Mathlib.AlgebraicGeometry.Fiber` is imported; the canonical residue-field point used here is `AlgebraicGeometry.Scheme.fromSpecResidueField` from `Mathlib.AlgebraicGeometry.ResidueField`. The statement itself requires this canonical point rather than a new fibre construction.
- `def-weil-pbc-normal-ring`: the recorded inline normal-domain conjunction `IsDomain ∧ IsIntegrallyClosed`, with `IsIntegrallyClosed` from `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`.

All recorded proof-dependency modules are imported privately. In particular these include
`WeilConjectures.Mathlib.AlgebraicGeometry.Normalization` (normalization in a function field,
normal stalks, finiteness and generic-field identification),
`WeilConjectures.RingTheory.FiniteTypeDomainDimensionLocalRing`,
`WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp`, and
`Mathlib.AlgebraicGeometry.SpreadingOut` (`spread_out_of_isGermInjective'`).
The docstring follows all seven DAG proof steps and names every proof dependency.

Edge cases checked before writing:

- An integral scheme is nonempty. The closed point with local dimension one excludes
  the zero-dimensional field spectrum and prevents c from being the generic point.
  The generic factorization through U makes the puncture nonempty; it cannot be
  silently replaced by an empty scheme.
- The identity extension L = K is allowed: no positive extension-degree or nontriviality
  condition appears. Purely inseparable extensions in positive characteristic are allowed.
- W and Y need not be affine, quasi-compact, reduced, integral or separated. The supplied
  generic map ensures W is nonempty; no additional condition is imposed.
- When the unwanted finite set of points is empty, the proof's product is one; the
  shrinking construction keeps all of N and still satisfies the required conclusion.
- Field k is arbitrary in characteristic and perfection. No smoothness or regularity
  assumptions are introduced. Normality is stated exactly as normal stalks.

Existing-declaration searches (all through the prescribed wrapper for Q109/item):

- LeanFinder: `A normal finite type curve model of a finite extension of a function field with a prescribed generic morphism on the punctured curve`. Eight hits, including `Scheme.RationalMap.ofFunctionField`, `Scheme.PartialMap.fromFunctionField` and Weierstrass models. None supplies the curve, chosen point, puncture and prescribed finite generic extension together.
- Loogle: `"normalization", "functionField"`. Zero hits.
- Mathlib grep: `fromFunctionField|normalizationIn|punctured`, restricted to `AlgebraicGeometry`. Five hits in `Mathlib/AlgebraicGeometry/Birational/RationalMap.lean`; they concern restrictions of already existing partial/rational maps. Read the relevant signatures and docstrings, including `RationalMap.ofFunctionField` and `RationalMap.fromFunctionField_ofFunctionField`.
- LeanSearch: `Normalize an integral curve in a finite extension of its function field and spread a prescribed generic morphism over the punctured curve`. Eight hits, including rational maps and relative normalization. No exact theorem.
- `rg -n 'punctured|normalCurve|normal_curve|normalizationIn'` in the prescribed `lean/WeilConjectures` and `lean/Sheaf` trees; followed by narrower `punctured.*generic|generic.*punctured|normal.*curve.*model` searches in their algebraic geometry subtrees. The normalization interfaces are the proof dependencies. Read `finite_normal_relative_curve_model` in `Sheaf.AlgebraicGeometry.FiniteNormalRelativeCurveModel`: it is a different relative, projective, separable construction and does not state this result.
- `grep -rn 'lem-sfb-normal-curve-punctured-generic-model' lean/WeilConjectures` gave no match. Searching the proposed full declaration name and module name in Mathlib, both project source roots and `dag/lean_names_upstream.json` gave no match.

No statement dispute or node fault found. The module compiled with `scompile.py` on
2026-10-24 in both sandbox and library module contexts, with no errors or warnings
(2.1 seconds and 2.6 seconds respectively, each within the default 60-second limit).
Independent review is the maintainer's review, as required by the dispatcher's direct-delivery workflow.

## Second reading by Q109

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
