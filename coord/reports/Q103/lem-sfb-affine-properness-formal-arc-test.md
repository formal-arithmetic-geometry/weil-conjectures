## Worker report

The module `Sheaf.AlgebraicGeometry.AffinePropernessFormalArcTest` states
`AlgebraicGeometry.isProper_iff_affine_formal_arc_test`. Its only theorem has proof `sorry`.
There are no definitions, helper theorems, new nodes, dependency repairs, or statement
corrections. Only the item's `lean` field changes. All variables and the universe are
explicitly bound, and `autoImplicit` is disabled.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| Given algebraically closed field k | `(k : Type u) [Field k] [IsAlgClosed k]` |
| Schemes X and Z | `{X Z : Scheme.{u}}` |
| Both schemes affine | `[IsAffine X] [IsAffine Z]` |
| Given structures over k | `sX : X ⟶ Spec (.of k)` and `sZ : Z ⟶ Spec (.of k)` |
| X finite type over k | `[LocallyOfFiniteType sX] [QuasiCompact sX]` |
| Z finite type over k | `[LocallyOfFiniteType sZ] [QuasiCompact sZ]` |
| f is a k-morphism | `(f : X ⟶ Z) (hf : f ≫ sZ = sX)` |
| A is the actual ring k[[t]] | `PowerSeries k`, Mathlib's univariate power-series ring |
| K is k((t)) = A[1/t] | `LaurentSeries k`; `LaurentSeries.of_powerSeries_localization` identifies it as localization at powers of `PowerSeries.X` |
| f proper if and only if the test | `IsProper f ↔ ...` |
| Every a : Spec K → X and b : Spec A → Z | The two universally quantified morphisms `a` and `b` |
| a a k-morphism | `a ≫ sX = Spec.map (CommRingCat.ofHom (algebraMap k (LaurentSeries k)))` |
| b a k-morphism | `b ≫ sZ = Spec.map (CommRingCat.ofHom (algebraMap k (PowerSeries k)))` |
| Square compatibility f composed with a equals restriction of b | `a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k))) ≫ b` |
| Unique lift Spec A → X | `∃! lift : Spec (.of (PowerSeries k)) ⟶ X, ...` |
| Lift is a k-morphism | The first conjunct equating `lift ≫ sX` with the spectrum of the coefficient map |
| Restriction of lift is a | The second conjunct, spectrum of the canonical inclusion followed by `lift`, equals `a` |
| f composed with lift is b | The third conjunct `lift ≫ f = b` |
| Original k, with no extension allowed | Both test rings have coefficient type exactly `k` |
| Nonreduced schemes allowed | No `IsReduced`, `IsIntegral`, or domain condition is imposed on X or Z |

Composition in Lean is written in diagram order. In particular the square is `a ≫ f`,
and restriction is precomposition with the spectrum of the power-series inclusion.
The three lift conjuncts lie inside `∃!`, so uniqueness is precisely among compatible
k-morphisms, as in the node. The structure maps are arbitrary specified maps, rather
than chosen maps or additional algebra structures. All schemes and rings use the
same arbitrary universe `u`; no quantification over smaller-universe test objects occurs.

Dependency declarations read and reused:

- `def-weil-field`: `Field`, in `Mathlib.Algebra.Field.Defs` (available through the
  public imports). Its signature extends `CommRing` and `DivisionRing`.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme`; the affine condition is the existing
  `AlgebraicGeometry.IsAffine` in `Mathlib.AlgebraicGeometry.AffineScheme`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`, in
  `Mathlib.AlgebraicGeometry.Scheme`. Spectrum of a ring map has the reversed direction.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`, in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and `AlgebraicGeometry.QuasiCompact`,
  in `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`. Their conjunction is the
  dependency's explicitly recorded finite-type interface, used for both structure maps.
- `def-weil-formal-power-series`: `PowerSeries`, in `Mathlib.RingTheory.PowerSeries.Basic`.
  It is `MvPowerSeries Unit`; `PowerSeries.coeff_mul` gives the Cauchy product.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`. It extends `IsSeparated`,
  `UniversallyClosed`, and `LocallyOfFiniteType`; universal closedness implies
  quasi-compactness, as noted in the dependency record.

Additional existing Mathlib notions used are `IsAlgClosed` from
`Mathlib.FieldTheory.IsAlgClosed.Basic`, `LaurentSeries` from
`Mathlib.RingTheory.LaurentSeries`, and the canonical `algebraMap`.
Laurent series are Hahn series with exponent group Z. Well-ordered subsets of Z
are bounded below, so this is exactly the series ring with finitely many negative
powers, not arbitrary doubly infinite sequences. The algebra map from power series
is definitionally `HahnSeries.ofPowerSeries ℤ k` (`LaurentSeries.coe_algebraMap`).
The localization instance in the same source supplies the stated A[1/t] interpretation.
These existing notions need no additional definition or private wrapper.

Proof planning: the theorem docstring reproduces all six DAG proof steps, naming
the dependencies each step uses. Every recorded proof-dependency module is imported
non-publicly unless already a public statement import. Mathlib proof leaves are
also imported: discrete valuation rings, valuative criterion, locally Noetherian
schemes, affine quasi-separatedness, and adic-completion local rings, algebra and
completeness. `lem-sfb-properness-normal-curve-local-test` currently has neither
`lean` nor `mathlib_match`; it is a proof dependency only and supplies no object
needed to type this statement, so there is no module to import for it. Its role is
explicit in the proof docstring; the theorem does not assume that criterion as a
hypothesis. No dependency interface used in the statement was unusable.

Sources: read the item's whole recorded proof and the local Stacks source
`limits.tex`, `lemma-essentially-finite-type-criterion-proper` (Tag 0GWX), including
its normal-curve test, local DVR square and uniqueness clause. Read the actual
Mathlib declaration signatures and docstrings above and the recorded proof modules.
The node's MFK book is locally WANTED; this report does not claim to have read it.
The supplied proof is explicitly an agent formulation grounded in the Stacks inputs,
and the module source notice preserves that distinction.

Edge cases checked before finalizing:

- Empty X: there is no map from the nonempty `Spec k((t))` into X, so the test is
  vacuous and the empty morphism is proper, consistently with the equivalence.
- Empty Z forces X empty if f exists; the same check applies. No nonemptiness
  hypothesis excludes this case.
- Identity maps and finite closed immersions have unique compatible lifts.
- For `Spec k[ε]/(ε²) → Spec k`, both test rings are domains, forcing ε to zero;
  the unique lift agrees with properness of this finite nonreduced scheme. This
  checks that adding reducedness is unnecessary and would incorrectly restrict
  the scope.
- For `A¹_k → Spec k`, the Laurent point with coordinate `t⁻¹` has no power-series
  extension. Thus the condition detects this nonproper affine finite-type map.
- Positive characteristic and characteristic zero are both included; no
  separability, characteristic or perfection binder was added.
- All compatible b are tested, not just constant arcs, and the lift must match
  both its generic restriction and its specified map to Z.

Searches for an existing statement (Q103 search wrapper):

1. `leanfinder`: "An affine finite type morphism over an algebraically closed field
   is proper iff every compatible k Laurent series point extends uniquely over k
   power series". Eight results, including
   `AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom`,
   `AlgebraicGeometry.IsProper.of_valuativeCriterion`, and `AlgebraicGeometry.IsProper`.
   None states the fixed-original-field formal-arc criterion.
2. `loogle`: `"IsProper", "LaurentSeries"`. Zero hits.
3. `grep` (Mathlib wrapper):
   `formalArc|formal.arc|LaurentSeries.*[Pp]roper|[Pp]roper.*LaurentSeries`.
   Zero hits.
4. Direct `rg` across `lean/WeilConjectures` and `lean/Sheaf` for Laurent series,
   formal arcs and this node id: existing Laurent points and smoothing modules
   use the same canonical inclusion, but no theorem states this criterion.
   Direct search of `dag/lean_names_upstream.json` and both Lean source trees for
   properness/formal-arc names also found no matching declaration.
5. Direct Mathlib source searches located `PowerSeries`, `LaurentSeries`, their
   coefficient multiplication and localization instance. These were reused rather
   than redefined. A DAG search for Laurent-series text also found no missing
   independently required interface; the item's own text already specifies K.

Validation: `scompile.py Q103 lem-sfb-affine-properness-formal-arc-test` compiled the
module against the live published library, both in its isolated sandbox and by its
real module name, with no errors or unexpected warnings. The 60-second limit was
unchanged. Local checks verified the 100-column limit and that the node copy differs
only in `lean`. No statement fault or STATEMENT-DISPUTED issue was found.

## Second reading by Q103

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
