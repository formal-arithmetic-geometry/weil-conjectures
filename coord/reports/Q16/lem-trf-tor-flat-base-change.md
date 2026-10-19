## Worker report

The immutable Q16 delivery at a140aa699464c5d49a78368bef4613f226750bf1
repaired the previous unspecified-isomorphism conclusion by constructing the
actual coefficient map and asserting its bijectivity. Its natural statement,
four statement dependencies, and five-step proof were unchanged.

The maintainer's independent reading found that the base already contains
`Sheaf.RingTheory.TorCoefficientModule`, owned by
`def-trf-tor-coefficient-module`. In particular it already declares
`ModuleCat.torCoefficientLinearMap`. The delivery's private coefficient-action
construction and duplicate declaration are therefore removed in the replacement
module. This report describes the complete corrected delivery.

The replacement imports and uses the existing `torCoefficientModule` and
`torCoefficientLinearMap`. It adds only `torFlatBaseChange_scalarTower`, a
named proposition about those existing actions, and the actual tensor
extensions `torCoefficientBaseChange` and `torFlatBaseChangeMap`. The data
comes from the existing actions and `LinearMap.liftBaseChange`; it is neither
an arbitrary map nor a choice from an existence assertion. The compatibility
theorem and the main theorem have exactly `sorry` as proof. No definition
contains `sorry`.

The main theorem `ModuleCat.tor_flat_base_change` states bijectivity of the
specified map and the faithfully flat vanishing consequence. The correspondence
with the node is:

| Node | Corrected Lean |
| --- | --- |
| Commutative rings R, A, B | `{R A B : Type u}` and their three `CommRing` instances |
| Ring maps R → A → B and their composite | `Algebra R A`, `Algebra A B`, `Algebra R B`, `IsScalarTower R A B` |
| Arbitrary R-module M | `{M : Type u} [AddCommGroup M] [Module R M]` |
| B flat over A | `(hf : Module.Flat A B)` |
| Every nonnegative degree | `(n : ℕ)` |
| Tor over R with coefficients A | `torCoefficientModule R A (ModuleCat.of R M) A n` |
| Tor over R with coefficients B, restricted to A | `torCoefficientModule R A (ModuleCat.of R M) B n` |
| Tor(M,A) tensor_A B | `TensorProduct A (torCoefficientModule R A (ModuleCat.of R M) A n) B` |
| Canonical coefficient map | Existing `torCoefficientLinearMap R A (ModuleCat.of R M) A B n (Algebra.ofId A B)` |
| Canonical base-change map | `torFlatBaseChangeMap`, tensor symmetry followed by `liftBaseChange` of that map |
| Isomorphism assertion | `Function.Bijective (torFlatBaseChangeMap ... n)` |
| Faithfully flat assumption | `Module.FaithfullyFlat A B →` |
| Vanishing over B implies vanishing over A | `IsZero (torCoefficientModule ... B n) → IsZero (torCoefficientModule ... A n)` |

The B-action used for the extension is the existing
`(torCoefficientModule R B (ModuleCat.of R M) B n).isModule`, on the same
underlying additive group. The helper states that this and the existing
A-action form a scalar tower. The defining formula of the resulting map is
`t ⊗ b ↦ b • Tor(M,g)(t)`. Thus bijectivity means invertibility of this
canonical map, including its B-linear interpretation through tensor symmetry.

No flatness over R, finite-generation, Noetherian, nonzero, or positive-degree
condition is imposed. The common universe is the existing monoidal
`Tor' (ModuleCat.{u} R)` convention: it can be chosen to contain all four
carriers, with the usual common-universe lifts for independently sized inputs.
There is no equality imposed on site or category object/morphism universes.

Dependencies and sources read:

- `def-weil-pbc-tor-modules`: Mathlib `CategoryTheory.Tor'`, derived in M,
  `Mathlib.CategoryTheory.Monoidal.Tor`, lines 49–53.
- `def-weil-pbc-flat-ring-map`: `Module.Flat`, `RingHom.Flat` and
  `RingHom.flat_algebraMap_iff`; injectivity and exactness characterizations.
- `def-weil-pbc-faithfully-flat-ring-map`: `Module.FaithfullyFlat`, including
  `iff_exact_iff_lTensor_exact`, in `Flat/FaithfullyFlat/Basic.lean`.
- `def-weil-pbc-module-tensor-product`: Mathlib `TensorProduct`, its lift,
  generators, and symmetry.
- Existing coefficient helper interface `def-trf-tor-coefficient-module`:
  its actual functorial multiplication action, module, and coefficient map
  in `Sheaf.RingTheory.TorCoefficientModule`, lines 41–106. Reused as the
  implementation of the coefficient actions already present in node proof
  steps 1 and 4; no new independent notion is introduced here.
- `LinearMap.liftBaseChange` and `liftBaseChange_tmul`, pinned
  `Mathlib/RingTheory/TensorProduct/Basic.lean`, lines 43–60.
- Proof imports: `Module.exists_free_resolution_ses_split` in the group
  clone's `lean/WeilConjectures/Algebra/Homology/FreeResolutionSesSplit.lean`;
  `Module.Flat.rTensor_exact` and `lTensor_exact`; and
  `Functor.preservesHomologyOfExact` with `ShortComplex.mapHomologyIso`.

The source places are Algebra 00LY (`section-tor`, lines 18215–18278),
00M7 (`section-functoriality-tor`, lines 18714–18731), 00M8
(`lemma-flat-base-change-tor`, lines 18734–18749), 00HB
(`definition-flat`, lines 8620–8639), 00HD (`lemma-flat`, line 8708),
00CV/00CW/00CX (tensor products, lines 1700–1758), and Homology 010N
(`lemma-exact-functor`, line 1545). The source's 00M8 changes the base;
the node explicitly uses its free-resolution method for fixed-base
coefficient extension. That adaptation is valid without R-flatness of A or B.

The five proof steps remain: take a free R-resolution; identify the two tensor
complexes by the displayed generator formulas; commute flat coefficient tensor
with homology; identify the composite with the canonical map on cycles; and
reflect vanishing through faithful flatness using the complex 0 → T → 0.
The main docstring includes each step and its cited DAG statements. The
compatibility helper has its own proof explanation and source/blueprint tag.

Edge cases checked: n = 0 uses the unaugmented complex and a zero term in
degree -1; M = 0 and zero coefficient rings are allowed; B = 0 gives zero on
both sides of the first comparison; faithful flatness then enforces the
appropriate vanishing. Identity coefficient maps give the usual tensor-unit
map. No characteristic, boundedness, or finiteness restriction is used.

The original report recorded LeanSearch, LeanFinder, Loogle and grep searches
for fixed-base Tor coefficient change; they found flatness and Tor-resolution
infrastructure but no exact main theorem. The review's independent `rg`
searches of Mathlib, upstream WeilConjectures and group `lean/Sheaf` found the
existing all-degree coefficient interface above. `TorOneSurjectiveFlatMiddle`
is a degree-one interface, not the all-degree base-change theorem. The original
claim that there was no reusable coefficient helper was incorrect.

Validation: the immutable module itself passed the prescribed `scompile.py`
wrapper (sandbox 2.1 s, library 2.3 s). The corrected module passed against the
existing side overlay (sandbox 1.8 s, library 2.2 s), with no diagnostics. The
wrapper also compiled `Sheaf.RingTheory.TorCoefficientModule` into its private
overlay. The final record contains the exact corrected signature and only the
four declarations owned by this file. No global build or live Lean write was
performed. No natural-language statement correction or citer audit is needed.

## Second reading by Q16

Independent maintainer reading of the immutable delivery and the complete
replacement, with the source, dependency nodes and declarations open:

1. The commutative rings, composable ring maps, arbitrary module, flatness
   over A only, and all n ≥ 0 match the binders in the table above.
2. Both Tor objects use the recorded `Tor'` with M in the derived argument.
   Their coefficient actions and coefficient map now reuse the landed
   all-degree interface, instead of duplicating it (H4/H9 repaired).
3. `Algebra.ofId A B` is the specified A-algebra map. Restricting it to R
   gives the original coefficient map because of `IsScalarTower R A B`.
   Tensor symmetry and `liftBaseChange_tmul` give the exact canonical formula.
   Bijectivity of that map is the asserted isomorphism, not an arbitrary one.
4. Both vanishing assertions are `IsZero` for the corresponding A-module.
   This is equivalent to zero underlying group, independently of restricting
   the B-action. Faithful flatness has its source exactness-reflection meaning.
5. The degree-zero, zero-module, zero-ring, identity-map and common-universe
   cases listed above are covered. No hypothesis was strengthened.
6. Definitions contain actual data; only the two named theorem proofs are
   postponed. All local declarations have source and blueprint docstrings;
   the main theorem carries all five proof steps. Line lengths are ≤ 100 and
   `autoImplicit false` binds all variables. The record is verbatim.
7. Route-pivot dropped nodes were compared with the item's statement/proof
   dependencies: none occurs. No route-pivot repair note exists for this item.
   The module uses ordinary resolutions and tensor/homology, with no dropped
   machinery or pro-etale substitute.

Verdict: FIX. The complete replacement module, Lean record and this report
resolve the duplicate coefficient construction and full-name collision.
