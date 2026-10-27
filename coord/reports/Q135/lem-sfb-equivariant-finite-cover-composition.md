## Worker report

The module `Sheaf.AlgebraicGeometry.EquivariantFiniteCoverComposition` states
`AlgebraicGeometry.equivariant_finite_cover_composition`, with a single `sorry` proof.
It introduces no definitions, axioms, helper theorems, or new nodes. The item's only
changed field is `lean`. All variables and universes are explicit; `autoImplicit` is false.

Source read: the complete node, its six proof steps, all eleven statement dependencies
and their recorded declarations/docstrings, and the six Mathlib proof dependencies.
The publisher scan https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf was opened:
de Jong, *Families of curves and alterations* (1997), Remarks 2.3(iii), printed p. 602,
expressly preserves generic etaleness under composition. The node also cites Situation
5.3 and the induction of Lemma 5.7. The stronger exact composite-kernel assertion is
explicitly the elementary agent strengthening already in the accepted node, not a
quotation from de Jong. The proof docstring includes all six accepted steps, including
the dense open on the target and both inclusions of the fixed field.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| A field k | `(k : Type u) [Field k]` |
| The three k-schemes | `V W T : Scheme.{u}` with the three specified maps `pV`, `pW`, `pT` to `Spec (.of k)` |
| All integral | `[IsIntegral V] [IsIntegral W] [IsIntegral T]` |
| All normal: local rings integrally closed domains | `hnormalV`, `hnormalW`, `hnormalT`, each quantifying over all points and asserting `IsDomain` and `IsIntegrallyClosed` of the actual structure-sheaf stalk |
| All projective over k in the node's convention | `[IsHProjective pV] [IsHProjective pW] [IsHProjective pT]` |
| All finite type over k | `LocallyOfFiniteType` and `QuasiCompact` on each structure map, exactly the recorded finite-type interface |
| Finite groups G,J,L | `G : Type v`, `J : Type w`, `L : Type z` with `Group` and `Finite` instances; independent universes |
| Surjective homomorphisms sigma and tau | `σ : J →* G`, `τ : L →* J`, `hσ`, `hτ` |
| G acts on k,V | `ρk : G →* (k ≃+* k)`, `ρV : G →* Aut V` |
| J acts on W, L on T | `ρW : J →* Aut W`, `ρT : L →* Aut T` |
| Actions on k through sigma and sigma-tau, compatible with structure maps | `hV`, `hW`, `hT`; inverse pullback on constants gives a left scheme action from a left field action, as in the published parent modules |
| Finite surjective morphisms a,c | `a : W ⟶ V`, `c : T ⟶ W` with `IsFinite` and `Surjective` instances |
| Equivariant through sigma,tau | `ha`, `hc`, equalities of scheme morphisms |
| Each etale over a dense open of its target | `haet`, `hcet`: existence of `U : V.Opens` or `W.Opens`, `Dense (U : Set _)`, `Etale (a ∣_ U)` or `Etale (c ∣_ U)` |
| K,M,F are the actual function fields, identified by the natural embeddings | `V.functionField`, `W.functionField`, `T.functionField`; `a.functionFieldMap a.apply_genericPoint_of_isDominant` and the analogous map for c |
| M fixed by ker sigma equals K | `hMa`: for every element of `W.functionField`, membership in the image of the canonical map from `V.functionField` iff fixed by every `j : σ.ker` |
| F fixed by ker tau equals M | `hFc`: the identical image/fixed-elements equivalence for c and `τ.ker` |
| Composite a after c finite, surjective | `IsFinite (c ≫ a) ∧ Surjective (c ≫ a)` |
| Composite etale over a dense open in V | The next existential over `V.Opens` with `Etale ((c ≫ a) ∣_ U)` |
| Composite group map surjective | `Function.Surjective (σ.comp τ)` |
| Composite equivariant through sigma-tau | The equality `(ρT l).hom ≫ (c ≫ a) = (c ≫ a) ≫ (ρV ((σ.comp τ) l)).hom` for every l |
| F fixed by ker(sigma-tau) equals K | Final elementwise equivalence using the canonical map of `c ≫ a` and all `l : (σ.comp τ).ker` |
| Actions need not be faithful | There is no `FaithfulSMul`, injectivity of an action, or Galois-group identification anywhere |
| Induced actions on function fields | Every fixedness assertion uses exactly `(Scheme.functionFieldAut (ρW j.val)).hom` or the T counterpart; no unrelated field action is supplied |
| T retains its normal/integral/projective/finite-type properties | The composite has exactly the original source T and original structure map pT, with the original hypotheses. No new terminal scheme or redundant conjunct is introduced. |

The fixed-field equalities are equalities of subfields inside the larger field written
extensionally: membership in the image of an injective field map is equivalent to being
fixed by all kernel elements. Unital field maps are injective. This is exactly the
node's convention of identifying the smaller field with its natural image. The final
map is the canonical generic stalk map of the composite, rather than an arbitrary ring
homomorphism. Surjectivity supplies dominance, and the existing generic-point theorem
supplies its generic-point equality without adding a hypothesis or existential choice.
The fixed subgroup is unchanged if every automorphism is replaced by its inverse, so
the published `functionFieldAut` pullback convention yields precisely the indicated
fixed fields for the left scheme actions.

Dependency declarations used:

- `Mathlib.Algebra.Field.Defs`: `Field` (`def-weil-field`).
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`
  (`def-pc-integral-scheme`), available through the function-field imports.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsHProjective` (`def-kun-projective`).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`
  (`def-weil-finite-type-morphism`), public transitively through the stated imports.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`
  (`def-weil-finite-integral-morphism`).
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`
  (`def-weil-surjective-morphism`), its dominance instance and composition instance.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`
  (`def-weil-etale-morphism`); the record's `IsEtale` spelling is a deprecated alias
  in this Mathlib, so the current name `Etale` is used.
- `WeilConjectures.AlgebraicGeometry.FunctionField` supplies the recorded interface
  for `def-sc-function-field`, whose integral-scheme clause expressly uses Mathlib's
  `AlgebraicGeometry.Scheme.functionField`. The component-product definition is not
  substituted for the generic stalk of an integral scheme.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra` (`def-pc-field-extension`); the node's
  equivalent ring-map formulation is used directly through canonical generic stalk maps.
- `Sheaf.FieldTheory.FieldTower`: `FieldExtension.degree` (`def-pc-field-tower`);
  the dependency module is imported, though the item asserts no degree formula.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`
  (`def-weil-open-immersion`), public through `Restrict`; `morphismRestrict` renders
  the inverse-image open subscheme map.
- `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback`:
  `Scheme.Hom.functionFieldMap`, together with the public imported
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree` declaration
  `Scheme.Hom.apply_genericPoint_of_isDominant`.
- `WeilConjectures.AlgebraicGeometry.StalkAut`: `Scheme.functionFieldAut`, the existing
  canonical induced automorphism, read in full.
- The proof dependencies are imported: finite composition/integrality through
  `Finite`; `Ideal.IsIntegral.comap_lt_comap` through `Ideal.GoingUp`; closed-map
  and finite-fibre facts through `Proper`, `UniversallyClosed`, `QuasiFinite`;
  etale base change and composition through `Etale`.

Edge cases checked before writing:

- Integral schemes are nonempty, so no empty-scheme case is silently lost.
- In dimension zero the dense opens are the entire integral spaces; the canonical
  function fields are still their generic stalks, and the same statement applies.
- Trivial groups, either surjection an isomorphism, and nonfaithful actions: kernel
  quantification makes each fixed-field equation have its ordinary meaning. No
  characteristic or group-order condition was introduced.
- If the second bad locus is empty, the proof's removed closed image is empty and
  the chosen dense target open is simply the first good open.
- The dense opens need not be invariant under any action; no invariant-open hypothesis
  has been added. The proof chooses an ordinary target open, as the node requires.
- No smoothness, global etaleness, flatness of the two original covers, separability
  hypothesis beyond the stated dense etale loci, or faithful action is imposed.
- The item calls a,c morphisms of schemes, without separate over-k equations. They
  remain scheme morphisms here; the action/structure-map compatibilities are exactly
  the three stated semilinear equations.

Searches (2026-10-24):

1. `msearch.py ... leanfinder "Composition of finite surjective generically etale
   equivariant covers and fixed fields of composite kernels"`: eight hits, including
   `IsGaloisGroup.to_isFractionRing`, `IsFractionRing.stabilizerHom_surjective`, and
   `finGaloisGroupMap.map_comp`; none states the combined geometric and exact-kernel result.
2. `msearch.py ... loogle '"AlgebraicGeometry.IsFinite", "comp"'`: five hits,
   including `IsFinite.instCompScheme`, `.of_comp`, `.comp_iff`; these cover only finiteness.
3. `msearch.py ... grep 'generically.?[eé]tale|fixedField.*ker|ker.*fixedField|equivariant.*cover'`:
   two hits in `FieldTheory/Galois/Basic.lean` and `Infinite.lean`, both Galois fixed-field
   restriction lemmas, not the item.
4. `msearch.py ... leansearch "Finite surjective generically etale equivariant scheme
   covers compose with equality of kernel fixed function fields"`: eight hits, including
   surjective composition and etale composition; no full match.
5. `rg -n 'functionFieldMap|functionField.*[Aa]ction|[Aa]ction.*functionField|
   finiteCoverComposition|EquivariantFiniteCover'` in `lean/WeilConjectures` and
   `lean/Sheaf` located the canonical generic map in `Curve/DivisorPullback.lean`
   and consumers; no duplicate theorem.
6. `rg -n 'lem-sfb-equivariant-finite-cover-composition' lean/WeilConjectures`: no hits.
7. `rg` in `lean/Sheaf/AlgebraicGeometry` and `lean/Sheaf/Paper` for normal integral
   projective bases, composite kernels, finite-cover composition, scheme automorphisms,
   and generically etale maps found the parent
   `FiniteEquivariantQuasiSplitNodalFibres.lean` and
   `EquivariantSingleCurveNodalReduction.lean`. Their statements were read: they use
   the same semilinear convention and actual `functionFieldAut`, but neither states
   this composition result. Reading `StalkAut.lean` found the already available
   induced automorphism, so no helper or definition node was needed.

Validation: prescribed `scompile.py Q135 lem-sfb-equivariant-finite-cover-composition
<module file>` compiled both its sandbox and actual module name in 2.1 seconds each,
with no errors or warnings. No direct compiler invocation or global build was run.
No statement dispute or correction was needed.

## Second reading by Q135

The dispatcher expressly forbids starting another agent, so this is a separate
self-review pass, not a claim of independent review. The maintainer's delivery review
remains independent. I reopened the node and the complete delivered module and checked
the correspondence above again. The three normality predicates use the actual local
rings; all three structure maps carry H-projectivity and the two finite-type conditions.
All three group universes are independent. The sigma and tau homomorphisms are
surjective hypotheses and their composite is a surjective conclusion. I checked the
order `c ≫ a`, the three inverse pullbacks of constants, the two equivariance squares,
the targets of the two dense opens, and each kernel in the three extensional fixed-field
formulas. In particular the final image is from V directly into T by the canonical map
of the composite; it is not merely a fixed-field inclusion or a field chosen separately.
The unchanged T explains the retained-properties clause without a tautological conjunct.
No mismatch was found and no node text was changed. There are no new nodes or repaired
dependency modules to review.
