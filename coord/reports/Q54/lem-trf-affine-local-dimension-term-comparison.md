## Worker report

The module `Sheaf.AlgebraicGeometry.AffineLocalDimensionTermComparison` states
`AlgebraicGeometry.affine_local_dimension_term_comparison` with a single `sorry`
proof. It introduces no definitions or additional nodes. The item changes only
in `lean`; its statement, dependencies, proof, and all other fields are retained.

Sources read: Stacks Project `morphisms.tex`, Tag 02JU
(`lemma-dimension-formula`, its affine reduction) and Tag 01RV
(`lemma-integral-scheme-rational-functions`), together with the signatures and
docstrings of the dependency declarations below. The eight-step natural-language
proof from the node is included in the theorem docstring, including the two zero
transcendence-degree arguments and the two domain tower applications. This helper
concerns the comparison terms, so it imposes neither the Noetherian nor the
finite-type assumptions of the dimension inequality itself.

Hypotheses and objects are rendered as follows:

| Node text | Lean rendering |
| --- | --- |
| Schemes X and S, integral | `{X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]` |
| Morphism f, dense image | `(f : X ⟶ S) [IsDominant f]`; Mathlib defines this as `DenseRange` |
| Affine opens U and V | `(U : S.Opens) (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V)` |
| f(V) contained in U | `(hVU : V ≤ f ⁻¹ᵁ U)` |
| x in V, s=f(x) | `(x : V)`, and `f x`; a subtype coercion supplies its underlying point |
| Nonempty opens | `x` witnesses nonemptiness of V, and `⟨f x, hVU x.property⟩` witnesses that of U; no independent nonemptiness assumption is needed |
| A and B are section rings | `Γ(S, U)` and `Γ(X, V)` throughout, without replacement carriers |
| Induced affine map phi | `(f.appLE U V hVU).hom` throughout |
| Corresponding primes p and q | `(p : PrimeSpectrum Γ(S, U))`, `(q : PrimeSpectrum Γ(X, V))`, fixed by `hp : p = hU.primeIdealOf ...` and `hq : q = hV.primeIdealOf x` |
| Generic points | Existing `genericPoint`, used by `Scheme.functionField`; the actual generic-point image equality is `f.apply_genericPoint_of_isDominant` |

Every conclusion is retained:

| Node clause | Lean rendering |
| --- | --- |
| Contraction phi^-1(q)=p | `∃ hc : p.asIdeal = q.asIdeal.comap (f.appLE U V hVU).hom, ...` |
| Canonical germ isomorphisms A_p and B_q to stalks | Existential `eS` and `eX`, each a `≃+*`, with their composites with the canonical localization maps equal to the actual germ maps |
| Localization/stalk square | `(f.stalkMap x).hom.comp eS.toRingHom = eX.toRingHom.comp (Localization.localRingHom ... hc)` |
| Both local dimensions equal heights | Two `ringKrullDim` equalities with the corresponding `Ideal.height`, coerced to `WithBot ℕ∞` |
| Quotient-induced residue-field isomorphisms | `rS` and `rX` from the scheme residue fields to `p.asIdeal.ResidueField` and `q.asIdeal.ResidueField`, with equations specifying their composites with the stalk quotient maps |
| Identification with fraction fields of quotient domains | Mathlib's `Ideal.ResidueField` carries its canonical `Algebra (A ⧸ p)` and `IsFractionRing (A ⧸ p) p.ResidueField` instance; similarly for B and q. Thus these are literally field-of-fractions models of the two quotients, without a second chosen field |
| Residue-field square | `rX.toRingHom.comp (f.residueFieldMap x).hom = (Ideal.ResidueField.map ... hc).comp rS.toRingHom` |
| Residue transcendence-degree equality | Explicit `@Algebra.trdeg` on each pair of residue fields, with `.toAlgebra` of the actual scheme residue map and the canonical `Ideal.ResidueField.map` |
| Affine/generic transcendence-degree equality | Explicit `@Algebra.trdeg Γ(S, U) Γ(X, V)` for the affine map equals `@Algebra.trdeg S.functionField X.functionField` for `(f.functionFieldMap f.apply_genericPoint_of_isDominant).hom.toAlgebra` |
| No Noetherian or finite-type hypothesis | Neither appears in the theorem |

The existential ring isomorphisms are canonical: their equations on the affine
rings determine them uniquely by localization; the quotient equations then
determine the residue isomorphisms by the surjectivity of the quotient maps.
The theorem does not substitute arbitrary uncharacterized field isomorphisms.
The orientation of `hc` is the one required by Mathlib's canonical localization
and residue-field maps; it is exactly the symmetric form of contraction.

Dependency declarations read and reused (including the Mathlib-match records of
proof dependencies with no `lean` record):

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`,
  `Scheme.Hom`, `Scheme.Hom.appLE`, and `Scheme.Hom.germ_stalkMap`.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffineOpen.primeIdealOf`,
  `IsAffineOpen.fromSpec_primeIdealOf`, `IsAffineOpen.fromSpec_app_self`,
  `IsAffineOpen.isLocalization_stalk`, `IsAffineOpen.comap_primeIdealOf_appLE`,
  and `IsAffineOpen.arrowStalkMapIso` (the latter covers one part, not this
  entire comparison statement).
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`,
  `Localization.localRingHom`, and its germ/fraction normalization.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor` and the underlying presheaf stalk;
  imported as the node's recorded stalk interface, while ring stalks in the
  statement use `X.presheaf.stalk` directly.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.RingTheory.Ideal.Height`: `Ideal.height` and
  `IsLocalization.AtPrime.ringKrullDim_eq_height`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.residue`, `Scheme.Hom.residueFieldMap`, and
  `Scheme.residue_residueFieldMap`.
- `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField`,
  `Ideal.ResidueField.map`, `Ideal.ker_algebraMap_residueField`,
  `Ideal.injective_algebraMap_quotient_residueField`, and the quotient
  fraction-ring instance.
- `Mathlib.RingTheory.AlgebraicIndependent.Basic`: `Algebra.trdeg`.
- `Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis`:
  `trdeg_add_eq`, imported as a proof dependency.
- `Mathlib.Topology.Sober`: `IsGenericPoint`, `genericPoint`,
  `genericPoint_spec`.
- `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`:
  `LocallyRingedSpace.Hom`, including its local stalk-map condition.
- `Mathlib.AlgebraicGeometry.FunctionField`: `Scheme.functionField`,
  `Scheme.germToFunctionField`, and
  `functionField_isFractionRing_of_isAffineOpen`.
- `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback`:
  `Scheme.Hom.functionFieldMap`, explicitly the generic stalk map, not an
  independently chosen field inclusion.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `Scheme.Hom.apply_genericPoint_of_isDominant`.

The statement imports expose the dependency interfaces through the existing
module import chains. The already recorded declarations are usable; no dependency
repair is necessary.

Edge cases checked mathematically before drafting: identity maps and identical
charts; spectra of fields (all heights zero); the generic point (residue and
function-field descriptions agree); arbitrary nonclosed points; strict inclusion
of affine opens; infinite prime height; and infinite transcendence degree. Heights
are not truncated to natural numbers, and transcendence degrees are cardinals.
The empty scheme is excluded by the node's integral assumption; empty affine opens
cannot supply the point `x`, exactly as in the node. No separation, finiteness,
finite dimension, or characteristic restriction is introduced. All universe
variables and parameters are explicitly bound; there are no `let` binders or
file-local abbreviations in the statement.

Searches for an exact existing statement:

- `msearch.py ... leanfinder "Affine open charts of a dominant morphism of integral schemes identify local dimensions with prime heights and residue and generic field transcendence degrees"`: 8 hits, including `IsAffineOpen.primeIdealOf_genericPoint`, `IsDominant`, and the function-field Field instance; no combined comparison theorem.
- `msearch.py ... loogle "AlgebraicGeometry.IsAffineOpen.primeIdealOf, AlgebraicGeometry.IsAffineOpen.isLocalization_stalk, Algebra.trdeg"`: 0 hits.
- `msearch.py ... grep "trdeg.*(stalk|residueField)|comap_primeIdealOf_appLE" AlgebraicGeometry`: 3 hits, all prime-contraction/smoothness uses; no exact statement.
- `msearch.py ... leansearch "For a dominant morphism of integral schemes affine charts identify stalk dimensions with prime heights and both residue field and function field transcendence degrees"`: 8 hits, including `localRingHom_comp_stalkIso` and `Scheme.arrowStalkMapSpecIso`, which state the local-map component only.
- Direct `rg` in Mathlib's affine-scheme, residue-field, function-field,
  localization, height, and algebraic-independence modules located the APIs above.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` with
  `affine.*(trdeg|dimension)|trdeg.*(stalk|residueField)` found the landed
  local dimension inequality, the algebra affine inequality, and other consumers;
  none gives this full comparison. The inequality uses the same explicit
  algebra structures and function-field carrier.
- Direct `grep -rn "lem-trf-affine-local-dimension-term-comparison" lean/WeilConjectures`
  and `rg` for the proposed declaration/module in both roots and
  `dag/lean_names_upstream.json` found no matching declaration.

Validation: `scompile.py Q54 lem-trf-affine-local-dimension-term-comparison`
compiled this single file in both sandbox and library-module mode against the live
server library, with no errors or warnings (2.6 seconds for each mode).
No statement dispute, node fault, statement correction, or missing notion was found.

## Second reading by Q54

A separate self-review pass reread the node and the completed file. The dispatcher
requires this worker to operate without other agents; the maintainer supplies the
independent delivery review. This paragraph does not claim an independent worker
reading.

Checked every row of both tables against the signature. In particular `hp` and
`hq` specify the actual chart primes; the direction of contraction is reversed
only to match `localRingHom`'s API; both germ equations fix the isomorphisms;
the two quotient equations fix the residue isomorphisms in the inverse direction;
the residue square uses the actual morphism map; and every transcendence degree
gets the intended algebra instance explicitly. Checked the fraction-ring instance
of `Ideal.ResidueField`, so its use retains the `Frac(A/p)` and `Frac(B/q)` clauses.
The last algebra is the genuine generic stalk map, and both height equalities
allow infinity. The eight proof steps and the absence of Noetherian and finite-type
assumptions agree with the node. No mismatch required a change.
