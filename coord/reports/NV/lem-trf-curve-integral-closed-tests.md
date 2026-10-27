## Worker report

The module `Sheaf.AlgebraicGeometry.CurveIntegralClosedTests` states
`AlgebraicGeometry.Scheme.Modules.curve_integral_closed_tests`, with one whole-proof
`sorry`. No definition, extra node, dependency repair, or statement correction is needed.
The Stacks source was read at `literature/stacks-project/varieties.tex`,
`lemma-degree-on-proper-curve` (0AYV), especially its condition-(2) proof, and
`definition-degree-invertible-sheaf` (0AYR).

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| Field k | `(k : Type u) [Field k]` |
| Integral scheme C over k | `(C : Scheme.{u}) [C.Over (Spec (.of k))] [IsIntegral C]` |
| Proper over k | `[IsProper (C ↘ Spec (.of k))]` |
| Topological dimension exactly one | `(hdim : topologicalKrullDim C = 1)` |
| Specified generic point ξ | `(ξ : C) (hξ : closure ({ξ} : Set C) = Set.univ)` |
| Invertible L | `(L : C.Modules) [L.IsInvertible]` |
| Every integral closed subscheme | `∀ (Z : Scheme.{u}) [IsIntegral Z] (i : Z ⟶ C) [IsClosedImmersion i]` |
| Exactly one alternative | `Xor (IsIso i) (...)` uses Mathlib's exclusive disjunction |
| First alternative: isomorphism over C | `IsIso i`: i itself is the structure map to C |
| Second: a closed point other than ξ | `∃ z : C, IsClosed ({z} : Set C) ∧ z ≠ ξ ∧ ...` |
| Identification with Spec κ(z) over C | `∃ e : Z ≅ Spec (C.residueField z), e.hom ≫ C.fromSpecResidueField z = i` |
| G is the structure module | Every occurrence of G is the explicit existing `SheafOfModules.unit C.ringCatSheaf` |
| G is coherent | `RingedSpace.IsCoherent C.toRingedSpace (SheafOfModules.unit C.ringCatSheaf)` |
| Support is C, with the specified definition | `{x : C \| ¬ Subsingleton ↑(TopCat.Presheaf.stalk ... x)} = Set.univ` |
| Generic maximal ideal is zero | `IsLocalRing.maximalIdeal (C.presheaf.stalk ξ) = ⊥` |
| The maximal ideal annihilates the generic stalk | Explicit `∀ a, a ∈ ... → ∀ m : TopCat.Presheaf.stalk ..., a • m = 0` |
| Generic stalk is κ(ξ) as a stalk-ring module | `Nonempty ((RingedSpace.moduleStalkFunctor C.toRingedSpace ξ).obj G ≅ (ModuleCat.restrictScalars (C.residue ξ).hom).obj (ModuleCat.of (C.residueField ξ) (C.residueField ξ)))` |
| Dimension one over κ(ξ) | `Module.finrank (C.presheaf.stalk ξ) ↑(TopCat.Presheaf.stalk ... ξ) = 1`, with the zero maximal ideal and residue-module identification in the preceding conjuncts |
| L tensor O_C is isomorphic to L | `Nonempty (L ⊗ SheafOfModules.unit C.ringCatSheaf ≅ L)` |
| Euler difference equals degree | `(L ⊗ SheafOfModules.unit C.ringCatSheaf).eulerChar k - eulerChar k (SheafOfModules.unit C.ringCatSheaf) = L.degree k` |

The module-stalk functor has the same carrier as the explicit abelian-presheaf stalk.
Scalar restriction is along the **canonical** quotient `(C.residue ξ).hom`, not an
unspecified map. Since the maximal ideal is zero, that quotient is an isomorphism;
linear independence and spanning over the stalk ring are exactly those over its
residue field. Thus the finrank conjunct expresses the requested dimension, using
the same generic-local-ring encoding as the parent theorem
`eulerChar_tensor_invertible_generic_rank`. No arbitrary field action is supplied.

The witness conjuncts are stated independently of i. This is logically equivalent
to placing them under the first alternative: instantiate the latter assertion at
`i = 𝟙 C` to recover the independent witness, and conversely use it for every
whole-curve case. This is a rearrangement of quantifiers, not an extra conclusion.

Dependency declarations read and used (Mathlib paths abbreviate the module prefix):

- `Algebra.Field.Defs`: `Field`.
- `AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Topology.KrullDimension`: `topologicalKrullDim`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` and its existing monoidal structure.
- `AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`.
- `AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map` (reexported by
  the residue-field statement import).
- `AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Scheme.residue`,
  `Scheme.fromSpecResidueField`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: the recorded public import exposes
  `AlgebraicGeometry.RingedSpace.IsCoherent`, whose full finite-type-kernel definition
  was read in `WeilConjectures.AlgebraicGeometry.Coherent`. The weaker conjunction
  `Scheme.Modules.IsQuasiCoherentFiniteType` is not substituted for coherence.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor` supplies the recorded general notion.
  For the actual scheme sheaf the node's note directs use of
  `RingedSpace.moduleStalkFunctor`, imported from
  `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`; its full definition was read.
  All carriers are Mathlib's existing `TopCat.Presheaf.stalk`.
- `LinearAlgebra.Dimension.Finrank`: `Module.finrank`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, the existing localization tensor.
- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`: `Scheme.Modules.eulerChar`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`: `Scheme.Modules.degree`.

Proof-only imports are the recorded
`WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`,
Mathlib's `AlgebraicGeometry.FunctionField` (integral-stalk statements), and
`CategoryTheory.Sites.Sheafification` (the sheafification adjunction and unit).
Scheme sobriety and the closed-point residue immersion criterion are already
provided by the public Properties/ClosedImmersion imports.
`lem-trf-proper-field-invertible-coherent` has no Lean record or Mathlib match in
this snapshot, so there is no module to import for that proof-only dependency.
It is referenced by its node in the proof docstring. It is not needed to type
this statement, and no theorem is being proved in this delivery.

Edge cases checked: integral C and integral Z are nonempty, so the empty
subscheme is correctly excluded. Dimension zero (including a singleton C) is
excluded exactly by hdim; dimension one is needed for exclusivity. Z need not
be normal, smooth, geometrically integral, or rational over k. Closed points
use their full residue fields, without a k-rationality condition. The identity
immersion is allowed and supplies the witness. A nontrivial line bundle is
allowed, and the unit bundle gives the expected zero degree difference. There
is no restriction on characteristic or algebraic closure of k. The field,
scheme and test scheme use the established common Scheme universe convention;
there is no independent smaller universe of test schemes. Every universe and
variable is explicitly bound; `autoImplicit` is false.

Searches for an existing complete statement:

- `msearch.py ... leanfinder`: “Integral closed subschemes of a proper integral curve
  are the whole curve or residue fields of closed points, and the structure sheaf
  is the generic Euler characteristic witness”. Eight hits, including IsIntegral,
  functionField, residueField and isField_of_universallyClosed. None includes the
  dichotomy and witness assertion.
- `msearch.py ... leansearch`: “Integral closed subschemes of a one dimensional
  integral scheme are the whole scheme or reduced closed points”. Eight hits,
  concerning integrality/reducedness and integral morphisms; no complete match.
- `msearch.py ... loogle`: `AlgebraicGeometry.IsClosedImmersion, AlgebraicGeometry.IsIntegral`.
  Zero hits.
- `msearch.py ... grep`: `(integral|Integral).*(closed|Closed)|finrank.*stalk`,
  subdirectory `AlgebraicGeometry`. Eleven hits (proper/integral morphisms and
  FlatRank), none states this assertion.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `integral_closed_tests`, and `curve_integral_closed`: no existing declaration.
- Concept searches for generic-stalk finrank and structure-module stalks found
  `InvertibleModuleGenericStalk`, `CurveEulerTensorGenericRank`, and the existing
  stalk functors. Their full interfaces were read; they provide pieces or a
  different conclusion, not the present dichotomy plus generic witness.

Validation: `scompile.py NV lem-trf-curve-integral-closed-tests` successfully compiled
this module on the server in 1.9 seconds, with no errors or warnings. During the
last invocation local scratch space was full; the wrapper's normal server
confirmation fallback completed successfully. Initial drafts were repaired to
use explicit abelian stalk carriers, explicit `eulerChar` on the structure
module, and scalar restriction along the residue map. No live files were edited.
No statement dispute or mathematical node fault was found.

## Second reading by NV

The final file and node were reread in this worker session; no separate agent
was started, as the dispatcher explicitly forbids that. The maintainer's
independent review remains the delivery review. This rereading checked the
whole clause table above against the final signature, especially exclusive
rather than inclusive disjunction, the equality of maps over C, exact coherence,
annihilation and the residue-module identification, and the order and signs
of the Euler difference. The only implementation changes during drafting
were the explicit stalk/coercion and scalar-restriction interfaces described
above. The mathematical statement, dependency list, and proof plan are unchanged.
