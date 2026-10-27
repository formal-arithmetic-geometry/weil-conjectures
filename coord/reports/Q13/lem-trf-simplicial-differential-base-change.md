## Worker report

The module `Sheaf.RingTheory.SimplicialDifferentialBaseChange` states
`Algebra.CotangentResolution.exists_simplicialDifferentialBaseChange`. Its
conclusion is the simultaneous existence of the base-changed augmented algebras,
their differential models and their natural comparison. It includes the chain
and derived isomorphisms as real functorial constructions, and the degreewise
formula assertion `SimplicialDifferentialBaseChange.complexIso_generators`.
Both theorem proofs are exactly `by sorry`; all definitions contain real data.
No existing node statement, dependency list or proof was changed. No new nodes
or dependency modules are required: the structure packages this item's own
multi-clause assertion, using the dependency's existing notions throughout.

Clause-by-clause correspondence (names below are in `Algebra.CotangentResolution`):

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Commutative ring maps R → R' → T | `{R R' T : CommRingCat.{u}} (α : R ⟶ R') (β : R' ⟶ T)`; no flatness or polynomial assumption |
| Arbitrary augmented simplicial R-algebra P → T | The fields range over every `P : Augmentation (Arrow.mk (α ≫ β))`, the dependency's structure with its base map, augmentation and triangle |
| Faces, degeneracies, simplicial identities and augmentation compatibility | `P.algebra : SimplicialObject CommRingCat`, and the natural transformations `P.base` and `P.augmentation`; the same holds for `baseChange P` |
| Q_n = P_n ⊗_R R' | `baseChange P : Augmentation (Arrow.mk β)` and `pushout P n : CategoryTheory.IsPushout (P.base.app ...) α (inclusion P).app ... (baseChange P).base.app ...`; this is the universal property of exactly the tensor algebra with its two inclusions |
| Induced simplicial maps on Q | `inclusion P` and `(baseChange P).base` are natural transformations. Their naturality and the pushout uniqueness force every operator to send `p ⊗ a'` to `θ(p) ⊗ a'` |
| Augmentation p ⊗ a' ↦ ε(p)a' | `inclusion_augmentation` fixes the augmentation on `p ⊗ 1`; the triangle of `baseChange P` fixes it on `1 ⊗ a'` to `β a'`. Multiplicativity fixes their product to `ε(p) * β a'` |
| Universal differentials and tensor with T | `sourceModel P : DifferentialModel P` and `targetModel P : DifferentialModel (baseChange P)` use the recorded `differentialTerm` and `differentialGenerator`, hence the actual universal Kähler modules extended to T |
| Natural simplicial isomorphism | `iso P : (sourceModel P).module ≅ (targetModel P).module`; a simplicial isomorphism commutes with all operators, and thus with all faces and degeneracies, in both directions |
| Forward formula dp ⊗ t ↦ d(p ⊗ 1) ⊗ t | `generator` evaluates `(iso P).hom.app` on the coordinate differential generator and gives the generator at `(inclusion P).app p` |
| Inverse formula d(p ⊗ a') ⊗ t ↦ dp ⊗ a't | `inverse_generator` evaluates the inverse on the generator at `inclusion(p) * base(a')`, the pure tensor, and gives `differentialGenerator P n (β a' * t) p` |
| Augmentation-preserving maps | `AugmentedMap (𝟙 (Arrow.mk (α ≫ β))) P P'`, so both R and T are fixed and augmentation preservation is explicit |
| Their induced maps after base change | `baseChangeMap` is an augmented R'-algebra map; `baseChangeMap_inclusion` fixes it on the P inclusion, and its `AugmentedMap.base` fixes coefficients; pushout uniqueness forces the tensor-product map |
| Natural maps on differentials | `sourceMap` and `targetMap` are simplicial module maps normalized by `sourceMap_generator` and `targetMap_generator` on every differential generator, not arbitrary maps |
| Naturality of the comparison | `naturality` is the equality `sourceMap h ≫ (iso P').hom = (iso P).hom ≫ targetMap h`; inverse naturality follows by composing with the inverse isomorphisms |
| Alternating chain isomorphism s(M)^(-n) = M_n | `complexIso` is `(negativeComplex (ModuleCat T)).mapIso (S.iso P)`, using precisely the dependency's alternating-face complex and extension by zero |
| Prescribed degree -n maps | `complexIso_generators` states both formulas at `f (-(n : ℤ))`, using the dependency's actual `complexGenerator` coordinates |
| Isomorphism in D(T) induced by these maps | `derivedIso` is `DerivedCategory.Q.mapIso (S.complexIso P)`, with an explicit arbitrary localization-size universe `v` |
| Neither flatness nor polynomial-resolution hypothesis | `exists_simplicialDifferentialBaseChange` has only the two ring maps as arguments; P ranges over all augmentations |

The pushout presentation is an equivalent universal-property presentation of the
same canonical tensor algebra, not an assumption of an arbitrary comparison or
a choice from a mere existence theorem. In `CommRingCat.pushoutCocone` the object
is the actual `TensorProduct`; `CommRingCat.isPushout_tensorProduct` proves this
universal property. For any of the pushouts in the assertion there is a unique
isomorphism respecting both inclusions. Thus `inclusion p * base a'` is literally
the pure-tensor coordinate under that canonical identification. No definition
extracts an unspecified object from `exists_simplicialDifferentialBaseChange`.
The differential-model coordinates likewise use the dependency's actual tensor
modules, and all operators and comparison maps are fixed on their generators.
Tensor factors are written in the dependency's symmetric order `t ⊗ dp`.

Dependency declarations read and used:

- `Sheaf.RingTheory.CotangentResolutionCoherence`:
  `Algebra.CotangentResolution.Augmentation`, `AugmentedMap`, `DifferentialModel`,
  `differentialTerm`, `differentialGenerator`, `negativeComplex`,
  `differentialComplex`, and `complexGenerator`. The complete module, including
  its docstrings and signatures, was read. No copy of these definitions is made.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: `LinearMap.baseChange`, with
  `TensorProduct` and extension-of-scalars structures; the dependency uses
  `ModuleCat.extendScalars` for exactly this scalar extension.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`,
  `KaehlerDifferential.D`, and `KaehlerDifferential.linearMapEquivDerivation`;
  these underlie the recorded `CommRingCat.KaehlerDifferential` in the models.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, and `DerivedCategory.Q`; used by `derivedIso`.
- Proof dependency `lem-weil-pbc-kahler-differentials-base-change` has the
  Mathlib match `KaehlerDifferential.tensorKaehlerEquivBase` in
  `Mathlib.RingTheory.Kaehler.TensorProduct`, imported as a proof dependency.
  Its full signature, generator formula and tensor-module variant were read.
- Proof dependency `def-weil-pbc-module-tensor-product` is Mathlib's
  `TensorProduct`, already publicly imported through Tower. No duplicate is made.

Source reading: `literature/stacks-project/cotangent.tex`,
`lemma-localize-at-bottom` (08QZ), displayed differential comparison;
`algebra.tex`, `lemma-differentials-base-change` (00RV), including its explicit
universal derivation and inverse; `cotangent.tex`,
`definition-cotangent-complex-ring-map` (08PN), its nonpositive-degree convention.
The node's balancing proof extends the displayed comparison from polynomial
algebras to arbitrary augmented algebras, without extra assumptions.

Edge cases checked before and after drafting: n = 0 has zero outgoing
differential and no augmentation term; positive cohomological degrees are zero
by the exact recorded negativeComplex construction; constant and zero
simplicial modules are allowed. Zero rings and zero augmentation rings are
allowed because neither CommRingCat nor pushouts require nontriviality. Ring
maps may be identities or nonflat (e.g. Z → Z/2), and no term of P need be
polynomial or surjective onto T. No finiteness or characteristic restriction
appears. The arbitrary common universe u accommodates every set of the ring
and simplicial data by taking a maximum; the derived localization universe v
is independent. The inverse formula uses β a' explicitly, rather than an
unbound scalar action. No statement dispute or correction was found.

Searches performed using the prescribed msearch.py wrapper:

- LeanFinder: `Base change of augmented simplicial algebra Kahler differentials
  tensored with augmentation ring gives natural chain isomorphism`. Eight hits:
  termwise `KaehlerDifferential.tensorKaehlerEquivBase` and `tensorKaehlerEquiv`,
  presentation cotangent maps and extension lemmas, none the simplicial result.
- Loogle: `KaehlerDifferential.tensorKaehlerEquivBase, SimplicialObject`.
  Zero hits; service reports unknown identifier SimplicialObject.
- Mathlib grep: `simplicial|tensorKaehlerEquivBase` in `RingTheory/Kaehler`.
  Five hits, all termwise equivalence/formula declarations in TensorProduct.lean.
- LeanSearch: `Augmented simplicial Kahler differential complexes have natural
  base change chain isomorphisms`. Eight hits, termwise differential equivalences,
  presentation cotangent maps and ChainComplex.augment, no exact statement.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for simplicial/base-change
  differential patterns and `DifferentialModel|differentialGenerator`: the
  existing coherence module supplies the models, but no base-change comparison.
  Other hits concern ordinary termwise differentials and unrelated geometry.
- `grep -rn lem-trf-simplicial-differential-base-change lean/WeilConjectures`:
  no hit. Exact-name searches for all newly declared names across Mathlib,
  `lean/WeilConjectures`, and `lean/Sheaf`: no hit.

Validation: scompile.py compiled the sandbox probe and the exact library module
successfully, with no errors or unexpected warnings. Earlier compile diagnostics
were repaired by qualifying CategoryTheory.IsPushout, parenthesizing morphism
return types, and explicitly specifying the two different ring-arrow indices
when applying differentialComplex/complexGenerator. No index equality or other
hypothesis was added to solve elaboration.

## Second reading by Q13

This is the dispatcher's worker's separate clause-by-clause second pass, not a
claim of an independent worker review; the brief assigns independent review to
the maintainer and forbids spawning other agents. I reopened the node and the
finished module and checked each row of the correspondence above against both.
The two ring maps, all augmentations, pushout inclusions, augmentation formula,
forward and inverse generators, all simplicial operators, augmented-map
naturality, negative cochain convention, chain maps and derived localization
are present. The dependent-arrow indices in complexIso, derivedIso and the
coordinate formulas were made explicit during compilation; their different
base rings share precisely the same target T. The direct generator equations
use the same symmetric tensor order as the recorded dependency. No hypothesis
or conclusion mismatch remains, and no source-based node correction is needed.
