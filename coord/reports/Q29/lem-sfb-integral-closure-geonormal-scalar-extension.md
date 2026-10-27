## Worker report

The module Sheaf.RingTheory.IntegralClosureGeonormalScalarExtension states
`integralClosure.geonormal_scalar_extension`, with `sorry` as its whole proof.
No definition, helper theorem, or additional node is introduced. The DAG statement,
statement dependencies, proof and proof dependencies are unchanged.

Source read: literature/stacks-project/varieties.tex, lines 5026–5090,
Tag 0C3N, lemma-normalization-and-change-of-fields. The affine proof identifies
A' tensor K with the integral closure when this tensor algebra is normal. The
node explicitly extends that argument to the geometric normality assumption and
adds field-map and principal-localization compatibility. The declaration's
docstring carries all six steps of the accepted DAG proof and their dependencies.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| Field k | `(k : Type u) [Field k]` |
| Commutative k-algebra A | `(A : Type v) [CommRing A] [Algebra k A]` |
| Finitely generated as an algebra | `hft : RingHom.FiniteType (algebraMap k A)` |
| Every field extension makes A tensor L a nonzero domain | `hgi : ∀ (L : Type (max u v w)) [Field L] [Algebra k L], IsDomain (A ⊗[k] L)` |
| F = Frac(A) | `FractionRing A`; hgi implies A is a domain, so this total fraction ring is its fraction field |
| B is the actual integral closure subring inside F | `B : Subalgebra A (FractionRing A)` and `hB : B = integralClosure A (FractionRing A)`; the equality specifies the named subalgebra, not an extra assumption on a preassigned independent object |
| B finite as an A-module | `[Module.Finite A B]` |
| Every local ring of Spec(B tensor L) is an integrally closed domain | `hgn` quantifies over all L and all prime ideals p, requiring `IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)`, exactly the recorded affine normal-ring form |
| Natural map to Frac(A tensor L) | The existential family `j L : B ⊗[k] L →ₐ[k] FractionRing (A ⊗[k] L)`, characterized by the displayed cleared-denominator formula for every b = a/s and every l |
| Injectivity | `Function.Injective (j L)` |
| Image equals integral closure | For every x in that exact fraction ring, `(∃ b, j L b = x) ↔ IsIntegral (A ⊗[k] L) x` |
| Integrally closed domain | `IsDomain (B ⊗[k] L) ∧ IsIntegrallyClosed (B ⊗[k] L)` |
| Finite over A tensor L | `RingHom.Finite` of `Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A B) (AlgHom.id k L)`, the canonical scalar-extension map; this is exactly Module.Finite for its induced module structure |
| Compatibility with every k-homomorphism L to M | Quantification over `t : L →ₐ[k] M`; the fraction-field map q extends `Algebra.TensorProduct.map (AlgHom.id k A) t` on C, and its composite with j L equals j M composed with the tensor transition on D |
| Compatibility with principal localization at any nonzero f | For every L and `f : A` with `f ≠ 0`, `aLoc` and `bLoc` embed `Localization.Away f ⊗[k] L` and `Localization.Away (algebraMap A B f) ⊗[k] L` into the same fraction field. The two generator equations give the localization square. The final iff says the localized B image is the integral closure of the localized A tensor algebra, using `aLoc.toRingHom.IsIntegralElem` |

The maps are specified canonically, not arbitrary maps assumed in the hypotheses.
The equation for j says j(b tensor l) times (s tensor 1) equals (a tensor l)
whenever b*s=a in F and s is nonzero. Every b admits such a representation;
s tensor 1 is nonzero by geometric integrality and faithful extension of scalars.
Thus the equation uniquely determines j. Taking b=1 and a=s=1 makes it the
canonical map on the L factor as well, despite expressing it as a k-algebra map
(to avoid introducing a second right-factor algebra structure on the tensor).

For the last clause, localization inverts precisely f and its image in B.
After tensoring, the denominators are powers of f tensor 1. The generator equations
for aLoc and bLoc therefore determine their values on all fractions: for example,
bLoc((b/f^n) tensor l) is j(b tensor l)/(f tensor 1)^n.
These equations are the commuting square after the standard tensor/localization
identification of the recorded base-change dependency. They identify the fraction
field of the localized A tensor algebra with the displayed common fraction field.
The final iff is consequently the localized comparison's integral-closure assertion,
not just an agreement on the unlocalized subring. Uniqueness on fractions also
implies the identity, composition and simultaneous field/localization compatibilities;
no restriction on t or on nonzero f beyond the node's is imposed.

Universes u and v for k and A are independent; the arbitrary additional universe w
allows extension fields of any larger size. Test fields live in max u v w, so the
geometric hypotheses cannot become vacuous by choosing a universe below A or k.
Pairs of differently sized fields are represented in their common maximum universe.
No domain instance is silently assumed on A: FractionRing is available for every
commutative ring, and hgi implies the needed domain property.

Dependency declarations used (the full recorded signatures and docstrings were read):

- Mathlib.Algebra.Field.Defs: `Field` (def-weil-field).
- Mathlib.Algebra.Algebra.Defs: `Algebra` and `algebraMap` (def-pc-field-extension).
- Mathlib.RingTheory.FiniteType: `RingHom.FiniteType` (the repaired recorded interface
  of def-weil-pbc-finite-type-algebra), equivalent to Algebra.FiniteType for algebraMap.
- Mathlib.LinearAlgebra.TensorProduct.Defs and Mathlib.RingTheory.TensorProduct.Maps:
  `TensorProduct`, `TensorProduct.mk`, `Algebra.TensorProduct.map` and its pure-tensor
  formula (def-weil-pbc-module-tensor-product and the algebra tensor universal property).
- Mathlib.RingTheory.IntegralClosure.Algebra.Basic: `integralClosure`, `IsIntegral`;
  Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs: `RingHom.IsIntegralElem`.
- Mathlib.Algebra.Module.LocalizedModule.Basic: `LocalizedModule`; ring specialization
  `Localization` is the same fraction quotient. `Localization.Away` and
  `Localization.AtPrime` give the principal and prime specializations.
- Mathlib.RingTheory.Finiteness.Defs: `Module.Finite`; `RingHom.Finite` uses exactly
  this finite module notion for the displayed canonical tensor algebra map.
- Mathlib.RingTheory.IntegralClosure.IntegrallyClosed: `IsIntegrallyClosed`;
  normal rings use the dependency's prescribed inline prime-localization conjunction.
- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Spec`. In this affine algebra statement the local-ring hypothesis
  is rendered by the recorded normal-ring interface at prime ideals, rather than
  introducing a redundant scheme argument.
- Proof imports: Mathlib.RingTheory.Flat.Basic and Mathlib.LinearAlgebra.Basis.VectorSpace
  for flatness over a field and preservation of injections;
  Mathlib.RingTheory.Localization.BaseChange for localization/tensor comparison;
  Mathlib.RingTheory.Localization.Integral for `IsLocalization.integralClosure`;
  Mathlib.AlgebraicGeometry.FunctionField for the affine local/fraction-field interface;
  WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal for
  `integral_totalFraction_mem_range_of_normal`. All stated proof dependencies are
  included directly or through their recorded Mathlib modules. No missing interface
  or import cycle was found.

Edge cases checked mathematically: A=B=k (all maps are scalar extension identities);
an already normal geometrically normal A; the cusp k[t²,t³] with B=k[t]; purely
inseparable extensions (no separability assumption was added); f=1 and any unit f;
f nonzero and nonunit; identity and composite extension-field maps. The zero algebra
is excluded precisely by the nonzero-domain part of hgi, not by an extra hypothesis.
f=0 is excluded precisely as in the node. No new statement fault was found.

Searches actually run:

- msearch leanfinder: “If a geometrically integral finite type algebra has finite
  geometrically normal integral closure then integral closure commutes with every
  field extension”. Eight hits include integralClosure.isIntegrallyClosedOfFiniteExtension,
  integralClosure.isFractionRing_of_finite_extension and IsIntegralClosure transport
  lemmas; none state the whole item or its two compatibility clauses.
- msearch loogle: `TensorProduct.toIntegralClosure`. Seven hits provide the canonical
  tensor comparison, injectivity under flatness, and bijectivity for smooth/localization
  base change. Arbitrary field extensions under the present hypothesis are not covered.
- msearch grep: `toIntegralClosure|integralClosure.*[Bb]ase`, subdirectory RingTheory.
  Hits in Mathlib/RingTheory/Smooth/IntegralClosure.lean describe those same comparisons.
  Read the comparison's full definition and the localization variant.
- msearch leansearch: “Integral closure commutes with scalar extension when normalization
  is geometrically normal”. Eight hits, including IsIntegralClosure.of_isIntegrallyClosed
  and IsLocalization.integralClosure, give ingredients rather than the present result.
- rg in lean/WeilConjectures and lean/Sheaf for `toIntegralClosure`, geometric normality
  and scalar normalization; the exact node id was also included. The normalization
  modules concern smooth or purely inseparable variants, and no module states this item.
- rg in dag/lean_names_upstream.json and both source roots for the proposed declaration
  name and normalization/scalar variants found no collision with
  `integralClosure.geonormal_scalar_extension`.

Validation: compiled through the required scompile.py wrapper against the published
live server library, in module mode. Both the sandbox-name and library-name passes
completed cleanly. The whole proof is the permitted single `sorry`. Delivery dry-run
and final delivery results are recorded below after the checks finish.

Delivery validation: `deliver2.py Q29 lem-sfb-integral-closure-geonormal-scalar-extension
--no-push` printed `OK (dry run)` for commit 646aa19b801: preflight and compilation
passed. A sandbox/base comparison confirmed `lean` is the only changed node field;
the module has no line exceeding 100 characters and exactly one whole-proof sorry.

## Second reading by Q29

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
