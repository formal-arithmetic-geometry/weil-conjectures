## Worker report

The module `Sheaf.AlgebraicGeometry.GenericSmoothBoundaryPreparation` states
`AlgebraicGeometry.exists_genericSmoothBoundaryPreparation` with one `sorry` proof.
It introduces no definitions. The node's mathematical statement and all dependency lists
are unchanged. There is no statement dispute or dependency-interface fault.

I read the node, all seventeen statement-dependency statements and records, their
recorded declaration signatures and docstrings, and the example CompactObject module.
The source is Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé X, proof of Theorem 3.5,
Step 5, printed pp. 163--164. I opened the PDF text, including the paragraph beginning
“Factorizing f through a relative curve” and the purely inseparable preparation paragraph
on p. 164. I also read the current main-20261015 unit sk-i-curve-zero. This is a tool lemma
under that unit, not its own statement. The source's normalization convention and the
node's correction of the schematic-closure description are respected: the theorem asserts
the resulting models and maps, without incorrectly declaring a normalization a subscheme.

### Every hypothesis

| Node hypothesis | Lean rendering |
| --- | --- |
| S is a field spectrum or an excellent integral trait | `hS`: either a field k with `Nonempty (S ≅ Spec (.of k))`, or a commutative domain R with `IsDiscreteValuationRing R`, `IsExcellent R`, and the corresponding spectrum isomorphism. |
| X is integral | `[IsIntegral X]`. |
| X → S is proper, dominant, finite type | `p`, `[IsProper p]`, `[IsDominant p]`, and `hft : LocallyOfFiniteType p ∧ QuasiCompact p`. |
| Z is a closed subscheme of X | `i : Z ⟶ X` and `[IsClosedImmersion i]`. |
| Z omits the generic point of X | `hZ : genericPoint X ∉ Set.range i`. For closed subsets of an integral scheme this is exactly nowhere density. |
| Y is excellent and integral | `[IsIntegral Y]` and `hexcY : ∀ U : Y.Opens, IsAffineOpen U → IsExcellent Γ(Y, U)`. |
| Y → S is projective and dominant | `q`, `[IsHProjective q]`, `[IsDominant q]`. This is the node's finite projective-space embedding convention. |
| X₀ is excellent and integral | `[IsIntegral X₀]` and `hexcX₀`, the same affine-ring excellence condition. |
| a : X₀ → X is proper and dominant | `a`, `[IsProper a]`, `[IsDominant a]`. |
| a is generically finite | `hafin : ∃ U : X.Opens, Dense (U : Set X) ∧ IsFinite (a ∣_ U)`. The restriction includes the entire inverse image of U. |
| g : X₀ → Y is proper and dominant | `g`, `[IsProper g]`, `[IsDominant g]`. |
| The composites to S agree | `hcomm : a ≫ p = g ≫ q`. |
| The induced function-field extension has transcendence degree one | A generic point `η : X₀`, `hη : IsGenericPoint η Set.univ`, and `htrdeg` use `@Algebra.trdeg` with the algebra `(g.residueFieldMap η).hom.toAlgebra`. |

The generic point parameter does not strengthen the hypothesis: an integral scheme has
one, and any such choice is unique. Dominance sends it to the generic point of Y. On an
integral scheme the generic stalk is a field, canonically isomorphic to its residue field.
Thus these are exactly the function fields in the node, with their induced map, rather
than unrelated fields or an arbitrary algebra structure. This agrees with the generic
residue-field interface already used by RelativeCurveFactorization.

### Every conclusion

| Node conclusion | Lean rendering |
| --- | --- |
| Excellent integral Y₁ and a morphism b : Y₁ → Y | Existential `Y₁`, `b`, `IsIntegral Y₁`, and excellence of every affine coordinate ring. |
| b is projective, proper, dominant and generically finite | `IsHProjective b ∧ IsProper b ∧ IsDominant b` and a dense open U of Y with `IsFinite (b ∣_ U)`. |
| Y₁ → S is projective | `IsHProjective (b ≫ q)`. |
| κ(Y₁)/κ(Y) is finite purely inseparable | The generic point `y₁` has `IsGenericPoint y₁ Set.univ`; `(b.residueFieldMap y₁).hom.Finite` and `@IsPurelyInseparable ... (b.residueFieldMap y₁).hom.toAlgebra` use exactly the same induced extension. RingHom.Finite is Module.Finite for the algebra induced by that ring map, hence finite dimensional over the base field. |
| Excellent integral X₁ | Existential `X₁`, `IsIntegral X₁`, and excellence of every affine coordinate ring. |
| c : X₁ → X₀ and f : X₁ → Y₁ | The corresponding existential morphisms. |
| g ∘ c = b ∘ f | `c ≫ g = f ≫ b`. |
| h = a ∘ c is proper, dominant, generically finite | `IsProper (c ≫ a) ∧ IsDominant (c ≫ a)` and finiteness of `(c ≫ a) ∣_ U` on a dense open U of X. No extra property of c itself is asserted. |
| f is proper and dominant | `IsProper f ∧ IsDominant f`. |
| The fibre over the generic point is smooth | `Smooth (f.fiberToSpecResidueField y₁)`, over the actual residue field κ(y₁). |
| That fibre is an irreducible curve | `IrreducibleSpace (f.fiber y₁)` and `topologicalKrullDim (f.fiber y₁) = 1`. Properness of f supplies finite type. |
| The generic fibre of the reduced inverse-image boundary is finite étale | Both `IsFinite` and `Etale` of the fibre structure map of `(pullback i (c ≫ a)).nilradical.subschemeι ≫ pullback.snd i (c ≫ a) ≫ f`. This first takes the scheme-theoretic inverse image of Z, then its reduction, then its fibre. |
| Possibly empty boundary | No `Nonempty`, integrality, irreducibility or connectedness assertion is placed on the boundary. |

### Dependency declarations and imports

All statement-dependency modules are imported publicly. Definitions are reused, with no
private copies:

- def-weil-proper-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`.
- def-weil-finite-type-morphism: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`; `AlgebraicGeometry.QuasiCompact` supplies the other finite-type clause.
- def-pc-integral-scheme: `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`.
- def-exc-excellent-ring: `Sheaf.RingTheory.ExcellentRing`, `IsExcellent`. Scheme excellence is written directly as the node's affine-ring quantification, without defining another scheme predicate.
- def-sc-discrete-valuation-ring: `Mathlib.RingTheory.DiscreteValuationRing.Basic`, `IsDiscreteValuationRing` (Mathlib match).
- def-weil-closed-immersion: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`.
- def-kun-projective: the published live `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`, `AlgebraicGeometry.IsHProjective`. I read its current source with `scompile.py --source`; the older source checkout lacks this file.
- def-sc-generic-point: `Mathlib.Topology.Sober`, `IsGenericPoint` (Mathlib match), together with `genericPoint` for integral schemes.
- def-sc-function-field: `Sheaf.AlgebraicGeometry.FunctionField`; its recorded integral-scheme clause reuses `Scheme.functionField`, the generic stalk. The statement expresses this field by the canonically isomorphic generic residue field, so the induced inclusion can be given directly by `Scheme.Hom.residueFieldMap` from `Mathlib.AlgebraicGeometry.ResidueField` (available through Fiber). The component-product declaration applies to nonintegral curves and is not copied or specialized incorrectly here.
- def-kun-transcendence-degree: `Mathlib.RingTheory.AlgebraicIndependent.Basic`, `Algebra.trdeg`.
- def-pc-scheme-fibre: `Mathlib.AlgebraicGeometry.Fiber`, `Scheme.Hom.fiber` and `Scheme.Hom.fiberToSpecResidueField`.
- def-sbc-smooth-morphisms: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`.
- def-weil-etale-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale`.
- def-weil-pbc-scheme-reduction: `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`, `Scheme.nilradical` and `Scheme.IdealSheafData.subschemeι` with its actual subscheme domain.
- def-weil-finite-integral-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite`.
- def-pc-field-extension: `Mathlib.Algebra.Algebra.Defs`, `Algebra`, concretely `RingHom.toAlgebra` for the induced field map.
- def-weil-pbc-finite-purely-inseparable-extension: `Mathlib.FieldTheory.PurelyInseparable.Basic`, `IsPurelyInseparable` and the Module.Finite encoding `RingHom.Finite`.

The eight proof-dependency modules with Lean records are imported without `public`:
NowhereDenseDimZero, ZeroDimensionalClosedSubschemeFinite,
FiniteInseparableGeometricReduction, ClosedIrreducibleDimensionTrdeg,
WeilConjectures.AlgebraicGeometry.GroupScheme.Defs, GeonormalDimOneSmooth,
NormalizationGeonormalInsep, ReducedAlgebraicNormalizationFieldChange.
The two proof dependencies lem-trf-normalization-inseparable-base-change and
lem-trf-projective-inseparable-spread-normalization currently have neither a Lean record
nor a Mathlib match; there is no module to import for them. Their proof roles are retained
in the theorem's five-step docstring. They are not needed to elaborate this statement.

Additional public imports provide the finite ring-map predicate, dominance, and the
existing topological Krull dimension API. Every scheme and ring universe is explicitly
bound to u. There are no unbound implicit variables, local notation, local instances,
helper axioms, hidden proof terms, or data defined by sorry.

### Edge cases checked

1. Empty Z is admitted: reduction and pullback of the empty closed subscheme remain empty,
   and the empty scheme over a field is finite étale. The theorem imposes no boundary point.
2. Nonreduced Z is admitted: the reduction is taken after inverse image, not assumed for Z.
3. In characteristic zero purely inseparable extensions may be trivial. There is no
   positivity, exponent, nontriviality, perfectness or algebraic-closure assumption.
4. In positive imperfect characteristic the reduced boundary can initially be inseparable;
   the two successive extensions in the proof docstring handle this independently of
   geometric normality of the curve. No geometric irreducibility is substituted for
   irreducibility of the generic fibre.
5. Both allowed base types are included up to isomorphism; no global affine presentation
   is imposed on X, Y, X₀, X₁ or Y₁.
6. Integrality excludes empty X, Y, X₀, X₁, Y₁ as in the source. Dimension one excludes
   a point as generic curve; empty boundaries remain permitted.
7. Each generic finiteness clause restricts the entire morphism over a dense target open,
   not an arbitrarily chosen open subset of its source. On integral targets such a dense
   open cannot be empty.

### Searches

Searches were made through msearch.py under this item before writing:

- LeanFinder: “After a finite purely inseparable extension and projective alteration a
  proper relative curve has smooth irreducible generic fibre and finite etale reduced
  boundary”. Eight hits: smooth relative dimension, standard smooth presentation,
  Weierstrass good reduction and étale declarations; no preparation theorem.
- Loogle: `IsPurelyInseparable, Algebra.trdeg`: zero hits.
- Mathlib grep: `genericallyFinite|GenericallyFinite|purelyInseparable` in AlgebraicGeometry:
  four hits in Morphisms/UniversallyInjective.lean, none the preparation result.
- LeanSearch: “A finite purely inseparable extension makes a normalized generic curve
  smooth and its reduced boundary finite etale”: eight algebraic purely inseparable
  extension hits, including isAlgebraic, normal, isIntegral and hasExponent; no geometric
  preparation theorem.
- rg of WeilConjectures and lean/Sheaf for `smooth.*boundary|boundary.*smooth` found
  unrelated boundary/purity lemmas and plurinodal statements, not the combined assertion.
- rg of WeilConjectures for the exact node id found no declaration.
- rg for function-field maps located the actual generic stalk and residue-field APIs;
  the existing RelativeCurveFactorization module provides the same induced generic
  residue-field encoding and dense-open finiteness convention.
- rg for excellence and generically finite conventions found ExcellentRing and the
  existing affine-chart expressions in RelativeCurveFactorization; no new notion is needed.

### Validation

`scompile.py Q25 lem-trf-generic-smooth-boundary-preparation` compiled the sandbox file
and its library module separately, with the prescribed 60-second per-file limit. Both
were clean (5.0 s and 3.3 s respectively), with no warnings or errors. The exact theorem
signature is recorded verbatim in lean.statement. The statement is left unproved as
required for stage 2. The required delivery dry run passed preflight and compilation (candidate cd52bab2a1).
The final delivery is made by the prescribed deliver2.py wrapper after that successful dry run.

## Second reading by Q25

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
