## Worker report

Item: lem-sfb-norm-pencil-differential-polynomial. Group Q55. Date 2026-10-24.

The module `Sheaf.AlgebraicGeometry.NormPencilDifferentialPolynomial` states
`AlgebraicGeometry.Scheme.Modules.norm_pencil_differential_polynomial`, with exactly one
postponed proof, that theorem's `sorry`. The auxiliary declarations expand the objects and
clauses of this same node: scalar-restricted global sections, the target sheaf, the local
formula, scalar-extended schemes and modules, the complete normalized base-change data,
the actual finite polynomial sums, and the polynomial conclusion. They do not introduce
independent mathematical notions requiring new nodes. All definition data is explicit;
the base-change comparisons are existential conclusions of the theorem, never choices
from a mere existence theorem used to define data.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean rendering |
| --- | --- |
| F is a field | `{F : Type u} [Field F]` |
| C is an F-scheme | `{C : Scheme.{u}} (f : C ⟶ Spec (.of F))` supplies its specified structure morphism |
| smooth | `[Smooth f]` |
| projective, in the blueprint's convention | `[IsHProjective f]`, the recorded finite-projective-space embedding convention |
| geometrically integral and integral | `[GeometricallyIntegral f] [IsIntegral C]` |
| finite type | `[LocallyOfFiniteType f] [QuasiCompact f]` |
| dimension one | `_hdim : topologicalKrullDim C = 1` |
| invertible M | `(M : C.Modules) [M.IsInvertible]` |
| omega and its universal derivation | `f.relativeDifferentials`, `f.relativeDifferentialsDerivation.d` |
| J = Gamma(C,M) | `pencilSections f M`; it is literally the existing section module with scalars restricted by `f.specStructureMap ⊤` |
| Q = Gamma(C,omega tensor M squared) | `pencilSections f (pencilTarget f M)`; `pencilTarget` is `omega ⊗ (M ⊗ M)`, i.e. two copies of M with the displayed parenthesization |
| omega is invertible | first conjunct `f.relativeDifferentials.IsInvertible` |
| J and Q are finite dimensional | the two `FiniteDimensional F ...` conjuncts |
| delta is F-bilinear | existential `δ : J →ₗ[F] J →ₗ[F] Q` |
| alternating | `∀ s, δ s s = 0` |
| frame-independent formula | `PencilLocalFormula f M ...` quantifies every open U, every frame e with `IsFreeGenerator e`, every a,b, and every global s,t restricting to a e,b e; restriction of delta equals `tmulSection (b • da - a • db) (tmulSection e e)` |
| any commutative F-algebra R | `bc : ∀ (R : Type u) [CommRing R] [Algebra F R], PencilDifferentialBaseChange f M δ R` |
| C_R and its two projections | `pencilCurve`, `pencilProjection`, `pencilStructure` are exactly `Limits.pullback f (Spec.map (algebraMap F R))`, `pullback.fst`, `pullback.snd` |
| M_R | `pencilModule` is `(tensorPullback pencilProjection).obj M` |
| omega_R is canonically Omega(C_R/R) | `omegaIso` with `omega_d`, the equation `1 tensor da ↦ d(p_R-sharp a)` on every open |
| canonical comparison of the tensor target | `targetIso` and `target_tmul` specify its action on all local pure tensors eta tensor s tensor t, using the same `omegaIso` |
| canonical J and Q section comparisons | `sectionsM` and `sectionsQ`, with `sectionsM_tmul` and `sectionsQ_tmul` fixing `r tensor s ↦ r p_R^*s`; the second uses `targetIso` |
| same local differential formula over R | `differential`, `alternating`, `local_formula` in each base-change datum |
| pullback of delta agrees with scalar extension | `differential_tmul` fixes it on arbitrary r tensor s,r' tensor t; bilinearity determines it on all finite sums |
| arbitrary m >= 0 | `∀ (N r m : ℕ)` in `PencilPolynomialLaw`; ULift Fin m is the finite coordinate type for `AffineSpace` |
| all polynomial-coordinate sections s_P,t_P | arbitrary arrays `a b : Fin N → MvPolynomial (ULift (Fin m)) F` in any basis `bJ`; the isomorphism `sectionsM` identifies these with all sections on C_P |
| polynomial Delta into A(Q) | existential Delta between `AffineSpace (ULift (Fin m)) (Spec F)` and `AffineSpace (ULift (Fin r)) (Spec F)`, using arbitrary target basis bQ; its coordinate-ring diagram equals `Spec.map (MvPolynomial.aeval h)` |
| finitely many coordinate polynomials | `h = pencilCoordinatePolynomials δ bJ bQ a b`, where `h_k = sum_i sum_j C(c_kij) a_i b_j` |
| agreement with specialization over arbitrary R | first universally quantified clause of `PencilPolynomialLaw`: the actual scheme-valued point of Delta has coordinates `aeval v (h k)`, and `differential` on the specialized section sums equals `sectionsQ` on the same evaluated Q-coordinate sum |
| agreement over every extension field | specialize that arbitrary-algebra clause to `[Field E] [Algebra F E]` |
| closed zero locus and open complement | `IsClosed (PrimeSpectrum.zeroLocus (Set.range h))` and `IsOpen ...ᶜ` |
| v in D_Delta(E) iff differential nonzero | the last quantified equivalence, using `PrimeSpectrum.comap (aeval v).toRingHom ⊥` for the E-point, and the actual `bc E` relative differential on its specialized sections |

The tensor convention is `R ⊗[F] J` and `R ⊗[F] Q`, the left-R-module form of the
node's `J ⊗_F R` and `Q ⊗_F R`. Tensor symmetry gives the canonical identification;
the pure-tensor equations specify its normalization. `@id` in `sectionsM_tmul` merely
supplies the already defined scalar-restricted carrier to elaboration. It changes no data.
No let/have is hidden in the public statement.

Dependency declarations read and used (each statement-dependency node's statement and
Lean/mathlib record was read):

- def-weil-field: Mathlib `Field` (Algebra.Field.Defs).
- def-sbc-smooth-morphisms: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `Smooth`;
  `SmoothOfRelativeDimension` is the rank-one proof input.
- def-kun-projective: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `IsHProjective` and its finite projective-space factorization.
- def-pc-geometrically-irreducible: `Mathlib.AlgebraicGeometry.Geometrically.Integral`,
  `GeometricallyIntegral` (all field-base-changes integral).
- def-pc-integral-scheme: `Mathlib.AlgebraicGeometry.Properties`, `IsIntegral`.
- def-weil-finite-type-morphism: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `LocallyOfFiniteType`, and Morphisms.QuasiCompact, `QuasiCompact`.
- def-kun-topological-krull-dimension: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim` as Krull dimension of `IrreducibleCloseds`.
- def-sc-invertible-module: `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `Scheme.Modules.IsInvertible` and its monoidal tensor on `X.Modules`.
- def-weil-pbc-kahler-differentials: `Mathlib.RingTheory.Kaehler.Basic`,
  `KaehlerDifferential`, `KaehlerDifferential.D`, `linearMapEquivDerivation`.
- def-pur-sheaf-tensor-product: recorded
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`,
  `SheafOfModules.cochainModulesMonoidal`. The scheme tensor is the existing
  `MonoidalCategory X.Modules`, and `tmulSection` is from
  `WeilConjectures.AlgebraicGeometry.Modules.TensorSection`; no tensor is redefined.
- def-pc-base-change: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`,
  its documented chosen fibre product and projections (rather than confusing the
  moduleBaseChange functor with the underlying base-changed scheme).
- def-pc-module-pullback: `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`,
  `tensorPullback` and `tensorPullbackSection` from its recorded declarations;
  this is the actual sheafified section, not an unspecified adjunction unit.
- def-sc-relative-differential-sheaf:
  `WeilConjectures.AlgebraicGeometry.Modules.Differentials`,
  `Scheme.Hom.relativeDifferentials` and `relativeDifferentialsDerivation`;
  `Modules.DifferentialsSections` supplies the canonical `specStructureMap`.
- def-sbc-affine-space: Mathlib match `AlgebraicGeometry.AffineSpace`,
  `Mathlib.AlgebraicGeometry.AffineSpace`, including `AffineSpace.SpecIso`.
- def-weil-affine-spectrum: `Mathlib.AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`.

The stated proof-dependency modules are imported privately: ProjectiveImpliesProper,
CoherentFiniteTypeLocallyNoetherian, Cohomology.DirectImage.FiniteFreeComplex,
Cohomology.EulerChar, Mathlib Noetherian, Separated, and Kaehler.TensorProduct.
The differential/invertible/tensor definition modules needed in the proof are already
public imports because the signature uses them. The genuine unstated proof dependency
lem-trf-relative-differential-sheaf-base-change has no Lean or Mathlib record, so has no
module to import; it is not needed to type this statement. No cycle or wait is introduced.
The existing EulerChar proof-dependency interfaces cover field extensions and abstract
cohomology comparisons, not the whole arbitrary-algebra canonical degree-zero clause;
this theorem explicitly retains the full source clause and does not silently replace it
by those weaker interfaces. No unusable statement-dependency interface needed repair.

Sources checked directly: algebra.tex, lemma-differentials-base-change (00RV);
morphisms.tex, lemma-smooth-omega-finite-locally-free (02G1); coherent.tex,
lemma-flat-base-change-cohomology (02KH). The latest blueprint chapter and
sk-thm-sf-ctf-stability unit were read for context. This node is the auxiliary local-pencil
argument identified by the accepted DAG source/proof, not a unit's own statement.

Searches for an existing declaration:

- msearch.py leanfinder: “An alternating bilinear differential of two line bundle sections
  t ds minus s dt glues independently of local frame and commutes with scalar extension”.
  OK, eight hits: inCoordinates_apply_eq₂, IsLocalFrameOn.coeff_sum_eq,
  VectorBundleCore.inCoordinates_eq, IsLocalFrameOn.coeff_apply_of_mem,
  IsLocalFrameOn.eventually_eq_sum_coeff_smul, ContinuousLinearMap.inCoordinates_eq,
  Trivialization.linearMapAt, Trivialization.coordChangeL_apply'. These are analytic
  vector-bundle results, not the algebraic sheaf theorem.
- msearch.py loogle: `Polynomial.wronskianBilin, KaehlerDifferential.D`.
  OK, zero hits for the combined query.
- msearch.py grep: `wronskian|Wronskian`, RingTheory. OK, ten hits, all in
  Polynomial.Wronskian or its polynomial-radical application. The full definition
  `Polynomial.wronskianBilin` was read: it concerns ordinary polynomial derivatives,
  with no line bundle, gluing, sheaf base change, or parameter locus.
- Direct rg of both lean/WeilConjectures and lean/Sheaf and dag/lean_names_upstream.json:
  `Wronskian|wronskian|pencilDifferential|PencilDifferential|PencilLocalFormula|norm_pencil_differential_polynomial`.
  No matches. `grep -rn lem-sfb-norm-pencil-differential-polynomial lean/WeilConjectures`
  also found none. An initial broader `differentialPolynomial` search found only the
  unrelated CategoryTheory.PolynomialDerivedBarComparison declaration.

Edge cases checked mathematically before writing and again against the final signature:
characteristic two uses cancellation, never division by two; empty section bases N=0 or
r=0 are admitted; when Q=0 the list h is empty and the nonzero open is empty; proportional
or zero sections give the zero differential; m=0 uses a polynomial ring in no variables;
finite F has no rational-point nonemptiness assertion; R is an arbitrary commutative
F-algebra, including nonreduced rings and the zero ring. The C=empty case is excluded by
exactly the source's integrality/dimension-one assumptions, not by an added hypothesis.
All geometric, field and algebra carriers share an arbitrary universe u, with no
independent lower test universe that could make the quantified algebra cases vacuous.

No statement correction, new node, or dependency-module repair. No STATEMENT-DISPUTED
flag: the frame cancellation, arbitrary-flat-algebra comparison, and polynomial argument
support every clause as stated. The sole deferred proof is documented step by step in
the theorem docstring.

Validation: scompile.py compiled the sandbox and its actual library module cleanly.
Only the prescribed wrapper was used; no build or source mutation in the read-only clone.
The final dry run and delivery results are recorded below when available.

## Second reading by Q55

This is a separate second pass by the same worker. The dispatcher expressly prohibited
starting another agent; the maintainer's independent review will read the delivery.
No independent-worker review is claimed here.

Re-opened the node and final module and matched every hypothesis and clause in the table
above. In particular, checked the sign b da - a db, use of ALL local frames rather than a
chosen chart, the pure-tensor normalizations of both sheaf isomorphisms and both section
isomorphisms, arbitrary rings rather than only extension fields, the scheme-valued
specialization equation for Delta, and the nonvanishing equivalence over every extension
field. The second pass replaced a redundant existential `Delta = constructedMap` with
the explicit coordinate-ring diagram and actual point-specialization equation. It also
made the scalar-restricted carrier explicit in the sectionsM normalization, avoiding
reliance on an unstated R-action on the raw Gamma notation. Empty bases and m=0 are
still included. No mathematical hypothesis or conclusion changed.
