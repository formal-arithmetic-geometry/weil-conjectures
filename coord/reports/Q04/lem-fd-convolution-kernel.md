## Worker report

Q04, stage 2, 2026-10-18. The delivery states
`WeilConjectures.fourierKernelConvolutionIso` in
`Sheaf.Paper.FourierKernelConvolution`. Its proof is `sorry`, with the node's eight-step
relative-chart proof in the docstring. Definitions contain actual constructions.
The original statement, proof and proof dependencies are unchanged. The item gains
one definition node and three already recorded statement dependencies, because its
helper definitions explicitly use the published adic operations.

Hypothesis and clause correspondence:

- Distinct primes, positive exponent, finite field and its algebraic closure, and
  the finite coefficient field containing all pth roots are `F : FourierSetting.{u}`.
  This is the recorded Fourier setting, not an independently bundled substitute.
  `F.field` contains the finite-field datum; `F.coefficients` contains l, its prime
  instance, the inequality of primes, Qbar, and its algebraic-closure structure.
  `F.extension`, `F.finiteExtension`, `F.rootsOfUnity_mem` give the fixed stage.
- `Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar` and `hΨ : Ψ ≠ 1`
  encode precisely a nontrivial multiplicative-valued additive character of F_p.
  Every AddChar value is a unit, since its value at the negative is its inverse.
  No hypothesis on `Ψ 1 - 1` or on a finite coefficient ring is added.
- The notation psi=Psi composed with finite-field trace introduces no independent
  character datum. The actual sheaf uses `fourierIntegralCharacter F Ψ` on ZMod p
  in the recorded prime-field Artin--Schreier construction. It never restricts psi
  back to F_p and never takes a trace from k. Consequently the case p divides a
  remains included. For inverse character the second factor uses `Ψ⁻¹`.
- `fourierGeometricBase F` is Spec k, `fourierGeometricSpace F n` is the standard
  affine space `𝔸(n; Spec k)`, and `r = Fintype.card n`. A finite coordinate type
  is equivalent to the source's nonnegative rank; the empty type covers rank zero.
  The standard basis identifies the dual with the same standard affine scheme.
- `fourierGeometricSquare`, `fourierGeometricTriple`, and `fourierGeometricR13`
  use the published categorical pullbacks and `pullback.tripleProj₁₃`. The triple
  is `(V × Vdual) ×_Vdual (Vdual × V)`, exactly the existing kernel convention.
  The two structural instances write the actual composites to Spec k.
- `fourierGeometricKernel` uses `fourierAdicKernel` of the standard evaluation
  function `AffineSpace.stdPairing`. The latter first uses the recorded upstream
  `Etale.fourierKernel` over the integral coefficient ring, then completed scalar
  extension, the recorded rationalization, and the actual common-stage pair.
  It is not a discrete Qbar étale-sheaf derived category.
- `fourierConvolutionIntegrand` is `integralCompletedTensor` of the two
  `integralDerivedPullback`s of their integral Artin--Schreier representatives.
  Those representatives are definitionally the representatives used by
  `fourierGeometricKernel`: `Etale.fourierKernel` unfolds to the same AS sheaf.
  They are written explicitly at the fixed stage to avoid extracting an opaque
  pair's stage as a dependent coefficient type. This builds the two-factor
  integrand, not a replacement character of x-y or x+y.
- `fourierGeometricConvolution` applies the published
  `sfQbarCompactSupportValue` to that actual integral integrand. This is the
  reduction-tower/derived-limit Rr13!, followed by rationalization and the pair
  inclusion, with no shift. Its compactification binder is an arbitrary choice
  used by the existing definition of Rf!: the schemes and projection already
  satisfy its geometric hypotheses. The theorem holds for every such choice,
  not for a specially chosen compactification or an arbitrary image object.
- `fourierIntegralDelta` uses the recorded
  `IntrinsicCoefficientTwists.integralCoefficientTwist` (in the public
  WeilConjectures namespace) with exponent `-(Fintype.card n : ℤ)`, followed by
  `sfCompletedDerivedDirectImage` along `pullback.diagonal`. This is the actual
  completed coefficient Tate line, not an arbitrarily selected rank-one object.
  `fourierDeltaKernel` rationalizes this object and includes it at the same E.
- `fourierSecondReflection` is `pullback.map` of identity on the first coordinate,
  the existing `AffineSpace.neg` on the second coordinate, and identity on Spec k.
  For `sign=true`, the delta definition additionally applies its ordinary derived
  image. For `sign=false`, it only applies the diagonal image. Both maps are proper,
  so these are the delta and reflected-delta images of the source statement.
- The first conjunct is `Nonempty (fourierGeometricConvolution F n Ψ Ψ⁻¹ c ≅ ...
  fourierDeltaKernel F n false)`. Our arguments list the r12 factor first and r23
  factor second, so this is K_(psi inverse) * K_psi, in exactly the source's
  convention K' * K = Rr13!(r12*K tensor r23*K').
  The second conjunct uses Ψ, Ψ and `true`, so it is K_psi * K_psi and the reflected
  diagonal. Each right side is shifted by `-2 * (Fintype.card n : ℤ)` with the
  recorded category's shiftFunctor. There is no transform shift inserted on the left.
- The functions and morphisms are their standard coordinate expressions over k;
  their coefficients 0, 1, -1 and the evaluation polynomial are defined over k0.
  The AS torsor and character projector are the same constructions over k0,
  followed geometrically to k. Upstream `artinSchreierSheafZModPullbackIso` is the
  canonical base-change identification for precisely this equation construction.
  Thus these are the geometric pullbacks required in the final clause; no descent
  datum or arbitrary sheaf is substituted for them.

The helper propositions `fourierPairingCharacteristic`, the two scalar-unit results,
`fourierSquareNoetherian`, `fourierConvolutionGeometry`, and the two constructibility
membership results are the proofs needed by these explicit definitions. Each has its
own source/blueprint tag and natural-language proof. All are postponed as named theorems;
none is used to choose unspecified data. The integral character is selected from an
existence-and-uniqueness theorem whose embedding equation uniquely determines it.
The invertible-p structure comes from the actual unit's inverse.

Dependency declarations read and used:

- `Sheaf.Paper.FourierSetting`: `WeilConjectures.FourierSetting`.
- `WeilConjectures.FourierTransform.ArtinSchreier`:
  `AlgebraicGeometry.Etale.artinSchreierSheaf`, `artinSchreierSheafZMod`, and its
  lisse/pullback declarations. The general-ring sheaf API is retained unchanged.
- `WeilConjectures.FourierTransform.Defs`: `AlgebraicGeometry.Etale.fourierKernel`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `WeilConjectures.generalAlgebraicallyClosedConstructibleCategory` and its actual pair.
- `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition`:
  `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_comp_of_nonempty_iso`;
  convolution is the same unshifted r12/r23 formula. This module is imported for the proof.
- `Sheaf.Paper.PbcCoefficientTwists`: `AlgebraicGeometry.Scheme.pbcTateTwist` publicly
  retains `IntrinsicCoefficientTwists`; the latter's `integralCoefficientTwist` is
  used before rationalization, since the item uses the intrinsic common-stage category.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `WeilConjectures.integralConstantToCompletionOfUniverses`, with its specified projections.
- `Sheaf.Paper.SfIntegralConstructible`: `WeilConjectures.sfIntegralConstructible`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the recorded integral and common-stage
  pullback/tensor interfaces, reexporting `integralDerivedPullback` and
  `integralCompletedTensor`. No second derived tensor is introduced.
- `Sheaf.Paper.QcqsCompactSupportRealization`: the recorded module, publicly retaining
  `IntegralRationalQbarCompactSupport.sfQbarCompactSupportValue` (all declarations
  are in namespace WeilConjectures). Its actual value definition is used.
- `Sheaf.Paper.SfDerivedDirectImage`: `WeilConjectures.sfCompletedDerivedDirectImage`.

Proof-only imports also cover all the proof dependencies currently having declarations:
QbarCompactSupportBaseChange, FourierTransform.Properties.Stalk,
FourierTransform.ArtinSchreierCohomology, SfRationalLocalGlobalPowerTorsion,
SfRationalBoundedConeTorsion, and SfOpenClosedTriangleAllStages. Dependencies with no
recorded declarations are retained in the node and in the eight-step proof docstring.

Edge cases checked before and during writing:

- Empty coordinate type/r=0: the twist and shift are zero and the projection is
  the point's identity up to the standard product isomorphism; no nonempty coordinate
  hypothesis or positive-rank assumption occurs. In the proof the open complement
  is empty, so the relative chart cover requires no index i.
- Characteristic two: negation equals identity and the two supports coincide;
  nothing assumes p is odd or that the supports differ.
- p divides a: the prime-field projector uses Psi, not the possibly trivial
  restriction of psi to F_p.
- Arbitrary finite coefficient extension satisfying the existing roots-of-unity
  assumption, including ramification: values of any additive character are pth
  roots of unity, hence integral units and uniquely lift. The trivial character is
  allowed by the new definition node, and only the main theorem excludes it.
- Geometric points with residue field larger than k: the definitions and proof plan
  are relative scheme constructions, not a reduction to k-valued closed points.
- No universe equality between site objects and morphisms is imposed. Coefficient
  module values are ULift into u+1, and the existing small coefficient model is used.

Searches for the item's exact statement:

1. msearch LeanFinder: “The convolution of Fourier Deligne Artin Schreier kernels is
   the diagonal delta sheaf with Tate twist and shift”: eight unrelated condensed
   monoidal/sheaf results; no match.
2. msearch Loogle: `"fourier", "convolution"`: six analytic Fourier/Schwartz results;
   no geometric kernel statement.
3. msearch Mathlib grep: `fourier.*[Kk]ernel|[Kk]ernel.*[Cc]onvolution`: zero matches.
4. msearch LeanSearch: “Artin Schreier sheaf with adic coefficients and convolution
   of Fourier Deligne kernels”: SchwartzMap Fourier convolution, FourierModule,
   sheaf abelian/additive instances and BDeRhamPlus; no match.
5. rg of the upstream source and the project Lean: no existing adic convolution
   theorem. Upstream FourierTransform.Inversion has
   `nonempty_iso_fourierKernel_convolution`, whose full signature was read: it assumes
   finite discrete coefficients, normalized finite Tate data and the unit condition
   on Ψ(1)-1, and supplies only the inverse-character identity. Its docstring explicitly
   leaves the adic Qbar reduction unformalized. It is not the item's statement.
6. rg and blueprint_refs searches for the added realization are recorded in full
   in the new node's mathlib_searches. Existing discrete AS/kernel and the general
   completed coefficient construction are used, rather than copied.

Validation: both delivered files compiled separately in dependency order through
`scompile.py Q04 lem-fd-convolution-kernel`. The final local wrapper run was clean
with no warnings. All statements use explicitly bound variables and universes.

No STATEMENT-DISPUTED issue, no statement correction, and no dependency-record repair.

## New nodes

`def-fd-adic-fourier-realization` owns `Sheaf.Paper.FourierAdicArtinSchreier`.
It supplies the missing canonical passage from the already recorded integral étale
character-projector sheaf to its completed pro-étale integral object, then its rational
common-stage Fourier kernel and integrand. Source: the current blueprint's sk-def-as,
sk-def-kernel and Fourier coefficient convention, as required by Step 1 of the item's
relative proof. The searches found the existing general-ring sheaf, the common-stage
category and the canonical constant-to-completion map, but no definition composing
these into this character/kernel realization. No existing node's valid general-ring
interface is replaced by an adic specialization. Its signature permits the trivial
character as well as the nontrivial character used by the consumer. The three theorem
helpers prove only the uniquely determined character lift, invertibility needed by
the projector, and membership of the explicit realization.

## Second reading by Q04

The section delivered here was, by its own words, the author's second self-reading. It is
replaced by the independent reading of the maintainer's stage-2 reviewer (cc review service,
2026-10-18), done on the immutable delivery 69a3a96f8215 with the node, the dependency
records and declarations and both modules open. No Lean file and no node record changed.

Node statement, item by item, with its Lean and the verdict:

1. Distinct primes p, l, a >= 1, q = p^a, k0 = F_q, k = closure of k0, Fourier conventions
   [def-fourier-set]: `F : FourierSetting.{u}` (recorded structure; `F.field` is the
   FiniteFieldDatum, `F.coefficients` gives l, l != p, Qbar; `F.extension` the finite E with
   mu_p in E). No extra hypothesis. Correct.
2. Nontrivial Psi : (F_p,+) -> Qbar^x: `Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar`,
   `hΨ : Ψ ≠ 1`. AddChar values are units. psi = Psi o Tr is notation only; the sheaf is
   the prime-field AS sheaf `Etale.artinSchreierSheafZMod` of the unique integral lift of Ψ
   (`fourierIntegralCharacter`), so the case p | a is covered. Correct.
3. D^b_c(-, Qbar) with adic common-stage coefficients: every object is in
   `generalAlgebraicallyClosedConstructibleCategory l Qbar` (the recorded declaration of
   def-weil-algebraically-closed-coefficients), formed at the stage E =
   `fourierCoefficientStage F` by `sfRationalConstructibleLocalization` of an object of the
   intrinsic integral category. Pro-etale completed coefficients, not discrete etale ones.
4. S = Spec k, r >= 0, V = A^r_k, V^dual: `fourierGeometricBase`, `𝔸(n; Spec k)` with
   `n : Type u` finite, r = `Fintype.card n` (empty n is r = 0). The dual is identified with
   the same coordinate scheme by the standard basis. Correct.
5. Fourier kernels of the evaluation pairings on V x V^dual and V^dual x V [def-fd-kernel]:
   `fourierAdicKernel` = completed realization of the recorded `Etale.fourierKernel` at
   `AffineSpace.stdPairing` (sum of pr1^* x_i * pr2^* x_i, symmetric). The convolution
   integrand uses `fourierAdicArtinSchreier` of the same square and pairing, which is
   definitionally the same integral representative (`Etale.fourierKernel` is
   `artinSchreierSheafZMod (pullback π π') Ψ b`, checked in slopmaster2 Defs.lean:154).
6. Unshifted convolution of [lem-fd-kernel-composition], K' * K = Rr13!(r12^*K (x) r23^*K'):
   triple `(V×V) ×_V (V×V)` with the recorded `pullback.tripleProj₁₃` (same convention as
   `kernelConvolution` upstream); r12 = `pullback.fst`, r23 = `pullback.snd`; integrand
   `integralCompletedTensor` of the two `integralDerivedPullback`s, r12 factor first; Rr13!
   is the recorded `sfQbarCompactSupportValue` at stage E, no shift. With (Ψ, Ψ⁻¹) this is
   K_{psi^-1} * K_psi; with (Ψ, Ψ) it is K_psi * K_psi. Correct order and characters.
7. Right sides Delta_* Qbar(-r)[-2r] and (id x iota')_* Delta_* Qbar(-r)[-2r]
   [def-coefficient-twists-detailed]: recorded `integralCoefficientTwist` on V with exponent
   `-(card n)`, `sfCompletedDerivedDirectImage` along `pullback.diagonal` (x |-> (x,x)), and
   for sign = true also along `fourierSecondReflection` = `pullback.map (𝟙) (neg) (𝟙)`,
   (x,y) |-> (x,-y). Shift `-2 * card n` by the category's recorded shift functor.
   Twist sign, shift sign and both supports are right.
8. Conclusion: two `Nonempty (_ ≅ _)` in a conjunction, as the node's two isomorphisms.
   The compactification `c` of r13 is universally quantified (the recorded Rf! takes one);
   the theorem is asserted for every choice. Not weaker, not stronger.
9. "Geometric pullbacks of finite-field models": all schemes, maps, the pairing and the
   AS construction are base changes of their k0 forms; upstream
   `artinSchreierSheafZModPullbackIso` is the canonical comparison. Acceptable rendering.

Edge cases: r = 0 (empty n: point, twist 0, shift 0, no positive-rank assumption);
characteristic 2 (neg = id, supports coincide, nothing assumes p odd); p | a (prime-field
character used, not a restriction of psi); E ramified (lift exists in O_E^x and is unique);
trivial character allowed in the new definition node, excluded only by `hΨ` in the item;
universes: one universe u for F, n and the schemes, coefficient modules in u+1 as in the
recorded categories, no equation imposed between site universes.

Helpers: all definitions have real data (no `sorry` in a def body). The eight theorems
(`fourierIntegralCharacter_existsUnique`, `fourierIntegerPrime_isUnit`,
`fourierAdicArtinSchreier_mem`, `fourierSquareNoetherian`, `fourierConvolutionGeometry`,
`fourierPairingCharacteristic`, the two `isUnit` results, `fourierConvolutionIntegrand_mem`,
`fourierIntegralDelta_mem`) are true, have source/blueprint docstrings and natural-language
proofs, and are `sorry`. The lift is selected from a uniqueness theorem, not a bare
existence. The new node def-fd-adic-fourier-realization is needed: no adic Fourier kernel,
adic AS sheaf or adic convolution exists in Mathlib, slopmaster2 (only discrete-coefficient
`fourierKernel`, `kernelConvolution`, and `nonempty_iso_fourierKernel_convolution` with finite
coefficients and only the inverse-character identity) or the side project's lean/Sheaf
(rg for fourierKernel, FourierSetting, artinSchreierSheafZMod: only FourierSetting.lean).

stmt_deps: the item gains the new node and three landed dependency nodes whose recorded
declarations the module uses (pullback/tensor, Qbar compact support, derived direct image);
the statement, proof and proof_deps are unchanged.

Compile: both modules through `nt_compile.py --json` in one call (siblings in order): rc 0,
FourierAdicArtinSchreier 6.8 s, FourierKernelConvolution 5.0 s, no error and no warning.
Lean statements equal the node records after whitespace normalization; no line over 100.
