## Worker report

Module: `Sheaf.RingTheory.SmoothLocalizationConormalSplit`.
Declaration: `Algebra.smooth_localization_conormal_split`.
Only the theorem is new; its proof is `sorry`. No definition is introduced or duplicated.
The original node is unchanged except for `lean`.

Hypothesis and clause correspondence:

- The arbitrary commutative ring is the explicitly bound section variable
  `(R : Type u) [CommRing R]`; `universe u` is explicit and `autoImplicit` is false.
- The nonnegative number of variables is `(n : ℕ)`. The polynomial ring is
  `MvPolynomial (Fin n) R`, so the indices 0 through n-1 label the n variables.
- The ideal is `(I : Ideal (MvPolynomial (Fin n) R))`. Local notation `A` is
  exactly `MvPolynomial (Fin n) R ⧸ I`, rather than an unrelated algebra.
- `(a : MvPolynomial (Fin n) R ⧸ I)` is arbitrary. Local notation `B` is
  `Localization.Away a`; `[Smooth R B]` is the sole substantive hypothesis.
  The R-algebra structure is the canonical tower through the polynomial quotient.
- `I.Cotangent` is Mathlib's quotient I/I², with its quotient-ring module instance.
  Local notation `M` is exactly `LocalizedModule.Away a I.Cotangent`, with
  `LocalizedModule.moduleOfIsLocalization` locally activated for its B-module structure.
- The free module on the n symbols dx_i is `Fin n → B`, whose coordinate vectors
  are `Pi.single i 1`. A finite product is canonically the finite direct sum.
- The statement supplies `d : M →ₗ[B] (Fin n → B)` and specifies it on the images
  `LocalizedModule.mkLinearMap (Submonoid.powers a) I.Cotangent (I.toCotangent g)`:
  its i-th coordinate is `algebraMap A B (Ideal.Quotient.mk I
  (MvPolynomial.pderiv i (g : _)))`. These are precisely the coefficientwise
  images of the formal partial derivatives, divided by one. The images of
  `I.toCotangent` span the conormal module and their localized images generate M
  over B, so this equation uniquely determines d; B-linearity forces the value
  on every fraction. Thus this specifies the localization of the stated
  conormal map, without replacing it by an unconstrained map or adding a hypothesis.
- The map π is supplied as `(Fin n → B) →ₗ[B] KaehlerDifferential R B` with
  `π (Pi.single i 1) = KaehlerDifferential.D R B
  (algebraMap A B (Ideal.Quotient.mk I (MvPolynomial.X i)))`.
  This uniquely specifies the canonical map on the same coordinate basis.
- Clause (1) is `∃ l : (Fin n → B) →ₗ[B] M, l.comp d = LinearMap.id`, followed
  by the explicitly recorded consequence `Function.Injective d`.
- Clause (2) is `Function.Surjective π` and
  `LinearMap.ker π = LinearMap.range d`.
- The asserted split short exact sequence is the preceding injectivity,
  surjectivity and kernel equality, together with both the left inverse and
  `∃ s : KaehlerDifferential R B →ₗ[B] (Fin n → B), π.comp s = LinearMap.id`.
- The final module isomorphism is
  `Nonempty ((M × KaehlerDifferential R B) ≃ₗ[B] (Fin n → B))`;
  the binary product represents the binary direct sum of modules.

The existential generator specification asserts the existence of the very maps
introduced in the node's “Let” clauses, alongside their asserted properties.
It adds no assumptions about the presentation, ideal generators or localization.
All section parameters are explicitly declared; they are abstracted into the theorem.

Dependency declarations read and used:

- def-weil-pbc-mv-polynomial-ring: `Mathlib.Algebra.MvPolynomial.Basic`,
  `MvPolynomial`; read `MvPolynomial.algHom_ext` and the associated evaluation
  declaration `MvPolynomial.aeval` in `Mathlib.Algebra.MvPolynomial.Eval`.
  No evaluation is necessary for the canonical quotient used here.
- def-weil-pbc-polynomial-partial-derivative (Mathlib leaf):
  `Mathlib.Algebra.MvPolynomial.PDeriv`, `MvPolynomial.pderiv`; its docstring,
  monomial formula and values on X_i were read.
- def-weil-pbc-smooth-ring-map: `Mathlib.RingTheory.Smooth.Basic`,
  `Algebra.Smooth`, the recorded smoothness predicate.
- def-weil-pbc-module-localization-away:
  `Mathlib.Algebra.Module.LocalizedModule.Basic`, `LocalizedModule.Away`,
  `LocalizedModule.mkLinearMap`. Read `IsLocalizedModule.lift` and its signature;
  the generator specification avoids an auxiliary invertibility-proof parameter.
- def-weil-pbc-kahler-differentials: `Mathlib.RingTheory.Kaehler.Basic`,
  `KaehlerDifferential`, `KaehlerDifferential.D`; read the full universal-property
  signature `KaehlerDifferential.linearMapEquivDerivation`.
- Additional existing Mathlib constructions are `Ideal.Cotangent`,
  `Ideal.toCotangent`, `Localization.Away`, `Pi.single`, `LinearMap.ker`,
  `LinearMap.range`, `LinearMap.comp`, and `LinearEquiv`. There is no missing
  specialized data structure: the concrete maps are fully specified in the theorem.

Edge cases checked before writing:

- n = 0: `Fin 0 → B` is the zero module. A smooth localization of a quotient
  of R over R is formally étale and its localized conormal vanishes. The
  basis condition is empty, but the only map from the zero free module is
  uniquely determined, and the claims retain their intended content.
- I = 0: the conormal is zero; the finite free module identifies with the
  differentials of the localized polynomial algebra. The derivative equation
  is consistent with the zero conormal class.
- I = top, a = 0, or nilpotent a: B is the zero ring; the localized conormal
  and differential modules vanish. No Nontrivial, IsDomain, nonzero-element,
  prime-ideal or Noetherian assumption excludes these cases.
- a a unit (especially a = 1): this is the ordinary smooth quotient conormal
  sequence under the canonical localization identifications.
- Arbitrary characteristic, arbitrary R universe, and arbitrary ideal I are
  retained. Neither finite generation of I nor global smoothness of A is imposed.

Searches made:

1. `msearch.py ... leanfinder "smooth principal localization of polynomial quotient
   has split exact conormal sequence"`: eight hits, including Algebra.Smooth,
   IsStandardSmooth, and smoothness-locus results, but no exact localized sequence.
2. `msearch.py ... loogle "Algebra.FormallySmooth.iff_split_injection,
   KaehlerDifferential"`: found Algebra.FormallySmooth.iff_split_injection.
   Read its full signature and docstring: it assumes a surjective map from a
   formally smooth algebra and treats the cotangent of its kernel, not the
   localization of the original presentation's conormal module.
3. `msearch.py ... grep "iff_split_injection|exact_kerCotangentToTensor_mapBaseChange"
   RingTheory`: twelve hits on the general splitting criterion and exact sequence.
   Read `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange` in full.
   Neither declaration directly states this localized, coordinatewise sequence.
4. `grep -rn "lem-weil-pbc-smooth-localization-conormal-split"` in the source
   WeilConjectures tree: no hit.
5. `rg` of cotangent/conormal and smooth-conormal-split patterns in project and
   source RingTheory: related regular-sequence and Jacobian statements, but no
   declaration of this statement. `rg` of the chosen declaration name across
   Mathlib, source, project and `dag/lean_names_upstream.json`: no collision.

Sources: the local Stacks source path in the node is absent on this machine.
Read the actual source online at https://stacks.math.columbia.edu/tag/07EZ
(part (e), localized split conormal sequence) and
https://stacks.math.columbia.edu/tag/07C6 (proof).
The proof docstring preserves the node's three steps and names all their inputs.
No statement dispute or correction is needed.

Validation: server single-file compilation passed cleanly, with every theorem
proof left as `sorry`. Delivery dry run is run after producing this report.

## Second reading by K1

The node introduces a commutative ring `R`, an integer `n ≥ 0`, the polynomial ring
`P = R[x_1,…,x_n]`, an ideal `I`, its quotient `A = P/I`, and an element `a : A`.
The Lean section variables `(R : Type u) [CommRing R]`, `(n : ℕ)`,
`(I : Ideal (MvPolynomial (Fin n) R))`, and `(a : MvPolynomial (Fin n) R ⧸ I)`
render these objects exactly; `A` is the quotient and `B = Localization.Away a` is
`A_a`. The hypothesis `[Smooth R B]` is exactly smoothness of the localized
`R`-algebra, with no extra finiteness, domain, characteristic, or nonzero assumptions.

The node's conormal module `(I/I²)_a` is rendered by
`M = LocalizedModule.Away a I.Cotangent`; `I.Cotangent` is Mathlib's quotient
`I/I²`, and the local is-localization module instance supplies its `B`-module
structure. The free module on the symbols `dx_i` is `Fin n → B`. The existential
`d` has precisely the node's prescribed values on localized classes
`LocalizedModule.mkLinearMap … (I.toCotangent g)`, with coefficient
`algebraMap A B (Ideal.Quotient.mk I (MvPolynomial.pderiv i (g : _)))`, matching
formal partial derivatives and reduction modulo `I`. The existential `π` has the
prescribed basis values `KaehlerDifferential.D R B` of the localized polynomial
variables.

The conclusion clauses match in order: existence of a left inverse `l` for `d`,
`Function.Injective d`, surjectivity of `π`, `LinearMap.ker π = LinearMap.range d`,
a section `s` of `π`, and the final linear equivalence represented by
`Nonempty ((M × KaehlerDifferential R B) ≃ₗ[B] (Fin n → B))`. The product is the
binary direct sum of modules, so the final clause is the node's direct-sum
isomorphism. No clause is added, dropped, weakened, or strengthened.

Edge cases remain covered: `n = 0` gives the zero free module; `I = 0` gives zero
conormal; `I = ⊤`, `a = 0`, and nilpotent or unit `a` are permitted (including the
zero localization); arbitrary characteristic and ring universe are retained.

I searched Mathlib and the project/source trees using LeanFinder/Loogle and grep
for smooth localized conormal sequences, `iff_split_injection`, and the chosen
declaration name. Only general smoothness and Kähler exactness results were found;
no declaration states this localized, coordinatewise sequence, so the new module is
needed. The dependency declarations and their signatures were opened and agree
with the uses above. No mismatch was found and no source or Lean change was needed.
