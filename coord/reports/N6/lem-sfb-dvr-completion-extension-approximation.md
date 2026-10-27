## Worker report

The module `Sheaf.RingTheory.DvrCompletionExtensionApproximation` states
`IsDiscreteValuationRing.exists_finite_extension_tensor_equiv`. Its only theorem
has proof `sorry`, with all seven accepted proof steps in its docstring. No
notion is redefined, no dependency interface needs repair, and the node's
statement and dependencies are unchanged.

Hypotheses and clauses, in the node's order:

- A is a DVR: `(A : Type u) [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A]`. This is the recorded Mathlib definition,
  including the nonfield condition.
- Its fraction field F: `(F : Type v) [Field F] [Algebra A F]
  [IsFractionRing A F]`. The actual fraction-field universal property is used,
  rather than an arbitrary extension of A.
- The chosen uniformizer: `(pi : A) (hpi : Irreducible pi)`. In a DVR,
  `IsDiscreteValuationRing.irreducible_iff_uniformizer` says precisely that
  this is equivalent to `maximalIdeal A = Ideal.span {pi}`.
- The completion is literally `AdicCompletion (IsLocalRing.maximalIdeal A) A`
  everywhere. Since the maximal ideal is `(pi)`, this is the specified inverse
  limit of A/(pi^n). Mathlib indexes also at n = 0, whose quotient is zero;
  this does not change the inverse limit over n ≥ 1.
- The completed fraction field is `(K : Type w) [Field K]` with
  `[Algebra (AdicCompletion (IsLocalRing.maximalIdeal A) A) K]` and
  `[IsFractionRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) K]`.
  Thus K denotes the node's F-hat, not a different extension field.
- The canonical inclusion F → K is `[Algebra F K]` together with `hcompat`:
  for every a in A, the images through F and through the actual completion
  agree. Localization uniqueness determines this map on every fraction.
  Every canonical inclusion satisfies this equation; no continuity, valuation,
  henselianity or extra algebraic hypothesis is imposed. A field algebra map
  is automatically injective.
- The given finite extension H/K is `(H : Type z) [Field H] [Algebra K H]
  [FiniteDimensional K H]`. Finiteness means vector-space dimension here.
- The first alternative of `hH` is `Algebra.IsSeparable K H`.
- The second alternative quantifies `p r : ℕ`, `M : IntermediateField K H`
  and `alpha : H`. `0 < p ∧ CharP F p` says F has positive characteristic p;
  p is automatically prime since F is a field. `Algebra.IsSeparable K M`
  is separability of M/K. M/K is finite automatically because it is an
  intermediate field of the finite-dimensional H/K.
- The prescribed root equation is `alpha ^ (p ^ r) = ... pi`, where the right
  side explicitly maps pi through A → completion → K → H. There is only one
  root element, living in the common field H. No new or unrelated uniformizer
  or root is chosen.
- The compositum is exactly `M ⊔ IntermediateField.adjoin K {alpha} = ⊤`.
  The supremum in intermediate fields is the generated subfield. Working
  inside H is equivalent to working inside the common ambient field of the
  node: both factors of their compositum H embed into H itself.
- The conclusion existentially chooses `(N : Type v) (_ : Field N)
  (_ : Algebra F N)` and requires `FiniteDimensional F N`.
  A finite extension always has a model in the universe of F (e.g. a quotient
  of F[T]), so `Type v` imposes no field-size restriction. The input rings and
  fields use four independent universes u, v, w, z.
- `Nonempty ((K ⊗[F] N) ≃ₐ[K] H)` is the required isomorphism of
  K-algebras, not only a ring or vector-space equivalence.
- `(Algebra.IsSeparable K H → Algebra.IsSeparable F N)` puts the optional
  separability on the same chosen N. When H/K is separable the witness N
  is separable, including when both alternatives of `hH` hold.
- There are no hypotheses on henselianity, excellence, or residue fields.

Recorded statement-dependency declarations read and used:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`:
  `IsDiscreteValuationRing`, `IsDiscreteValuationRing.irreducible_iff_uniformizer`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `algebraMap`, via the public
  imports which use them. Field extensions use the recorded algebra structure.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, with its
  canonical commutative-ring and algebra structures from
  `Mathlib.RingTheory.AdicCompletion.Algebra`.
- `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable` (its definition already
  implies algebraicity).
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`, with the ring and
  left K-algebra structures from `Mathlib.RingTheory.TensorProduct.Basic`.

The supporting Mathlib interfaces used directly to express the statement are
`IsFractionRing` (`Mathlib.RingTheory.Localization.FractionRing`),
`FiniteDimensional` (`Mathlib.LinearAlgebra.FiniteDimensional.Defs`), and
`IntermediateField.adjoin` and its lattice
(`Mathlib.FieldTheory.IntermediateField.Adjoin.Defs`). They are existing notions,
so no helper definition or new node is needed.

All already stated proof dependencies are imported (non-public when needed only
for the future proof). In particular the recorded upstream modules
`WeilConjectures.RingTheory.CompletionOfDVR`,
`WeilConjectures.RingTheory.FiniteOverCompleteLocalProduct`,
`WeilConjectures.RingTheory.IntegralExtensionDimension`, and
`WeilConjectures.AlgebraicGeometry.Morphisms.DvrUniformizerRootAlgebra`
are used, together with Mathlib completion/locality, primitive element,
monic quotient basis, finite algebra integrality, Nakayama, tensor universal
property, separable derivative and simple-extension results, and linear
disjointness of separable and purely inseparable extensions. The proof-only
node `lem-sfb-complete-local-domain-root-perturbation` has no Lean record yet
in the read repository; no import can be added for it now. Its accepted
statement is explicitly cited in the proof docstring. It is not a missing
notion required to type this statement.

Edge cases checked mathematically: r = 0 gives exponent p^0 = 1, so alpha is
exactly the image of pi, its adjoin is the bottom intermediate field, and the
compositum condition reduces to M = H. H = K permits N = F, which is finite
and separable over itself. If A is already complete, transport H across the
canonical identification F ≃ K. Mixed characteristic is covered by the
separable alternative; the positive-characteristic alternative correctly
refers to F rather than only its residue field. Imperfect residue fields and
nonhenselian DVRs are permitted. pi = 0 and pi a unit are excluded exactly by
the uniformizer condition. The zero ring and fields are excluded exactly by
the DVR and field classes, not by additional assumptions.

Source verification: read `literature/stacks-project/more-algebra.tex`,
lemma-approximate-separable-extension (09EJ), statement and complete proof,
and theorem-epp (09F9), completion paragraph. These give precisely the two
alternatives of the node and its same-root construction. No statement fault
or STATEMENT-DISPUTED flag was found.

Searches for an existing theorem (2026-10-24):

- `msearch.py`, LeanFinder: “A finite separable extension of the fraction field
  of a completed DVR descends as tensor base change from a finite extension of
  the original fraction field”. Eight results, including
  `Algebra.IsAlgebraic.isBaseChange_of_isFractionRing`, adic completion algebra
  instances, and integral-closure fraction-field results. These concern
  localization/base change or constructing completions, not this descent.
- `msearch.py`, Loogle: `IsDiscreteValuationRing, Algebra.IsSeparable`.
  Zero results.
- `msearch.py`, Mathlib grep in RingTheory:
  `approximate.*separable|separable.*completion|completion.*separable|Krasner`.
  Zero results.
- `msearch.py`, LeanSearch: “Every finite separable extension of the fraction
  field of the adic completion of a discrete valuation ring is a tensor
  product with a finite separable extension of its fraction field”. Eight
  results: finite-module completion as a tensor product, p-adic completion
  equivalences, Laurent-series completion and adele constructions. None
  descends a given finite extension of a completed fraction field.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` with the same conceptual
  pattern and the item id. Hits concern complete local fibres and nodal
  completion, not this theorem. Exact search for the chosen declaration name
  in both source trees and `dag/lean_names_upstream.json` found no collision.
- Read the nearby `Sheaf.RingTheory.FieldExtensionCompletionPresentation`:
  it concerns completed local rings after extension of residue fields and is
  not a match. The node's own earlier three-kind searches also found no match.

Validation: `scompile.py N6 lem-sfb-dvr-completion-extension-approximation`
compiled this file on the server as both sandbox and library module, cleanly
(9.1 s and 2.7 s). There are no `#check` commands, auto-bound implicits,
private definitions, local notation, or local instances in the delivered file.

## Second reading by N6

No second worker was started, as required by the dispatcher brief. The
maintainer's independent review reads this delivery. A final self-check
compared the actual node and Lean file: all clauses are mapped above; the
canonical map is constrained on A, the completion is the literal maximal-ideal
completion, the root equation uses that map and the same pi, and the final
isomorphism is over K. No mismatch or statement correction was required.
