# Q113: flat graded fibre regular lift

## Worker report

This stage-2 delivery states `Ideal.flat_graded_fibre_regular_lift` in
`Sheaf.RingTheory.FlatGradedFibreRegularLift`. Its only postponed proof is `sorry`.
The helper `Ideal.associatedGradedFibreMul` constructs the actual multiplication
map on the tensor product from the existing quotient class and homogeneous
inclusion. It contains real data and no postponed proof. It belongs to the
same fibre-initial-form notion, so it is listed in this node's declarations;
no new node or dependency repair is needed. Neither statement nor dependencies
nor the accepted stage-1 proof is changed.

The inherited BLOCKED ending was a stage-1 re-splitting refusal. The current
node has no Lean record, and `coord/queue.tsv` lists it at stage 2. The explicit
stage-handoff paragraph of `coord/brief-stage2.md` §0 permits precisely this
stage-2 statement delivery without reopening Q58's accepted split.

Hypotheses and clauses, read against the whole node:

- A commutative Noetherian local R is `{R : Type u} [CommRing R]
  [IsLocalRing R] [IsNoetherianRing R]`. The arbitrary explicit universe `u`
  excludes no ring. Mathlib's local-ring convention includes nontriviality,
  as does having a unique maximal ideal in the source.
- The ideal and containment are `(I : Ideal R)` and
  `(hI : I ≤ IsLocalRing.maximalIdeal R)`. A is literally `R ⧸ I`.
  The maximal ideal n=m/I of A is only explanatory notation in the proof,
  not an independently chosen ideal or additional hypothesis.
- G is the recorded `Ideal.associatedGraded I`; G_j is the recorded
  `Ideal.associatedGradedPiece I j`, literally the quotient of I^j by the
  comap of I^(j+1). The ring, multiplication, inclusion and coefficient
  algebra are all the published associated-graded construction.
- Flatness is `[Module.Flat (R ⧸ I) (associatedGraded I)]`. I read
  `Module.Flat` and `Module.Flat.rTensor_preserves_injective_linearMap`
  (Mathlib/RingTheory/Flat/Basic.lean, lines 107--147). This is equivalent
  to the node's preservation of arbitrary module injections; using the
  class does not restrict to finitely generated test modules.
- Every G_j is finite free: the FIRST conjunct is unconditional on the
  later fibre regularity premise. It says `∀ j, ∃ r, ∃ v : Fin r → G_j,
  ∀ x : G_j, ∃! c : Fin r → (R ⧸ I), sum_i c_i • iota_j(v_i)=iota_j(x)`.
  This is exactly a finite basis with unique coefficients, including rank
  zero. The inclusion is injective, and its image is stable under the
  canonical A-action by `Ideal.associatedGraded_smul`. Consequently this
  expansion condition is exactly finite freeness of G_j over A. No
  alternative scalar action or abstract isomorphic replacement is chosen.
  This follows the landed basis-expansion convention in
  `Sheaf.RingTheory.RegularSequenceGradedPolynomial`.
- The residue field k is literally `R ⧸ IsLocalRing.maximalIdeal R`.
  Its A-action is given by the real ring map `Ideal.Quotient.factor hI`.
  In the helper signature, `φ.toAlgebra.toModule` supplies this canonical
  action explicitly; a `letI` only INSIDE the definition equips the
  actual tensor product with its ring structure. The helper permits
  any coefficient map, but the theorem specializes to the required one.
  Thus the fibre is exactly G tensor_A k, with the same tensor order as
  the node. There is no arbitrary map, existence choice or extra algebra
  compatibility hypothesis.
- `∀ (n : ℕ) (a : (I ^ n : Ideal R))` covers every n≥0 and every a∈I^n.
  `Submodule.Quotient.mk a` is alpha=a mod I^(n+1), and the helper tensors
  its canonical degree-n inclusion with 1. It then multiplies by this
  element, exactly h=alpha tensor 1.
- `Function.Injective (associatedGradedFibreMul I
  (Ideal.Quotient.factor hI) n a)` is injectivity of multiplication by h
  on the entire fibre, rather than just one homogeneous component.
- The next conclusion is `∀ j : ℕ, Function.Injective
  (associatedGradedMul I n j (Submodule.Quotient.mk a))`:
  multiplication by alpha from G_j to G_(n+j). The codomain is the node's
  G_(j+n), since n+j=j+n; no degree or multiplication convention changes.
- The last clause `∀ b : R, a.val * b = 0 → b = 0` is the node's exact
  nonzerodivisor conclusion. No reducedness, characteristic, positivity
  of n, nonzero graded-piece or residue-field infinitude assumption is
  imposed.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` from
  `Mathlib.RingTheory.Noetherian.Defs`, whose docstring and signature
  identify every ideal being finitely generated.
- `def-weil-pbc-associated-graded-ring`: all constructions above from
  `WeilConjectures.RingTheory.AssociatedGradedRing`, especially
  `Ideal.associatedGradedPiece`, `Ideal.associatedGraded`,
  `Ideal.associatedGradedMul`, `Ideal.associatedGradedAlgebra`,
  `Ideal.associatedGraded_smul`. I read the full module.
- `def-weil-pbc-module-tensor-product`: its Mathlib match is usable,
  although it has no Lean record. I read `TensorProduct` and
  `TensorProduct.mk` in `Mathlib.LinearAlgebra.TensorProduct.Defs`,
  `TensorProduct.lift` and `ext'` in `.Basic`, and `LinearMap.rTensor`
  and `rTensor_tmul` in `.Map`. The fibre ring operations are the actual
  `Algebra.TensorProduct` operations in
  `Mathlib.RingTheory.TensorProduct.Basic`.
- Proof-only imports retain the stated proof plan:
  `Module.free_of_flat_of_isLocalRing` from
  `Mathlib.RingTheory.LocalRing.Module` (00NZ);
  `flat_mod_injective` from
  `WeilConjectures.RingTheory.FlatModInjective` (00ME);
  `Ideal.iInf_pow_smul_eq_bot_of_le_jacobson` from
  `Mathlib.RingTheory.Filtration` (00IQ(2)). Their actual source
  signatures and docstrings were read. The theorem's docstring carries
  all six DAG proof steps, including the explicit quotient-tensor
  identification and the induction that increases filtration degree
  even when n=0.

I read the local supporting source `literature/stacks-project/algebra.tex`
at lemma-finite-flat-local, lemma-mod-injective,
lemma-intersect-powers-ideal-module-zero and
lemma-intersection-powers-ideal-module. They support the synthesis as
specified in the node, not individually the whole theorem.

Edge cases checked before writing: I=0 has G_0=R and zero higher pieces;
positive-degree h then fails injectivity on the nonzero residue fibre.
For n=0, fibre regularity means a has nonzero residue and hence is a unit;
all assertions hold, with no strict positivity requirement. Rank-zero
pieces admit r=0 and the unique empty coefficient function. Nilpotent I
causes no problem since the induction eventually reaches zero.
For R=k[epsilon]/(epsilon^2), I=(epsilon), the initial epsilon has square
zero and correctly fails the regular-fibre premise. Rings of arbitrary
characteristic and arbitrary nonreduced local rings remain included.
No statement dispute or node fault was found.

Searches for an existing statement or helper:

- `msearch.py ... leanfinder`, query: “In a Noetherian local ring with
  flat associated graded algebra, graded pieces are finite free and a
  homogeneous element regular on the residue fibre lifts to a
  nonzerodivisor”. Eight hits concerned regular sequences under flat
  base change, homogeneous localizations and smooth loci; no match for
  the conjunction or the fibre multiplication helper.
- `msearch.py ... loogle`, query: `"associatedGraded", "Injective"`:
  zero hits.
- `msearch.py ... grep`, query:
  `associatedGraded.*(regular|Regular)|[Ii]nitial[Ff]orm.*[Rr]egular|[Rr]egular.*associatedGraded`:
  zero hits.
- `msearch.py ... leansearch`, query: “Flat associated graded ring over
  a local quotient, finite free homogeneous pieces, injective special
  fibre multiplication implies a nonzerodivisor in the filtered ring”:
  eight hits; Module.Flat, its injection criterion, 00NZ and regularity
  preserved by flat modules are ingredients, not the requested statement.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  regular initial forms and regularity of associated graded rings found
  no exact declaration. I also checked both new full names against
  Mathlib, both library trees and `dag/lean_names_upstream.json`:
  neither name exists.
- A broader homogeneous-piece/fibre search found the parent module
  `Sheaf.RingTheory.NormalConeDirectrixMinimalPrimes` and its
  `normalConeFibre`/`normalConeFibreClass`. I read it: it defines the
  tensor in the opposite order with an implicit scalar structure inside
  its abbreviation, and does not expose the multiplication endomorphism
  with the explicit quotient action used here. Importing that downstream
  theorem would also make the proof dependency circular. The present
  helper merely composes existing TensorProduct, quotient and
  multiplication operations for this node; it does not redeclare any
  fibre type, scalar structure or initial-form notion. The existing
  associated-graded approximation and regular-sequence polynomial
  results also state different assertions.

Validation: the final module compiled both as a sandbox and under its
library module name with scompile.py, cleanly (only the permitted sorry
proof). Every variable and universe is explicitly bound; autoImplicit
is disabled in the file. No repository or launcher script was edited,
no direct Git command was run, and no global build was run. The required
server dry run and delivery are performed next.

## Second reading by Q113

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
