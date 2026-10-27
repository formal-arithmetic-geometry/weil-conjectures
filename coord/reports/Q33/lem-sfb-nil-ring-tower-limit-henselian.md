## Worker report

The module `Sheaf.RingTheory.NilRingTowerLimitHenselian` states
`CommRingCat.limit_henselian_of_surjective_nil_ker`, with one `sorry` and no new definitions.
The source is Stacks Project Tag 0CT7, `more-algebra.tex`, lemma-limit-henselian,
read together with its proof. The accepted node expands this source with projection
surjectivity and the canonical quotient identification; both are retained.
Only the item's `lean` field changes. No node correction or disputed statement.

The correspondence with every hypothesis and conclusion is as follows:

- The inverse sequence of commutative unital rings is
  `F : ℕᵒᵖ ⥤ CommRingCat.{u}`. Index `n : ℕ` represents positive index `n+1`
  in the node; the arrow `(homOfLE (Nat.le_succ n)).op` goes from `n+1` to `n`.
  A sequence of ring maps determines exactly such a functor by composites
  (Mathlib `Functor.ofOpSequence`), so this formulation adds no coherence assumption.
- Unitality is built into the category's ring homomorphisms, accessed as `.hom`.
- `hsurj` requires every successive map to be surjective.
- `hnil` quantifies separately over every stage and every element of its transition
  kernel and requires `IsNilpotent x`. There is no common exponent, nilpotent-ideal
  assumption, or locality, nontriviality, Noetherianity, or adic hypothesis.
- `limit F : CommRingCat.{u}` is the standard ring limit, and `limit.π F ⟨n⟩`
  its projection. Mathlib's `CommRingCat.limitCommRing`, `RingCat.sectionsSubring`,
  and the created-limit construction in `Mathlib.Algebra.Category.Ring.Limits`
  construct the compatible-tuples ring with componentwise operations (using `Shrink`
  for the carrier). This is the node's ring, not an arbitrary ring with unrelated maps.
- `∀ n : ℕ` includes every positive stage of the original indexing.
- `Function.Surjective (limit.π F ⟨n⟩).hom` is precisely projection surjectivity.
- `Function.Bijective (RingHom.kerLift (limit.π F ⟨n⟩).hom)` expresses that the
  canonical map from the quotient by the projection kernel to the target is an
  isomorphism. `RingHom.kerLift` has exactly this domain and codomain, and is the
  map induced by the projection, as witnessed by `RingHom.kerLift_mk`.
  Bijectivity of this ring hom is equivalent to the specified ring isomorphism,
  without choosing any unrelated equivalence.
- `RingHom.ker (limit.π F ⟨n⟩).hom ≤ Ideal.jacobson (⊥ : Ideal ...)` is the
  inclusion of `I_n` into the intersection of all maximal ideals of the limit ring.
- `HenselianRing (limit F : CommRingCat.{u}) (RingHom.ker ...)` is the recorded
  henselian-pair notion of `def-weil-pbc-henselian-terminology`.
- The last clause quantifies over every `f : Polynomial (limit F : CommRingCat.{u})`
  with `f.Monic`, and `gₙ hₙ : Polynomial (F.obj ⟨n⟩)` with both monic.
  `IsCoprime gₙ hₙ` says that the factors generate the unit ideal via a Bezout identity.
  `f.map (limit.π F ⟨n⟩).hom = gₙ * hₙ` is the prescribed reduced factorization.
  The existential `g h` requires both monic, `f = g * h`, and both exact prescribed
  reductions. It imposes no additional uniqueness or coprimality conclusion.

Dependency declarations read and used:

- `def-weil-pbc-henselian-terminology`: public import
  `WeilConjectures.Mathlib.RingTheory.Henselian`; the record explicitly identifies
  the pair notion as Mathlib `HenselianRing`, defined in `Mathlib.RingTheory.Henselian`.
  Its full signature and docstring were read, as were the recorded local and strictly
  local variants. No replacement definition is needed. The idempotent description
  agrees via the project's factorization/idempotent criterion.
- `lem-weil-pbc-henselian-factorization-locally-nilpotent`: plain proof import
  `Sheaf.RingTheory.FactorizationLocallyNilpotent`, declaration
  `Polynomial.existsUnique_monic_factorization_of_locally_nilpotent`.
- `lem-weil-pbc-henselian-factorization-criterion`: plain proof import
  `WeilConjectures.RingTheory.HenselianFactorizationCriterion`, declaration
  `henselianRing_iff_factorization_criterion`.
- Mathlib proof matches: `Ideal.mem_jacobson_bot` in
  `Mathlib.RingTheory.Jacobson.Ideal`, and `Ideal.map_le_iff_le_comap` in
  `Mathlib.RingTheory.Ideal.Maps`. Both modules are imported for the planned proof.
  These signatures, and the full signatures/docstrings of the two project proof
  dependencies, were read. The module docstring gives all seven node proof steps,
  including the coprimality repair and bounded-degree coefficient construction.

Edge cases checked before writing: the zero ring is allowed at every stage. If any
stage is zero, nilness of the next kernel makes its unit nilpotent and hence that
stage zero; induction and surjectivity propagate zero in both directions. The whole
limit is then zero and every clause holds. Index `0` is the original first stage,
not an extra stage. Constant towers give zero projection kernels and the identity
quotient identification. Degree-zero monic factors are allowed and require no
nontriviality binder. Nil kernels without any uniform exponent are allowed: the
proof uses powers for individual elements and finitely many polynomial coefficients.
The fixed index is countable and small in every ring universe `u`, including `u=0`;
there are no universe equalities imposed on rings beyond a common universe for a
set-indexed sequence. The standard categorical limit includes all compatible tuples.

Searches performed with the prescribed `msearch.py` (Q33, this item):

- LeanFinder: "An inverse limit of surjective commutative ring towers with nil kernels
  is henselian along each projection kernel". Eight hits: adic-complete henselianity,
  HenselianRing/local variants, and AdicCompletion projection declarations. No match:
  adic completeness is not a hypothesis of this node.
- Loogle: `HenselianRing`. Six hits: the class and its constructor/fields, local-ring
  instance, and `IsAdicComplete.henselianRing`. None states the arbitrary tower result.
- LeanSearch: "Inverse limits of surjective commutative ring sequences with nil kernels
  are henselian pairs". Eight hits: henselian classes, direct ring limits, an adic
  instance, a formally smooth nilpotent lift, and `AdicCompletion.subring`. No match.
- Mathlib grep: `(inverse|limit|surject|nilpotent).*henselian|henselian.*(inverse|limit|surject|nilpotent)`.
  No exact tower theorem found. Additional direct source reads located the categorical
  ring-limit construction and canonical kernel-quotient map used in the statement.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for inverse-limit henselianity,
  nil towers, and the node id found no declaration stating this node. The similar
  filtered-colimit and nil-maximal-ideal results have different hypotheses and objects.
  Name search of both trees and `dag/lean_names_upstream.json` found no collision for
  `CommRingCat.limit_henselian_of_surjective_nil_ker`.

Validation: `scompile.py` compiled the final module both in sandbox and library module
mode in 2.6 and 3.1 seconds respectively, with no errors or unexpected warnings.
The initial elaboration ambiguity of `limit F` in a type position was fixed by an
explicit `CommRingCat.{u}` annotation; this changes no mathematical data.

## Second reading by Q33

I reopened the node and the final signature for a separate clause-by-clause self-check;
this is not an independent agent review (the dispatch brief forbids spawning agents).
The maintainer supplies the independent review. The check matched the sequence's
index shift, the two transition hypotheses, every-stage projection surjectivity,
the *canonical* quotient map's bijectivity, the radical inclusion, the recorded
henselian class, and all five factorization conclusions. No clause was missing or
added. In particular the quotient assertion is about `RingHom.kerLift`, not a bare
existence of an arbitrary ring equivalence, and zero rings are not excluded.
No changes were needed after the successful compile.
