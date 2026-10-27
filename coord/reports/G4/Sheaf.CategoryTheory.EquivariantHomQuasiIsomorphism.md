## What changed

In `Sheaf.CategoryTheory.EquivariantHomQuasiIsomorphism`, proved
`equivariantHomTensorPair_naturality` and `equivariantHom_forget_properties`.
No declaration signature, definition data, or public import changed.

Naturality is the naturality of the two product projections followed by that of
the presheaf morphism formed from the sheafification unit and the inverse tensor
comparison. The structural theorem uses the existing Grothendieck theorem,
`fixedPairCreatedAbelianStructure` for created products, and the existing source
instances for exactness and K-injective preservation. Creation in universe u is
transported to `Discrete ℤ` through `Discrete (ULift ℤ)`. Mathlib's exact-functor
quasi-isomorphism reflection lemma closes the last clause.

Replaced the proof import `Sheaf.CategoryTheory.FixedPairDerivedForgetComparison`
by `Sheaf.CategoryTheory.FixedPairCreatedAbelianStructure`, and removed the unused
proof import `WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap`. Updated step 2,
proof dependencies and proof origin in the existing node to record the actual
structural proof. The remaining theorem is marked STATEMENT-DISPUTED; see below.

Validation: remote `lcompile.py` compiled the changed module. The exact finite-field
arithmetic in the counterexample was also checked exhaustively on its 16-element
module in Python; this is supporting arithmetic, not a Lean refutation theorem.

## Proved and sorry left

Closed 2 of the original 3 holes:

- `CategoryTheory.Endofunctor.IsoAlgebra.equivariantHomTensorPair_naturality`.
- `CategoryTheory.Endofunctor.IsoAlgebra.equivariantHom_forget_properties`.

One original hole remains, unchanged, attached to
`lem-sf-equivariant-hom-quasi-isomorphism`:

- `CategoryTheory.Endofunctor.IsoAlgebra.exists_equivariantHom_quasiIso`.

Added zero holes and split off zero theorems. This is a partial proof delivery,
not a proof of the disputed construction. The product-creation proof still
uses the existing declared theorem `fixedPairCreatedAbelianStructure`, which
currently has its own sorry; this delivery makes no claim to have closed that
separate item.

## No longer needed

The structural proof does not need
`Sheaf.CategoryTheory.FixedPairDerivedForgetComparison` or its node
`lem-sf-fixed-pair-derived-forget-comparison`: the exact orbit-sum adjunction and
its K-injective-preservation instance already have complete source-library proofs.
Step 2 now cites the existing source input node
`lem-weil-pbc-right-adjoint-preserves-kinjective`. Removed the obsolete top-level
`tool_uses` approval for `lem-sf-fixed-pair-derived-forget-comparison`; retained
all other approvals in their original order.

`WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap` is not used by the two
proved clauses, so its proof import is removed. The mathematical node
`lem-pur-rhom-well-defined` remains in the unresolved construction's proof plan;
this delivery does not claim that input is unnecessary to a repaired main proof.
No modules or declarations are withdrawn. No unit statement or realized step is
bypassed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the Lean theorem quantifies over a `RingedPresentationAt e`
whose `underlying` field is only a natural isomorphism of sheaves of sets.
It need not preserve local scalar multiplication. Its single `structural`
equation on the rank-one module does not imply that compatibility. This is a
defect of the Lean attachment, not of Stacks 0A95 or the intended ringed-pullback
mathematical statement. The stage-2 review's assertion that these fields fix the
required normalized comparison is false.

Here is an explicit counterexample to the first conjunct, before any complexes
or K-injectives are involved.

Take the one-object category of G = C₂ × C₂, with trivial topology (only maximal
sieves cover). Write h and k for the commuting involutions. Sheaves of sets on
this small site are G-sets. Let R be F₄ = F₂[w]/(w²+w+1), with h acting by
σ(r)=r² and k acting trivially. R-module sheaves are R-modules with commuting
involutions h and k, h being σ-semilinear and k R-linear.

Let e be the identity ringed-topos morphism. Take P.transport to be the identity
module equivalence with all its usual identity comparisons, and P.pushforward
the identity. For EVERY such module M define a natural set-sheaf isomorphism

    a_M = id_M + (k_M - id_M) h_M.

These components are additive, commute with h and k, and commute with every
morphism of R-module sheaves. In characteristic 2, b=(k-1)h satisfies b²=0,
so a²=id. Consequently a is a natural automorphism of `presentationForget R`.
On the rank-one module R we have k_R=id, so a_R=id. We may therefore take
P.underlying=a, and P.structural holds. None of the fields of
`RingedPresentationAt` requires a_M to be R-linear.

For a concrete M take R², with h(x,y)=(σx,σy), k(x,y)=(y,x). Then

    a_M(x,y) = (x + σ(x+y), y + σ(x+y)).
    a_M(1,0) = (0,1).
    a_M(w,0) = (1,w²), whereas w a_M(1,0) = (0,w).

Thus a_M is not R-linear. The involution and commutation identities were checked
on all 16 elements, and additivity on all 256 pairs.

Now specialize the theorem's pure-tensor equation to T=id and N=R. At the unique
site object it says

    a_(M tensor R)(χ_(M,R)^(-1)(x tensor r)) = a_M(x) tensor r,

because a_R=id. The two input pairs (w x,1) and (x,w) give exactly the same input
tensor. Hence their right-hand sides must coincide. Under the standard module
isomorphism M tensor_R R ≅ M, that forces a_M(w x)=w a_M(x), contradicted above
by x=(1,0). No χ satisfying the theorem exists. The other conjuncts and the
derived-category universe cannot repair this failure.

A repair must require compatibility of the displayed underlying comparison
with the ring and module operations (or use the canonical induced algebraic
comparison instead). Merely fixing its value on the rank-one module is
insufficient. I have not changed that shared definition, silently added a
hypothesis to this theorem, or weakened its conclusion. The two structural
lemmas proved in this delivery do not use the defective comparison and remain
valid for every existing P.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
