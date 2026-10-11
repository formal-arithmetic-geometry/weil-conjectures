## Worker report

(Rewritten by reviewer R-hen0910, 2026-10-11, FIX of H1's delivery 0019751f4; H1's own
worker report described the dropped module.)

H1's delivery defined its own idempotent-lifting predicate `Ideal.IsHenselianPair` (plus a
universe parameter `v`), `IsLocalRing.IsIdempotentHenselian`,
`IsLocalRing.IsStrictlyIdempotentHenselian` and two definitions for `Spec (A ⧸ I)`. That is
the H4 fault for which the earlier delivery of this item was returned (R-hen0715, 06:17,
coord/returns/C1.md). The return said to drop the redefinitions and use Mathlib's classes. The
re-delivery did not follow it: its searches found `HenselianRing`, `HenselianLocalRing` and the
source docstring that identifies them with this node, and it still wrote a second definition.
The reviewer replaced the module with the version the return asked for.

Module `Sheaf.RingTheory.HenselianTerminology`, one definition, no theorem, no `sorry`.

Clause-by-clause:

- *Henselian pair* `(A, I)`: Mathlib's `HenselianRing A I` (Mathlib/RingTheory/Henselian.lean):
  `I ≤ jacobson ⊥` and every monic `f` with a root `a₀` mod `I` at which `f'` is a unit mod
  `I` has a root `a ≡ a₀ mod I`. This is Stacks' henselian pair (09XE). The node's wording, a
  bijection on idempotents for every finite `A`-algebra `B` and `B/IB`, is the equivalent
  condition 09XI (3). The source repository fixes this identification for this node in the
  module docstring of `WeilConjectures/Mathlib/RingTheory/Henselian.lean`, and every source
  statement on henselian pairs uses `HenselianRing`. The equivalence with the idempotent
  wording is proved in the DAG by lem-weil-pbc-henselian-factorization-criterion and
  lem-weil-pbc-henselian-local-root-lifting, so it is not a reason to add a second definition.
  Existing declaration, recorded.
- *Henselian local ring* (its maximal-ideal pair is henselian): Mathlib's
  `HenselianLocalRing A`, which extends `IsLocalRing A` and lifts simple roots modulo the
  maximal ideal. This is Stacks 04GF (1). Mathlib's instance gives
  `HenselianRing A (maximalIdeal A)` from it. The converse is immediate: the Jacobson
  condition holds in a local ring, and the root-lifting fields are the same. Existing
  declaration, recorded.
- *Strictly henselian*: the new
  `IsStrictlyHenselianLocalRing (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  HenselianLocalRing A ∧ IsSepClosed (IsLocalRing.ResidueField A)` (Stacks 04GF (2):
  henselian, with separably algebraically closed residue field). There is no extra universe.
  Neither Mathlib nor the source repository has this notion: a grep for
  StrictlyHenselian/strictHensel found only a section name.
- `T₀ = Spec (A/I)` for `T = Spec A`: this is notation and gets no declaration. A citer
  writes `Spec (.of (A ⧸ I))` with the closed immersion
  `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))` (`AlgebraicGeometry.Spec`, the
  recorded declaration of def-weil-affine-spectrum). The module docstring and the record's
  note say this.

Edge cases: the zero ideal is henselian (`HenselianRing.bot`), and a field is henselian
local (`Field.henselian`). Local rings are nonzero by Mathlib's convention. All
characteristics are allowed.

Sources read: literature/stacks-project algebra.tex `definition-henselian` (04GF),
more-algebra.tex `definition-henselian-pair` (09XE) and
`lemma-characterize-henselian-pair` (09XI (3)).

Validation: the module compiled under `SHEAF_GROUP=L tools/lean_file.sh` (1.4 s, exit 0).
Lines are at most 100 characters, and both imports are used.

## Second reading by H1

(Kept verbatim by reviewer R-hen0910. It reads H1's dropped version, which had five
definitions and its own idempotent predicate. What it missed: the H4 return R-hen0715 of
06:17. Its own reading of the source docstring, "the source prose identifies these
notions", was the identification that the return asks it to follow.)

I independently opened the node copy, the complete Lean module, both statement-dependency
nodes, and the declarations below. The node's list of objects, hypotheses and clauses is:

1. A commutative ring A and an ideal I: `{A : Type u} [CommRing A] (I : Ideal A)`.
   Verdict: exact; neither nontriviality nor a local, Noetherian or finiteness condition
   is imposed on A.
2. Every finite commutative A-algebra B: `∀ (B : Type (max u v)) [CommRing B]
   [Algebra A B] [Module.Finite A B]`. Verdict: exact after the universe repair below.
   `Module.Finite` means finite generation as an A-module, as finite algebras do in
   Stacks; it does not mean finitely many elements or merely finite type.
3. Its extended ideal IB and quotient B/IB: `I.map (algebraMap A B)` and
   `B ⧸ I.map (algebraMap A B)`. Verdict: exact. I read `Ideal.map`, whose body is the
   ideal span of the image, and `Ideal.Quotient.mk`, the quotient ring map.
4. Every idempotent of that quotient: `∀ e : B ⧸ I.map (algebraMap A B),
   IsIdempotentElem e →`. Verdict: exact; `IsIdempotentElem e` is `e * e = e`.
5. A unique idempotent lift: `∃! e' : B, IsIdempotentElem e' ∧
   Quotient.mk (I.map (algebraMap A B)) e' = e`. Verdict: exact, including uniqueness
   among all idempotent lifts and with the quantifiers in the node's order.
6. A local ring is henselian precisely for its maximal-ideal pair:
   `IsLocalRing.IsIdempotentHenselian (A : Type u) [CommRing A] [IsLocalRing A]`
   unfolds to `Ideal.IsHenselianPair.{u, v} (maximalIdeal A)`. Verdict: exact. I read
   `IsLocalRing` and `maximalIdeal`; the latter is the unique maximal ideal, not
   an arbitrarily chosen ideal. Local rings are nonzero in both conventions.
7. Strict henselianity additionally requires separably closed residue field:
   `IsStrictlyIdempotentHenselian` unfolds to
   `IsIdempotentHenselian.{u, v} A ∧ IsSepClosed (ResidueField A)`. Verdict: exact.
   `ResidueField A` is A modulo its maximal ideal; `IsSepClosed` says every separable
   polynomial splits. Both existing definitions are used directly.
8. For T = Spec A, the closed subscheme T0 = Spec(A/I): `henselianClosedFiber I`
   is `Spec (CommRingCat.of (A ⧸ I))`; `henselianClosedFiberι I` is
   `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))` into `Spec (CommRingCat.of A)`.
   Verdict: exact. The canonical surjective quotient map specifies the closed
   subscheme inclusion; it needs no henselian assumption.

Sources and dependencies: the local literature checkout contains neither the blueprint
nor the Stacks .tex files. I read the source .tex online from the Stacks repository:
`more-algebra.tex`, `lemma-characterize-henselian-pair` (09XI), condition (3), and
`definition-henselian-pair` (09XE); `algebra.tex`, `definition-henselian` (04GF).
I also opened the rendered tag pages. Condition (3) has exactly the finite-algebra
idempotent bijection and imposes no extra ambient hypothesis. The local source defines
strict henselianity by henselianity plus separable algebraic closure of the residue field.
The node explicitly chooses the idempotent formulation; its comparison with root
lifting is a separate DAG item. No source assumption has been silently added or dropped.
`def-weil-pbc-scheme-conventions` fixes no independent notion (`lean.convention = true`).
`def-weil-affine-spectrum` records Mathlib's `AlgebraicGeometry.Spec` and `Spec.map`.
I read their signatures and bodies in `Mathlib.AlgebraicGeometry.Scheme`; both are used.
There are no new definition nodes, dependency modules or statement corrections to review.
The node has no proof steps, and the module has no theorem, proof or sorry.

Mismatch and repair: the first version quantified B in the independent universe v.
When v is smaller than u this can omit A itself and finite algebras with genuinely large
carriers; the report's instruction to choose v at least u did not enforce that in Lean.
I changed only that binder to `Type (max u v)` and documented why in its docstring.
This universe always contains presentations of all finite algebras over A: finite
module generation exhibits each as a quotient of a finite power of A, so its carrier
can be represented in universe u and lifted to max u v. Higher universe presentations
transport the same ring, algebra, quotient and idempotent data. The local predicates
inherit the repair. The node's `lean.statement` remains verbatim the unchanged signature
`def IsHenselianPair {A : Type u} [CommRing A] (I : Ideal A) : Prop`.
No other semantic mismatch was found, and I left the other declarations unchanged.

Edge cases: I = 0 gives unique lifts through the identity quotient; I = A fails for
nonzero A because the finite self-algebra has distinct lifts 0 and 1, and succeeds for
the zero ring. Zero finite algebras are included. The pair and spectrum definitions
include the zero ring and empty spectrum; the local clauses correctly exclude zero
rings. T0 is empty for I = A and the whole spectrum for I = 0. Module generators may
have size zero. No index set or integer n is otherwise present. All characteristics
are allowed, all universes are explicitly bound, and no hidden field or finiteness
hypothesis occurs on the base ring.

Independent searches (2026-10-11):

- LeanFinder query `finite module algebra idempotent quotient unique lift henselian`:
  eight hits, including `HenselianRing`, `HenselianLocalRing`, nilpotent-kernel lifting
  and formally smooth lifting; none states this finite-algebra predicate.
- Loogle query `IsIdempotentElem, Ideal.Quotient.mk`: six hits about idempotent-induced
  product decompositions and quotients, none the henselian pair predicate.
- LeanSearch query `henselian ideal finite algebra unique lifting idempotents`:
  Internal Server Error; unavailable, with no mathematical verdict inferred.
- Independent `rg` across all Mathlib, WeilConjectures and lean/Sheaf for henselian
  idempotent combinations, strict-henselian names and `IsHenselianPair`: no matching
  declaration. Broader readings of RingTheory/Henselian and RingTheory/Idempotents
  found only root-lifting definitions and lifting with a nilpotent-kernel hypothesis.
  Exact-name search found no collision with any of the five delivered declarations.

I read Mathlib's actual `HenselianRing` and `HenselianLocalRing` fields and the source
module `WeilConjectures.Mathlib.RingTheory.Henselian`. The source prose identifies
these notions, but does not declare the node's finite-algebra idempotent predicate.
The Jacobson-radical and simple-root fields are not this node's signature, and their
identification requires the already-recorded comparison node. Thus this delivery
keeps the explicit idempotent formulation rather than asserting an unproved equivalence.
All elementary notions used in it come from the existing Mathlib declarations above.

Validation: the repaired module compiled on the server with scompile.py, exit 0,
without errors or warnings. I checked every binder and universe by eye, every
complete definition body, source/blueprint docstring, and the 100-character line limit.

The broader grep also found
`AlgebraicGeometry.Scheme.bijective_appTop_idempotent_of_henselianRing` in the source
module `WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale`. I opened its signature:
it assumes `HenselianRing A I`, a proper scheme and its pullback closed fibre, and
concludes a bijection on global-section idempotents. It is a different theorem,
not an existing definition of this node's finite-algebra predicate.
