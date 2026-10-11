## Worker report

The module `Sheaf.RingTheory.HenselianIntegralIdempotentLifting` states
`Algebra.existsUnique_isIdempotentElem_of_henselianRing`, with its sole proof `sorry`.
It introduces no definition. The docstring gives all three steps of the node's direct
finite-subalgebra proof, including the essential membership witnesses.

Hypothesis and clause correspondence:

- The commutative ring A is `(A : Type u) [CommRing A]`; its ideal is `(I : Ideal A)`.
- The henselian pair is `[HenselianRing A I]`, exactly the existing predicate selected
  by the dependency record. Its root-lifting definition is equivalent to the node's
  finite-algebra unique-idempotent criterion by Stacks 09XI. This is one hypothesis,
  not an additional root-lifting assumption alongside an idempotent assumption.
- The commutative ring C and the homomorphism A → C are `(C : Type v) [CommRing C]
  [Algebra A C]` and `algebraMap A C`. Every unital homomorphism between commutative
  rings induces such an algebra structure; injectivity is not assumed.
- Integrality of every element is `[Algebra.IsIntegral A C]`, whose field asserts
  `∀ x : C, IsIntegral A x`, i.e. a monic equation over A.
- The generated ideal IC is `I.map (algebraMap A C)`, and the quotient is
  `C ⧸ I.map (algebraMap A C)`.
- An arbitrary quotient idempotent is `(e₀ : C ⧸ I.map (algebraMap A C))`
  with `(he₀ : IsIdempotentElem e₀)`.
- Existence is the existence part of `∃! e : C, IsIdempotentElem e ∧
  Ideal.Quotient.mk (I.map (algebraMap A C)) e = e₀`.
- The first conjunct says the lift is idempotent, the second says its quotient image
  is exactly e₀. The uniqueness part asserts equality of any two such idempotent
  lifts. Because a ring homomorphism preserves idempotents, this is precisely
  bijectivity on the sets of idempotents, including the node's injectivity clause.

Dependency declarations read and used: `HenselianRing` from
`Mathlib.RingTheory.Henselian`, reexported through the recorded module
`Sheaf.RingTheory.HenselianTerminology`. Read the whole dependency module and the
Mathlib class signature/docstring; `IsStrictlyHenselianLocalRing` concerns the other
clause of that dependency and is not needed here. Read also the upstream module
`WeilConjectures.Mathlib.RingTheory.Henselian`, which explicitly fixes this same
predicate for the blueprint. Other existing notions are `Algebra.IsIntegral`,
`IsIdempotentElem`, `Ideal.map`, and `Ideal.Quotient.mk`.

Source checked: https://stacks.math.columbia.edu/tag/09XI, Lemma 15.11.6,
conditions (1), (3), (4). The repository's literature TeX was unavailable on this
machine; the official Stacks page supplies the stated equivalences. The proof in
this module is the node's agent-written finite-subalgebra argument rather than the
longer chain in Stacks. No statement correction or disputed statement is needed.

Edge cases checked mathematically: A and C may be zero rings; no `Nontrivial`,
local, Noetherian, domain, or finiteness hypothesis was imposed. For I = 0 the map
is the identity quotient on idempotents. If I = A, the henselian hypothesis forces
A to be the zero ring (I lies in the Jacobson radical); its unital algebras are then
zero rings, so uniqueness is consistent. C = 0 is allowed even when A is nonzero.
Noninjective structure maps and integral algebras that are not module-finite are
included. The two carrier universes are independent, and there is no quantification
over test algebras in an undersized universe.

Searches for an existing statement:

- `msearch.py leanfinder`: "Idempotents lift uniquely modulo an extended ideal in an
  integral algebra over a henselian pair". Eight hits include `HenselianRing`,
  `HenselianLocalRing`, formally unramified uniqueness, and nilpotent-kernel lifting;
  none is this statement.
- `msearch.py loogle`: `IsIdempotentElem, Algebra.IsIntegral`. One auxiliary hit,
  `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq_aux₂`, describes étale
  localization and is not this theorem.
- `msearch.py grep` in Mathlib/RingTheory: `HenselianRing|henselian.*idempotent|
  idempotent.*henselian`. Five hits, all in Henselian.lean; no lifting theorem.
- `rg` of the project source `WeilConjectures` for `henselian|Henselian` and the
  item id: matches concern proper schemes, étale cohomology, and root-lifting
  definitions, not this integral-algebra theorem. The exact item-id grep is empty.
- `rg` of `lean/Sheaf` for `henselian.*integral|integral.*henselian|
  existsUnique.*[Ii]dempotent`: no existing statement matching the item.
- Full proposed declaration-name search in Mathlib, WeilConjectures, lean/Sheaf,
  and dag/lean_names_upstream.json: no collision.

No new nodes or dependency modules are required. The original node is copied with
only `lean` changed. Server compilation and delivery preflight are the validation;
the independent second reading is left to the assigned second reader.

## Second reading by J1

I independently compared the node's objects and clauses with
`Algebra.existsUnique_isIdempotentElem_of_henselianRing`.

- The commutative base ring (A) is `(A : Type u) [CommRing A]`; the ideal is
  `(I : Ideal A)`.
- The henselian-pair hypothesis is `[HenselianRing A I]`, the Mathlib realization
  recorded by `def-weil-pbc-henselian-terminology` (equivalent to the node's finite
  algebra idempotent criterion in Stacks 09XI).
- The commutative (A)-algebra (C) is `(C : Type v) [CommRing C] [Algebra A C]`,
  with no injectivity assumption on `algebraMap A C`.
- Integrality is `[Algebra.IsIntegral A C]`, asserting that every element of `C`
  is integral over `A`.
- The extended ideal (IC) is rendered as
  `I.map (algebraMap A C)`, and the quotient is
  `C ⧸ I.map (algebraMap A C)`.
- The arbitrary quotient idempotent is `(e₀ : C ⧸ I.map (algebraMap A C))` with
  `(he₀ : IsIdempotentElem e₀)`.
- The conclusion is `∃! e : C, IsIdempotentElem e ∧
  Ideal.Quotient.mk (I.map (algebraMap A C)) e = e₀`: existence of an idempotent
  lift with the prescribed image and uniqueness of every such lift. This is exactly
  surjectivity and injectivity of the quotient map on idempotents, with the same
  quantifier order as the node.

No mismatch was found, and no Lean or node change was needed. The independent
universes `u` and `v` preserve the node's unrestricted base and algebra cases.
The zero rings, zero ideal, unit ideal, noninjective structure map, empty/degenerate
idempotent cases, and non-finite integral algebras are all permitted by the binders;
no Noetherian, local, domain, nontrivial, or finiteness hypothesis was added.

I checked the dependency declaration and its source module: `HenselianRing` is the
Mathlib class imported through `Sheaf.RingTheory.HenselianTerminology`; the separate
`IsStrictlyHenselianLocalRing` declaration is irrelevant. Existing declarations for
`Algebra.IsIntegral`, `IsIdempotentElem`, `Ideal.map`, and `Ideal.Quotient.mk` are used.
Searches (LeanFinder/LeanSearch, Loogle, and `rg`/grep over Mathlib, the upstream
`WeilConjectures` source, and `lean/Sheaf`) found no declaration of this theorem;
nearby hits only concern nilpotent-kernel lifting or different henselian statements.
The source comparison was Stacks Project More on Algebra, Lemma 15.11.6 (Tag 09XI),
condition (3) ⇒ (4), whose conclusion is the same integral-algebra idempotent
bijection. Compilation with `scompile.py` succeeds with only the intentional `sorry`.
