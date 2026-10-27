## Worker report

This delivery attaches the existing theorem
`AddCommGroup.divisible_unit_lattice_extension` in
`Sheaf.GroupTheory.DivisibleUnitLatticeExtension` to the live sfb node. No Lean
module is added or changed. I read the complete declaration and proof docstring
in the shared source and independently retrieved its current server source with
`scompile.py --source Sheaf.GroupTheory.DivisibleUnitLatticeExtension`; they agree.
The theorem has precisely the statement of ILO, Travaux de Gabber, Exposé XVI,
Lemme 3.6.4, printed pp.252–253 (PDF pp.258–259), which I read using pdftotext.

Hypotheses, clause by clause:

- The positive integer is `(n : ℕ) (hn : 1 ≤ n)`.
- The finite free abelian group is `(L : Type u) [AddCommGroup L]
  [Module.Free ℤ L] [Module.Finite ℤ L]`. The conjunction means a finite
  basis, equivalently an isomorphism with ℤ^d for some d including zero.
- The ambient abelian group, subgroup, and homomorphism are `(B : Type v)
  [AddCommGroup B] (D : AddSubgroup B) (φ : L →+ B)`.
- Divisibility by this n alone is `(hD : ∀ d : D, ∃ e : D, n • e = d)`;
  divisibility by every integer is not assumed.
- Torsion-freeness of B/D is `[IsAddTorsionFree (B ⧸ D)]`. The class
  definition is injectivity of nsmul for every nonzero natural number,
  exactly the positive-integer condition in the node.
- The quotient of B/D by the image of L is
  `(B ⧸ D) ⧸ ((QuotientAddGroup.mk' D).comp φ).range`. Its finiteness is
  the `Finite` instance binder; `hQ` says that n annihilates every class.

Conclusions, clause by clause:

- `∃ (G : Type u) (_ : AddCommGroup G), Module.Free ℤ G ∧ Module.Finite ℤ G`
  gives a finite free abelian group. Sharing L's universe loses no case:
  the node's explicit construction uses successive subgroups of L.
- `∃ (i : L →+ G) (h : G →+ B)` gives the two homomorphisms.
- `Function.Injective i` is the required embedding.
- `∃ s : ℕ, ∀ q : G ⧸ i.range, n ^ s • q = 0` says exactly that the
  quotient is killed by one power of n, allowing exponent zero.
- `h.comp i = φ` says that h extends the given map.
- `Function.Surjective ((QuotientAddGroup.mk' D).comp h)` says that G
  surjects onto B/D.

Dependency declarations read and used: `Module.Free` from
`Mathlib.LinearAlgebra.FreeModule.Basic` is the recorded declaration of
`def-weil-pbc-free-module` and is used directly by the existing theorem.
`Module.Finite` from `Mathlib.RingTheory.Finiteness.Defs` expresses finite
rank together with freeness; `IsAddTorsionFree` from
`Mathlib.Algebra.Group.Defs` and `QuotientAddGroup.mk'` from
`Mathlib.GroupTheory.QuotientGroup.Defs` give the other standard notions.
The existing module also imports `Mathlib.LinearAlgebra.FreeModule.PID`,
which supplies `Submodule.basisOfPid`, the Mathlib match of the live proof
node `lem-weil-subgroup-finite-free-abelian-group-free`.

Edge cases checked mathematically: n=1 makes the cokernel trivial and permits
G=L, i=id, h=φ, exponent zero. For L=0, the finite torsion-free quotient
B/D is zero, so G=0 works. Non-injective φ is allowed, with no injectivity
hypothesis on its projection. D=0 includes φ=n· on ℤ, where i=n· and h=id
work. D=B permits G=L and the original map. Arbitrary independent universes
u and v remain available. No hypothesis is hollow or excludes rank zero.

Searches made:

- `msearch.py leanfinder`: “Extend a finite free abelian lattice mapping to B
  across an n divisible subgroup with torsion free quotient and finite
  cokernel killed by n” returned Baer extension, ModN, quotient and torsion
  lemmas. Baer requires divisibility by every integer; none is this theorem.
- `msearch.py loogle`: `Module.Free, DivisibleBy` returned zero hits.
- `msearch.py grep`:
  `[Dd]ivisible.*[Ll]attice|[Ll]attice.*[Dd]ivisible|extension_property_addMonoidHom`
  returned CharacterModule and Injective Baer-extension uses, not the theorem.
- `rg` in `lean/WeilConjectures` for the node id and the lattice/divisibility
  patterns returned no matches.
- `rg` in `lean/Sheaf` found the exact existing theorem in
  `GroupTheory/DivisibleUnitLatticeExtension.lean`, whose full signature and
  docstring were read. Its docstring supplies all eight proof steps: induction
  on the cokernel cardinality, a cyclic generator of order d dividing n,
  adjustment by d-divisibility, the relation calculation, the finite free
  subgroup dL+ℤa, extension of φ, shrinking the cokernel, and composition
  with the exponent increased by one.

The existing module was originally attached to
`lem-per-divisible-unit-lattice-extension`. The live sfb node's stage-1 review
removed a circular proof citation of that dropped node. This attachment does
not restore that citation: the item's statement, stmt_deps, eight-step proof,
proof_deps, and every other non-lean field remain unchanged. Reusing an exact
existing declaration follows the one-definition-per-notion rule. The current
node has no recorded Lean attachment yet and no repair note was present.
No statement correction, new definition node, or dependency module is needed.
The declaration retains its stage-2 sorry; nothing is proved in this delivery.

Validation: the prescribed deliver2.py dry run checks the existing declaration
by a module-mode server #check probe, followed by the maintainer's preflight.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
