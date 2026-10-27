## Worker report

The module Sheaf.RingTheory.PolynomialPresentationPseudoCoherence states
DerivedCategory.isPseudoCoherent_restrictScalars_polynomial_presentation_iff.
Its sole theorem has proof `sorry`; it introduces no definitions. The node's accepted
statement and split are unchanged. The inherited BLOCKED ending concerned the accepted
stage-1 split, not a Lean statement: the current item has no lean or reviewed_lean record
and remains a stage-2 queue item. No released repair note for it was found.

Clause-by-clause correspondence:

- Commutative rings R and A: `{R : Type uR} {A : Type uA} [CommRing R] [CommRing A]`.
- The common R-algebra structure on A: `[Algebra R A]`. Both maps are algebra
  homomorphisms for precisely that same structure.
- Arbitrary nonnegative numbers of variables: `{r s : ℕ}`; P and Q are literally
  `MvPolynomial (Fin r) R` and `MvPolynomial (Fin s) R`.
- The two displayed maps: `α : MvPolynomial (Fin r) R →ₐ[R] A` and
  `β : MvPolynomial (Fin s) R →ₐ[R] A`.
- Their surjectivity: `(hα : Function.Surjective α)` and
  `(hβ : Function.Surjective β)`.
- Every K in D(A): `(K : DerivedCategory (ModuleCat.{max uR uA v} A))`.
  HasDerivedCategory binders for A, P and Q fix the chosen localization size;
  their three morphism universes wA, wP, wQ are independent. Module carriers live in
  max uR uA v, which contains both rings and allows arbitrary larger module universes.
- Restriction along α and β: `(ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory`
  and the analogous expression for β. The ordinary functor's obj' uses Module.compHom,
  its map' keeps the additive map; mapDerivedCategoryFactors identifies its derived
  functor with this functor applied termwise, then localized. It is the specified
  restriction, without any scalar extension or derived tensor.
- Pseudo-coherence and both directions: `IsPseudoCoherent (...) ↔ IsPseudoCoherent (...)`,
  using the existing bounded-above finite-free-representative predicate over P and Q.
- There are no further hypotheses on K, R, A or the kernels. In particular no boundedness,
  flatness, finite presentation, Noetherian or nonzero hypothesis occurs.

Dependency declarations read and used:

- Mathlib.Algebra.MvPolynomial.Basic: MvPolynomial and its canonical R-algebra structure;
  read MvPolynomial.algHom_ext and Mathlib.Algebra.MvPolynomial.Eval's MvPolynomial.aeval
  for the universal-property clauses of def-weil-pbc-mv-polynomial-ring.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory, HasDerivedCategory,
  DerivedCategory.Q, as recorded by def-weil-abstract-derived-category. This is publicly
  imported through Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor.
- WeilConjectures.RingTheory.RingPseudoCoherent: DerivedCategory.IsPseudoCoherent,
  exactly the recorded declaration of def-pc-ring-pseudo-coherent-complex. Read its full
  finite-free, strictly bounded-above, derived-isomorphism definition and source docstring.
- Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact: the general-universe exactness
  instances for ModuleCat.restrictScalars; the underlying functor is from ChangeOfRings.
- Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor:
  CategoryTheory.Functor.mapDerivedCategory and mapDerivedCategoryFactors.

The proof docstring follows all four DAG steps: the monic translated-variable two-term
resolution; the 064Z scalar-restriction equivalence; lifts of the two sets of generators
and their common polynomial ring; finite variable-by-variable induction on both sides.
The proof-only node lem-sfb-pseudocoherent-algebra-scalar-restriction has no lean record
or mathlib_match in the read base, so it supplies no module to import yet. Its later
proof import belongs to the maintainer's normal proof-dependency propagation. The other
proof dependencies are already public statement dependencies. No import cycle is added.

Read the source in literature/stacks-project/more-algebra.tex: Tag 065H,
lemma-relatively-pseudo-coherent, including its final pseudo-coherence clause and common
presentation proof; also 065G's evaluation argument. No statement correction is needed.

Edge cases checked before writing: r=0 or s=0 uses Fin 0 and permits the coefficient-only
presentation; r=s=0 has no forbidden size or nonempty assumption. K=0, A=0 and R=0 are
allowed. For k[x] → k, x ↦ 0, versus k → k, the polynomial-side two-term resolution
matches the equivalence. The monic argument works for Z/4 and evaluation at 2. Unbounded
K and non-pseudo-coherent K remain in the quantification; no model or boundedness is
assumed. Distinct ring and derived morphism universes remain independent.

Searches through the prescribed msearch.py wrapper (raw answers in searches.jsonl):

- LeanFinder: "Pseudo coherence of a derived complex is independent of its surjective
  finite polynomial presentation" returned eight hits concerning algebra presentations,
  cotangent complexes, finite presentation and smoothness; none is this statement.
- Loogle: `"PseudoCoherent", MvPolynomial` returned zero hits.
- Mathlib grep: `pseudo.?coher|pseudoCoherent|PseudoCoherent` in RingTheory returned zero hits.
- LeanSearch: "Pseudo coherent complexes over two surjective finite polynomial
  presentations of an algebra" returned eight hits concerning finite presentation and
  quasicoherent sheaves, with no pseudo-coherence invariance theorem.
- rg of lean/WeilConjectures and lean/Sheaf for the exact node id returned no declaration.
  Searches for polynomial/presentation pseudo-coherence names and for the proposed full
  declaration name returned no match. Searches for IsPseudoCoherent and scalar restriction
  found the existing definition and nilpotent-kernel invariance, which has different
  hypotheses and does not state the item. The upstream names index has no proposed-name hit.

Server validation: scompile.py compiled this delivered file both as a sandbox module and
at its library module path successfully (1.1 s and 1.2 s), with no errors or warnings.
No statement dispute, missing notion or dependency interface defect was found.

## Second reading by Q18

The dispatcher explicitly requires a single worker and prohibits starting other agents.
This section records my second reading with both node and file open; the maintainer's
independent review remains to follow delivery.

I rechecked that α and β are surjective algebra maps to the same A with the same
R-algebra structure, rather than unrelated ring maps. Their finite variable sets are
Fin r and Fin s with r,s : ℕ, so zero variables are included. K is an arbitrary derived
A-module; it is not replaced by a chosen finite-free complex. Both sides restrict K
using the actual exact restriction functor and test the published IsPseudoCoherent
predicate over the appropriate polynomial ring. The equivalence gives both implications.
No condition on A as a module over R or on either presentation kernel is present.
The three localization universes are distinct and module size contains both rings.
The docstring retains the translated-variable proof and the two independent inductions.
No mismatch or change was found in this second reading. There are no new nodes or
dependency modules to review, and only the item's lean field is changed.
