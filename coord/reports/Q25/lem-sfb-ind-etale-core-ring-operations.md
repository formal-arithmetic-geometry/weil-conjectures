## Worker report

The module `Sheaf.RingTheory.IndEtaleCoreRingOperations` states
`Algebra.finiteEtaleSubalgebra_ring_operations` with one postponed proof. It adds
no definitions. The node statement and all non-Lean node fields are unchanged.

Hypothesis and clause correspondence:

- `k : Type u` with `[Field k]` is the base field; `R : Type v` with
  `[CommRing R] [Algebra k R]` is an arbitrary commutative unital algebra. There
  is no nontriviality assumption except in the last implication.
- Every occurrence of B_k is the dependency's actual
  `Algebra.finiteEtaleSubalgebraUnion`, not a new construction. Its defining
  supremum equals the set-theoretic union by the dependency theorem.
- Reducedness is `IsReduced (finiteEtaleSubalgebraUnion k R)`: the ambient
  commutative-ring operations are inherited, and nilpotents are zero.
- Functoriality quantifies over every `S : Type w`, its commutative-ring and
  k-algebra structures, and every `f : R →ₐ[k] S`. The existential algebra
  homomorphism `g` has inclusion-composition equal to `f.comp` the source
  inclusion. Thus it is exactly the restriction of f, not an arbitrary map.
- A unital subalgebra is `D : Subalgebra k R`. Mapping its own core into R
  along `D.val` gives exactly `D ⊓ finiteEtaleSubalgebraUnion k R`. This is
  the asserted intersection inside the ambient algebra (called S in the node).
- The reduction is `R ⧸ nilradical R`. Mathlib's `mem_nilradical` identifies
  this ideal with nilpotent elements, with no bound on the whole ideal's
  nilpotency. An existential `k`-algebra equivalence has the explicit equation
  `(e x).val = Ideal.Quotient.mkₐ k (nilradical R) x.val`, so its direction
  and underlying map are exactly the quotient-induced map in the node.
- Products quantify over `I : Type t` with `[Finite I]`, a family
  `A : I → Type w`, and every factor's commutative-ring and algebra structures.
  An algebra equivalence from the product's core to the product of cores has
  `(e x i).val = x.val i` for all coordinates: its components are precisely
  the restrictions of the projections. Neither an inhabited index set nor
  nonzero factors are assumed. The independent index universe is harmless
  here: these are explicit finite products, not filtered colimit tests.
- The last clause assumes `Nontrivial R` and
  `∀ e : R, e ^ 2 = e → e = 0 ∨ e = 1`. Its conclusion is `IsField` of the
  existing core ring and `Algebra.IsSeparable k` that core. `IsField` asserts
  nontriviality and inverses for the inherited multiplication; it does not
  choose a different ring structure. The recorded separability predicate is
  defined for commutative algebras and already implies algebraicity over a
  field (`Algebra.IsSeparable.isAlgebraic`), so no field-structure choice or
  additional field-extension predicate is necessary.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field` (def-weil-field).
- Sheaf.RingTheory.FiniteEtaleSubalgebraUnion:
  `Algebra.finiteEtaleSubalgebras`, `Algebra.finiteEtaleSubalgebraUnion`,
  `Algebra.finiteEtaleSubalgebra_directed_union` (full source and docstrings read).
- Mathlib.FieldTheory.Separable: `Algebra.IsSeparable`, including its
  explanation that nonalgebraic elements have zero, nonseparable minimal
  polynomial, and `Algebra.IsSeparable.isAlgebraic`.
- Additional standard notation uses Mathlib's `IsReduced`, `IsField`,
  `nilradical`, `Subalgebra.map`, `Ideal.Quotient.mkₐ`, and Pi algebras.

Proof-dependency imports: Mathlib.RingTheory.Etale.Field (field-product
classification), Mathlib.RingTheory.Etale.Pi (finite-product étaleness),
Sheaf.AlgebraicGeometry.EtaleComparison (the four comparisons), and
Sheaf.RingTheory.WeaklyEtaleField (the finitely generated subalgebra theorem).
Mathlib.AlgebraicGeometry.Morphisms.Finite is also directly imported for the
finite-morphism definition; its affine finite-module criterion was read.
`lem-sfb-etale-nil-ideal-map-lift` has no recorded module yet; no proof import
is available for it. It is a proof dependency only, and does not prevent typing
this node. A source lookup for a prospective
Sheaf.RingTheory.EtaleNilIdealMapLift also reported it unavailable.

Source checked: literature/stacks-project/more-algebra.tex, the complete
lemmas class-weakly-etale-over-field, max-weakly-etale-subalgebra, and
properties-of-max-weakly-etale-subalgebra (Tags 0CKR, 0CKS, 0CKT). The node
already corrects the printed proof's reversed reduction arrow and excludes
R=0 from the last clause; no statement correction is needed.

Edge cases: R=0 has zero core and zero reduction; maps out of zero only exist
into zero; a map from nonzero R to zero still restricts as required. A zero
subalgebra can occur in a zero ambient ring. The empty product is a
subsingleton ring, and both sides of its equivalence are zero rings; the
coordinate equation is vacuous but the algebra equivalence still asserts the
full identification. Arbitrary zero factors are permitted. The last clause
excludes zero but allows a connected ring with nilpotents (for example dual
numbers); only the core is asserted to be a field. No perfectness or
characteristic restriction is imposed. Arbitrary and distinct universes for
k, R, S, factors, and finite indices are allowed.

Searches for an existing statement:

- msearch leanfinder: “The union of finite etale subalgebras over a field is
  reduced and commutes with reduction finite products and intersections”.
  Eight hits include reducedness of formally unramified finite-type algebras,
  geometrically reduced algebras, finite products of formally étale algebras,
  the finite étale field classification, and coefficient descent. None is
  the core-operations statement for arbitrary algebras.
- msearch loogle: `"Etale", "Subalgebra"`: only
  `Algebra.Etale.exists_subalgebra_fg`, which descends coefficients and does
  not discuss the union of finite étale subalgebras or its operations.
- msearch grep in Mathlib/RingTheory:
  `finiteEtaleSubalgebra|indEtaleCore|max.*[Ee]tale|[Ee]tale.*[Ss]ubalgebra`:
  only coefficient descent and a quotient in the finite field classification.
- rg of the same expression in lean/WeilConjectures and lean/Sheaf found the
  directed-union dependency, weakly étale finitely generated subalgebras, and
  unrelated finite-stage/descent statements; no operations theorem. The
  new declaration name was separately checked in both trees and the upstream
  name inventory, with no match. The item-id grep in WeilConjectures had no hit.
- msearch leansearch: “The maximal ind etale subalgebra over a field commutes
  with reduction and finite products”; eight hits on finite products of formally étale algebras, the étale predicates,
  finite field classifications, base change, and finite presentation; none
  states the core operations for arbitrary algebras.

No STATEMENT-DISPUTED flag, node fault, new node, or dependency repair.

## Second reading by Q25

Independent second reading (maintainer review service, 2026-10-24). This replaces the earlier
self-check by the delivering worker. It reads the node, Stacks more-algebra.tex Tag 0CKT
(lemma-properties-of-max-weakly-etale-subalgebra, line 30913, parts (1),(2),(4),(5),(6)) and
Tag 0CKR, and the statement dependency records, against
`Algebra.finiteEtaleSubalgebra_ring_operations`.

Node objects, hypotheses and clauses, with the Lean for each:

- k a field: `(k : Type u) [Field k]`, def-weil-field = Mathlib `Field`. Correct.
- R an arbitrary commutative unital k-algebra, R = 0 allowed: `(R : Type v) [CommRing R] [Algebra k R]`
  with no nontriviality assumption. Correct.
- B_k(R), the union of finite étale subalgebras: `finiteEtaleSubalgebraUnion k R`, which is the
  dependency's own declaration (sSup of `{D | Module.Finite k D ∧ Etale k D}`). Its carrier is the
  literal union by clause 3 of `finiteEtaleSubalgebra_directed_union`. This is the dependency's
  object and not a copy; the node itself defines B_k "as in" that lemma.
- (a) B_k(R) is reduced: `IsReduced (finiteEtaleSubalgebraUnion k R)` with the inherited ring
  structure. Correct.
- (b) f : R →ₐ[k] S restricts: every `S : Type w` and every f, `∃ g` with
  `B(S).val ∘ g = f ∘ B(R).val`. Since val is injective, g is the restriction of f, which is
  unique and not an arbitrary map. Correct.
- (c) R ⊆ S gives B(R) = R ∩ B(S): `∀ D : Subalgebra k R, (B k D).map D.val = D ⊓ B k R`. Here the
  ambient algebra is R and the subalgebra is D. The equality of subalgebras holds inside the
  ambient algebra, so this is the node clause after renaming. Correct.
- (d) B(R) ≅ B(R_red), induced by the quotient: `∃ e : B R ≃ₐ[k] B (R ⧸ nilradical R)` with
  `(e x).val = mkₐ (nilradical R) x.val`. The arrow is pinned to the quotient-induced map in the
  node's direction. Mathlib `nilradical` = {r | IsNilpotent r} = N_R, with no assumption that
  the ideal is nilpotent. Correct.
- (e) For finite families, B(∏ R_i) = ∏ B(R_i) via the projections:
  `∀ (I : Type t) [Finite I] (A : I → Type w) …, ∃ e` with `(e x i).val = x.val i`. The
  equivalence is pinned on all coordinates. The empty I is allowed, and both sides are then the
  zero ring. Correct.
- (f) If R ≠ 0 and its only idempotents are 0 and 1, then B(R) is a field that is separable
  algebraic over k: `Nontrivial R → (∀ e, e^2 = e → e = 0 ∨ e = 1) → IsField (B R) ∧
  Algebra.IsSeparable k (B R)`. `Algebra.IsSeparable` is the recorded Mathlib declaration of
  def-weil-pbc-separable-algebraic-extension. It implies algebraicity
  (`Algebra.IsSeparable.isAlgebraic`), and `IsField` uses the inherited ring operations.
  Correct. The R ≠ 0 requirement is the node's own explicit correction of the source.

Edge cases:
- R = 0: the core is 0, (a)–(e) hold, and (f) is excluded by `Nontrivial`.
- k[ε]/ε²: (f) applies, and the core is k.
- Empty and zero product factors.
- A map from nonzero R to 0.
- Inseparable k: Algebra.IsSeparable still demands separable minimal polynomials, as in the source.
- Universes: k, R, S/factors and index are independent (u, v, w, t). S and the factors share w
  only across separate ∀-clauses of a universe-polymorphic theorem, which is harmless.

Checks:
- Records: the node record is identical to side-live apart from `lean`. The stmt_deps are
  unchanged and the lean statement occurs verbatim once in the file.
- Docstrings carry the Stacks source and `(blueprint: lem-sfb-ind-etale-core-ring-operations)`,
  plus all six proof steps.
- No definitions, a single `sorry`, and no pro-étale material.
- No existing declaration was found: rg over lean/Sheaf and lean/WeilConjectures for
  finiteEtaleSubalgebraUnion found only the dependency module, and the delivery's searches
  matched no Mathlib declaration.
- Imports of the proof dependencies are private.

No mismatch in the Lean. Only this section was changed.
