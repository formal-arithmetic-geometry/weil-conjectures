## Worker report

The module states `RingHom.exists_fs_adic_lift_over_finite_coefficient_map`, the existence of a complete Noetherian local ring C, a formally smooth local map from A₀, a local map to B compatible with the given maps, and a bijective tensor-product ring map with the prescribed pure-tensor formula. The hypotheses render Noetherianity by `IsNoetherianRing`, locality by `IsLocalRing` and `IsLocalHom`, completeness by `IsAdicComplete`, finiteness by `Module.Finite`, flatness by `RingHom.Flat`, and formal smoothness by `Algebra.FormallySmoothAdic`. The residue-field isomorphism is `IsLocalRing.ResidueField A₀ ≃+* IsLocalRing.ResidueField A`. The closed-fibre ideal is the image of B's maximal ideal under the quotient by the image of A's maximal ideal. The conclusion uses `TensorProduct A₀ C A` and `TensorProduct.tmul` for the base-change ring and pure tensors.

Dependencies used: `Mathlib.RingTheory.Noetherian.Defs.IsNoetherianRing`, `Mathlib.RingTheory.AdicCompletion.Basic.IsAdicComplete`, `Mathlib.RingTheory.Finiteness.Defs.Module.Finite`, `Mathlib.RingTheory.RingHom.Flat.RingHom.Flat`, `Sheaf.RingTheory.FormallySmoothAdic.Algebra.FormallySmoothAdic`, and Mathlib's `TensorProduct`.

Edge cases checked: no positivity or nonzero assumptions were added; the formulation permits zero-dimensional local rings and arbitrary universes `u v w`, with tensor products at `max u v`.

Searches: `msearch.py leanfinder` and `loogle` for formal-smooth complete-local lifting (no matching declaration); grep of Mathlib and `WeilConjectures` for the theorem name and Cohen/formal-smooth lifting (no match); `rg` over `lean/Sheaf` for existing declarations (no match).

## Earlier second reading (a previous round; superseded)

The theorem binders match the node's Noetherian complete local rings, finite coefficient map inducing a residue-field isomorphism, flat local map to a complete Noetherian local ring, and formally smooth closed fibre. The existential clauses provide exactly C, γ, ψ, compatibility, and the tensor map isomorphism with the stated pure-tensor formula.

## Second reading by F1

Independent review on 2026-10-11 with the node, all six statement-dependency
nodes, their recorded declaration sources, and the delivery module open.
The node's TeX is correct and unchanged. No statement_change, new definition
nodes, or dependency modules are needed.

Source read: the repository does not contain the fetched Stacks .tex, so I read
its available local copy /home/ubuntu/c1-stacks-review/more-algebra.tex:
lemma-lift-fs (07NR), remark-what-does-it-mean (07NS), lemma-lift-continuous
(07NJ), proposition-fs-regular (07PM), definition-formally-smooth (07EB),
lemma-formally-smooth (07EC), and definition-formally-smooth-adic (07NI).
Remark 07NS assumes all maps local and all rings Noetherian complete local,
requires the induced residue map to be an isomorphism, and assumes smoothness
over the common residue field. Its finite case and flat case together give
this node, as 07PM explicitly explains: no tensor completion is necessary.
There is no additional field, domain, characteristic, regularity, or finite-type
hypothesis on this lemma itself.

Object/hypothesis/conclusion checklist (each verdict is for the repaired file):

1. A₀, A, B are arbitrary commutative rings: `{A₀ : Type u} {A : Type v}
   {B : Type w}` and three `CommRing` instances. Match.
2. All three are Noetherian local: three `IsNoetherianRing` and three
   `IsLocalRing` instances. Match; these are the standard recorded definitions.
3. All three are complete and separated for their respective maximal ideals:
   three `IsAdicComplete (IsLocalRing.maximalIdeal ...) ...` instances. Match.
4. α : A₀ → A is local: `(α : A₀ →+* A) [IsLocalHom α]`. The algebra instance
   and `hα : algebraMap A₀ A = α` ensure every module and tensor operation uses
   this particular map. They encode its algebra structure, with no restriction
   beyond the node's map. Match.
5. A is a finite A₀-module via α: `[Module.Finite A₀ A]`, with hα above. Match.
6. α induces an isomorphism on residue fields: now
   `Function.Bijective (IsLocalRing.ResidueField.map α)`. Match. The old binder
   was an arbitrary ring equivalence between the residue fields and said
   nothing about the induced map of α. Replaced it with bijectivity of the
   recorded canonical residue map, whose signature and map_residue theorem
   were read in Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean.
7. φ : A → B is flat and local: `(φ : A →+* B) [IsLocalHom φ]`
   `(hflat : RingHom.Flat φ)`, with `hφ : algebraMap A B = φ`. Match.
   RingHom.Flat is exactly Module.Flat for φ.toAlgebra, not a flatness condition
   on a different map.
8. The closed fibre is E = B/m_A B: `B ⧸ Ideal.map φ
   (IsLocalRing.maximalIdeal A)`. Its topology is defined by
   `Ideal.map (Ideal.Quotient.mk ...) (IsLocalRing.maximalIdeal B)`. Match:
   locality puts m_A B inside m_B, so this is exactly m_B/m_A B.
9. The closed fibre is formally smooth over k = A/m_A: now
   `Algebra.FormallySmoothAdic (IsLocalRing.ResidueField A) E ...`.
   Match. The old statement used A as the base, which is a different lifting
   condition (for example the discrete quotient of a nonreduced A is not
   formally smooth over A even when its residue field is smooth over itself).
   The local `letI` constructs the canonical k-algebra structure using
   `Ideal.Quotient.algebraQuotientOfLEComap`, `Ideal.le_comap_map`, and
   equality transport along hφ. Its quotient map is induced by φ. This is
   actual data, with no sorry, no new definition, and no extra hypothesis or
   arbitrary residue-field action. The hypothesis is an implication before
   the existential, preserving quantifier order.
10. A complete Noetherian local commutative C exists: `∃ (C : Type
    (max u v w)) (_ : CommRing C) (_ : IsLocalRing C) (_ : Algebra A₀ C),
    IsNoetherianRing C ∧ IsAdicComplete (IsLocalRing.maximalIdeal C) C ∧ ...`.
    Match. The old universe max u v excluded large closed fibres when w is
    larger: with A₀ = A = k and B a large complete local field extension,
    the tensor isomorphism requires a C as large as B. Including w repairs it.
11. γ : A₀ → C is local and C is formally smooth over A₀ in its maximal-ideal
    topology: `∃ γ, algebraMap A₀ C = γ ∧ IsLocalHom γ ∧
    Algebra.FormallySmoothAdic A₀ C (IsLocalRing.maximalIdeal C) ∧ ...`.
    Match; the equality binds the smoothness and tensor action to γ.
12. ψ : C → B is local and ψγ = φα: `∃ ψ, IsLocalHom ψ ∧
    ψ.comp γ = φ.comp α ∧ ...`. Match.
13. The indicated ordinary tensor-product map is a ring isomorphism:
    `∃ F : RingHom (TensorProduct A₀ C A) B, Function.Bijective F ∧
    ∀ c a, F (TensorProduct.tmul A₀ c a) = ψ c * φ a`. Match.
    Bijectivity of a ring homomorphism is equivalent to being an isomorphism;
    the pure-tensor formula uniquely determines the map and includes both
    input actions. No completed tensor product or weaker bare isomorphism
    has been substituted.

Dependencies checked by source, not name alone: IsNoetherianRing in
Mathlib.RingTheory.Noetherian.Defs (all ideals finitely generated);
IsAdicComplete in Mathlib.RingTheory.AdicCompletion.Basic (Hausdorff plus
precomplete); Module.Finite in Mathlib.RingTheory.Finiteness.Defs (fg_top);
RingHom.Flat in Mathlib.RingTheory.RingHom.Flat (flat for the given map);
Algebra.FormallySmoothAdic in Sheaf.RingTheory.FormallySmoothAdic (all
square-zero lifting tests, killed positive ideal powers, test universe max
of base and target); and TensorProduct/tmul with the commutative ring
structure in Mathlib.RingTheory.TensorProduct.Basic. The module-base-change
node records TensorProduct among its declarations; using it here is the
recorded notion, not a private base-change definition. All six dependencies
are usable; no replacement modules are required.

Edge cases: IsLocalRing extends Nontrivial, correctly excluding the zero ring
since a local ring has a proper maximal ideal and residue field. Zero-dimensional
local rings, fields, maximal ideal zero, and all residue characteristics are
covered. No positive-dimension, perfectness, or nonzero characteristic assumptions
are present. Empty finite generating families are not excluded; finiteness is
Module.Finite. There are no index-set, scheme, or degree-n binders in this node,
so empty schemes and n = 0 add no separate case. The adic definitions include
all natural powers. All u, v, w and all variables are explicitly bound; C is
in max u v w, the tensor in that same universe, and formal-smoothness tests
use the dependency's max-of-base-and-target universe.

Independent searches with wording different from the worker's:
- msearch.py leanfinder: "finite local extension residually trivial flat complete
  local algebra tensor product lifting". Eight candidates; discrete smoothness,
  residue-field finiteness, tensor representatives, or faithful flatness only.
  None constructs C with the node's hypotheses and tensor isomorphism.
- msearch.py loogle: "IsLocalRing.ResidueField.map". Confirmed the canonical map
  and its compatibility with residue; no theorem matching this node.
- msearch.py leansearch: full natural-language flat complete local algebra/base
  change statement. Service returned Internal Server Error, recorded unavailable.
- msearch.py grep on Mathlib/RingTheory: "residually trivial|fs_adic_lift_over_finite|
  coefficient.*lift|lift.*coefficient". Only Witt-vector Teichmüller coefficient
  lifting, unrelated. rg on WeilConjectures, lean/Sheaf, and lean_names_upstream
  with these phrases and FormallySmoothAdic found no duplicate. Existing
  FormallySmoothAdicLift is the residue-fibre lifting dependency (07NR), not
  the finite-coefficient base-change statement. Its signature was opened too.

Other repairs: added the standard copyright/license/author header; made the
source/blueprint tags whole; expanded the theorem docstring to all eight node
proof steps, naming their dependencies. Every theorem proof remains sorry;
there is no hollow definition and nothing is proved in this stage-2 delivery.
The node's lean.statement was regenerated verbatim modulo whitespace from the
final signature. The source TeX, stmt_deps, proof and proof_deps stay unchanged.

Validation: scompile.py compiled the repaired module cleanly on the server
in 1.6 seconds, without errors or warnings. Delivery preflight and final
compile are run below by deliver2.py.
