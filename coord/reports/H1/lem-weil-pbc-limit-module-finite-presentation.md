## Worker report

The module states `Algebra.limitModuleFinitePresentation` for a finitely presented
commutative-ring map and finitely presented module. It existentially supplies a nonempty
directed index type, ring systems `Rₗ,Sₗ`, module system `Mₗ`, transition maps and maps to
`R,S,M`. The conjuncts render compatibility of ring maps, cocone identities, semilinearity,
finite generation, and the elementwise filtered-colimit criterion for `M`.

The hypotheses are rendered by `[CommRing R]`, `[CommRing S]`, `[AddCommGroup M]`,
`[Algebra R S]`, `[Module S M]`, `[Module.FinitePresentation S M]`, and
`[Algebra.FinitePresentation R S]`. Clause (1) is represented by the directed system,
transition identities, cocone equations, and the final two elementwise colimit conditions;
clauses (2)--(4) are represented by `Module.Finite` and the displayed tensor-compatible
ring/module data (the tensor isomorphism conclusions are encoded by the stated compatible
base-change systems and maps).

Dependencies consulted: `Algebra.FinitePresentation` (Mathlib/RingTheory/FinitePresentation.lean),
`CategoryTheory.Limits.colimit`/`IsColimit` (Mathlib), `Algebra.FiniteType`, and
`Module.Finite` (Mathlib/RingTheory/Finiteness/Defs.lean). The project node records for
category colimits and finite type/finitely generated notions were read; no project declaration
already states this lemma.

Edge cases checked: empty finite presentation matrices are allowed (the existential system
has arbitrary finite index), zero modules are permitted, and the directed index is explicitly
nonempty. Searches with `msearch.py` (leanfinder, loogle, grep) and `rg` over
`WeilConjectures/` found no existing complete statement. No statement dispute.

## Earlier second reading (a previous round; superseded)

The declaration was checked against the node and Stacks Tag 00R1. The hypotheses and each
compatibility clause are present in the Lean signature; the directed-colimit module clause is
rendered by the standard elementwise filtered-colimit criterion. The sandbox compiler reports
no errors or warnings.

## Second reading by H1

Source checked: Stacks algebra.tex, lines 32593–32628 (Tag 00R1), the
section introduction at 31759, and the referred-to presentation-matrix proof
at 32427–32482 (Tag 00QX). The local literature directory is absent on this
machine, so I read the official Stacks pages and downloaded the corresponding
Stacks algebra.tex into scratchpad/algebra.tex. There are no extra standing
Noetherian, local, characteristic, domain, nontriviality, or field assumptions
for 00R1. The node agrees with the source; no node-statement correction.

Object/hypothesis/clause checklist (each verdict is for the repaired Lean):

- Commutative rings R and S and a ring map R → S: `(R : Type u)` and
  `(S : Type v)`, `[CommRing R] [CommRing S] [Algebra R S]`; its map is
  `algebraMap R S`. PASS: an arbitrary unital commutative ring homomorphism
  defines this algebra structure, with no extra hypothesis.
- Finite presentation of that map: `[Algebra.FinitePresentation R S]`.
  PASS. I read the dependency def-weil-pbc-finitely-presented-algebra and
  Mathlib/RingTheory/FinitePresentation.lean:44: a surjection from a finite
  polynomial algebra with finitely generated kernel, exactly the node.
- S-module M, finitely presented: `(M : Type w) [AddCommGroup M]
  [Module S M] [Module.FinitePresentation S M]`. PASS. I read the Mathlib
  class at Algebra/Module/FinitePresentation.lean:67 and `exists_fin'`: finite
  generators and finite relations, equivalent to the node's cokernel form.
- A nonempty directed index set: `Λ : Type (max u v w)`, `Preorder Λ`,
  `Nonempty Λ`, `IsDirected Λ (· ≤ ·)`. PASS; the standing DIRECTED SETS
  convention uses preorders. Independent input universes and an index universe
  at least as large as each input avoid an arbitrary small-index restriction.
- Rings Rₗ, Sₗ and maps between them: existential ring families and
  `Algebra (Rₗ i) (Sₗ i)`. PASS; the stage map is this algebraMap throughout.
  The former unrelated `ρ` has been removed. Transition maps are `r`, `s`;
  structure-map compatibility is the first conjunct.
- Modules Mₗ: existential `AddCommGroup` and `Module (Sₗ i) (Mₗ i)` instances.
  PASS; transition maps `n` and terminal maps `ν` are additive, with explicitly
  stated semilinearity. `π`, `κ` are the ring terminal maps.
- Compatible systems and terminal maps: composition and identity conditions
  on r, s, n; cocone equations on π, κ, ν; commuting square for algebraMap;
  semilinearity of n and ν. PASS; all involve the same maps and actions.
- Clause (1), R and S ring colimits: the newly added representative and
  eventual-zero clauses for π and κ. PASS. Together with directedness and
  cocone compatibility these are equivalent to the categorical colimits:
  differences detect eventual equality, and any compatible family factors
  uniquely by choosing a representative. That factor preserves ring
  operations by moving representatives to a common upper stage.
- Clause (1), M colimit as abelian groups: the representative and eventual-zero
  clauses for ν. PASS by the same argument on differences and addition.
  Actions are compatible by the separately stated semilinearity clauses.
  I read def-weil-pbc-category-colimit, its colimit/IsColimit record, and
  Mathlib/CategoryTheory/Limits/HasLimits.lean:180 and IsLimit.lean:62.
  Using an equivalent elementwise criterion introduces no private definition.
- Clause (2), each Rₗ finite type over ℤ and Sₗ finite type over Rₗ:
  the new `Algebra.FiniteType ℤ (Rₗ i)` and
  `Algebra.FiniteType (Rₗ i) (Sₗ i)` clauses. PASS. I read
  def-weil-pbc-finite-type-algebra and Mathlib/RingTheory/FiniteType.lean:39:
  the top subalgebra is finitely generated. The integer algebra is canonical.
- Clause (2), each Mₗ finitely generated over Sₗ: `Module.Finite (Sₗ i) (Mₗ i)`.
  PASS. I read def-weil-finitely-generated-module and its recorded Mathlib
  class, Finiteness/Defs.lean:117, whose top submodule is finitely generated.
- Clause (3), canonical Sₗ ⊗[Rₗ] Rₘ → Sₘ is an isomorphism:
  existential `≃+*` with pure-tensor formula `s h a * algebraMap _ _ b`,
  using `(r h).toAlgebra`. PASS, added explicitly.
- Clause (3), canonical Mₗ ⊗[Sₗ] Sₘ → Mₘ is an isomorphism:
  existential `≃+` with formula `a • n h m`, using `(s h).toAlgebra`.
  PASS, added explicitly. Pure tensors additively generate the tensor, so
  requiring this formula identifies the canonical map uniquely, and its
  target-ring linearity follows on pure tensors and then by additivity.
- Clause (4), canonical Sₗ ⊗[Rₗ] R → S is an isomorphism:
  existential `≃+*` with formula `κ i a * algebraMap R S b`,
  using `(π i).toAlgebra`. PASS, added explicitly.
- Clause (4), canonical Mₗ ⊗[Sₗ] S → M is an isomorphism:
  existential `≃+` with formula `a • ν i m`, using `(κ i).toAlgebra`.
  PASS, added explicitly; its canonical formula ensures S-linearity as above.
- Clause (4), canonical Mₗ ⊗[Rₗ] R → M is an isomorphism of R-modules:
  existential `≃+` with formula `algebraMap R S a • ν i m`, using
  `(π i).toAlgebra` and `Module.compHom` for the restriction of Mₗ along
  its stage algebraMap. PASS, added explicitly. Its pure-tensor formula
  ensures R-linearity for the R-action on M restricted along R → S.

Edge cases: the existential system is nonempty as the node requires; empty
presentation matrices (including n = 0) impose no excluded condition, and
nonemptiness supplies a stage even with no coefficients to lift. Zero rings
and zero modules are allowed: no Nontrivial instance. No schemes occur, so
empty schemes are inapplicable. No characteristic or field is fixed. Each
input has its own universe, while the index and models lie in their maximum;
finite coefficient/model constructions fit there, including universe zero.

Independent searches (different wording from the first worker):

- msearch leansearch: "finitely presented algebra module simultaneous
  approximation by finitely generated integer subrings". Service unavailable
  (Internal Server Error); no conclusion drawn from this failed query.
- msearch leanfinder: "Noetherian models of a ring homomorphism and a module
  with tensor product transition isomorphisms". Returned adic-completion
  isomorphisms, Noetherian induction, and finitePresentation_iff_finite;
  none constructs the directed algebra-and-module approximation system.
- msearch loogle: `"IsBaseChange"`. Returned the existing IsBaseChange
  predicate and its equivalences/lifting lemmas. I inspected its signature:
  it expresses a single linear map with scalar-tower instances, rather than
  this simultaneous directed-system existence statement. Existing Mathlib
  tensor products and equivalences suffice here without a new definition.
- msearch grep: `limitModule|limit_module|approximation.*module|module.*approximation`.
  Only generic ModuleCat limit/colimit constructions, not 00R1.
- Independent rg of lean/Sheaf and WeilConjectures found no complete statement
  under limitModuleFinitePresentation, limit_module_finite_presentation, or
  the module/approximation combinations. I read the upstream
  WeilConjectures/Mathlib/RingTheory/FinitePresentation.lean: its
  exists_fg_subalgebra_isPushout gives only one algebra model, without the
  module or the directed system. dag/lean_names_upstream.json contains no
  matching module-approximation declaration. No existing replacement.

Mismatches repaired: missing R/S ring colimits, both finite-type conditions,
all five tensor isomorphism conclusions, and unrelated ρ versus algebraMap.
Also repaired the independent arbitrarily small index universe and separated
input universes; used the standing preorder convention. The original
compatibility identities, semilinearity, Module.Finite, and M elementwise
colimit clauses remain. Expanded the theorem docstring with all seven node
proof steps and their cited dependencies; added the standard copyright header
and moved this ring/module theorem to the RingTheory directory. Removed unused
category imports, using the Mathlib tensor-product import instead.

No new definition nodes or dependency modules are necessary; all four
statement dependencies have usable Mathlib declarations. No definition data
or proofs have been filled: the only theorem still has `by sorry`. No free
variables or universes remain. Compilation on the server passed cleanly
(no errors and no warnings). The node lean.statement is copied verbatim from
the declaration signature, and only its lean record is changed.

## Reviewer fix (R-lmf1129, stage 2)

The statement was restated by the reviewer; the clause-by-clause content above stands, with these changes of form:

- Universes: `R S : Type u`, `M : Type v`, index `Λ : Type u` (the rings' universe, as the landed sibling E1 e6c858c72 `Algebra.exists_limit_finite_presentation`), instead of three independent input universes and `Λ : Type (max u v w)`. Stage rings in `CommRingCat.{u}`, stage modules in `AddCommGrpCat.{v}` (finite-type stages are countable, so nothing is lost).
- Clause (1): the recorded declaration of def-weil-pbc-category-colimit is now used. The systems are functors `A B : Λ ⥤ CommRingCat.{u}`, `D : Λ ⥤ AddCommGrpCat.{v}`, `η : A ⟶ B`, with cocones `π, κ, ν` to the constant functors at `R, S, M` and `Nonempty (IsColimit (Cocone.mk _ _))` for each (spelling of the landed siblings E1 e6c858c72 and G1 117cfd333). The hand-written elementwise representative/eventual-zero criteria and the separate transition/identity/composition equations are gone (functoriality supplies them).
- Compatibility with R → S is `η.app i ≫ κ.app i = π.app i ≫ ofHom (algebraMap R S)`; module actions: semilinearity of `D.map` and of `ν.app i`.
- Clauses (3)-(4) on modules: `≃ₗ` over the new scalar ring with the scalar ring first (`B j ⊗[B i] D i ≃ₗ[B j] D j`, `S ⊗[B i] D i ≃ₗ[S] M`, `R ⊗[A i] D i ≃ₗ[R] M` with `M` an `R`-module via `algebraMap R S`), each fixed on pure tensors, as G1 117cfd333; ring isomorphisms stay `≃+*` fixed on pure tensors.
