## Worker report

The module `Sheaf.RingTheory.FiniteTypeFieldExtensionNeighbourhood` states
`RingHom.exists_finiteType_away_of_fieldExtension`, with its proof postponed by
`sorry`. It states the conditional coefficient-subalgebra consequence of the
module-neighbourhood principle, exactly as the node does. No new definitions,
new nodes, dependency repairs, or statement corrections are required. Only the
item's `lean` record changes.

Hypotheses and clauses, matched individually:

- The field k, field K, and extension K/k are `{k : Type u} {K : Type v}`,
  `[Field k] [Field K] [Algebra k K]`.
- The commutative k-algebras A and B are `{A : Type w} {B : Type x}`,
  `[CommRing A] [CommRing B] [Algebra k A] [Algebra k B]`. Their universes
  are independent of one another and of the fields.
- The universally quantified module-neighbourhood principle is `hdesc`.
  It quantifies over `C`, its commutative-ring and k-algebra structures,
  `M`, `N`, their additive groups and C-module structures, and the C-linear
  map `φ`. There are no finite-generation assumptions on any of these.
  The algebra C ranges in B's universe (so coefficient subalgebras are included);
  the module universes `max x y` and `max x z` allow arbitrary independent
  module sizes and include C and B, using canonical universe lifts when needed.
- In that principle, `C_K` is `C ⊗[k] K`. The scalar-extended linear map is
  `φ.baseChange (C ⊗[k] K)`. This is precisely the recorded dependency's
  representation: its domain is `(C ⊗[k] K) ⊗[C] M`, canonically identified
  with `M ⊗[k] K` by `(c ⊗ λ) ⊗ m ↦ (c • m) ⊗ λ`; the inverse sends
  `m ⊗ λ` to `(1 ⊗ λ) ⊗ m`. The maps correspond to `φ ⊗ id_K`.
- Its arbitrary element v and prime P are `(v : C ⊗[k] K)`,
  `(P : Ideal (C ⊗[k] K)) [P.IsPrime]`. The premise `v ∉ P` appears
  explicitly, followed by surjectivity of
  `LocalizedModule.map (Submonoid.powers v) (φ.baseChange (C ⊗[k] K))`.
- Its conclusion is `∃ d : C, algebraMap C (C ⊗[k] K) d ∉ P ∧`
  surjectivity of `LocalizedModule.map (Submonoid.powers d) φ`.
  The algebra map sends d to d tensor 1, and `Submonoid.powers` gives exactly
  localization at 1, d, d^2, and so forth.
- The specified k-algebra homomorphism alpha is `(α : A →ₐ[k] B)`.
- The prime upstairs is `(qK : Ideal (B ⊗[k] K)) [qK.IsPrime]`.
  The contracted prime q is written directly as
  `Ideal.comap (algebraMap B (B ⊗[k] K)) qK`; it is the set of b
  with b tensor 1 in qK, so no independent q or contraction hypothesis is added.
- The element u outside that prime is `(u : B ⊗[k] K) (hu : u ∉ qK)`.
- The premise `hfinite` is `RingHom.FiniteType` of the composite of
  `(Algebra.TensorProduct.map α (AlgHom.id k K)).toRingHom`
  with `algebraMap (B ⊗[k] K) (Localization.Away u)`. Thus its source
  is A tensor_k K, its target is the localization of B tensor_k K at u,
  and its structure map is exactly alpha tensor id_K followed by localization.
- The result chooses `c : B` outside the displayed contraction and asserts
  `RingHom.FiniteType ((algebraMap B (Localization.Away c)).comp α.toRingHom)`.
  This is finite type of B_c over A via the original alpha, not over k or B.

Dependency declarations read and used:

- `def-pc-field-extension`: `Algebra` in `Mathlib.Algebra.Algebra.Defs`,
  specialized to fields, with its `algebraMap`.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`; its map representation is
  `LinearMap.baseChange` in `Mathlib.LinearAlgebra.TensorProduct.Tower`.
  `Algebra.TensorProduct.map` in `Mathlib.RingTheory.TensorProduct.Maps`
  supplies the scalar extension of alpha.
- `def-weil-pbc-module-localization`: `LocalizedModule` and the standard
  `LocalizedModule.map`, with `Submonoid.powers`; ring localization is
  `Localization.Away`, imported from `Mathlib.RingTheory.Localization.Away.Basic`.
- `lem-sc-module-surjectivity-field-extension-neighbourhood`:
  `LinearMap.exists_localizedMap_away_surjective_of_fieldExtension` in
  `Sheaf.RingTheory.ModuleSurjectivityFieldExtensionNeighbourhood`. Its full
  signature and docstring were read. The explicit principle uses exactly
  its scalar-extension/localization interface; the imported declaration also
  supplies the proof plan's module-surjectivity dependency for stage 3.
- `def-weil-pbc-finite-type-algebra`: `RingHom.FiniteType` in
  `Mathlib.RingTheory.FiniteType`. This avoids introducing an A-algebra
  structure on B independent of alpha.

Source verification: read `literature/stacks-project/varieties.tex`,
`lemma-change-fields-flat` (Tag 0C4Y), and `algebra.tex`,
`lemma-finite-type-descends` (Tag 00QP), including the coefficient-subalgebra
proof. Also read the current blueprint's
`sec-abelian-varieties/sk-prop-av-ntorsion-etale/lem-sc-mult-n-etale-kernel.proof.md`.
The node deliberately gives an agent-written conditional auxiliary result,
not a verbatim statement from Stacks or the current unit. The docstring
records its four proof steps, including the inverse 1/c among final generators.

Edge cases checked: K = k; u = 1; empty lists of algebra generators and tensor
coefficients; no finiteness of A, B, C, M, or N; different field/algebra/module
universes. If B is the zero ring, qK cannot be prime, exactly as in the node.
The condition u outside qK rules out the vacuous zero localization at u = 0.
The chosen c is outside the contraction; no unit or nonzero-divisor assumption
on c is imposed. Nothing is restricted to finite or algebraic field extensions.
There is no statement dispute or other node fault.

Searches for an existing statement (all via prescribed msearch.py, Q129/item):

- LeanFinder: "Finite type near a contracted prime from a principal localization
  after a field extension assuming module surjectivity descends on neighbourhoods".
  Eight hits, including `RingHom.finiteType_ofLocalizationSpanTarget`,
  `RingHom.finiteType_ofLocalizationSpan`, and localization/finite-module facts;
  no pointwise conditional field-extension descent statement.
- Loogle: `Algebra.FiniteType, Localization.Away`. Nine hits, including
  `instFiniteTypeAway`, `Algebra.FiniteType.of_span_eq_top_target`, and
  `Localization.exists_finite_awayMapₐ_of_surjective_awayMapₐ`. These assume
  global finite type, a covering, or integrality; none is this statement.
- Mathlib grep: `finiteType.*(desc|[Ll]ocal|[Tt]ensor)|[Ff]inite[Tt]ype.*[Ff]ield`
  under RingTheory. Twenty-five hits. Global faithfully flat descent in
  `Finiteness/Descent.lean` and localization results are component lemmas only.
- LeanSearch: "finite type of localized scalar extension descends near contracted
  prime of a field extension". Eight hits on module localization, finite
  presentation and residue fields; no match.
- Local rg in both `lean/WeilConjectures` and `lean/Sheaf` for finite-type,
  field, neighbourhood, contraction and fieldExtension naming combinations,
  plus the upstream names index: no declaration states this result.
  The required literal item-id grep in `lean/WeilConjectures` has no hit.
  The broader field/finite-type search found unrelated geometric declarations.

Validation: prescribed `scompile.py` compiled the complete module cleanly in
both sandbox mode and the intended library-module mode; no warnings or errors.
All theorem proofs in this delivery are `sorry`, and there are no data definitions.

## Second reading by Q129

I separately reread the node and final file after elaboration. The explicit
`hdesc` retains the node's conditional principle; the theorem is not silently
strengthened by deleting it merely because its dependency has a declaration.
Both occurrences of finite type are on the exact composites specified above.
`Ideal.comap` is the contraction used in the node; the conclusion uses c outside
that ideal. Arbitrary modules, empty generating sets, and distinct universes
remain permitted. No mathematical mismatch was found, and no node correction
was made. This is a worker self-check; the maintainer performs the independent
review required by this dispatcher brief (no subagents are authorized).
