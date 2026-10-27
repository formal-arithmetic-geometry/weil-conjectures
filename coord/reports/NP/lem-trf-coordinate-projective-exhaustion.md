## Worker report

The module `Sheaf.RingTheory.CoordinateProjectiveExhaustion` states
`Module.exists_coordinate_projective_exhaustion`, with its sole proof `sorry`.
The node's mathematical statement, dependencies, proof, and other metadata are unchanged;
only `lean` is supplied. There are no new nodes, dependency repairs, helper definitions,
or statement corrections. No statement dispute was found.

Sources read: Stacks Project `algebra.tex`, Tag 05A9,
`theorem-ffdescent-projectivity`, including its initial, limit, successor, and exhaustion
paragraphs; the current blueprint `latest`, ancestor
`lem-trf-local-term-locality.proof.md`, (1)--(2). The auxiliary node abstracts the
successor construction of 05A9 as a hypothesis and does not assume the faithfully flat
hypotheses used there to obtain that construction. The module docstring carries all six
accepted DAG proof steps, with totalized recursion, monotonicity, the coordinate invariant,
finite-expression limit argument, stationary quotient, and exhaustion.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The commutative ring homomorphism `A → B` is `[CommRing A] [CommRing B]
  [Algebra A B]`. For commutative rings, the algebra structure is precisely a chosen
  unital ring homomorphism; no injectivity, flatness, or faithful flatness is required.
- `M : Type w`, `[AddCommGroup M] [Module A M]` is the specified A-module. The set of
  indices is `I : Type s`; `Q : I → Type t` with componentwise additive-group and
  B-module instances is an arbitrary family of B-modules. All five size universes are
  independent and explicitly declared; no countability, generation, or projectivity
  hypothesis is imposed on `I`, `M`, or any `Q i`.
- `θ : (B ⊗[A] M) ≃ₗ[B] DirectSum I Q` is exactly the fixed B-linear isomorphism.
- The coordinate submodule `D_H` is the already landed
  `DirectSum.coordinateSubmodule B I Q H`, whose carrier is the finite-support families
  with every coordinate outside `H` zero. Its source and docstring were read.
- `T(U)` is written directly as `(U.baseChange B).map θ.toLinearMap`. In Mathlib's
  `TensorProduct.Tower`, `Submodule.baseChange` is definitionally
  `LinearMap.range (U.subtype.baseChange B)`, and `LinearMap.baseChange` sends
  `b ⊗ u` to `b ⊗ U.subtype u`. Thus this expression is the specified inclusion-induced
  tensor image transported by θ, even for a non-flat homomorphism. No new tensor-image
  notion or arbitrary map is introduced.
- `henlarge` quantifies over every `U : Submodule A M` and `H : Set I` with exactly
  `T(U) = D_H`, then every `x : M` with `x ∉ U`. Its witnesses `V`, `H'` satisfy,
  in order, `U ≤ V`, `x ∈ V`, `H ⊆ H'`, and `T(V) = D_H'`.
- In that same hypothesis `V/U` is `V ⧸ U.comap V.subtype`. Because the witness also
  includes `U ≤ V`, the denominator is precisely U viewed inside V. Countable generation
  is `∃ S : Set (V ⧸ U.comap V.subtype), S.Countable ∧ Submodule.span A S = ⊤`;
  `span` uses finite linear combinations and `Set.Countable` means at most countable.
  Projectivity is exactly `Module.Projective A (V ⧸ U.comap V.subtype)`.
- The fixed well-order on the underlying set of M is `[LinearOrder M]` together with
  `(κ : Ordinal.{w}) (e : Set.Iio κ ≃o M)`. An order isomorphism from the ordinal's
  initial segment both gives the specified enumeration and certifies that the order
  on M is well-founded. A separate well-foundedness hypothesis would repeat this fact.
  This is a fixed order and fixed enumeration, universally bound before the conclusion;
  the theorem does not choose a different enumeration or existentially weaken it.
- The two families indexed by all `α ≤ κ` are
  `F : Set.Iic κ → Submodule A M` and `H : Set.Iic κ → Set I`.
  `Monotone F ∧ Monotone H` gives exactly both increasingness assertions.
- `F ⟨0, bot_le⟩ = ⊥`, `H ⟨0, bot_le⟩ = ∅`, and `F ⟨κ, le_refl κ⟩ = ⊤`
  are the three stated initial/terminal conditions. No terminal condition on H is added:
  zero summands can leave unused indices.
- For every `α : Set.Iic κ`, the first universally quantified conclusion is exactly
  `((F α).baseChange B).map θ.toLinearMap = coordinateSubmodule B I Q (H α)`.
- For every `l : Set.Iic κ` with `Order.IsSuccLimit l.val`, the next two conjuncts give
  `(F l : Set M) = ⋃ (α : Set.Iic κ) (_ : α < l), (F α : Set M)` and the identical
  indexed-union identity for H. On ordinals `IsSuccLimit` means a nonzero limit, so
  these assert the two exact set unions requested, not just lattice suprema.
- Every `α : Set.Iic κ` with `hα : α.val < κ` has successor index
  `⟨Order.succ α.val, Order.succ_le_of_lt hα⟩`. Its quotient is the successor
  submodule modulo `(F α).comap successor.subtype`, as required. The first two
  successor conjuncts state existence of an at most countable spanning subset and
  `Module.Projective A` for this quotient.
- The third successor conjunct, conditional on `F α ≠ ⊤`, supplies `x ∉ F α`,
  `∀ y : M, y < x → y ∈ F α`, and membership of x in the successor module.
  In the fixed linear order these first two properties say precisely that x is the
  least missing element. No particular choice beyond leastness is assumed.
- The fourth successor conjunct, conditional on `F α = ⊤`, says both successor
  families equal their predecessors. This is the exact stationary branch of the node.
- The final conjunct `∀ (α : Set.Iic κ) (β : Set.Iio κ), β.val < α.val → e β ∈ F α`
  renders the stated inclusion of every earlier enumerated element, through the endpoint.

Dependency declarations used, with their complete recorded signatures and docstrings read:

- `def-weil-pbc-module-tensor-product`: Mathlib `TensorProduct`, `TensorProduct.mk`,
  `TensorProduct.lift`, `TensorProduct.ext'`, and `LinearMap.rTensor` in
  `Mathlib.LinearAlgebra.TensorProduct.{Defs,Basic,Map}`; the B-linear specialization is
  `LinearMap.baseChange` and its range `Submodule.baseChange` in
  `Mathlib.LinearAlgebra.TensorProduct.Tower` (public import).
- `def-weil-pbc-direct-sum-modules`: `DirectSum`, `DirectSum.instModule`,
  `DirectSum.lof`, `DirectSum.component`, `DirectSum.induction_on` in
  `Mathlib.Algebra.DirectSum.{Basic,Module}`, publicly available through CoordinateSubmodule.
- `def-trf-coordinate-submodule`: `DirectSum.coordinateSubmodule` in
  `Sheaf.RingTheory.CoordinateSubmodule` (public import, unchanged).
- `def-weil-pbc-projective-module`: `Module.Projective` in
  `Mathlib.Algebra.Module.Projective` (public import); its free-summand and lifting
  characterization is the standard recorded notion, not a second definition.
- `def-weil-pbc-quotient-module`: `Submodule.hasQuotient`, `Submodule.Quotient.module`,
  `Submodule.mkQ`, `Submodule.mkQ_surjective`, `Submodule.ker_mkQ` in
  `Mathlib.LinearAlgebra.Quotient.{Defs,Basic}` (public import of Basic).
- Proof-only dependencies `lem-weil-pbc-well-ordering-theorem` and
  `lem-weil-pbc-transfinite-recursion`: `exists_wellFoundedLT` in
  `Mathlib.SetTheory.Cardinal.Order` and `WellFoundedLT.fix`, `WellFoundedLT.fix_eq`
  in `Mathlib.Order.RelClasses` (plain imports).
- The countability and ordinal notation needed by the signature are imported publicly
  from `Mathlib.Data.Set.Countable` and `Mathlib.SetTheory.Ordinal.Basic`.

Edge cases checked before writing:

- `M = 0` as a module has a singleton underlying set, so its well-order has type 1,
  not 0. The initial zero submodule is already top; every successor is stationary,
  the quotient is zero, and the sole enumerated element belongs at the endpoint.
  The conditional successor branches and the spanning-set existential permit this.
- There is no missing empty-module case: modules have zero. The binder `e` cannot exist
  for κ = 0 and a nonempty module, exactly as for an actual order type.
- Empty I, all zero summands, zero rings, and a non-flat map are not excluded. A zero
  tensor image is allowed at every stage, and H need not exhaust I. The successor
  property alone supplies any required projective quotient.
- Both successor and nonzero-limit order types are included. The successor index proof
  uses only α < κ; nonzero-limit continuity is required at the endpoint too when relevant.
- Early stabilization forces equality of both families on subsequent successors. The
  zero quotient is spanned by the empty set, so the countability encoding includes it.
- The limit proof handles empty pure-tensor expressions and empty coordinate supports
  by using stage zero below a nonzero limit. The formulation uses images, so it never
  silently requires tensoring an inclusion to be injective.

Searches made on this item (the prescribed search wrapper also recorded the raw results):

- `leanfinder`: "A successor enlargement property produces an exhaustive continuous
  ordinal filtration of a module with countably generated projective successive quotients";
  eight hits: `Field.Emb.Cardinal.iSup_filtration`, `IsModuleFiltration`,
  `Field.Emb.Cardinal.directed_filtration`, `Field.Emb.Cardinal.filtration_succ`,
  `Ideal.Filtration`, `Field.Emb.Cardinal.filtration_apply`,
  `Field.Emb.Cardinal.filtration`, `Ideal.Filtration.Stable`. None is this theorem:
  they concern field extensions, graded filtrations, or ideal-adic filtrations.
- `loogle`: `Submodule, Ordinal, Module.Projective`; zero hits.
- Mathlib `grep` wrapper:
  `((transfinite|ordinal|exhaustive).*(filtration|submodule))|((filtration|submodule).*(transfinite|ordinal))`;
  zero hits.
- `leansearch`: "continuous exhaustive transfinite filtration of submodules from a
  successor enlargement property"; eight hits including `IsModuleFiltration`, its
  `toIsFiltration`, `Field.Emb.Cardinal.filtration_succ`, ideal filtration definitions
  and recursors, and a measure-theory filtration lemma. No exact match.
- Direct `rg` over Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and the upstream
  declaration index found no declaration with the new theorem's name or the coordinate
  projective exhaustion statement. The exact blueprint-id search in WeilConjectures
  likewise found nothing.
- The concept search in `lean/Sheaf` found
  `DirectSum.exists_invariant_coordinate_transfinite_filtration` and
  `Module.nonempty_linearEquiv_directSum_of_split_transfinite_filtration`; both full
  modules were read. The first concerns an endomorphism-invariant filtration of the
  coordinates themselves from prescribed countable blocks. The second identifies an
  already supplied split filtration with its direct sum of quotients. Neither constructs
  this tensor-coordinate filtration from the assumed enlargement property. Mathlib's
  `IsModuleFiltration` and the field-extension filtration source were also read to rule
  out these search hits.

Validation: the delivered module compiled cleanly with `scompile.py`, in module mode,
against the live published library; the sandbox check and the library-name check both
passed (1.2 s and 1.8 s respectively). All variables and universes are explicitly bound;
`autoImplicit` is disabled, no local notation or instance is introduced, all Lean lines
are at most 100 characters, and the only postponed proof is the named theorem above.

## Second reading by NP

No second worker was started, as the dispatcher explicitly forbids delegation. The
maintainer's independent delivery review supplies the second reading under the current
worker-direct-delivery procedure. The correspondence above is the author's own check.
