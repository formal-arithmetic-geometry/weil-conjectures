## Worker report

Delivered module: `Sheaf.AlgebraicGeometry.AdequateModuliEtaleLocality`.
It states the two clauses of the node as
`CategoryTheory.adequateModuliSpace_iff_etale_family` and
`CategoryTheory.adequateModuliSpace_iff_affine_global_power`.
Both proofs are `sorry`; there are no definitions or auxiliary postponed theorems.
The node's mathematical statement is unchanged.

Source checked: Alper, arXiv:1005.2398v3,
https://arxiv.org/html/1005.2398v3, Lemma 4.1.8(3), Remark 4.1.3,
Definition 5.1.1, Propositions 4.2.1(3),(4) and 5.2.9(1),(2).
The introduction also states explicitly that the affine-target definition is
exactly the two global conditions. The proof docstrings carry the six DAG steps:
affine direct image for the affine criterion, then test-stack comparison,
sheaf gluing, finite affine refinement and faithful-flat cokernel descent.

Hypotheses and conclusions, clause by clause:

- The field is `{k : Type u} [Field k]`. The stack is the arbitrary
  `F : BasedCategory.{v, w} (Over (Spec (CommRingCat.of k)))` with
  `hF : IsAlgebraicModuliStack F`; the two stack universes are independent.
- The target space is `Y : AlgebraicSpace (Spec (CommRingCat.of k))`.
  The map is `φ : BasedFunctor F (discreteModuli Y.obj.obj)`.
  Both qcqs assumptions are explicit: `hqc` is the exact universe instance of
  `IsQuasiCompactAlgebraicModuliMap` used by `IsAdequateModuliSpace`, and `hqs`
  is `IsQuasiSeparatedAlgebraicModuliMap φ`.
- An arbitrary family is `I : Type z`, `Yᵢ : I → AlgebraicSpace ...`, and
  `p : ∀ i, Yᵢ i ⟶ Y`. The assumption `hp : ∀ i, IsChartwiseEtale (p i)`
  is chartwise etaleness, not the stronger scheme-representable-map condition.
  The assumption `hsurj : IsJointlySurjective (fun i ↦ (p i).hom.hom)`
  is the existing joint surjectivity on field-valued point classes.
- The first conclusion is an `↔` between `IsAdequateModuliSpace F hF Y φ`
  and the same property for every actual two-fibre product. The product is
  `moduliTwoFiberProduct (discreteModuliMap (p i).hom.hom) φ` and the map to
  `Yᵢ i` is its actual first projection `moduliTwoFiberFst ...`. The factor
  order is reversed relative to the written `Z ×_Y Y_i`; both are the same
  two-fibre product up to its canonical exchange. No arbitrary projection is used.
- The predicate takes a proof of algebraicity as an argument. Accordingly the
  local side binds `∃ hFi : IsAlgebraicModuliStack ..., IsAdequateModuliSpace ...`.
  This supplies a witness instead of adding a hypothesis. Algebraicity follows
  from the node's fibre-product input. Proof irrelevance makes its choice immaterial.
- The arbitrary quasi-coherent algebras on each base change are quantified inside
  the imported `IsAdequateModuliSpace`, whose definition was read in full.
  It quantifies `A B` on that base change, not only restrictions from `F`.
- For the affine clause the target is literally the representable algebraic space
  `schemeSpace (Over.mk c)`, with `C : Type u`, `[CommRing C]` and arbitrary
  `c : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of k)`. This includes all
  commutative k-algebras, without requiring a chosen `Algebra` instance or a
  finite-type hypothesis. `φ` is a map to its existing discrete groupoid.
- The affine structural-isomorphism clause is
  `∀ t : moduliGlobalSectionsRing (moduliStructureSheaf F hF.1.1), ∃! r : C, ...`.
  The equality following `∃!` says at EVERY object `x` that `t` is the pullback
  of `r`. The morphism of schemes used there is exactly the Yoneda preimage of
  `(φ.obj x).hom`, after the source transport supplied by `φ.w_obj x`.
  `Scheme.ΓSpecIso ... .inv` converts the scalar into the regular function on
  its spectrum, and `Scheme.Γ.map` pulls it back. `ULift.up` is exactly the
  coefficient transport of the existing `moduliStructurePresheaf`, not a new ring.
  These pullbacks are automatically compatible by functoriality. Thus unique
  preimages of every compatible family express bijectivity of the CANONICAL
  ring map `C → Γ(F,O_F)`, hence its being an isomorphism. This avoids choosing
  an unrelated ring isomorphism and does not replace global functions by a chart.
- The second affine conjunct quantifies all `A B : ModuliAlgebraSheaf F hF.1.1`,
  requires `IsQuasicoherentModuliAlgebra A` and the same for `B`, and quantifies
  `f : A ⟶ B` with `IsSurjectiveModuliAlgebra f`. The latter is fppf-local
  surjectivity of sheaves, not objectwise surjectivity. For every
  `b : moduliGlobalSectionsRing B.right`, the conclusion is `∃ n : ℕ, 0 < n ∧`
  `∃ a : moduliGlobalSectionsRing A.right, ∀ x, ... = (b.1 x) ^ n`.
  Equality at every object is precisely equality of global sections. There is
  no finite-generation assumption on either algebra and no uniform exponent
  assumption as the surjection or target section varies.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.AdequateModuliSpace`:
  `CategoryTheory.IsAdequateModuliSpace` (read its full definition).
- Its public dependencies `StackQcqsMorphism`, `AlgebraicModuliStack`,
  `StablePointedModuliGroupoids` and `StackQuasiCoherentAlgebra` supply
  `IsQuasiCompactAlgebraicModuliMap`, `IsQuasiSeparatedAlgebraicModuliMap`,
  `IsAlgebraicModuliStack`, `discreteModuli`, `discreteModuliMap`,
  `moduliTwoFiberProduct`, `moduliTwoFiberFst`, `ModuliAlgebraSheaf`,
  `IsQuasicoherentModuliAlgebra`, `IsSurjectiveModuliAlgebra`,
  `moduliGlobalSectionsRing`, and `moduliStructureSheaf`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace` supplies `AlgebraicSpace` and its
  full subcategory morphisms. Its chartwise definition was also read.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite` directly supplies
  `AlgebraicGeometry.AlgebraicSpace.IsChartwiseEtale` and `schemeSpace`.
  Their definition owners are `def-sfb-space-chartwise-etale-morphism` and
  `def-trf-scheme-algebraic-space`; their node records, definitions and docstrings
  were read. The module is a public statement import.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity` supplies
  `AlgebraicGeometry.AlgebraicSpace.IsJointlySurjective` (read in full).
- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.AlgebraicGeometry.Scheme`:
  `Spec`; `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
  Their signatures and docstrings were checked. The canonical spectrum/global
  functions isomorphism is the existing `Scheme.ΓSpecIso`.

Added to `stmt_deps` the already-landed definition nodes
`def-sfb-space-chartwise-etale-morphism`, `def-trf-scheme-algebraic-space` and
`def-trf-algebraic-space-jointly-surjective-family`, to expose precisely the
chartwise etaleness, representable target and covering hypotheses. Their node records are not changed. No new node or dependency repair
is required. The proof-only modules that already exist are imported with plain
`import`, including `ChartwiseEtalePermanence` (retained in `proof_deps` only),
`CohomologyColimit`, the relevant flatness modules,
`AlgebraicGeometry.Limits`, `Algebra.DirectSum.Module` and tensor right exactness.
The proof prerequisites without a recorded module are left for stage 3 and the
maintainer's later import propagation; no unstated proof prerequisite is assumed
as a hypothesis of either theorem.

Edge cases checked before writing:

- Empty family: permitted by `I : Type z`; joint surjectivity then forces the
  target empty. There is no `Nonempty I` hypothesis.
- Infinite family: permitted, with independent index universe `z`; finite
  refinement is needed only inside the proof on a quasi-compact affine test.
- Empty scheme / zero ring: permitted by `[CommRing C]`. The global-function
  clause still requires unique scalar preimages, so it does not silently make
  a nonzero scalar ring isomorphic to the zero ring on an empty stack.
- All characteristics: no characteristic assumptions. The positive exponent
  is `n : ℕ` with `0 < n`, so exponent zero cannot trivialize the requirement.
- Both the algebras on `F` and those inside each adequate base-change predicate
  are arbitrary; no finite-type or descendability condition is hidden.
- No arbitrary base-change algebraicity witness or arbitrary structural map is
  supplied as a hypothesis. The projection and scalar function pullbacks are fixed.

Searches made, on 2026-10-24:

- `msearch.py ... leanfinder "Adequate moduli spaces are etale local on the target
  and satisfy an affine global section power lifting criterion"`: eight hits,
  about ordinary scheme etaleness and affine-local ring properties; no match.
- `msearch.py ... leansearch "adequate moduli spaces etale locality affine global
  section power lifting"`: eight hits, about etale ring-map locality and affine
  scheme global sections; no adequate-moduli statement.
- `msearch.py ... loogle "CategoryTheory.IsAdequateModuliSpace,
  AlgebraicGeometry.AlgebraicSpace"`: zero hits, identifier unknown to Mathlib.
- `msearch.py ... grep "AdequateModuli|adequate.moduli" AlgebraicGeometry`:
  zero Mathlib hits.
- `rg -n -i "adequateModuli|adequate_moduli|lem-sfb-adequate-moduli-etale-locality"`
  in the read-only `lean/WeilConjectures` and `lean/Sheaf`: only the adequate
  definition and the related adequately-affine/finite-flat-groupoid modules;
  no existing statement of this locality or affine criterion.
  The finite-flat-groupoid module's `moduliAffineFunctionValue` was also read:
  it uses the same canonical scalar-pullback formula, but does not state either
  theorem and does not provide a global-section ring isomorphism criterion.

No `STATEMENT-DISPUTED` flag or mathematical correction is needed.
The prescribed example `CompactObject.lean` is currently withdrawn and contains
no declarations; the current `AdequateModuliSpace.lean` supplies the active header
and module conventions followed here.

Validation: `scompile.py NX lem-sfb-adequate-moduli-etale-locality` on the delivered
file passed both the sandbox and library module checks (3.5 seconds each), with
no errors or warnings. No local/global build was run.

## Second reading by NX

A second pass by this dispatcher-started worker compared both final signatures
with the full node statement and the source. No separate agent was started, as
required by the launcher's brief; the maintainer supplies independent review.

The first signature has exactly the field, algebraic stack, algebraic space,
qcqs map, arbitrary etale family and joint surjectivity hypotheses. Its conclusion
uses the actual base-changed map and the original adequate predicate, including
all algebras on the changed stack. The existential algebraicity proof is part
of expressing that predicate, not a new restriction. The affine signature keeps
both required conjuncts, uses actual compatible families on the original stack,
and specifies the canonical scalar pullback rather than an arbitrary isomorphism.
Every algebra, surjection, section and positive power quantifier is present.
The empty family and zero-ring cases are retained. No mismatch was found in this
pass; no node statement or source assumption was changed.

## Repair of return H2

Return reviewed immutable head `d03d88b6c7bd`. The restored sandbox matched that
returned delivery. A field-by-field comparison with the current shared main node
found only the intended delivery additions (`lean` and `stmt_deps`); every other
node field is unchanged. The delivery wrapper rebases the repaired files onto
the current server branch.

H2 repaired: removed `lem-trf-space-chartwise-etale-permanence` from `stmt_deps`
and replaced it with the existing definition owners
`def-sfb-space-chartwise-etale-morphism` and `def-trf-scheme-algebraic-space`.
Kept `def-trf-algebraic-space-jointly-surjective-family`. The public import is now
`EnlargedEtaleRingedSite`, which actually defines `IsChartwiseEtale` and
`schemeSpace`. `ChartwiseEtalePermanence` remains a plain proof-only import,
as required by its unchanged entry in `proof_deps`. Both theorem signatures and
proof bodies are byte-identical to the returned delivery, verified by comparing
the source from the first theorem onward before and after the import repair.
The mathematical statement and all earlier clause-by-clause checks stand.

Repair validation: the prescribed `scompile.py` passed the sandbox check in
17.1 seconds and library check in 3.6 seconds, with no errors or warnings.
