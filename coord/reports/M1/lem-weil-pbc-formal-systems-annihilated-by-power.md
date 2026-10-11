## Worker report

The module `lean/Sheaf/AlgebraicGeometry/CoherentFormalModuleAnnihilated.lean` states the
four-way equivalence, the finite-cover doubling bound, and the commutative algebra reduction
fact. All three theorem proofs are `sorry`; it introduces no definitions or instances.
No statement correction, missing dependency, or disputed statement was found.

Hypotheses and setup:

- The Noetherian scheme is `(X : Scheme.{u}) [IsNoetherian X]`.
- The quasi-coherent ideal sheaves are `(I K : X.IdealSheafData)`; this is the shared
  closed-subscheme ideal encoding, not arbitrary submodules of the structure sheaf.
- The two coherent formal systems and their compatible morphism are
  `(F G : CoherentFormalModule X I) (α : F ⟶ G)`.
- An affine open is `U : X.affineOpens`. Its ring A is `Γ(X, U.1)`, and its ideal K is
  `K.ideal U`. No choice of affine presentation, or extra trivialization hypothesis, is
  imposed. Quasi-coherence identifies these ideals with the tilde ideal sheaves on U.
- The map alpha_U is `(lim.map (Functor.whiskerRight α.hom
  (SheafOfModules.evaluation X.ringCatSheaf (op U.1)))).hom`. Its source and target are
  literally the inverse limits of F_n(U) and G_n(U) in modules over A. The affine
  dependency theorem identifies this limit, by its limit cones and naturality, with
  the underlying A-linear map of finite modules over the I-adic completion. Restricting
  scalars does not change the kernel or quotient by the image, nor annihilation by
  K^t, which is an ideal of A. Thus this is exactly the map of the node; its completed
  scalar action and finiteness are supplied by that shared equivalence rather than
  added as hypotheses or independently redefined here.

Clauses:

1. The first entry of `List.TFAE` is `∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ, ...`: each product
   of the t-th ideal-sheaf power with `kernel (α.hom.app (op n))` and with
   `cokernel (α.hom.app (op n))` is `IsZero`. These are kernels and cokernels in
   X.Modules. The dependency convention `op n` is positive level n+1, so all and only
   the positive levels of the node are quantified, with one uniform exponent.
2. The second entry is `∀ U : X.affineOpens, ∃ t : ℕ, 1 ≤ t ∧ ...`. The two ideal
   inclusions `K.ideal U ^ t ≤ Module.annihilator ...` kill the linear-map kernel and
   the inverse-limit target modulo its image, respectively. The exponent may depend
   on U, and is the same for both modules on that U.
3. The third entry quantifies `r : ℕ`, `U : Fin r → X.affineOpens`, and a single
   positive `t`, with `(⨆ i, (U i).1) = ⊤`. It imposes the same two annihilator
   inclusions on each member. Fin r models every finite affine covering, including
   the empty covering of the empty scheme. Taking the maximum permits a common
   exponent without strengthening the finite-cover condition.
4. The fourth entry chooses `k : KernelFork α` and `c : CokernelCofork α`, with
   `Nonempty (IsLimit k)` and `Nonempty (IsColimit c)`. These universal properties
   specify the kernel and cokernel in the formal category itself, independently of
   any choice of representatives or an Abelian instance. The positive uniform t
   annihilates every level of their vertex objects via the shared ideal products.
   This is exactly the definition of formal-object annihilation, written for the
   shared power inclusion because `idealSheafPower` returns a module and its
   inclusion, rather than an `IdealSheafData` argument for `AnnihilatedBy`.
5. `List.TFAE` says that all four propositions are equivalent, not just one direction.
6. `coherentFormalModule_annihilated_double` takes a finite affine cover, a specified
   positive exponent t and its two annihilation conditions. Its conclusion kills
   the kernel and cokernel of every component by the sheaf power `2 * t`.
7. `LinearMap.ker_coker_reduction_annihilated_double` quantifies an arbitrary
   commutative A, modules M and N in independent universes, arbitrary ideals K and J,
   positive t, and u. Its hypotheses kill ker u and N/range u. These are precisely
   T and Q of the given exact sequence, up to their forced linear isomorphisms;
   conversely the canonical kernel inclusion and quotient projection give such an
   exact sequence. The reduced map is `Submodule.mapQ` for `J • ⊤` in M and N,
   using Mathlib's `Submodule.smul_top_le_comap_smul_top` (no postponed definition).
   Its kernel and quotient by its range are annihilated by `K ^ (2 * t)`.
   No finiteness or Noetherian hypothesis is imposed on this algebraic clause.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.CoherentFormalModule`: `AlgebraicGeometry.CoherentFormalModule`,
  `IsCoherentFormalModule`, the `.hom` natural transformations, and the positive-index
  convention. Ideal multiplication and powers are its shared `Scheme.idealModuleProduct`
  and `Scheme.idealSheafPower` from `Sheaf.AlgebraicGeometry.IdealModuleProductStalk`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`:
  `AlgebraicGeometry.coherentFormalModules_affine`, including its natural limit cones,
  surjective projections with I-power kernels and completed scalar-action clause.
  This justifies the intrinsic inverse-limit presentation above; no new equivalence.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian`:
  `AlgebraicGeometry.coherentFormalModule_abelian`, providing the abelian category and
  the termwise-cokernel identification. Universal forks avoid assuming an extra
  structure as a hypothesis.
- `Mathlib.RingTheory.AdicCompletion.Basic` / `.Algebra`: `AdicCompletion` and its
  algebra structure, used through the affine theorem rather than redefined.
- Mathlib's `SheafOfModules.evaluation`, `lim`, `Functor.whiskerRight`, module
  annihilators, quotient modules, and `Submodule.mapQ` supply all other notions.

Edge cases checked before writing: the empty scheme admits r=0 and t=1; there is no
Nonempty index hypothesis. Zero systems and zero maps retain the exact kernel/cokernel
conditions. K=0 kills all modules for positive t; K=O_X forces kernel and cokernel
vanishing. I=0 allows constant systems, and I=O_X forces zero components; both fit
all four conditions. The quantifier n : ℕ denotes n+1 and does not accidentally add
level zero; all exponents are positive. The algebraic theorem allows zero rings,
J=0 (the original map), J=top (zero quotients), non-Noetherian rings, and unrelated
module universes v,w. No characteristic restriction appears.

Searches (2026-10-11):

- msearch.py leanfinder, query "kernel and cokernel of morphism of coherent formal
  modules annihilated by power of ideal": eight hits on local cohomology and adic
  completion; none states the equivalence or cover bound.
- msearch.py loogle, query "LinearMap.ker, Submodule.mapQ": one hit
  `Submodule.ker_mapQ`, a quotient-kernel computation, not this statement.
- msearch.py grep, query "annihilat.*(kernel|cokernel)|formalModule", AlgebraicGeometry:
  zero hits.
- msearch.py leansearch, query "coherent formal inverse systems kernel cokernel
  annihilated by an ideal power": service unavailable, Internal Server Error.
- rg on WeilConjectures for annihilation and the item id: unrelated annihilator uses,
  no formal-system equivalence and no tagged declaration for the item. The upstream
  name index (`tools/lean_names_upstream.py show <item>`) gives no attachment.
- rg on lean/Sheaf for annihilation and formal systems: the shared definitions and
  the affine/abelian dependencies; no four-way equivalence or cover bound. The
  already-landed `Sheaf.RingTheory.KernelCokernelAnnihilatedModIdeal` contains the
  stronger three-part scalar quasi-inverse/naturality/reduction/converse package.
  The algebraic statement here states only the final clause of this item's own node,
  without copying any notion or canonical-map definition. Its stage-3 proof may
  use clause (c) of that package. Fresh declaration names were searched in Mathlib,
  WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json: no collisions.

Source: the local Stacks checkout is absent on this machine, so the original text was
read at [Stacks Remark 0888](https://stacks.math.columbia.edu/tag/0888).
Conditions (1)-(3) and the doubling argument agree with that source; the node explicitly
adds (4) via the shared abelian-category description. No source correction is needed.

Validation: server scompile.py completed in 3.6 seconds with exit code 0 and no warnings.

## Second reading by M1

I reread the node statement, its seven proof steps, the dependency declarations, and
the Lean module item by item. The setup is rendered by `(X : Scheme.{u})
[IsNoetherian X]`, `(I K : X.IdealSheafData)`, coherent formal modules `F G` over
`I`, and `α : F ⟶ G`; this matches the node's Noetherian scheme, two
quasi-coherent ideal sheaves, and compatible system morphism. The four `List.TFAE`
entries render respectively: a uniform positive power killing every component
kernel and cokernel; affine-open annihilator conditions for the inverse-limit map
and its cokernel; a finite `Fin r` affine cover with one common exponent; and
kernel/cokernel forks with their universal properties and one common exponent.
The affine map is exactly the limit of evaluated section maps, and the quotient is
the module quotient by its linear-map range. The two companion declarations render
the finite-cover doubling bound and the stated arbitrary-commutative-ring
reduction fact, with independent module universes and no finiteness assumptions.
All quantifier orders and hypotheses agree; `op n` is the positive level `n+1` used
by `CoherentFormalModule`.

Edge cases checked: `r = 0` is available for the empty scheme, while the cover
equation prevents it for a nonempty scheme; zero systems and zero maps; `n = 0`
as level one; zero and unit ideals; `t = 1`; zero rings and `J = 0` or `J = ⊤` in
the algebraic clause; arbitrary characteristic and independent module universes.
No extra hypotheses or universe restrictions occur. Searches with LeanFinder,
Loogle, grep over Mathlib, WeilConjectures, and `lean/Sheaf`, plus the upstream-name
index, found no existing equivalent declaration. The local Stacks checkout is
absent; the cited Remark 0888 and Lemmas 087W/087X were checked from the referenced
source. No mismatch was found and no source or statement correction was needed.

The module compiles cleanly with `scompile.py`; all proofs remain the required
named `sorry`s and every declaration docstring cites the blueprint.
