## Worker report

Group Q04, stage 2, item lem-per-ideal-torsion-preserves-injectives, 2026-10-19.

The module `Sheaf.Algebra.Homology.IdealPowerTorsionInjective` states
`ModuleCat.idealPowerTorsion_obj_injective`. Its only theorem has proof `sorry`.
There are no new definitions, dependency repairs, new nodes, or statement changes.

Clause-by-clause correspondence:

- The commutative ring A is `{A : Type u} [CommRing A]`.
- Noetherian is `[IsNoetherianRing A]`, the recorded Mathlib definition that every
  ideal is finitely generated.
- The arbitrary ideal K is `(K : Ideal A)`; neither properness nor a separate
  finite-generation hypothesis is imposed.
- The arbitrary A-module E is `(E : ModuleCat.{u} A)` and its injectivity is
  `[CategoryTheory.Injective E]`, exactly the recorded categorical definition.
  There is no `Module.Finite A E` hypothesis.
- The torsion submodule Γ_K(E) is `((idealPowerTorsion K).obj E)`, using the
  dependency's actual functor, not a new predicate or construction.
- In that definition the underlying submodule is `Ideal.primaryComponent E K`.
  Its `primaryComponent_mem` equivalence says that there exists `n : ℕ` with
  membership in `Submodule.torsionBySet A E (K ^ n)`. The latter's
  `mem_torsionBySet_iff` means every `a ∈ K ^ n` annihilates the element.
  Thus both the existential exponent and the universal annihilator condition
  are precisely the stated ones, including exponent zero.
- Injectivity as an A-module, rather than over A/K, is the conclusion
  `CategoryTheory.Injective ((idealPowerTorsion K).obj E)` in `ModuleCat A`.
  Ring and modules are in one arbitrary universe `u`, matching the recorded
  functor and the node's Baer proof's common-universe convention; `u` is not
  fixed to the small universe. Every variable and universe is explicitly bound.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and
  `isNoetherianRing_iff_ideal_fg` (def-weil-pbc-noetherian-ring).
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`:
  `CategoryTheory.Injective`, whose `factors` extends each map across every
  monomorphism (the injectivity clause of def-sp-injective-resolutions).
  I also read `CategoryTheory.InjectiveResolution` in the recorded Resolution
  module; this statement does not require a resolution.
- `Sheaf.Algebra.Homology.IdealPowerTorsionFunctor`:
  `ModuleCat.idealPowerTorsion` (def-sbc-ideal-power-torsion-functor). Its object
  is the primary-component submodule, and its maps restrict the original maps.
- Proof-only imports are `Mathlib.Algebra.Category.ModuleCat.Injective`, giving
  `Module.injective_iff_injective_object` and `Module.Baer.iff_injective`
  (lem-sf-baer-criterion), and `Mathlib.RingTheory.Filtration`, giving
  `Ideal.exists_pow_inf_eq_pow_smul` (lem-weil-pbc-artin-rees).

The docstring transcribes all six reviewed proof steps. It uses finite generation
only for the domain ideal J and applies Artin–Rees only to the finite module A.
The well-defined linear map on J + K^n and the torsion-valued extension are
explained explicitly. This alternative proof is honestly attributed to the
node's agent-written argument. The statement itself is exactly Stacks 08XW (2),
read in `literature/stacks-project/dualizing.tex`, lemma-injective-module-divide.

Edge cases checked before writing: K = 0 gives the whole E (exponent 1); K = A
gives the zero submodule, since every power contains 1; nilpotent K gives E;
E = 0 and the zero ring are included. At n = 0 the condition is A x = 0, hence
x = 0, which adds exactly the zero element. Empty generating families for J = 0
are covered by m = 1 + sum m_i in the proof. No domain, locality, nonzero-ring,
proper-ideal, or finiteness-of-E assumption has been introduced.

Searches performed using the prescribed msearch.py wrapper:

- LeanFinder: "Over a commutative Noetherian ring the submodule of an injective
  module annihilated by powers of an ideal is injective". Eight hits, including
  `AdicCompletion.map_injective`, `Ideal.exists_pow_inf_eq_pow_smul`, and Krull
  intersection lemmas; none states injectivity of the torsion submodule.
- Loogle: `Ideal.primaryComponent, Module.Injective`. Zero hits.
- Mathlib grep: `(injective.*(primaryComponent|[Tt]orsion)|primaryComponent.*[Ii]njective)`
  in `Algebra/Module`. Six hits about injective functions, torsion-free modules,
  or submodule maps, not injective objects. Read the primary-component file and
  the module and categorical injectivity files directly.
- `rg` in the upstream WeilConjectures tree and the project's `lean/Sheaf` for
  `idealPowerTorsion`, injectivity and torsion, and primary-component injectivity:
  the functor and its derived constructions exist; no theorem gives this item.
  In particular the local-cohomology sum spectral sequence cites this item in
  its proof Step 3 but does not state it. The torsion-injective-subcomplex result
  concerns abelian sheaves and is different. The upstream blueprint-id grep
  returned no hit. The upstream-name index has only unrelated primary-component
  base-change and quotient results.

No statement dispute or mathematical node fault was found. The previous worker's
stale-assignment conclusion confused stage 1 with stage 2: Q18's ledger entry at
line 41742 explicitly lands the stage-1 split, its report says it writes no Lean,
and the current node has no `lean` record. This delivery leaves that reviewed
split unchanged and adds only its stage-2 Lean binding.

Compilation and delivery checks are performed with scompile.py and deliver2.py;
no direct git command, live source edit, or global build is used.

## Second reading by Q04

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
