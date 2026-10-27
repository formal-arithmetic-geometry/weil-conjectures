## Worker report

Item: lem-trf-principal-support-quotient-exact. The module
`Sheaf.AlgebraicGeometry.PrincipalSupportQuotientExact` states both numbered
clauses, using four named theorems with `sorry` proofs. It supplies the canonical
maps needed to name the objects in those clauses. No statement correction, new
independent notion, or dependency-interface repair is needed. Only the item's
`lean` record changes.

Hypotheses and constructions:

- The arbitrary commutative ring is `R : CommRingCat.{u}`. The chosen element
  is `a : R`. Each module is `ModuleCat.{u} R`; a common sufficiently large
  universe accommodates the ring and any three modules. There is no nonzero-ring,
  regular-element, finite-generation, or noetherian assumption.
- The maps are `i : N₁ ⟶ N₂`, `j : N₂ ⟶ N₃`. The short exact hypothesis is
  `Function.Injective i`, `Function.Exact i j`, `Function.Surjective j`, as
  explicitly prescribed by the exact-sequence dependency's module convention.
- Injectivity modulo every power is exactly
  `∀ n : ℕ, Function.Injective (QuotSMulTop.map (a ^ n) i.hom)`. This is the
  existing map `N₁/a^nN₁ → N₂/a^nN₂`; its case `n=0` is included.
- `T` is the recorded `Submodule.powTorsion R N a`, not a new torsion definition.
  Its sheafified inclusion is `principalTorsionι`. The existing torsion quotient
  is only packaged into `ModuleCat` by `principalTorsionQuotient`.
- `Spec R` is the recorded spectrum. The principal open inclusion is
  `Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen a)`, with Mathlib's
  open-immersion instance. `tilde N` is the recorded associated module sheaf.
- `principalSupportRestriction` is the unit of the actual restriction/direct-image
  adjunction for that inclusion. `principalSupportι` is its kernel inclusion.
  `principalSupportQuotient` is the cokernel of that inclusion, and
  `principalSupportπ` its cokernel projection. These are genuine constructions in
  `(Spec R).Modules`, the specialization of the recorded sheaf-of-modules category.
  `principalSupport_section_kernel` asserts for EVERY open `W` that the image of
  this inclusion is exactly the sections restricting to zero on `W ∩ D(a)`.

Clause (1):

- `principalSupport_basicOpen` quantifies over every `s : R`, hence every `D(s)`.
  Its first conjunct is injectivity of the component of the sheafified inclusion
  `T~ → N~`. These components ARE `T_s → N_s`: the recorded `tilde.toOpen`
  localization instance identifies the section modules with the localized modules,
  and `tilde.toOpen_map_app` identifies their maps with the localized inclusion.
- Its second conjunct says that the image of that component is the supported
  kernel's submodule. The third identifies that submodule, as a set of sections
  on `D(s)`, with `{x | ∃ n : ℕ, a ^ n • x = 0}`. Over `O(D(s)) = R_s`, this
  action is multiplication by `(a/1)^n`; thus it is precisely the node's
  `Γ_(a/1)(N_s)`, expressed in the actual canonical realization of `N_s`.
- `principalSupport_comparison` gives a family `e` of sheaf isomorphisms
  `T~ ≅ K` with `e.hom ≫ principalSupportι = principalTorsionι`. This is equality
  as submodules of `N~`, not just an abstract isomorphism. Being sheaf morphisms,
  these identifications commute with restrictions on arbitrary opens.
- The next conjunct is the naturality square for `e` and every `R`-linear map.
  `principalTorsionMap` is literal restriction of that map to power torsion;
  `principalSupportKernelMap` is Mathlib's kernel map from the naturality square
  of the open-restriction unit.
- The family `θ` is `Q ≅ (N/T)~`. The following conjunct states
  `principalSupportπ ≫ θ.hom = tilde.map (ModuleCat.ofHom T.mkQ)`, the required
  compatibility with maps out of `N~`. The final two conjuncts state the square
  defining the induced quotient map from `tilde f`, and naturality of `θ` for
  every linear `f`. `principalSupportQuotientMap` is the canonical cokernel map.

Clause (2):

- `principalSupportQuotient_exact` asserts injectivity, middle exactness and
  surjectivity of `principalTorsionQuotientMap a i` and the corresponding `j` map.
  These use upstream `Submodule.torsion'QuotientMap (Submonoid.powers a)`.
- The two following conjuncts explicitly give the coset formulas `[y] ↦ [i(y)]`
  and `[x] ↦ [j(x)]` on all representatives.
- The next conjunct asserts the zero composite and `ShortComplex.ShortExact`
  for the sheafifications of these quotient maps.
- The final conjunct asserts the same for the canonical `Q` maps induced from
  `tilde i` and `tilde j`. The family `θ` and its naturality squares in the
  comparison theorem identify these two short complexes including their arrows.
- All four statements have complete source/proof docstrings referring to the
  same DAG node. Steps 1–6 of the node are distributed between their docstrings;
  the printed Stacks last-variable typo is corrected as in the accepted node's
  proof (`x-i(z)`, not `x-y`). Every theorem proof remains `sorry`. Definitions
  contain actual maps; their structural proof fields use naturality, the kernel
  universal property, or the direct elementary check that linear maps preserve
  annihilation. No arbitrary comparison map or object is an input.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`:
  `CategoryTheory.ShortComplex.ShortExact`; its `Exact` is equivalent to
  image = kernel in the abelian category. The module convention on
  `def-weil-pbc-exact-sequence` explicitly authorizes the three `Function`
  predicates used for the algebraic sequence.
- `WeilConjectures.Mathlib.Algebra.Module.Torsion`:
  `Submodule.powTorsion`, its membership lemma, `powTorsion_eq_ker_localization`,
  `localized'_powTorsion`, and the canonical `torsion'QuotientMap` construction.
  The first declaration realizes both recorded power-torsion dependencies.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`.
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
  Their definitions are available through the public tilde import.
- `Mathlib.AlgebraicGeometry.Modules.Tilde`: `AlgebraicGeometry.tilde`,
  `tilde.toOpen`, `tilde.toOpen_res`, the basic-open localization instance,
  `tilde.map`, `tilde.toOpen_map_app`, `tilde.functor`, `tilde.adjunction`.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, a transparent alias of Mathlib's
  `SheafOfModules`; `(Spec R).Modules` uses precisely this existing category.
- `Mathlib.LinearAlgebra.Quotient.Defs` and `.Basic`:
  `Submodule.hasQuotient`, `Submodule.Quotient.module`, `Submodule.mkQ`,
  `mkQ_surjective`, `ker_mkQ`, the quotient-module dependency's Mathlib match.
- Proof imports: `WeilConjectures.AlgebraicGeometry.TildePreservesFiniteLimits`
  (`tilde_preserves_finite_limits`); `Mathlib.Algebra.Module.LocalizedModule.Exact`
  (`IsLocalizedModule.map_exact`, with injection/surjection in Basic);
  `Mathlib.Topology.Sheaves.SheafCondition.Sites` (`restrictHomEquivHom`,
  `extend_hom_app`, `hom_ext`, `isIso_iff_isIso_basis`). The remaining proof
  dependencies are already imported publicly for statements.

Edge cases checked before writing: zero ring/empty spectrum; zero modules;
`a=0` and general nilpotent `a` (T=N, D(a) empty, Q=0); unit `a` (T=0,
D(a)=Spec R, K=0, Q=N~); `s=0` (empty principal open); `n=0` (quotient by
1 is zero). No cancellation by `a` was used. The powerwise assumption is
substantive: for `0 → ℤ --2→ ℤ → ℤ/2 → 0` with `a=2`, quotienting by
power torsion loses middle exactness, while the map modulo 2 is not injective.
No statement dispute was found.

Searches on 2026-10-24:

- `msearch.py ... leanfinder "Quotient of associated sheaf by sections supported
  on a principal closed subset equals tilde of quotient by power torsion and
  preserves powerwise exact sequences"`: eight hits, tilde constructions and
  `Scheme.IdealSheafData.isLocalization_away`; no theorem giving these clauses.
- `msearch.py ... loogle '"torsion", Function.Exact'`: zero hits.
- `msearch.py ... grep 'powTorsion|supportedSections|supported.*[Qq]uotient'`:
  zero Mathlib hits.
- `msearch.py ... leansearch "Associated module sheaf quotient by sections
  supported on principal closed subset equals power torsion quotient"`: eight
  hits, generic torsion quotients, module support and tilde; no match.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for `powTorsion`,
  `principalSupport`, and supported-section quotient terminology found the
  existing upstream torsion API and the global blowup-specific
  `ModuleStrictTransform` API. The latter requires blowup data and defines a
  different object, so is not a replacement for arbitrary affine principal
  support. Exact item-id search in `lean/WeilConjectures` had no hits.
  The maps needed only by this item's statement are auxiliary declarations in
  its owning module, as expressly authorized by the launcher; no duplicate
  torsion, localization, quotient, or tilde construction is introduced.

Source check: read Stacks `divisors.tex`, Definition strict-transform (080D) and
Lemma strict-transform-universally-injective (080W) with its full algebra proof.
Read the current `literature/blueprint/latest/` local-term-locality statement and
proof; its modern contracting-correspondence route does not alter this inherited
algebra helper's accepted statement.

Validation: all files compiled separately through the prescribed `scompile.py`
against the live server build. Final preflight and delivery results are below.

## Second reading by Q15

Self-check only: the launcher forbids starting another agent and assigns the
independent reading to the maintainer's delivery review. I reopened the node and
module, checked the two numbered clauses and all hypotheses against the mapping
above, and added the explicit quotient-projection naturality square to make the
maps induced from `tilde f` visible in the statement. Checked that `K = T~` is
expressed compatibly with inclusions, not merely as an abstract isomorphism;
that both sheaf sequences use the canonical arrows; that no regularity or
finiteness assumption appears; and that all four theorems are recorded and have
only `sorry` proofs. No remaining mismatch found.

Dry run: `deliver2.py Q15 lem-trf-principal-support-quotient-exact --no-push`
returned `OK (dry run): commit 13d9ac8be28 passes the preflight and compiles;
nothing pushed`. No preflight repairs were required.
