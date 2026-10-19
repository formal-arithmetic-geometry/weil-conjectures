## Worker report

This stage-2 delivery states Stacks Project, Algebra, Tag 046Y
(`lemma-mod-injective-general`) as
`Algebra.local_essentially_finite_presentation_mod_injective` in
`Sheaf.RingTheory.LocalEssentiallyFinitePresentationModInjective`.
Its only theorem has proof `sorry`. There are no new definitions, helper theorems,
new nodes, dependency repairs, statement corrections, or disputed statements.

I read the current node, its three statement-dependency nodes and their recorded
interfaces, the example `CompactObject` module and its node, and the complete
statement and proof of Tag 046Y in `literature/stacks-project/algebra.tex`.
The node's statement agrees with that source. Its nine proof steps are reproduced
in the theorem docstring, including simultaneous arrow descent, propagation of
stage flatness, finite source-comparison kernels, the localization/colimit
identifications, stabilization, the faithful-field fibre-square argument,
Noetherian stage injectivity, elementwise limit injectivity, and the actual
localized-base-change argument for cokernel flatness.

Hypothesis and conclusion correspondence:

- The commutative local rings are `R : Type u`, `S : Type v`, `[CommRing R]`,
  `[CommRing S]`, `[IsLocalRing R]`, and `[IsLocalRing S]`. The map is
  `algebraMap R S` for `[Algebra R S]`, and its locality is
  `[IsLocalHom (algebraMap R S)]`. Bundling the specified ring map as an algebra
  structure is equivalent to starting with an arbitrary local ring homomorphism.
- Essential finite presentation is expressed by explicit witnesses, as Mathlib
  does in `FormallySmooth.of_formallySmooth_residueField_tensor`:
  `P : Type p`, `[CommRing P]`, `[Algebra R P]`,
  `[Algebra.FinitePresentation R P]`, `W : Submonoid P`, `[Algebra P S]`, and
  `[IsLocalization W S]`. The condition `[IsScalarTower R P S]` says that this
  localization is compatible with the specified `R`-algebra structure of `S`.
  The universal-property predicate `IsLocalization` characterizes `S` as
  `W⁻¹P` up to its canonical algebra isomorphism. These are witness data for the
  node's existential property; no finite type, Noetherianity, domain, or flatness
  hypothesis on `S` has been added. No new private notion is introduced.
- The modules are `M : Type w`, `N : Type z`, their additive commutative group
  structures and `[Module S M]`, `[Module S N]`. Their finite presentation is
  `[Module.FinitePresentation S M]`, `[Module.FinitePresentation S N]`.
- `[Module R M]`, `[Module R N]`, `[IsScalarTower R S M]`, and
  `[IsScalarTower R S N]` encode the restricted `R`-actions. They assert only
  compatibility with the given `S`-actions, so do not restrict the modules.
  `u : M →ₗ[S] N` is exactly the node's `S`-linear map.
- Flatness of the target over the base is `[Module.Flat R N]`.
- `IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)` and its counterpart for
  `N` are precisely `m_R M` and `m_R N`, as `R`-submodules.
  `Submodule.mapQ` on `u.restrictScalars R` is the canonical map between the
  two quotients, taking `[x]` to `[u x]`. The proof argument is the existing
  `Submodule.smul_top_le_comap_smul_top` theorem; there is no additional
  compatibility hypothesis or postponed well-definedness theorem.
  `h_fibre : Function.Injective (...)` is exactly closed-fibre injectivity.
- `Function.Injective u` is the first conclusion. The second is
  `Module.Flat R (N ⧸ LinearMap.range (u.restrictScalars R))`.
  Restricting scalars does not change the underlying function or its range, so
  this quotient is exactly `N/u(M)` with its required `R`-module structure.

The three statement dependencies use their recorded Mathlib notions:

| Node | Module and declaration |
| --- | --- |
| `def-weil-pbc-finitely-presented-algebra` | `Mathlib.RingTheory.FinitePresentation`, `Algebra.FinitePresentation` |
| `def-sc-finitely-presented-module` | `Mathlib.Algebra.Module.FinitePresentation`, `Module.FinitePresentation` (the node is a Mathlib leaf and its `mathlib_match` is its record) |
| `def-weil-pbc-flat-ring-map` | `Mathlib.RingTheory.RingHom.Flat`, `RingHom.Flat` and its underlying `Module.Flat`, defined in `Mathlib.RingTheory.Flat.Basic` |

I read each class's full declaration and docstring in the pinned Mathlib.
`Algebra.FinitePresentation` gives a surjective finite polynomial presentation
with finitely generated kernel; `Module.FinitePresentation` gives finite
module generators and a finitely generated relation kernel; `Module.Flat` is
Mathlib's flatness predicate, equivalent to preservation of injections under
tensoring. The recorded flatness node explicitly includes `Module.Flat`.
I also read the localization predicate and its universal-property documentation,
`Submodule.mapQ`, and `Submodule.smul_top_le_comap_smul_top`.

All already stated proof dependencies are imported, including the project
modules `ColimitEventuallyFlat`, `ColimitVaryingRings`, `FlatModInjective`, and
`LocalizedBaseChangeQuotientFlat`, and the Mathlib modules supplying the leaf
statements. The two statement-only, unstated proof dependencies
`lem-trf-local-module-arrow-noetherian-descent` and
`lem-trf-localization-system-kernel-stabilization` have no recorded Lean module
to import. They are retained in the proof plan and docstring. Neither is needed
to type this statement, so no prerequisite is restated in this delivery.

Edge cases checked against the source and the encoding:

- `M = 0`: the fibre and original maps are injective and the quotient is `N`,
  whose base flatness is assumed.
- `N = 0`: fibre injectivity forces `M/m_R M = 0`. This is not a vacuous case:
  finiteness over local `S` and `m_R S ⊆ m_S` force `M = 0` by Nakayama, giving
  the claimed injectivity and flat zero cokernel.
- An identity map has flat zero cokernel. A zero map satisfies fibre injectivity
  only when its finite source is zero by the same Nakayama argument.
- A field base is allowed; its maximal ideal is zero, so fibre injectivity is
  precisely injectivity and every cokernel is flat over the field.
- Non-Noetherian base rings and nontrivial localization kernels are allowed.
  Neither localization injectivity nor base/target Noetherianity is assumed.
- `W` may contain zero; the resulting zero localization cannot be local under
  Mathlib's nontrivial local-ring convention, just as for the source's local
  rings. Ordinary identity localizations and all characteristics are allowed.
- The five universes are explicitly bound and independent. No size equality
  restricts the rings, presentation witness or either module. There is no test
  object quantification that could become vacuous in a smaller universe.

Searches were run through `msearch.py`, with actual results in the sandbox's
`searches.jsonl` (UTC 2026-10-17):

- LeanFinder query: “A map of finitely presented modules over a local essentially
  finitely presented algebra, with flat target and injective reduction modulo
  the maximal ideal, is injective with flat cokernel”. Eight hits: ordinary
  localization detection, flat factorization, local residue splitting,
  faithful flatness, and tensor exactness. None is Tag 046Y.
- Loogle query: `Module.FinitePresentation, Module.Flat, Function.Injective`.
  Zero hits.
- Mathlib grep query: `mod-injective-general|essentially of finite presentation|mod_injective`
  in `RingTheory`. Six hits, in `Smooth/Fiber.lean` and
  `Extension/Cotangent/Basic.lean`; none states this criterion. The former's
  docstring explicitly explains the same `P`, `W`, `IsLocalization` witness
  encoding used here.
- LeanSearch query: “A map of finitely presented modules over a local essentially
  finitely presented algebra with flat target and injective closed fibre is
  injective and has flat cokernel”. Eight hits: flatness criteria,
  faithful-flat tensor detection, finite free/projective module results, and
  `Module.Flat.toAlgebra_injective`; none has this local-algebra criterion.
- Direct `rg` in `WeilConjectures` and `lean/Sheaf` searched
  `mod_injective|mod-injective|essentially of finite presentation|FinitePresentation.*Flat|injective.*[Cc]okernel`.
  The project's `FlatModInjective` is the Noetherian Tag 00ME tool, and
  `ValuationFiniteModuleInjectivity` is the valuation-base Tag 0GSG consumer;
  neither has this statement. Read both full signatures. Direct
  `grep -rn 'lem-trf-valuation-general-mod-injective'` in `WeilConjectures`
  found nothing. The exact new declaration name was searched across Mathlib,
  `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`, with no hit.

The previous worker's reported rejection concerned an attempt to re-split the
already reviewed stage-1 item. This delivery preserves the current reviewed
split and every existing node field, adding only `lean` and a new Lean module.
No stage-1 re-splitting is attempted.

Validation: the required `scompile.py Q84 lem-trf-valuation-general-mod-injective`
compiled the delivered module cleanly in both its sandbox and library-path
checks (2.9 s and 2.0 s), with no errors or warnings. Every variable/universe is
explicit; the module also sets `autoImplicit false`. No proof is supplied.

## Second reading by Q84

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
