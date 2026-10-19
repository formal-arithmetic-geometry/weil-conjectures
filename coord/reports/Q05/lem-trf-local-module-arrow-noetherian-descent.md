## Worker report

The module `Sheaf.RingTheory.LocalModuleArrowNoetherianDescent` states
`RingHom.exists_local_module_arrow_noetherian_descent` with proof `sorry`.  It introduces a
small nonempty directed preorder `I`, functors `Rdiag` and `Sdiag` of commutative rings,
a ring map `ρ`, cocone maps `π` and `κ`, additive-group diagrams `Mdiag` and `Ndiag`,
cocones `μ` and `ν`, stage module structures, and stage linear maps `ui`.
Functoriality gives identity and composition for all ring and additive transitions;
naturality gives all cocone compatibilities.

The hypotheses are rendered as follows.  `R S B : Type u` are commutative rings,
`α : R →+* S` is local, `B` is a finitely presented `R`-algebra, `W` is a submonoid,
`f : B →+* S` satisfies `f.comp (algebraMap R B) = α`, and `hS` is
`IsLocalization W S` for the induced `B`-algebra.  `M N : Type v` are additive
commutative groups with `S`-module structures and `Module.FinitePresentation`; `u` is
`M →ₗ[S] N`.  The existential output binds the directed index, ring and module
functors, cocones, stage module instances, and `ui` exactly in this order.

The first conjunction states local rings and local homomorphisms for every stage,
local transition, and cocone, plus the commuting square
`ρ.app i ≫ κ.app i = π.app i ≫ CommRingCat.ofHom α`.  The next four clauses state
semilinearity of both module transitions and both cocones.  The following two clauses
state transition and cocone commutation with `ui` and `u`.

The Noetherian/finite-type clauses are `IsNoetherianRing` for both stage rings,
`(algebraMap ℤ (Rdiag.obj i)).EssFiniteType`, and essential finite type for each
`ρ.app i`; the two subsequent clauses retain finite presentation of both stage
modules.  The colimit block uses `Nonempty (IsColimit (Cocone.mk ...))` for both
rings and both additive-group diagrams, together with explicit representation and
common-later-stage equality criteria for every ring and module element.  The transition
block gives the canonical pure-tensor ring map and `IsLocalization`, and linear
isomorphisms for both modules with the displayed pure-tensor formulas.  The final block
gives the analogous ring localization and the two limit module isomorphisms, together
with the pure-tensor arrow compatibility.  Tensor products are written with the scalar
ring first where Mathlib's `LinearEquiv` API requires its canonical module structure;
the pure-tensor formulas are the same canonical maps as the node's displayed
`x ⊗ s ↦ s • m(x)` maps (using the commutativity symmetry of tensor products).

Dependency declarations used:

* `Algebra.FinitePresentation` from `Mathlib.RingTheory.FinitePresentation`.
* `Module.FinitePresentation` from `Mathlib.Algebra.Module.FinitePresentation`.
* `IsNoetherianRing` from `Mathlib.RingTheory.Noetherian.Defs`.
* `Algebra.EssFiniteType` from `Mathlib.RingTheory.EssentialFiniteness`.
* `CategoryTheory.Limits.Cocone`, `IsColimit`, `colimit`, and `CategoryTheory.IsFiltered`
  from `Mathlib.CategoryTheory.Limits.HasLimits`.
* `TensorProduct`, `TensorProduct.comm`, and pure tensors from
  `Mathlib.LinearAlgebra.TensorProduct.Basic` and `.Tower`.
* `IsLocalization` from `Mathlib.RingTheory.Localization.Basic`.

Edge cases checked: zero modules and zero map; empty finite presentations (`Fin 0`),
identity transitions and cocone maps supplied by functor/natural-transformation laws,
empty and singleton directed indices (the statement requires nonempty directedness),
submonoids containing zero (which cannot localize to a nonzero local ring) and the identity localization, and arbitrary independent ring/module
universes `u` and `v`.

Searches for an existing declaration (all through `msearch.py Q05
lem-trf-local-module-arrow-noetherian-descent`):

* LeanFinder, query `Simultaneous Noetherian local approximation of a morphism of finitely
  presented modules`: 8 hits. These include `Module.FinitePresentation.exists_notMem_bijective`,
  `IsLocalizedModule.exists_isLocalizedModule_powers_of_finitePresentation`,
  `exists_bijective_map_powers`, the localization lift and equivalence lemmas,
  `Module.Flat.exists_factorization_of_isFinitelyPresented`,
  `RingHom.finitePresentation_isLocal`, and the finite free localization lemma.
  None states the simultaneous local Noetherian tower and arrow theorem.
* Loogle, query `Module.FinitePresentation, Module.DirectLimit`: 0 hits.
* LeanSearch, query `A linear map between finitely presented modules over a local essentially
  finitely presented algebra descends to a directed system of Noetherian local rings`:
  8 hits, including `Module.Finite.linearMap`, `Module.DirectLimit.map`,
  `isNoetherian_linearMap`, `DirectLimit.Module.lift`,
  `Submodule.FG.lTensor.directedSystem`, `isNoetherian_range`,
  `ModuleCat.directLimitIsColimit_desc`, and `DirectLimit.Module.lift_apply`.
  These concern fixed-ring module direct limits or finiteness, without the ring tower.
* Mathlib grep, query
  `(descend|descent|exists).*(linearMap|LinearMap|module.*map)|Noetherian.*[Dd]escent`:
  25 hits, mostly unrelated continuous linear maps, bilinear maps, and matrix results;
  no simultaneous Noetherian local approximation theorem.
* `rg` over the upstream `WeilConjectures` and the shared `lean/Sheaf` for
  `local_module_arrow_noetherian|simultaneous.*[Aa]pproximation|simultaneous.*[Dd]escent`
  found no copy of this statement. Related tower constructions were inspected in
  `Sheaf.Paper.LimitTowerEssentiallyFinitePresentation` and
  `Sheaf.Paper.LimitTowerOverLocalSystem`; the first is a proof prerequisite.
* The item id has no hit in upstream `WeilConjectures`; the final declaration name has
  no hit in `dag/lean_names_upstream.json`, Mathlib, upstream, or the shared library.

The dependency declarations were read in their recorded Mathlib files, including their
signatures and docstrings. Source text read: `literature/stacks-project/algebra.tex`,
`lemma-limit-essentially-finite-presentation` (00QV),
`lemma-limit-module-essentially-finite-presentation` (00QX), and the first proof paragraph
of `lemma-mod-injective-general` (046Y). The latter explicitly approximates both modules
and their arrow together. The theorem docstring contains all six DAG proof steps and
their named dependencies. The stated proof prerequisites are privately imported as the
stage instructions require. No `STATEMENT-DISPUTED` or node fault was found.

## Second reading by Q05

This is a self-rereading: the dispatcher explicitly forbids starting other agents;
the maintainer supplies the independent review after delivery. I reread the node and
the complete declaration.  Every input hypothesis is present in
Lean, including locality of `R → S`, the localization presentation of `S`, finite
presentation of both modules, and the arbitrary linear arrow.  The existential data
match the node's rings, modules, maps, transitions, cocones, and arrow.  Functor and
natural-transformation laws supply the identity/composition and cocone compatibility
clauses.  The Noetherian, essential-finite-type, colimit, localization, tensor
isomorphism, and arrow-square clauses are each present.  The tensor equivalences, pure-tensor formulas, and arrow compatibility now share the
same `eM` and `eN` witnesses in each transition/limit block. The namespace is `RingHom`,
without the forbidden declaration prefix `Sheaf`. The only elaboration-driven
presentation choice is scalar-first tensor notation (`S_j ⊗ M_i` and `S ⊗ M_i`), which
is canonically identified with the node's `M_i ⊗ S_j` notation by `TensorProduct.comm`;
the pure-tensor formulas retain exactly the node's maps.  No hypothesis or edge case was
added or omitted.
