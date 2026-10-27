## Worker report

Module: `Sheaf.AlgebraicGeometry.RelativeMPseudoCoherentHighQCoh`.
Declaration: `AlgebraicGeometry.Scheme.isQuasicoherent_homology_of_isMPseudoCoherentRelativeTo`.
This states exactly the first assertion of Stacks 0CSU; its only proof is `sorry`.
No definitions, dependency repairs, new nodes, or statement corrections are needed.

Hypothesis and conclusion correspondence:

- Schemes X and S: `{X S : Scheme.{u}}`.
- A scheme morphism f: `(f : X ⟶ S)`.
- Locally finite type: `[LocallyOfFiniteType f]`; not finite type or finite presentation.
- An arbitrary integer m: `(m : ℤ)`.
- An unbounded derived object E: `(E : schemeDerivedCategory X)` on the recorded
  `SheafOfModules.{u} (moduleRings X.toRingedSpace)` carrier.
- Relative m-pseudo-coherence: `(hE : IsMPseudoCoherentRelativeTo f m E)`, precisely
  the dependency's local affine closed-embedding definition, not absolute or full
  pseudo-coherence.
- Every integer degree strictly greater than m: `∀ i : ℤ, m < i →`.
- Its cohomology sheaf: `(DerivedCategory.homologyFunctor
  (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E`.
- The conclusion quasi-coherent: `.IsQuasicoherent`, the Mathlib predicate exposed
  by the recorded `pqf-def-coherent` module. Finite type and coherence are not asserted.
- The node's explicit absence of quasi-compactness, separatedness, Noetherianity,
  and a lower bound is respected: none appears in the binders.

Universes `u w` are explicitly bound and `autoImplicit` is false. The family
`[∀ Y : Scheme.{u}, HasDerivedCategory.{w}
  (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]` is exactly the localization
interface already required by the relative pseudo-coherence dependency for the
source, affine ambient schemes, and open subschemes. It introduces no geometric
hypothesis or equality between universes.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms
  (def-pc-scheme).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, as directed by the convention-only
  def-pc-morphism-conventions node, which has no module or declaration of its own.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory`; its `schemeDerivedQCohProperty`
  docstring confirms the same homology-functor carrier for quasi-coherence.
- `Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex`:
  `AlgebraicGeometry.Scheme.IsMPseudoCoherentRelativeTo` (the degreewise declaration
  in the recorded declarations list; the main recorded declaration is the all-m
  `IsPseudoCoherentRelativeTo`). Full signatures and defining terms were read.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: exposes
  `SheafOfModules.IsQuasicoherent`. The module also exposes finite type and coherence;
  its conjunction `Scheme.Modules.IsQuasiCoherentFiniteType` is not the notion
  this conclusion asks for, so that conjunction is not substituted here.

The proof dependencies' recorded modules are imported privately, with the proof
plan retained step by step in the theorem docstring:

- `Sheaf.AlgebraicGeometry.MPseudoCoherentComplex`:
  `AlgebraicGeometry.Scheme.IsMPseudoCoherent`.
- `WeilConjectures.AlgebraicGeometry.PerfectComplex`:
  `AlgebraicGeometry.Scheme.IsStrictlyPerfect` and `IsPerfect`.
- `WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh`:
  `AlgebraicGeometry.schemeDerivedQCohProperty_of_isPerfect`.
- `WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage`:
  `AlgebraicGeometry.RingedSpace.derivedModuleDirectImage` and its K-injective
  resolution computation interface.
- `WeilConjectures.AlgebraicGeometry.ClosedModulePushforwardHomology`:
  `AlgebraicGeometry.closed_modulePushforward_preservesHomology`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`:
  `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pullback`.
- `WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful`:
  `AlgebraicGeometry.closedImmersion_pushforward_fullyFaithful` (its counit clause).

Sources and edge cases checked before writing:

Read local `literature/stacks-project/more-morphisms.tex`, Definition
`definition-relative-pseudo-coherence` (09UI), and Lemma
`lemma-relative-pseudo-coherence` (0CSU), including its proof. It has precisely
locally finite type f and unbounded E, and its first conclusion uses i > m.
Empty X, empty base (then empty source), zero E, arbitrary negative or positive m,
and zero-dimensional affine ambient space are permitted by the existing
relative definition and by this theorem. Degree i = m is deliberately excluded:
the approximation is only surjective there, so quasi-coherence of that degree
is not concluded. No global bound is imposed on an infinite affine covering,
and the proof computes only one cohomology triple, so there is no hidden
boundedness assumption. No statement dispute or node fault was found.

Searches (2026-10-24, all via prescribed tools / read-only source searches):

- msearch.py leanfinder, query: "A relatively m pseudo coherent complex for a locally
  finite type scheme morphism has quasi coherent cohomology in degrees greater
  than m". Eight hits, including DerivedCategory isGE/isLE facts,
  SheafOfModules.IsFiniteType, and finite-presentation/quasi-coherence interfaces;
  none states the relative degreewise assertion.
- msearch.py loogle, query: `"IsMPseudoCoherent", "IsQuasicoherent"`.
  OK, zero hits.
- msearch.py grep, query: `pseudo.?coher|IsMPseudoCoherent`.
  OK, zero Mathlib hits.
- msearch.py leansearch, query: "Relative m pseudo coherence implies quasi coherent
  cohomology sheaves in all degrees strictly greater than m". Eight hits, all
  quasi-coherence definitions/constructors or finite-presentation implications;
  no exact theorem.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for
  `IsMPseudoCoherentRelativeTo|relative.*[Qq]uasi|[Pp]seudo[Cc]oherent.*[Hh]omology|[Pp]seudo[Cc]oherent.*[Qq][Cc]oh`:
  found the existing relative definition and absolute/full pseudo-coherence
  results, not this theorem. In particular PseudoCoherentQCoh requires full
  absolute pseudo-coherence and does not give this degreewise relative assertion.
- grep -rn for the exact node id in `lean/WeilConjectures`: no hits.
- rg for the proposed declaration name and relative quasi-coherence variants in
  both project trees and `dag/lean_names_upstream.json`: no conflicting name.

Validation: scompile.py passed both the sandbox and final library module checks
(2.4 s and 2.5 s), with no errors or unexpected warnings. deliver2.py --no-push
reported OK: preflight and per-file compilation passed. Only the item node's
`lean` field changes; the module has no lines over 100 characters. The maintainer
performs the independent review as specified by the direct-delivery brief.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
