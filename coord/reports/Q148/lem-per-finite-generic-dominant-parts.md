## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteGenericDominantParts` states
`AlgebraicGeometry.finite_generic_dominant_parts`, with its only proof `sorry`.
The declaration docstring gives all six DAG proof steps and their dependencies.
There is no statement correction, new definition, dependency repair, or disputed statement.

The following matches every hypothesis and clause of the unchanged node statement.

| Node | Lean |
| --- | --- |
| Integral Noetherian base S | `{S : Scheme.{u}} [IsIntegral S] [IsNoetherian S]` |
| Noetherian means a finite affine cover by Noetherian rings | Mathlib `IsNoetherian S`; `isNoetherian_iff_of_finite_affine_openCover` is exactly the stated equivalence |
| Generic point eta and K = kappa(eta) | `(η : S) (hη : IsGenericPoint η Set.univ)`; the target of `f.fiberToSpecResidueField η` is `Spec (S.residueField η)` |
| Finite-type S-scheme T | `(f : T ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]` |
| Generic fibre finite over K, including affineness and finite-dimensional coordinate algebra | `(hfinite : IsFinite (f.fiberToSpecResidueField η))`; `IsFinite` includes `IsAffineHom` and finite affine coordinate-ring maps, precisely this condition over a field |
| Reduced union of dominating components | `(dominantReducedPartIdeal f).subscheme`, with canonical inclusion `(dominantReducedPartIdeal f).subschemeι` |
| Dominant part finite type over S | First two conjuncts: `LocallyOfFiniteType (… ≫ f)` and `QuasiCompact (… ≫ f)` |
| Every component generic point maps to eta | For every `ξ`, `closure {ξ} ∈ irreducibleComponents …` implies `(… ≫ f) ξ = η` |
| Its residue extension is finite through the structure map | `((… ≫ f).residueFieldMap ξ).hom.Finite`; its source is `S.residueField ((… ≫ f) ξ)`, identified with K by the preceding equality, and the scalar map is the actual induced map |
| Finite family of etale morphisms to T | `∀ (J : Type v) [Finite J] (V : J → Scheme.{u}) (a : ∀ j, V j ⟶ T), (∀ j, Etale (a j)) → …` |
| Each member finite type over S | `(∀ j, LocallyOfFiniteType (a j ≫ f) ∧ QuasiCompact (a j ≫ f)) → …` |
| Each member has finite generic fibre | `(∀ j, IsFinite ((a j ≫ f).fiberToSpecResidueField η))` |
| Additional complete decomposition hypothesis | `∀ t : T, ∃ (j : J) (z : V j), a j z = t ∧ IsIso ((a j).residueFieldMap z)` |
| Base-changed family completely decomposed | For each `t'` of the dominant part, there is `z'` in `pullback (a j) …subschemeι` mapping to `t'` by `pullback.snd`, with `IsIso` of this projection's residue-field map |
| Empty family permitted for empty T | No `Nonempty J`, no `Nonempty T`; the lift predicates are universal over the target points |

`dominantReducedPartIdeal` is reused from the already landed node
`def-per-dominant-reduced-part`, which is added to `stmt_deps`. Its definition is the
vanishing ideal of the closure of the union of components with dense image. Here T is
Noetherian because it is finite type over Noetherian S, so it has finitely many components;
the selected union is closed already. Its subscheme therefore is exactly the node's reduced
induced structure on that union. The general-base `dominantPart` also exists, but the
integral-base construction states this node's component selection directly.

The complete-decomposition condition is expanded inline, without defining a new predicate.
`PrimeToEllAlteration.IsCompletelyDecomposedEtaleFamily` was read, but requires all schemes
to be bundled objects of `Alt S`. T and the V j here need not be reduced or maximally
dominant, so using that bundled predicate would add hypotheses. The inline lift condition
is the same canonical residue-map condition. The base-changed morphisms are automatically
etale by the recorded Mathlib base-change instance; no extra conjunct is added.

Dependency declarations read and used (names below are in their recorded modules):

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral` and
  `AlgebraicGeometry.IsReduced`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; the scheme specialization
  `AlgebraicGeometry.IsNoetherian` and its finite affine-cover equivalence are in
  `Mathlib.AlgebraicGeometry.Noetherian`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `AlgebraicGeometry.Scheme.residueField` and
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback` and `.snd`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.Topology.Sober`: `IsGenericPoint`.
- `Mathlib.AlgebraicGeometry.Fiber`: `AlgebraicGeometry.Scheme.Hom.fiber` and
  `.fiberToSpecResidueField`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, via the canonical residue ring homomorphism;
  `RingHom.Finite` in `Mathlib.RingTheory.Finiteness.Defs` means module-finite for that
  homomorphism's induced algebra structure. For fields this is finite-dimensional.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`, for the
  reduced induced subscheme construction; its underlying `vanishingIdeal`, `subscheme`
  and `subschemeι` are reused by the integral-base definition.
- `Sheaf.AlgebraicGeometry.DominantReducedPart`:
  `AlgebraicGeometry.dominantReducedPartIdeal` (added landed definition dependency).

Imports of recorded proof dependencies include `DimZeroFiniteOverField`, `Dimension`,
`FibreProductPointResidueField`, `UnramifiedFibrePointIsolated`, `UnramifiedMorphism`,
and Mathlib's Artinian, Proper, ZariskisMainTheorem, FiniteDimensional.Basic modules. Finite, Etale, Fiber and
Noetherian public imports also supply the recorded Mathlib proof matches. The proof
node `lem-per-dominant-part-coreflection` has no current Lean record or Mathlib match,
so no module import is claimed for it; the guessed server source name was checked and
is unavailable. This does not obstruct the present statement, whose construction is
already independently defined. All other proof dependencies are available as recorded
project declarations or Mathlib matches.

Edge cases checked mathematically before writing:

- T empty: the selected union and reduced subscheme are empty, the fibre is Spec 0,
  and component/lift quantifiers are vacuous. J may be empty.
- Only vertical components, e.g. Spec F_p over Spec Z: the dominant part and generic
  fibre are empty; any etale V also has empty generic fibre.
- Mixed dominant and vertical components, e.g. Spec Z disjoint union Spec F_p:
  only the dominant component survives, with finite type inherited from its inclusion.
- T = Spec k[e]/(e^2) over Spec k: reduction is essential, and the residue-field
  extensions still use the actual structural map.
- A nontrivial finite extension L/K is allowed; no separability or degree-one assumption
  was imposed on the dominant generic residue extension.
- An empty J for nonempty T is allowed in the finiteness conclusion; it cannot satisfy
  complete decomposition, exactly as in the natural-language implication.
- General etale V j without separatedness are allowed. Finite type over S is retained
  explicitly, and no properness or separatedness hypothesis is added.
- Scheme universe u and arbitrary finite-family universe v are explicitly bound.

Source reading: the local ILO PDF, physical pages 31--32 (printed pp. 25--26),
II 1.2.5--1.2.6 and 2.1.1; physical pages 43--44 (printed pp. 37--38), III 3.1 and
its proof. These identify X_r and give the Nisnevich base-change step used here.

Searches for existing notions/statements:

- `msearch.py`, leanfinder: “For a finite type scheme over an integral Noetherian base
  with finite generic fibre, the reduced union of dominating irreducible components
  has finite generic residue extensions and etale covers have finite generic fibres”.
  Eight hits concern finite morphism fibres, Noetherian components, quasi-finiteness
  and integral schemes; none states the node.
- `msearch.py`, loogle: `AlgebraicGeometry.IsFinite, AlgebraicGeometry.IsEtale` gave
  no hits because `IsEtale` was unknown to that service. Retried with
  `AlgebraicGeometry.Etale`: twelve hits, including its definition and base-change
  stability, but no finite-generic dominant-part theorem.
- `msearch.py`, grep under Mathlib AlgebraicGeometry:
  `dominantPart|dominantClosure|CompletelyDecomposed` found only the unrelated
  `DominantPartialMap` comment in Birational/Composition.
- `rg` over project `WeilConjectures` and `Sheaf` for dominant parts, dominating
  components and complete decomposition found the already recorded DominantPart,
  DominantReducedPart and PrimeToEllAlterationTopology definitions. These were read
  in full, and the precise integral-base construction is reused.
- `rg` for the item id in `WeilConjectures`, and for
  `finite_generic_dominant_parts|FiniteGenericDominantParts` in both project libraries
  and `dag/lean_names_upstream.json`, found no existing declaration.
- DAG searches for dominant definitions identified `def-per-dominant-reduced-part`
  and `def-per-dominant-part`, both already landed. No new notion is introduced.

Validation: `scompile.py Q148 lem-per-finite-generic-dominant-parts` compiled both the
sandbox and the named library module cleanly (1.9 s and 2.0 s). An initial point binder
needed explicit `↥(pullback …)` to prevent Lean from trying to infer a pullback in Type;
this was fixed without changing the mathematics. Every variable and universe is explicit,
`autoImplicit` is disabled, and there are no extra axioms or hollow definitions.

## Second reading by Q148

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
