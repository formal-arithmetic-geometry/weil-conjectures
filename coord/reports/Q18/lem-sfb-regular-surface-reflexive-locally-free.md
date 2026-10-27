## Worker report

Item: lem-sfb-regular-surface-reflexive-locally-free. The module
`Sheaf.AlgebraicGeometry.RegularSurfaceReflexiveLocallyFree` states
`AlgebraicGeometry.Scheme.Modules.isIso_bidual_iff_isFiniteLocallyFree_of_isRegularScheme`.
Its sole theorem has proof `by sorry`; it defines no new mathematical object.
The item node changes only in `lean`. No statement correction, new nodes, dependency
repairs, or statement disputes are needed.

The source was read in `literature/stacks-project/divisors.tex`, lines 2336–2374,
Tag 0B3N (`divisors-lemma-reflexive-over-regular-dim-2`). It states exactly the
reflexivity/finite-local-freeness equivalence for a coherent module on a regular
scheme of dimension at most two. Its proof distinguishes local dimensions zero,
one, and two. The declaration docstring carries all eight proof steps of the DAG,
including the named dependencies, the zero-module depth exception and the empty
scheme case.

Clause-by-clause statement correspondence:

- “Let X be a scheme”: `(X : Scheme.{u})`, with explicit `universe u` and
  `set_option autoImplicit false`.
- “X regular”: `(hX : IsRegularScheme X)`. The recorded predicate unfolds to
  `IsLocallyNoetherian X ∧ IsRegular X`, so this includes local Noetherianity and
  regular local stalk rings. It does not require connectedness, integrality,
  global Noetherianity, quasi-compactness, or separatedness.
- “Topological Krull dimension at most two”: `(hdim : topologicalKrullDim X ≤ 2)`.
  The dimension is Mathlib's `WithBot ℕ∞` supremum of strict chains of nonempty
  irreducible closed subsets; no nonnegative lower bound is added.
- “F a coherent O_X-module”: `(F : X.Modules)` and
  `(hF : RingedSpace.IsCoherent X.toRingedSpace F)`. This is the exact finite-type
  and finite-type-kernel coherence predicate exposed by the repaired recorded
  `pqf-def-coherent` module, not merely its retained quasi-coherent/finite-type
  conjunction.
- “F-dual = sheaf Hom(F,O_X)”: the codomain of
  `SheafOfModules.bidual (R := X.sheaf) F` unfolds to
  `SheafOfModules.homObj (SheafOfModules.homObj F (SheafOfModules.unit _))
    (SheafOfModules.unit _)`. Both internal Homs use the same structure sheaf.
  The unit module is O_X itself.
- “Evaluation sends s to (lambda maps to lambda(s))”: the existing canonical
  `SheafOfModules.bidual` uses `PresheafOfModules.bidual`. The latter's
  `bidual_app_app_apply` was read: over any V mapping to U, it applies the local
  functional to the restriction of s; at the identity V = U this is lambda(s).
- “F reflexive if evaluation is an isomorphism”: the left side is exactly
  `IsIso (SheafOfModules.bidual (R := X.sheaf) F)`. It does not replace the
  canonical evaluation by existence of an arbitrary double-dual isomorphism.
- “If and only if F finite locally free”: `↔ SheafOfModules.IsFiniteLocallyFree F`.
  The recorded predicate has finite local generators on a locally free cover,
  allowing a separate finite rank on each member; no constant rank is imposed.

Recorded statement dependencies read and used:

- def-weil-regular-scheme:
  `Sheaf.AlgebraicGeometry.IsRegularScheme`, `AlgebraicGeometry.IsRegularScheme`.
  Its underlying upstream `AlgebraicGeometry.IsRegular` signature was also read.
- def-kun-topological-krull-dimension:
  `Mathlib.Topology.KrullDimension`, `topologicalKrullDim`.
- pqf-def-coherent:
  `Sheaf.AlgebraicGeometry.CoherentFiniteType`, exposing
  `AlgebraicGeometry.RingedSpace.IsCoherent` from
  `WeilConjectures.AlgebraicGeometry.Coherent`. Both module docstrings and the
  complete defining signature were read. The node's `lean.declarations` explicitly
  includes this exact coherence predicate.
- def-pur-sheaf-hom:
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`,
  `SheafOfModules.homObj`. The signature and slice-linear-Hom docstring were read.
- def-sc-finite-locally-free-sheaf:
  `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`,
  `SheafOfModules.IsFiniteLocallyFree`. The full class and local-generators
  description were read, together with the local free-isomorphism criteria.

The canonical map comes from the existing public
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Bidual` module, declaration
`SheafOfModules.bidual`. The complete map and its presheaf evaluation formula
were read. The already recorded proof dependency
`lem-sf-locally-free-sheaf-evaluation-biduality` also uses this same map. All
recorded proof dependency modules with published declarations are included as
plain imports; Mathlib matches for stalk dimension, vector-space freeness, and
DVR finite torsion-free freeness are imported from their recorded files. Statement
dependencies and the canonical evaluation construction are public imports.

Edge cases checked before writing:

- Empty X: `topologicalKrullDim X = ⊥` satisfies the bound; no point or nonempty
  cover is assumed. The empty trivializing cover and vacuous stalk criterion apply.
- Zero F and rank zero: both canonical evaluation and local freeness admit this
  case. The proof plan separates zero stalks before using depth equality.
- Dimension zero or one is included by `≤ 2`, rather than imposing dimension two.
- Disconnected regular schemes and varying local ranks are included; no integral
  scheme hypothesis is used.
- Arbitrary characteristic is included. No base field or characteristic is bound.
- The universe is the same explicitly bound `u` used by the recorded scheme,
  coherence and finite-local-freeness interfaces; no equality of independent
  coefficient or site universes is imposed.

Searches (2026-10-24):

- `msearch.py ... leanfinder "Coherent reflexive sheaves on a regular scheme of
  dimension at most two are finite locally free"`: eight hits for finite type,
  finite presentation, local generators, and the module-sheaf condition. None
  states the regular-scheme reflexivity equivalence.
- `msearch.py ... leansearch "A coherent reflexive sheaf on a regular scheme of
  dimension at most two is finite locally free"`: eight hits, including
  `Module.IsReflexive.of_finite_of_free`, `Module.IsReflexive.to_isTorsionFree`,
  and sheaf finite-presentation definitions. The algebraic reflexivity definition
  and finite-free implication were opened in Dual/Defs.lean and Dual/Lemmas.lean;
  they are not the scheme theorem.
- `msearch.py ... loogle "Module.IsReflexive, Module.Free"`: one hit,
  `Module.IsReflexive.of_finite_of_free`, whose signature assumes finite and free
  algebraic modules and proves only the opposite implication at module level.
- `msearch.py ... grep "reflexive|IsReflexive" AlgebraicGeometry`: zero Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `regular.*reflexiv|reflexiv.*regular`: no theorem match. More focused searches
  in the module-sheaf directories found `SheafOfModules.bidual` and the already
  recorded `locallyFreeEvaluationBiduality`; both were read and reused.
- `rg` in `lean/WeilConjectures` for this item's id: no hits.
- `rg` in `dag/lean_names_upstream.json` for `bidual|IsReflexive` found the existing
  invertible-module biduality result, which assumes rank one and does not prove
  this equivalence. Exact proposed-name searches in Mathlib, WeilConjectures,
  Sheaf and the upstream name index found no declaration collision.

Validation: the prescribed `scompile.py Q18
lem-sfb-regular-surface-reflexive-locally-free <file>` compiled both the sandbox
module and its final library module name cleanly (2.2 seconds each). No diagnostic
commands remain; the only postponed proof is the named theorem above.

## Second reading by Q18

This is a separate self-review pass in the dispatcher worker; no other agents
were started. The maintainer supplies the independent review required by the
assignment. I reopened the completed Lean module and compared its signature to
the node and the source, checking each binder and both sides of the equivalence.
`hX` uses the complete locally-Noetherian regular predicate, `hdim` is the
unreduced topological dimension bound, and `hF` is Stacks coherence. The target of
`bidual (R := X.sheaf) F` is the correct iterated sheaf Hom into O_X, with the
source's actual evaluation. The right side is variable-rank finite local freeness.
There is no extra hypothesis, omitted case, replacement map, or missing clause.
No mismatch was found and no correction was made on this pass. I also checked
that every explicit universe/variable is bound, the source/proof docstrings
cover the eight DAG proof steps, the node's non-Lean fields are unchanged, and
there are no lines longer than 100 characters in the Lean module.
