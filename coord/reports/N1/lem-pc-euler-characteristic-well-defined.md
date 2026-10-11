## Worker report

The module states well-definedness of cohomology finiteness for a proper scheme over a field. It binds `k`, `X`, a proper structure morphism `f`, a module `F`, and coherence `hF`; `letI := f.ΓAlgebra` supplies the structure map. For every `i : ℕ`, `Module.compHom _ (algebraMap k Γ(X, ⊤))` renders the induced k-vector-space structure and the conclusion is `FiniteDimensional k ((RingedSpace.moduleCohomology X.toRingedSpace i).obj F)`. The second conjunct renders finiteness of the set of indices whose cohomology object is not zero via `Set.Finite {i : ℕ | ¬ IsZero ...}`.

Dependencies used: `AlgebraicGeometry.IsProper` from `Mathlib.AlgebraicGeometry.Morphisms.Proper`; `AlgebraicGeometry.RingedSpace.IsCoherent` from `Sheaf.AlgebraicGeometry.Coherent`; `AlgebraicGeometry.RingedSpace.moduleCohomology` from `Sheaf.Topology.RingedSpaceModuleCohomology`; `Scheme.Hom.ΓAlgebra` from `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`; `Module.finrank`/`FiniteDimensional` from Mathlib dimension modules.

Edge cases checked: `i = 0`; zero cohomology objects satisfy `IsZero`; the finite set may be empty; the induced scalar action is explicit through the structure map. The file compiles with the expected theorem `sorry` warning only.

Searches: `rg` over project and source for Euler/cohomology/proper declarations; Mathlib search records in the node found no exact theorem for proper coherent cohomology finiteness or Euler characteristic. Existing project Euler characteristic definitions were inspected in `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`; they use a different `Scheme.Modules.H` carrier and do not state this node.

## Earlier second reading (a previous round; superseded)

The Lean theorem matches the node hypotheses clause by clause: field, scheme, proper structure morphism, coherent module, induced k-action, finite-dimensionality in every degree, and finite support of nonzero cohomology. No mismatch found.

## Second reading by N1

I opened the node copy, the delivered Lean, all four statement-dependency nodes,
Coherent.lean, PQFCohomology.lean and RingedSpaceModuleCohomology.lean, and the relevant
Mathlib and upstream declarations. The source checkout here lacks literature/stacks-project;
I read the available Stacks TeX copy /home/ubuntu/c1-stacks-review/varieties.tex,
lines 6153–6183 (section-euler, definition-euler-characteristic and the following paragraph).
The section assumes exactly a field, a proper scheme over it, and a coherent module.
There is no algebraic-closure, characteristic, smoothness, projectivity, or dimension assumption.

Object/hypothesis/conclusion list and match:

- Field k: `(k : Type u) [Field k]`. Exact; no characteristic restriction.
- Scheme X proper over k: `(X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsProper f]`.
  Exact. The explicit structure morphism supplies the map needed for scalar restriction.
  The recorded Mathlib IsProper extends separated, universally closed, locally finite type;
  universally closed implies quasi-compact, giving the node's finite-type condition.
- O_X-module F: `(F : X.Modules)`. This is the same module-sheaf carrier used by the
  dependency's `RingedSpace.IsCoherent X.toRingedSpace F` definition.
- Coherence: `(hF : RingedSpace.IsCoherent X.toRingedSpace F)`. Exact: finite type and
  finite-type kernels of maps from finite free modules on every open. No extra
  quasi-coherence, Noetherian, finite-presentation, or finiteness hypothesis is imposed.
- Each H^i is a Γ(X,O_X)-module for i ≥ 0: `(RingedSpace.moduleCohomology
  X.toRingedSpace i).obj F`, with `i : ℕ`, is an object of ModuleCat over global sections.
  This is precisely PQFCohomology's established right-derived global-sections functor.
  I use its defining module directly; no copy of cohomology is introduced.
- The induced k-vector space: `ModuleCat.restrictScalars
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom` applied to that object.
  ChangeOfRings.lean defines the action as r • m = f(r) • m. FiberDegree.lean's
  Scheme.Hom.ΓAlgebra uses exactly this ring homomorphism. Exact same action as before,
  now with no hidden `let`/`have` binders and no imported ΓAlgebra solely for instances.
- Every H^i finite dimensional: the first conjunct universally quantifies `i : ℕ` and
  asserts `FiniteDimensional k` of this scalar-restricted module. Exact.
- Finitely many nonzero H^i: `Set.Finite {i : ℕ | ¬ IsZero (...)}`. Exact. IsZero is
  categorical zero in ModuleCat, not IsZero of a bare Type.
- Hence the alternating dimension sum is a finite sum of integers: the new final
  conjunct `∃ n : ℕ, (∑ᶠ i : ℕ, ...) = ∑ i ∈ Finset.range n, ...` explicitly displays
  the integer finsum as a finite sum. Each term is `(-1 : ℤ)^i` times the integer cast
  of the dependency's `Module.finrank k` of the same scalar-restricted module.
  Together with finite nonzero support and finite dimensionality this gives exactly
  the source's well-defined Euler integer (not the finsum fallback on infinite support).
  No new Euler-characteristic definition duplicates the existing one; this clause
  writes the formula inline. A larger truncation bound adds only zero terms.

Edge cases: degree zero is included by ℕ. A zero module and the empty scheme are not
excluded by any binder; zero cohomology has empty nonzero support and all terms zero.
The finite sum permits n = 0 (`Finset.range 0` empty), so χ = 0 is covered. Arbitrary
field characteristic is allowed. Universe u is explicit and arbitrary, matching the
recorded Scheme/Modules/cohomology carrier; there is no test-object quantification
or small-index restriction, and no unbound universe/variable. Schemes and coefficient
fields can be placed in a common universe as in the dependency declarations.

Independent searches (recorded by msearch.py in searches.jsonl):

- LeanSearch: `Proper schemes over a field have coherent sheaf cohomology finite over
  the base and bounded above`; service unavailable (Internal Server Error), no verdict.
- Loogle: `AlgebraicGeometry.IsProper, Module.Finite`; zero hits.
- Mathlib grep: `cohomology.*(finite|bounded)|eulerChar|eulerCharacteristic` in
  AlgebraicGeometry; zero hits.
- Direct rg in repository lean/Sheaf and upstream WeilConjectures for Euler names,
  finiteDimensional/H, and moduleCohomology with finite: no exact existing theorem.
  I opened upstream Cohomology/Defs.lean (finrankH and eulerChar) and
  Cohomology/DirectImage/AffineMorphism.lean (finiteDimensional_H_of_isProper).
  They use Modules.H (underlying abelian-sheaf cohomology), not the dependency's
  module-valued right-derived cohomology. The latter theorem gives only finiteness,
  with different quasi-coherence/finite-presentation binders, and not the whole node.
  The project valuation-ring theorems are specializations with other hypotheses.
  None is an exact existing realization of this node. I also read Mathlib
  Module.finrank, FiniteDimensional, and ModuleCat.restrictScalars rather than
  introducing any alternative dimension or scalar-action notion.

Mismatches repaired: the old statement lacked the final finite Euler-sum clause;
added the integer finsum-to-finite-sum equality. The file lacked its copyright/module
header and the statement docstring did not carry any proof steps; supplied the source
and all five node proof steps with their dependencies. Replaced both letI binders
by explicit scalar restriction along the same structure map, and adjusted imports.
The field/proper/coherence hypotheses and the two correct finiteness clauses are
preserved. Updated lean.statement verbatim to the signature; the node's natural-language
statement, dependencies and proof are unchanged. No new nodes or dependency modules.
There is one theorem, with proof `sorry`; no hollow definitions, auxiliary proofs,
private declarations, local instances, or local notation were introduced.

Validation: scompile.py compiled the revised complete module on the server in 1.9 s,
exit code 0, with no errors or warnings. All variables/universes were checked by eye.
