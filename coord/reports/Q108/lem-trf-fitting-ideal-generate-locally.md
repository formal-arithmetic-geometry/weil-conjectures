## Worker report

The delivery states `AlgebraicGeometry.Scheme.Modules.fitting_ideal_generate_locally` in
`Sheaf.AlgebraicGeometry.FittingIdealGenerateLocally`, with `sorry` as its entire proof.
It also supplies the missing canonical Fitting ideal sheaf as real data in
`Sheaf.AlgebraicGeometry.FittingIdealSheaf`. No mathematical statement was corrected,
no dependency record was replaced, and no theorem was proved.

The statement is matched clause by clause as follows.

- A scheme S is `(S : Scheme.{u})`; its structure-sheaf module is `(F : S.Modules)`.
  The source's finite-type and quasi-coherence hypotheses are `[F.IsFiniteType]` and
  `[F.IsQuasicoherent]`. There is no finite-presentation, Noetherian, flatness, or
  separatedness hypothesis. The nonnegative index is `(r : ℕ)`.
- The setup's affine description is the first conjunct: for every affine open `U`,
  every number `n` and every surjective linear presentation `π` of `Γ(F, U.1)`,
  `(fittingIdealSheaf F r).ideal U = π.presentationFittingIdeal r`. The recorded
  dependency defines this ideal using all kernel-row minors and makes it the unit
  ideal when `n ≤ r`. This conjunct verifies that the concrete sheaf construction
  really glues exactly the ideals specified in the node; it adds no additional
  mathematical assertion beyond that setup.
- The closed subscheme Z_r is the existing canonical Mathlib object
  `(fittingIdealSheaf F r).subscheme`, with inclusion `.subschemeι` (a closed
  immersion). Its underlying set is `.support`: Mathlib constructs the subscheme
  on this very subtype and `subschemeι_apply` is the inclusion. Thus its open
  complement is exactly `(fittingIdealSheaf F r).support.compl`.
- Clause (1) quantifies over every `(T : Scheme.{u}) (g : T ⟶ S)`, with no property
  imposed on g. The pullback is the recorded `(tensorPullback g).obj F`, not
  Mathlib's different module-pullback functor. Its local generation condition is
  `∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ s : ULift.{u} (Fin r) →
  (((tensorPullback g).obj F).over U).sections, Epi (...freeHomEquiv.symm s)`.
  The epimorphism is precisely the generating-sections dependency's local
  sheaf-surjectivity condition. The other side is an actual scheme morphism
  `h : T ⟶ Scheme.Opens.toScheme (X := S) ...support.compl`, with
  `h ≫ Scheme.Opens.ι (X := S) ...support.compl = g`.
- Clause (2) quantifies over all `x : S`. The common condition
  `x ∉ (fittingIdealSheaf F r).support` is equivalent separately to each of:
  surjectivity of the stalk map of `.toModulesι` (equality of the ideal stalk
  with the local ring); the identical neighbourhood-generation predicate for F;
  and existence of a family `s : Fin r → (moduleStalkFunctor ... x).obj F`
  whose `Submodule.span (S.presheaf.stalk x) (Set.range s)` is top. The stalk
  scalar ring is the actual local structure-sheaf ring, not the affine ring.
- Exactly r sections/elements expresses at most r by padding a shorter family
  with zeros. `ULift (Fin r)` changes only the universe, allowing Mathlib's
  free sheaf to take its index in `Type u`; it does not change cardinality.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`; the canonical instance for the specified
  subscheme inclusion comes through `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`.
- `Sheaf.RingTheory.PresentationFittingIdeal`:
  `LinearMap.presentationFittingIdeal` and
  `LinearMap.presentationFittingIdeal_independence_baseChange` (including its
  canonical base-change and localization presentations).
- `WeilConjectures.AlgebraicGeometry.Coherent`: its docstring explicitly identifies
  the node's finite-type and quasi-coherent notions with Mathlib's
  `SheafOfModules.IsFiniteType` and `SheafOfModules.IsQuasicoherent`.
- `WeilConjectures.AlgebraicGeometry.TensorPullback`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`:
  `SheafOfModules.GeneratingSections`, in particular its `epi` field, rendered
  directly as `Epi (M.freeHomEquiv.symm s)` for the specified finite family.
- New dependency `def-trf-fitting-ideal-sheaf`:
  `AlgebraicGeometry.Scheme.Modules.fittingIdealSheaf`.

Every recorded proof-dependency module with a declaration is imported. These are
`WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`,
`Mathlib.AlgebraicGeometry.Modules.Tilde`,
`WeilConjectures.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization`,
`Sheaf.RingTheory.PresentationFittingIdeal`,
`Sheaf.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine`,
`Mathlib.LinearAlgebra.Matrix.Adjugate`,
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`,
`WeilConjectures.AlgebraicGeometry.TensorPullbackTilde`, and
`Mathlib.AlgebraicGeometry.OpenImmersion`. The public statement imports expose
only the notions in the signature. The theorem docstring reproduces all five
proof steps and adds the affine-family verification needed for the real definition.
Current upstream sources absent in the older local checkout were read using
`scompile.py --source`, as required.

Edge cases checked mathematically before writing:

- `r = 0`: the empty generating family is allowed. It generates exactly a zero
  sheaf or stalk; the complement of Fit_0 is the vanishing locus of F, as required.
- `F = 0`: every affine presentation has unit Fitting ideal for all r; the open
  complement is all of S, and zero sections padded to r generate all pullbacks.
- `r ≥ n`: the existing presentation ideal is top by its actual definition.
- Empty S, T, or neighbourhoods: affine empty opens have the zero section ring,
  and zero-generator surjections exist there. Pointwise assertions are vacuous;
  the empty T factors through every open.
- A free module of rank n over a field has empty bounded-generator locus for
  `r < n` and full locus for `r ≥ n`.
- For `A/J` with J not finitely generated, r = 1 gives the unit ideal while
  r = 0 gives J. The statement retains this finite-type, non-finitely-presented
  case; no finite-presentation condition has slipped into the sheaf definition.
- Nonflat arbitrary g is included: right exactness and extension of Fitting
  ideals, not flatness, are the planned pullback argument.

Searches made (all before defining the missing notion):

1. `msearch.py ... leanfinder "Fitting ideal sheaf complement locus locally generated
   by at most r sections"`: eight hits, including generic `IdealSheafData` constructors
   and `Module.isOpen_freeLocus`; no Fitting ideal sheaf or generator criterion.
2. `msearch.py ... loogle "LinearMap.presentationFittingIdeal,
   SheafOfModules.GeneratingSections"`: zero hits, unknown first identifier in
   the search service. The local recorded presentation definition was read directly.
3. `msearch.py ... grep "Fitting|fittingIdeal|fitting_ideal"`: twenty displayed
   hits, all unrelated uses of 'fitting', Fitting decompositions, or Lie weights.
4. `msearch.py ... leansearch "Fitting ideal sheaf of a finite type quasi coherent
   module on a scheme"`: eight hits for generic ideal sheaves, finite type and
   quasi-coherence, but no Fitting construction.
5. `msearch.py ... loogle "AlgebraicGeometry.Scheme.IdealSheafData.ofIdeals"`:
   six hits, providing the generic largest-subordinate-ideal-sheaf constructor,
   its affine comparison lemma and Galois-coinsertion API. Its full definition
   was read; it is used, not reimplemented.
6. `rg` for Fitting/fittingIdeal/fitting_ideal/generatorLocus in upstream
   `WeilConjectures` and project `lean/Sheaf`, plus node-id grep upstream and
   name checks in `dag/lean_names_upstream.json`: no existing statement, and
   only the ring-level presentation ideal in the project.
7. DAG grep for Fitting ideal sheaves and `tools/blueprint_refs.py search
   "Fitting ideal sheaf"`: no generic definition node; blueprint search reports
   zero matches. The existing `def-trf-first-fitting-singular-subscheme` is a
   special construction for differential modules, not this general notion,
   and currently has no Lean record.

No statement dispute or source fault was found.

## New nodes

`def-trf-fitting-ideal-sheaf` defines the general Fitting ideal sheaf needed in the
item's setup, following Stacks Divisors Tag 0C3C and More on Algebra 07Z8/07ZA(3).
Its module contains a single real definition: on every affine open, form the
supremum of all surjective finite-free presentation ideals and apply Mathlib's
`IdealSheafData.ofIdeals`. Supremums and `ofIdeals` are real complete-lattice
constructions, with no choice from a postponed existence assertion, no proof
obligation hidden in a definition, and no `sorry`. Presentation independence
makes the first supremum the common ideal; localization makes `ofIdeals` recover
the family. The item's first conjunct states this affine identification.
The new node cites the existing scheme, quasi-coherence/finite-type and
presentation-Fitting nodes; the item gains this new node in `stmt_deps`.
Its search records preserve the actual search-tool outputs. No existing generic
DAG definition, Mathlib declaration, upstream declaration, or side declaration
was found. The specialized first-Fitting singular-subsheme definition is distinct.

## Second reading by Q108

The dispatcher explicitly requires this worker to work alone and deliver for the
maintainer's independent review. No second agent was started and no independent
worker review is claimed. For the final self-check, I reopened the item and both
modules, matched every hypothesis and clause as listed above, and checked that
the added affine equality certifies the setup's specified Fitting ideal, rather
than assuming an arbitrary ideal sheaf or merely a radical with the same support.
The supremum construction introduces no chosen map or new presentation hypothesis.

The first compiler pass found only field-notation resolution on the complement
open: its inferred type was the underlying `TopologicalSpace.Opens S`, so Lean
did not find `Scheme.Opens.toScheme` and `Scheme.Opens.ι` by projection. Both
are now written explicitly with `(X := S)`; the mathematical statement is unchanged.

Validation: both modules compiled successfully through `scompile.py`, without
errors or warnings. Direct dependency imports were then made explicit; the
required delivery dry run rechecks the final files and their node records.

The first dry run compiled both final files cleanly, then caught a metadata
extraction error: the recorded signature ended at the named argument `(X := S)`
instead of the theorem proof delimiter. The node record now contains the whole
signature, including every equivalence. No Lean statement changed for this repair.
