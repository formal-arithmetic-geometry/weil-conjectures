## Worker report

The module `Sheaf.CategoryTheory.ModuleObjects.LfpScalarIsomorphism` states
`AlgebraicGeometry.ProEtale.isLocallyFinitelyPresented_comap_iff_sameCover`, with proof
`sorry`. It defines no new notion and changes only the item's `lean` record.

The source paragraph was read in main-20261015,
`sec-six-functors-basics/sk-def-sfb-dc-restricted-functors/`
`lem-sfb-dc-open-lower-shriek-preserves.proof.md`: it uses locally finitely presented
restrictions on strata and the restriction identities. The node's reviewed four-step
proof supplies precisely the needed coefficient relabelling.

Clause-by-clause translation:

- An arbitrary scheme is `{X : Scheme.{u}}`. No Noetherian, characteristic, separation,
  nonemptiness or quasi-compactness condition is added.
- The two abelian sheaves are `{R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}`.
  `[MonObj R] [MonObj S]` give their ring-object structures, and
  `[IsCommMonObj R] [IsCommMonObj S]` impose exactly commutativity. The tensor is the
  existing localized sheaf tensor; it is not a pointwise tensor on sheaves.
- `(φ : R ⟶ S) [IsMonHom φ] [IsIso φ]` is an invertible ring-object homomorphism.
  Its inverse is automatically a monoid homomorphism. These binders are the unbundled
  encoding of the node's isomorphism of ring objects.
- The arbitrary S-module is `{N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}`.
  The first conjunct states
  `IsLocallyFinitelyPresented S N ↔ IsLocallyFinitelyPresented R ((Mod.comap φ).obj N)`.
  Thus both preservation and reflection are stated, not merely preservation.
- The second conjunct quantifies over the actual
  `𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X`, each `i : 𝒰.I₀`, and each fixed
  `(m n : ℕ)`. Each side is `∃ f : finiteFree ... m ⟶ finiteFree ... n,
  Nonempty (restrictedModule ≅ cokernel f)`. The left restricted module is
  `((upperStar Ab (𝒰.f i)).mapMod S).obj N`; the right is
  `((upperStar Ab (𝒰.f i)).mapMod R).obj ((Mod.comap φ).obj N)`.
  The rings are respectively `u_i^*S` and `u_i^*R`. This unfolds only the existential
  ranks in `Mod.IsFinitelyPresented`, keeping the existing `Mod.finiteFree`, `mapMod`,
  and categorical `cokernel`. The same bound `𝒰`, `i`, `m`, `n` occur on both sides:
  no new cover, refinement or rank is allowed. Quantifying over all members gives
  exactly that the same family witnesses local finite presentation, with the same
  rank functions on the two sides (also for an empty family).
- The final conjunct quantifies over every R-module `M`. It states
  `IsLocallyFinitelyPresented R M ↔
  IsLocallyFinitelyPresented S ((Mod.extendScalars φ).obj M)`, and then repeats the
  same fixed-cover/member/rank biconditional for M and its extension. This includes
  the node's entire equivalent extension clause, with both directions and unchanged
  covers and ranks.

The recorded dependency declarations were opened and used directly:

- `sk-def-sfb-ring-object`: `WeilConjectures.CategoryTheory.RingObjects.RingPresheaf`,
  with `CategoryTheory.MonObj`, `IsMonHom`, `IsCommMonObj` and the abelian tensor
  from its public `RingObjects.Ab` import.
- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`,
  `CategoryTheory.Mod`; it bundles the module action and action-compatible maps.
- `def-sfb-finitely-presented-module`:
  `WeilConjectures.CategoryTheory.ModuleObjects.Free`, `Mod.IsFinitelyPresented`
  and `Mod.finiteFree`. The latter is the Fin n biproduct of the regular module;
  the former uses a cokernel presentation, in the module category.
- `def-sfb-locally-finitely-presented`:
  `WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def`,
  `AlgebraicGeometry.ProEtale.IsLocallyFinitelyPresented`. Its definition uses
  `Scheme.Cover.{u}` and `upperStar.mapMod`, exactly as the displayed refinements.
- `sk-def-sfb-change-of-scalars`:
  `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`, `Mod.comap` and
  `Mod.extendScalars`. Its extension is the constructed balanced coequalizer.
  `ModuleObjects.MapMod` supplies the existing `extendScalarsIsoComapInv` and
  restriction equivalence used in the proof plan.

All recorded proof-dependency modules are imported, including SheafTensor,
GrothendieckSheafification, InternalExtensionFinitePresentation, both pro-étale
monoidal modules, and Mathlib Abelian.Basic and Sites.Proetale. The proof-only node
`def-sfb-comap-mapmod-square` currently has no Lean record; no import can name it.
The identity-comparison specialization needed in the proof is already
`Functor.mapModComapIso` in the imported upstream `ModuleObjects.MapMod`.
The theorem docstring carries all four node proof steps, including why inverse
images preserve commutative ring objects.

Edge cases checked before finalizing:

- φ = identity: both scalar functors are naturally the identity; all fixed covers
  and rank pairs are retained.
- Zero rings and zero modules: permitted by MonObj; no nontriviality hypothesis.
- m = 0 or n = 0, including both zero: `Mod.finiteFree` uses the empty biproduct,
  and the module-category cokernel exists as in the dependency definition.
- Empty X and empty covering family: memberwise clauses are vacuous and no
  Nonempty hypothesis is introduced. The global local-presentation predicates
  still use their recorded cover definition.
- Arbitrary ranks varying with i: the theorem quantifies independently over each
  member and both ranks, so no uniform bound is imposed.
- Independent scheme size u is retained; the coefficient Hom universe is u+1,
  as in the recorded small pro-étale site and locally-finitely-presented API.

Searches (executed through the prescribed wrapper and source searches):

- `msearch.py leansearch`, query “Restriction of scalars along an isomorphism of
  ring objects preserves and reflects local finite presentations with the same
  covers and ranks”: eight hits including RestrictScalars,
  Module.Presentation.restrictScalars, RingHom.finitePresentation_respectsIso,
  ModuleCat.restrictScalars, PresheafOfModules.restrictScalars. These concern
  ordinary modules/rings, or give only the functor; none is the internal statement.
- `msearch.py leanfinder`, query “Local finite presentation of internal modules
  is invariant under scalar restriction along an isomorphism”: eight hits on
  ordinary localization/finite-presentation transport, including
  Module.FinitePresentation.of_equiv and Module.Presentation.restrictScalars;
  none matches pro-étale internal module objects and the fixed ranks.
- `msearch.py loogle`, query `CategoryTheory.Mod.comap`: four hits, the restriction
  functor and its underlying-object/action/map formulas, no presentation theorem.
- `msearch.py grep`, query
  `(IsLocallyFinitelyPresented|IsFinitelyPresented).*(comap|extendScalars)|(comap|extendScalars).*(IsLocallyFinitelyPresented|IsFinitelyPresented)`:
  zero Mathlib hits.
- `rg` in WeilConjectures finds `Mod.IsFinitelyPresented.comap` in
  `ModuleObjects.FinitelyPresentedComap` and
  `ProEtale.IsLocallyFinitelyPresented.comap` in
  `SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible`; both are
  one-way preservation only. The latter's proof retains the cover, but its
  statement does not express reflection, extension or unchanged ranks.
- `rg` in lean/Sheaf finds `localFinitePresentation_comap` and
  `localFinitePresentation_of_comap` in ProEtaleModuleConstructiblePullback,
  and fixed-scalar/quotient variants in CondensedConstructibleSerre. These
  separate preservation/reflection lemmas do not state the fixed-rank or
  extension clauses of this item. No full existing declaration was found.
- Searching the exact item id in WeilConjectures and the new full theorem name
  in Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json gives no hit.

No node fault or STATEMENT-DISPUTED issue was found. No new definition or
unusable-dependency repair was necessary.

Validation: scompile.py compiled this module cleanly on the server (sandbox 2.1 s,
library module 2.1 s). The initial server cache miss resolved on retry. An initial
missing monoidal instance was repaired by importing the recorded RingPresheaf
module (which publicly imports the abelian tensor); no hypothesis was added.

## Second reading by Q41

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
