## Worker report

The module `Sheaf.AlgebraicGeometry.FinitePushforwardPreservesFinitePresentation` states
`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_pushforward_of_isFinite`, with
`sorry` as its sole proof. No definitions, new nodes, dependency repairs, or statement
corrections are needed. The item's JSON changes only in `lean`.

Source read: `literature/stacks-project/descent.tex`, Tag 05B4,
`lemma-finite-finitely-presented-module`, statement and affine proof (lines 2098–2125).
The node requests its forward implication. The source says finite and of finite
presentation; for a finite morphism quasi-compactness and quasi-separatedness are automatic,
so the node's finite plus locally-of-finite-presentation formulation is equivalent.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes and their morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)`. The universe is explicitly
  declared; `autoImplicit` is disabled. There are no separation, Noetherian, flatness,
  nonemptiness, or characteristic restrictions.
- Finite morphism: `[IsFinite f]`, the recorded Mathlib class extending `IsAffineHom f`
  and requiring finite section ring maps on every affine open of the target.
- Locally of finite presentation: `[LocallyOfFinitePresentation f]`, the recorded Mathlib
  affine-local finite-presentation class.
- An O_X-module: `(F : X.Modules)`, Mathlib's category of sheaves of modules over
  `X.ringCatSheaf` on the Zariski opens.
- Quasi-coherent: `[F.IsQuasicoherent]`, the precise quasi-coherent predicate exposed by
  `pqf-def-coherent`. We retain this explicit node hypothesis even though finite presentation
  also implies it. The conjunction `IsQuasiCoherentFiniteType` is not used, since the node
  asks for quasi-coherence alone at this point.
- Finite presentation of F: `[F.IsFinitePresentation]`, Mathlib's local finite-free
  cokernel-presentation predicate, recorded by
  `def-weil-pbc-module-finite-type-presentation`.
- Zariski direct image with the specified action: `(pushforward f).obj F`. The definition
  `Scheme.Modules.pushforward` in `Mathlib.AlgebraicGeometry.Modules.Sheaf` (line 166)
  uses `SheafOfModules.pushforward f.toRingCatSheafHom`.
  `pushforward_obj_obj` (line 170) identifies sections on V definitionally with
  `Γ(F, f ⁻¹ᵁ V)`. Reading `Sheaf.PushforwardContinuous` and
  `Presheaf.Pushforward` shows the underlying operation is precomposition followed by
  `restrictScalars` along the given ring-sheaf map, hence exactly the action through
  `f.app V = f^sharp(V)` in the node. No arbitrary direct-image object or comparison map
  is introduced, and no extra section formula is added as a theorem clause.
- Conclusion: `((pushforward f).obj F).IsFinitePresentation`, using the same local
  finite-presentation predicate on Y. The node asks for preservation, so there is no
  reverse implication or additional quasi-coherence conclusion.

Dependency declarations read and used:

- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite` (class signature and docstring at lines 35–42).
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation` (lines 41–48).
- `pqf-def-coherent`: import its recorded module
  `Sheaf.AlgebraicGeometry.CoherentFiniteType`; use its exposed
  `SheafOfModules.IsQuasicoherent`. Read that whole module and the upstream coherence
  docstring explaining the three distinct predicates; no second notion is defined.
- `def-weil-pbc-module-finite-type-presentation`:
  `SheafOfModules.IsFinitePresentation` in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` (lines 265–270), the finite
  presentation declaration explicitly named in the node's `lean.declarations` and match.
- Proof imports follow the recorded plan: Mathlib's affine and separated permanence
  declarations and finite coproducts in `Mathlib.AlgebraicGeometry.Limits`;
  `Scheme.Modules.isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated` in
  `WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs`;
  `LocallyOfFinitePresentation.finitePresentation_appLE` in the already public Mathlib
  finite-presentation module;
  `Scheme.Modules.quasicoherent_finite_type_affine` in
  `WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`;
  `Module.finitePresentation_iff_of_finite_of_finitePresentation` in
  `Sheaf.RingTheory.FiniteExtensionModuleFinitePresentation`.
  The last three recorded project theorem signatures/docstrings were read. All four
  steps of the item's proof are included in the theorem docstring, with their DAG ids.

Edge cases checked before writing: identity maps retain F; the zero module has a presentation
with zero generators and relations and remains zero under direct image; empty source and
empty target schemes are admitted without a chosen point or nonempty affine cover. Affine
reduction is precisely restriction of scalars along a finite finitely presented algebra,
including zero rings. Finite non-flat maps and non-Noetherian bases remain allowed. Local
finite presentation is a necessary hypothesis and was not inferred from finiteness alone.
There is no disputed statement or node fault.

Searches run using the prescribed `msearch.py` wrapper:

- LeanFinder: `A finite morphism locally of finite presentation preserves finitely presented
  quasi-coherent modules under direct image` — eight hits, including affine ring-map finite
  presentation and the sheaf finite-presentation predicates, but no preservation theorem.
- Loogle: `SheafOfModules.IsFinitePresentation` — five hits: the class, its constructor,
  presentation data, and the finite-type/quasi-coherent instances; no pushforward theorem.
- Mathlib grep:
  `(finitePresentation|IsFinitePresentation|finite_presentation).*pushforward|pushforward.*(finitePresentation|IsFinitePresentation|finite_presentation)`
  — zero hits.
- Direct `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for the node id and the
  finite-presentation/pushforward combinations found related results only. The read
  `Modules/FinitePushforward.lean` theorem `isFinitePresentation_pushforward_unit`
  assumes a locally Noetherian base and concerns only the structure sheaf; its
  `isFiniteLocallyFree_pushforward` assumes flatness and finite local freeness. The existing
  singleton-fibre theorem is a neighbourhood/stalk equivalence with a specified singleton
  fibre, not the present global assertion. Presentation transport under equivalences in
  `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean` is likewise different.
- The chosen declaration name was searched in Mathlib, both project source roots, and
  `dag/lean_names_upstream.json`: no existing declaration with that name.

Validation: prescribed `scompile.py Q146 lem-trf-finite-pushforward-preserves-finite-presentation`
compiled the delivered file successfully both as a sandbox module (15.8 seconds) and with
its library module name (3.8 seconds), with no errors or unexpected warnings.

## Second reading by Q146

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
