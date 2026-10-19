## Worker report

The module `Sheaf.AlgebraicGeometry.ArbitrarySchemeUntensoredBaseChange` states
`AlgebraicGeometry.Etale.arbitraryScheme_untensored_baseChange`, with proof `sorry`.
It defines no new object. The statement is the F_ℓ-linear bounded-below exchange
isomorphism for the product of an arbitrary K-scheme with S', with g qcqs.

Clause-by-clause reading:

- K is a field: `{K : Type u} [Field K]`.
- Z and S' are K-schemes: `{Z S' T : Scheme.{u}}`,
  `(z : Z ⟶ Spec (.of K))` and `[S'.Over (Spec (.of K))]`.
  The explicit structure map z is used in the product, as in the existing finite-type
  theorem. T acquires its K-structure by `g ≫ (S' ↘ Spec (.of K))`; no independent
  structure or compatibility assumption on T is necessary.
- The arbitrary qcqs morphism is `(g : T ⟶ S') [QuasiCompact g] [QuasiSeparated g]`.
- X' is exactly `pullback z (S' ↘ Spec (.of K))`. Its projection f' is
  `pullback.snd z (S' ↘ Spec (.of K))`; its projection p is `pullback.fst`.
- Y is exactly `pullback f' g`, h is `pullback.fst f' g`, and e is
  `pullback.snd f' g`. They are the inferred corners and sides of
  `CommSq.mk (pullback.condition (f := f') (g := g)).symm`.
  The symmetry is required: the exchange interface takes `CommSq e h g f'`,
  whose equation is `e ≫ g = h ≫ f'`.
- ℓ is prime: `(ℓ : ℕ) [Fact ℓ.Prime]`; invertibility in K is `_hℓ : IsUnit (ℓ : K)`.
- An arbitrary F_ℓ-vector-space sheaf is the binder F in
  `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))`.
  For prime ℓ, ZMod ℓ is F_ℓ; ULift is the standard ring universe lift used throughout
  this project's constant-coefficient six-functor interface, not a coefficient change.
- F is placed in degree zero by `(_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F`.
- The claimed isomorphism is `IsIso ((derivedBaseChangeMapPlus _ sq).app (F[0]))`.
  The existing definition has source `Rg_* ⋙ D⁺(f'⁻¹)` and target
  `D⁺(e⁻¹) ⋙ Rh_*`, so its component is the exact map in D⁺(X'_et,F_ℓ).
- The canonical-map clause is rendered by the existing `derivedBaseChangeMapPlus`,
  not by a freely chosen arrow or by an existential isomorphism. Its source docstring
  defines the right-derived descent of the termwise `baseChangeMap`;
  `baseChangeMap` is the mate of `squareUpperStarIso` under the inverse/direct-image
  adjunctions. `upperStar_map_baseChangeMap_app_counit` gives precisely the square
  identification followed by e⁻¹ of the counit of g. Right-derived descent gives
  the stated bounded-below adjoint mate, with exact inverse images termwise.
- No finite-type, Noetherian, separatedness, boundedness, or constructibility condition
  on any scheme or on F is present.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, `pullback.condition`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and its QuasiCompact import:
  `AlgebraicGeometry.QuasiCompact`. `LocallyOfFiniteType` is deliberately not a hypothesis.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `AlgebraicGeometry.QuasiSeparated`, defined by quasi-compactness of the diagonal.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the recorded D, D⁺ and module
  sheaf encoding. Its current source was read with `scompile.py --source`, since the
  older source checkout lacks that module. It uses the same ModuleCat universe as here.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, `upperStar`, `upperStarLowerStarAdjunction`.
  `rightDerivedLowerStarPlus` is in the imported `Derived.UpperLowerStarCoherence`.
- `WeilConjectures.SixFunctors.BaseChange.Derived`:
  `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`, already recorded for
  `def-weil-pbc-derived-exchange` in the item's proof dependencies.
- `DerivedCategory.Plus.singleFunctor` places the sheaf in degree zero.

The module also imports every available recorded module of the stated proof dependencies
as ordinary imports; the theorem docstring transcribes all seven steps, including the
termwise restriction argument, finite-type approximation, coefficient forgetting, and
bounded/unbounded agreement required by the reviewed DAG.

Source read: `literature/stacks-project/etale-cohomology.tex`,
`lemma-punctual-base-change` (0F1I), its first proof paragraph,
`lemma-base-change-Rf-star-colim` (0EZT), and the use in 0F1J.
0F1I itself explicitly quantifies over arbitrary K-schemes; its proof makes the
finite-type reduction using affine inverse limits, exactly as this node's proof does.

Edge cases checked against the binders and map:

- Z empty and T empty are admitted: no nonemptiness assumption occurs.
- F = 0 is admitted; the map remains the canonical exchange on its zero-degree complex.
- Z = Spec K and g an identity are admitted without a nontriviality assumption on g.
- Z = Spec K[t₁,t₂,…] is admitted: there is no finite-type binder on z.
- Positive characteristic excludes exactly ℓ equal to that characteristic through
  `IsUnit (ℓ : K)`; characteristic zero admits every prime ℓ. ℓ = 0 and 1 are
  excluded by the prime assumption, as required.
- Universes are explicitly bound. The sites and coefficient categories retain the
  existing Scheme.{u}/ModuleCat.{u+1} convention; no site universes are identified.

Searches (2026-10-17):

- msearch LeanSearch, query "Base change for etale sheaves of prime-field modules along
  an arbitrary scheme over a field": eight generic hits, including Scheme.Modules
  pullback/pushforward and smallEtaleTopology; no exchange-isomorphism theorem.
- msearch LeanFinder, query "Etale cohomology product base change arbitrary scheme over
  a field": eight hits on algebraic etaleness and differential base change; no match.
- msearch Loogle, query `"baseChange", "Sheaf"`: two sheaf-coverage hits; no match.
- msearch Mathlib grep, query `punctual|untensored|derivedBaseChangeMapPlus`: zero hits.
- rg in WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json for
  `arbitrary_scheme|arbitraryScheme|baseChange_towardsSpecField|punctual_base|untensored`:
  the existing finite-type-only `baseChange_towardsSpecField` and discussion in the
  parent tensor theorem, but no arbitrary-scheme theorem. The finite-type-only
  theorem was opened in full and does not match this statement.
- The literal item-id search in upstream WeilConjectures finds no declaration.

Validation: `scompile.py Q13 lem-kun-0f1j-arbitrary-scheme-untensored-base-change`
compiled both its sandbox and library module forms cleanly (1.9 s and 2.2 s),
including the required current overlay dependencies. No compiler errors or warnings.

No statement correction, new node, dependency repair, or statement dispute is needed.

## Second reading by Q13

A separate reading pass by this worker compared the node, Stacks 0F1I and 0EZT, and the
finished Lean signature. This is not a claim of a second independent agent; the required
independent maintainer review remains the delivery gate. The pass checked the field and
prime hypotheses, both product projections, all four square arrows, degree zero, and
the D⁺ rather than unbounded exchange. In particular the square must be oriented
`CommSq e h g f'`, hence the `.symm` on `pullback.condition`. It checked that arbitrary
Z is retained (the finite-type theorem is a proof input only), and that T is allowed
its induced K-structure without an added `IsOver` hypothesis. The ULift coefficient
choice agrees with the recorded derived-category module and existing project uses.
No mismatch or file correction was found in this pass.
