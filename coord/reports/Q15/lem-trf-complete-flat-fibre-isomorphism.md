## Worker report

The module `Sheaf.RingTheory.CompleteFlatFibreIsomorphism` states
`IsLocalRing.complete_flat_fibre_isomorphism`, with one `sorry` and no new definitions.
Only the item's `lean` field changes. No dependency interface needs repair and no statement
correction is necessary.

Hypothesis-by-hypothesis rendering:

- The three commutative local rings are `{A : Type u} {C : Type v} {B : Type w}` with
  their `CommRing` and `IsLocalRing` instances. Universes are independently quantified.
  Their maximal ideals are the canonical `IsLocalRing.maximalIdeal` ideals.
- Noetherianity of C and B is `[IsNoetherianRing C] [IsNoetherianRing B]`.
  No Noetherianity of A is imposed.
- Completeness for the respective maximal ideals is
  `[IsAdicComplete (maximalIdeal C) C] [IsAdicComplete (maximalIdeal B) B]`.
  These include Hausdorffness, as required by the node.
- The given maps from A are encoded by `[Algebra A C] [Algebra A B]`. Their locality
  is `[IsLocalHom (algebraMap A C)] [IsLocalHom (algebraMap A B)]`.
- The local A-algebra map is `(φ : C →ₐ[A] B) [IsLocalHom φ.toRingHom]`;
  `AlgHom.commutes` expresses compatibility with the given A maps.
- Flatness of the target over A is `[Module.Flat A B]`. There is no C-over-A flatness
  hypothesis.
- The fibre isomorphism is `hFibre : Function.Bijective (...)`, where the map is the
  canonical `Submodule.mapQ` of `φ.toLinearMap` from C/mC to B/mB. Here mC is
  `maximalIdeal A • (⊤ : Submodule A C)`, and likewise for B. These are exactly the
  extended maximal ideals, viewed as A-submodules. The map sends the class of c to the
  class of φ(c), by `Submodule.mapQ_apply`. This is the underlying A-linear map of the
  induced quotient ring homomorphism; bijectivity is precisely that homomorphism being
  an isomorphism. It does not assert a freely chosen isomorphism between the fibres.
  The existing `Submodule.smul_top_le_comap_smul_top` supplies well-definedness.

Conclusion-by-conclusion rendering:

- Injectivity: `Function.Injective φ`.
- Extended maximal ideal equality: `(maximalIdeal C).map φ.toRingHom = maximalIdeal B`.
- Isomorphism of the specified residue-field map:
  `Function.Bijective (IsLocalRing.ResidueField.map φ.toRingHom)`. This existing canonical
  ring homomorphism is the map C/c to B/n; bijectivity expresses that it is an isomorphism.
- Finiteness via φ: `@Module.Finite C B _ _ (Module.compHom B φ.toRingHom)`.
- Generation by 1: `@Submodule.span C B _ _ (Module.compHom B φ.toRingHom) {1} = ⊤`.
  The two explicit module arguments ensure the action is exactly c • b = φ(c)b, without
  introducing an unrelated C-module structure or a let binder.
- The final A-algebra isomorphism: `∃ e : C ≃ₐ[A] B, e.toAlgHom = φ`.
  The equality ties the equivalence to the original map, rather than asserting only
  that the rings happen to be isomorphic.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (and its ideal-FG interpretation).
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete`, extending `IsHausdorff`
  and `IsPrecomplete`; `AdicCompletion.of_bijective_iff` confirms the node's interpretation.
- `Mathlib.RingTheory.RingHom.Flat`: `Module.Flat` and `RingHom.Flat`, with
  `RingHom.flat_algebraMap_iff` identifying the algebra-module encoding.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.RingTheory.LocalRing.ResidueField.Basic`: `IsLocalRing.ResidueField.map`.
- Proof-only import `WeilConjectures.RingTheory.FlatModInjective`: `flat_mod_injective`.
- Proof-only import `WeilConjectures.RingTheory.FiniteOverCompleteRing`:
  `Module.finite_and_span_eq_top_of_adicComplete`.

The recorded dependency source signatures and docstrings were read in full. The module's
proof docstring follows all five steps of the node: flat-target injectivity (00ME), elementary
maximal-ideal and residue calculations, separation by completeness, finiteness and the specific
generator from 031D, then surjectivity and inversion. The source paragraphs were read in
`literature/stacks-project/curves.tex` (0CBX, final paragraph) and `algebra.tex` (00ME and 031D,
including the proof's chosen-generator assertion). This is the historical extracted tool
identified in the node's blueprint metadata; it does not alter the current blueprint unit.

Edge cases checked before writing:

- If A is a field, m = 0 and the fibre map is the original map, so the assertions agree.
- Identity maps on complete Noetherian local algebras give all the required clauses.
- Zero rings are excluded already by Mathlib's standard nontrivial local-ring notion,
  matching the node's unique-maximal-ideal convention.
- A need not be Noetherian or complete. The signature imposes neither requirement.
- Without target flatness, k[ε]/(ε²) → k over A = k[ε]/(ε²) has identical closed fibres
  but is not injective. The flatness condition is substantive.
- Without completeness of C, k[t]_(t) → k[[t]] over A = k[t]_(t) has equal closed fibres
  and flat target, but is not surjective. Completeness of C is retained.
- There is no finite-residue-field, equal-universe, or finite-dimensional assumption.

Searches for an existing statement (all on 2026-10-24):

- `msearch.py ... leanfinder`: “A local map of complete Noetherian local algebras over a
  local ring is an isomorphism if its closed fibre is an isomorphism and the target is flat”.
  Eight hits included `Module.FaithfullyFlat.of_flat_of_isLocalHom` and
  `Algebra.FormallySmooth.flat_of_algHom_of_isNoetherianRing`; none states this criterion.
- `msearch.py ... loogle "IsAdicComplete, Function.Bijective"`: only
  `AdicCompletion.of_bijective` and `AdicCompletion.of_bijective_iff`, which concern the
  canonical completion map, not an arbitrary local map of complete algebras.
- `msearch.py ... leansearch`: “A local map between complete local algebras with flat target
  and bijective reduction modulo the base maximal ideal is bijective”. Eight hits gave
  localization and faithfully-flat tensor descent criteria, not this theorem.
- `msearch.py ... grep "bijective.*(adic|complete)|isomorph.*fibre|injective.*flat"
  RingTheory`: 25 hits, concerning tensor injectivity, spectra and similar separate facts.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` for
  complete/flat isomorphism and adic bijectivity patterns: related formal-smoothness and
  completion results only. `grep -rn` of the item id in `lean/WeilConjectures` found nothing.
  A name-collision search for `complete_flat_fibre_isomorphism` over Mathlib, both project
  source trees and the upstream names index found nothing.

No STATEMENT-DISPUTED flag or node fault was found. The prescribed `scompile.py` compiled the
file both as a private sandbox module and as its final library module, cleanly (1.5 s and 4.4 s).

## Second reading by Q15

This is the worker's final self-reading; the maintainer supplies the independent review as
specified in the dispatch brief. Reopened the node and final module and matched every binder
and all six conclusion clauses as listed above. In particular, checked that the fibre map is
the one induced by φ, that both module conclusions use `Module.compHom B φ.toRingHom`, that
the residue map is canonical, and that the final equivalence has underlying map exactly φ.
No mismatch was found, so no mathematical changes were made. The statement remains unchanged;
there are no new nodes or dependency modules.
