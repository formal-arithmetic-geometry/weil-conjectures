## Worker report

The module `Sheaf.AlgebraicGeometry.InfinitesimalVanishingSectionLifting` states
`AlgebraicGeometry.Scheme.Modules.exists_neighbourhood_section_of_infinitesimal_vanishing`.
Its proof is exactly `sorry`. The docstring gives all eight steps of the DAG proof,
including the finite-level image-stabilization argument, without assuming completeness
or flatness of the original proper morphism.

The auxiliary definition `infinitesimalSectionLiftingLayer` is the concrete object K_n
introduced in this very statement. It only composes existing constructions, has real
data, and is recorded in `lean.declarations`. It introduces no independent notion:
its local let names precisely the specified extended ideal, not an arbitrary ideal.
No node statement, dependency interface, or dependency list was changed.

Clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| Schemes Z and S, and f: Z → S | `{Z S : Scheme.{u}} (f : Z ⟶ S)` |
| Proper f | `[IsProper f]` |
| Noetherian base, explicitly locally Noetherian and quasi-compact | `[IsLocallyNoetherian S] [CompactSpace S]` |
| A point s of S | `(s : S)` |
| An invertible O_Z-module E | `(E : Z.Modules) [E.IsInvertible]` |
| A = O_{S,s}, m = maximal ideal | `S.presheaf.stalk s`, `IsLocalRing.maximalIdeal (S.presheaf.stalk s)` in the layer definition |
| k = κ(s) = A/m | Mathlib `f.fiber s` and `f.fiberι s` use `S.fromSpecResidueField s`; `Scheme.residueField` is `IsLocalRing.ResidueField` of that same stalk |
| X = Z ×_S Spec A along the canonical map | `Limits.pullback f (S.fromSpecStalk s)` |
| The projections h and g | `pullback.fst f (S.fromSpecStalk s)` and `pullback.snd f (S.fromSpecStalk s)` |
| E_X = h*E | `(tensorPullback (pullback.fst f (S.fromSpecStalk s))).obj E` |
| J = m O_X | The maximal ideal is mapped through `(Scheme.ΓSpecIso (S.presheaf.stalk s)).inv.hom`, associated by `IdealSheafData.ofIdealTop`, then extended by `.comap (pullback.snd ...)` |
| J^n and J^n/J^(n+1) | `(Scheme.idealSheafPower J.toModulesι n).1` and `formalModuleQuotient J 1` of this object; its denominator is the multiplication image J J^n, exactly J^(n+1) |
| Tensor that layer with E_X | `⊗` in the existing monoidal category of module sheaves, in `infinitesimalSectionLiftingLayer` |
| Vanishing for every integer n ≥ 1 | `hvanishing : ∀ n : ℕ, 1 ≤ n → IsZero ((RingedSpace.moduleCohomology ... 1).obj (infinitesimalSectionLiftingLayer f s E n))`; the natural index enumerates precisely the positive integer powers |
| Every t in Γ(Z_s,E_s) | Unrestricted `(t : Γ((tensorPullback (f.fiberι s)).obj E, ⊤))` |
| An open neighbourhood U of s | `∃ U : S.Opens, s ∈ U ∧ ...` |
| A section on f^{-1}U of E restricted there | `∃ σ : Γ(E, f ⁻¹ᵁ U), ...`; evaluation on the open is exactly sections of the restricted sheaf |
| Its pullback to Z_s equals t | `tensorPullbackSection (f.fiberι s) E (f ⁻¹ᵁ U) σ` equals the restriction of t by the existing presheaf map |

For the last equation, both sides are evaluated on
`(f.fiberι s) ⁻¹ᵁ (f ⁻¹ᵁ U)`. This open is the entire fibre: Mathlib's
`Scheme.Hom.range_fiberι` says the range of `f.fiberι s` is exactly `f ⁻¹' {s}`,
and `s ∈ U`. Writing the equation on this definitionally common open avoids a
transport cast while retaining equality on the whole fibre. The right side is the
canonical restriction of t, not a separately chosen section or map. The left side
uses the actual section `1 ⊗ σ` in the recorded normalized tensor pullback API.

Dependency declarations read and used (imports may supply some elementary notions
transitively):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` and its monoidal module structure.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor`; the local ring uses the same Mathlib stalk.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, as used by the fibre.
- `WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism`:
  `Scheme.fromSpecStalk_local_properties` and the canonical Mathlib `Scheme.fromSpecStalk`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `Limits.pullback`,
  `pullback.fst`, `pullback.snd`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSection`,
  `tensorPullbackSectionAdjunction` (the explicit functor is publicly imported from upstream).
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `Scheme.Hom.fiberι`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`: `Scheme.IdealSheafData.comap`.
- `WeilConjectures.AlgebraicGeometry.CoherentFormalModule`: `formalModuleQuotient`;
  its publicly imported `Scheme.idealSheafPower` and `Scheme.idealModuleProductι`
  give the powers and multiplication-image quotient.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  the recorded shared sheaf tensor/monoidal interface; the scheme monoidal instance
  is the existing specialization from the invertible-module module, not a new tensor.
- `WeilConjectures.AlgebraicGeometry.PQFCohomology`:
  `sheafCohomologyAndHigherDirectImages`, using its recorded
  `RingedSpace.moduleCohomology` (right derived module global sections).

All stated proof-dependency modules are imported privately when not already public
statement imports: localization permanence, the coherent finite-type criterion,
quotient base change, closed-immersion unit quotient, section-boundary exactness,
Mittag-Leffler cohomology bounds, local-stalk comparison and the higher-direct-image
presheaf. The Mathlib affine-open and finite-type Noetherian results, and proper
base-change instance, are already in the public Noetherian/Proper imports.

Edge cases checked: n = 1 is included; n = 0 imposes no vanishing condition.
If the local ring is a field, J = 0 and all positive layers vanish; the conclusion
is the expected local spreading of a fibre section. If the fibre is empty, its
only section is zero and zero lifts. Empty Z is permitted. Empty S has no s, so
its pointwise statement is vacuous, without requiring Nonempty S globally.
The zero fibre section is unrestricted. No surjectivity, flatness, completeness,
nonzero section, or global triviality assumption has been introduced. The one
explicit universe u is shared by schemes, their rings and sheaves as in the
recorded scheme-module definitions, with no independent smaller test universe.

Searches performed on 2026-10-24 using the prescribed wrapper:

- LeanFinder: “For a proper morphism over a Noetherian base vanishing H1 of
  successive maximal ideal layers of an invertible module implies every fibre
  section lifts near the base point”. Eight hits, including
  `exists_lift_of_germInjective`, `ModuleCat.Tilde.exists_const`, and affine-limit
  section spreading; none is the cohomological infinitesimal lifting statement.
- Loogle: `AlgebraicGeometry.IsProper`. Twelve class, permanence and stability hits;
  no fibre-section lifting criterion.
- Mathlib grep: `infinitesimal|ML_cohomology|section.*lifting`, subdirectory
  `AlgebraicGeometry`. Two hits, both the unrelated formally unramified criterion.
- LeanSearch: “Vanishing H1 of successive ideal quotients of an invertible sheaf
  on a proper local base change implies neighbourhood lifting of every fibre section”.
  Eight hits on stalk spreading, formal smoothness, ideal sheaves and quotient
  morphisms, with no matching theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for infinitesimal vanishing/section
  combinations found unrelated formal Hom algebraization, section-image stabilization
  for spaces, units kernels and marked infinitesimal automorphisms. No exact theorem.
- The literal node-id grep in `lean/WeilConjectures`, and declaration-name searches
  in both source roots and `dag/lean_names_upstream.json`, found no match.

Source checked: local `literature/stacks-project/coherent.tex`, lines 5995–6089
(Tag 0D2M), including local-base-change reduction, successive quotient sequences,
and the final citation of Tag 02OB(3). This node extracts exactly the degree-zero
lifting argument under its explicit H1 hypothesis. No statement dispute or correction.

Validation: `scompile.py Q73 lem-trf-infinitesimal-vanishing-section-lifting` compiled
both the sandbox and final library module cleanly (4.8 and 4.9 seconds).
The initial probe exposed the namespace ambiguity between scheme fibre-product
`Limits.pullback` and module `pullback`; all scheme fibre products are now qualified.

## Second reading by Q73

Author's second pass, with the DAG statement and final Lean file open; the maintainer
performs the independent review under the dispatcher's direct-delivery protocol.
I checked every row above against the binders, the helper body and the section equation.
The key points were that the quotient uses J times J^n, not the unrelated J^n times E;
that only n ≥ 1 is assumed; that cohomology is the module right-derived functor; and
that the section equation is on the whole fibre because s lies in U. The helper uses
the genuine extended maximal ideal, and both pullbacks use the recorded tensor functor.
The chosen section map is the actual `tensorPullbackSection` rather than a freely
chosen adjunction unit. No mathematical hypothesis or conclusion changed on this pass.
The sole elaboration repair was qualifying `Limits.pullback`; an unnecessary `show`
term in the signature was replaced by a type annotation, keeping the signature free
of hidden let/have expressions. All theorem proof content remains `sorry`.
