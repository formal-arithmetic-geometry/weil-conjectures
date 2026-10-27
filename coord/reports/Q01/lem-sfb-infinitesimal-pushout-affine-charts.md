## Worker report

Delivered one module, `Sheaf.AlgebraicGeometry.InfinitesimalPushoutAffineCharts`, with two real canonical section-map definitions and seven theorem statements, all theorem proofs `sorry`. No new independent notion or dependency interface is needed. Theorem names listed below are in namespace `AlgebraicGeometry`.

Source read: `literature/stacks-project/more-morphisms.tex`, lines 4206–4340, Tags 07RT (`lemma-pushout-along-thickening`) and 07RV (`lemma-equivalence-categories-schemes-over-pushout`). The node's nine proof steps are distributed across the theorem docstrings, including the matching-sections construction, principal localization, gluing on affine covers of overlaps, module base change, and restriction compatibility.

Hypotheses and clauses:

- All schemes are explicit `Scheme.{u}` binders. `hi : IsThickening i` is the upstream conjunction of closed immersion and surjectivity on points, hence a homeomorphism; no nilpotence exponent is imposed. `[IsAffineHom a]` is exactly the inverse-image affine-open condition.
- The two pushouts are arbitrary specified cocones `hp : IsPushout a i j b` and `hz : IsPushout uX uY k l`. Their existence is the recorded `exists_scheme_affine_thickening_pushout`; selecting an arbitrary cocone with this universal property neither strengthens the geometric hypothesis nor substitutes a chosen arbitrary map.
- The compatible pair of schemes is expressed using `hX : IsPullback uX t x a` and `hY : IsPullback uY t y i`, sharing the SAME map `t : U ⟶ T`. This is equivalent to a specified isomorphism of the two fibre products over T: identify U with the first fibre product and transport the second projection through the specified isomorphism. It excludes precisely the non-T-linear isomorphisms corrected below.
- `p`, `hk`, `hl` specify the unique induced morphism Z to P. `infinitesimalPushout_recovery` concludes `IsPullback k x p j ∧ IsPullback l y p b`. These universal properties say the two canonical comparison maps are isomorphisms with their prescribed projections, and retain the specified overlap through the shared `t` and the pushout equation.
- `infinitesimalPushout_base_affine_chart` quantifies over EVERY `P0` with `IsAffineOpen P0`. `hS0`, `hT'0`, `hT0` identify its inverse images; the redundant containment witnesses merely type `appLE`. They always follow from these equalities and pushout commutativity. Its first three conclusions assert all three inverse images affine, then surjectivity of the actual A' to A map and elementwise nilpotence of its kernel. Its final `IsIso` is the canonical map R to the ring pullback of B and A', defined by their actual restriction maps.
- `infinitesimalPushout_total_affine_chart` quantifies over EVERY affine `Z0` with `hmap : Z0 ≤ p ⁻¹ᵁ P0`. `hX0`, `hY0`, `hU0` specify the three inverse images. The first three clauses give affineness. The next two canonical pushout comparisons give C = D tensor_B A and C = C' tensor_A' A. Surjectivity of C' to C and equality of its kernel with `Ideal.map` of ker(A' to A) give EXACTLY C = C'/IC'. The next canonical pullback comparison is E = D times_C C'. The final two `IsPushout` clauses are E tensor_R B = D and E tensor_R A' = C'. Universal properties are in `CommRingCat` with the actual structural arrows, hence specify algebra isomorphisms over the indicated bases, rather than merely abstract ring isomorphisms. No alternative algebra structures or comparison maps are assumed.
- `infinitesimalSectionPullback_restriction` explicitly equates restricting R/E first and applying the canonical comparison with applying it first and the induced ring-pullback restriction. It applies to both fibre-product identifications. `infinitesimalSectionPushout_restriction` gives the analogous explicit equation for all four tensor comparisons. The generic commutative square specializes respectively to `(uX,t,x,a)`, `(uY,t,y,i)`, `(k,x,p,j)`, `(l,y,p,b)`.
- `infinitesimalQuotient_restriction` uses Mathlib's canonical `RingHom.quotientKerEquivOfSurjective` and `Ideal.quotientMap` and asserts the equation with section restriction. Specialize f = uY; the total-chart kernel equality identifies its quotient with C'/IC'. The containment `hker` is the naturality consequence that types the induced kernel quotient map. These equations apply to all compatible smaller opens; there is no principal-open or affineness restriction on the equations. Compatibility of inverse identifications follows formally by cancellation of the canonical isomorphisms.
- `infinitesimalPushout_open_restriction` states the pushout universal property for every open O of ANY affine-thickening pushout. Apply it to the second pushout, with O = h inverse-image H0, for the node's final assertion for any compatible maps X,Y to any H. The restrictions are the actual `resLE` maps. Affineness of U to X and the thickening U to Y follow from hX/hY and the base hypotheses; no added assumption on X,Y is needed.
- No flatness, finite presentation, Noetherianity, separatedness, or finite-order hypotheses occur.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`, `Scheme.Hom.appLE` and section restriction via `presheaf.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion` (publicly available through the recorded pushout module).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `CategoryTheory.Limits.pullback` and `pushout`, their projections and universal maps; `IsPullback`/`IsPushout` in the corresponding `IsPullback.Defs` module.
- `Sheaf.AlgebraicGeometry.SchemeAffineThickeningPushout`: `AlgebraicGeometry.exists_scheme_affine_thickening_pushout`, imported publicly, supplies the original and total pushout existence.
- `WeilConjectures.AlgebraicGeometry.Thickening`: `AlgebraicGeometry.IsThickening`, reused through that public dependency, never copied.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`; `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffineOpen`; `Mathlib.AlgebraicGeometry.Restrict`: `Scheme.Hom.resLE`.
- Canonical ring construction APIs: `Mathlib.Algebra.Category.Ring.Limits`, `Mathlib.RingTheory.Ideal.Quotient.Operations` (`Ideal.map`, `RingHom.ker`, `Ideal.quotientMap`, `RingHom.quotientKerEquivOfSurjective`).

Proof imports include the available affine-thickening, affine-pinching, affine-open basis, principal-open immersion, scheme morphism gluing, fibre-product affine spectra, quotient spectrum, and radical lemmas. The proof dependencies `lem-sfb-ring-fibre-product-spectrum` and `lem-sfb-patched-module-base-change` have no Lean record or Mathlib match; their imports are omitted and their exact planned uses are retained in the docstrings. They are not prerequisites for typing these statements. `lem-pc-closed-imm-base-change` currently points to an unrelated very-ample lemma; no declaration of that record is used as a replacement for the missing ideal base-change proof. This proof-stage attachment fault does not affect the statement or require a dependency repair here.

Edge cases checked: identity thickenings; empty schemes and empty affine opens; zero coordinate rings; arbitrary locally nil ideals with no common exponent; nonaffine X,Y and arbitrary nonaffine target H; smaller opens not principal and overlaps not affine. All are admitted by these binders. Section rings are in the same universe u as the schemes, so there is no smaller test universe or implicit size restriction. No declaration uses auto-bound variables. Definitions use only actual section maps and categorical universal maps, with their commutativity proved from existing naturality; no definition data is `sorry`.

Searches actually run through msearch.py:

- LeanFinder: `Scheme pushout along thickening affine morphism base change recovery compatible affine charts` returned eight hits, including ideal-sheaf gluing maps, `Scheme.isPullback_toSpecΓ_toSpecΓ`, and affine coproduct descent. None is this infinitesimal pushout theorem.
- Loogle: `AlgebraicGeometry.Scheme, CategoryTheory.IsPushout` returned `isPullback_SpecMap_of_isPushout`, `isPushout_appTop_of_isPullback`, and `isIso_pushoutSection_iff`. These concern scheme pullbacks and ring tensor pushouts; they are useful encodings, not the present recovery and fibre-product chart assertion.
- Mathlib grep: `thicken.*pushout|pushout.*thicken|Milnor|patching` in AlgebraicGeometry returned zero hits.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for thickening/pushout and this node id found the existence module and downstream curve/space uses, not the present statement. Read the existence module and its complete signature/docstring. Also inspected Mathlib Scheme, Restrict, Affine, Pullbacks, ring limits, pullback universal-property, and quotient APIs directly.

Validation: scompile.py compiled both sandbox and destination module views without errors or warnings. Every theorem remains a whole-proof `sorry` as required by stage 2. The definitions compile using actual universal-property data. No new nodes or dependency modules are delivered.

## Statement corrected

The only statement edit makes the displayed overlap isomorphism explicitly **over T**. The old statement is preserved verbatim in `statement_change.old_statement`. Without this condition the induced map Z to P need not exist: let i = a = identity on a scheme T with a nontrivial automorphism σ, take X = Y = T with identity structural maps, and use σ as the overlap isomorphism. The two maps from the overlap to P = T are then identity and σ. For a concrete example take T = Spec(Q[t]) and the automorphism t ↦ t+1. Their proposed common extension would force σ = identity.

Tag 07RV defines the compatible triples as a fibre product of slice categories over Sch/T, and the first proof paragraph explicitly uses a map over T. The correction restores exactly this source hypothesis; the node is not the statement of a blueprint unit (`blueprint.is` is null). No proof step or dependency list changes are needed.

All citers were read; the six uses remain valid:

- `lem-sfb-scheme-pushout-flat-patching`: holds=true. The compatible triple is an object over the common base T in Tag 07RX; its overlap identification is T-linear, so recovery and all ring charts remain available.

- `lem-sfb-proper-scheme-deformation-hull`: holds=true. The deformation gluing in proof step 2 explicitly identifies the deformations over A, hence over Spec A = T.

- `lem-sfb-space-relative-flat-module-pushout`: holds=true. Only the identity pair over the original scheme pushout is used; its overlap identification is the identity over T.

- `lem-sfb-scheme-infinitesimal-etale-patching`: holds=true. The etale triples and their overlap maps are over T as in Tag 07RV; the canonical unit and its chart calculations are unchanged.

- `lem-sfb-space-coherent-tangent-finite`: holds=true. Only the identity pair is used to identify the Artinian base pushout with its ring fibre product.

- `lem-sfb-space-affine-thickening-pushout`: holds=true. Scheme recovery is applied to compatible triples over T; the recorded recovery theorem already requires the overlap projection equation hφ.

## Second reading by Q01

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
