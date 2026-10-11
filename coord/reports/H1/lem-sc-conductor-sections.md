## Worker report

The module `Sheaf.AlgebraicGeometry.ConductorSections` states
`AlgebraicGeometry.Scheme.Modules.conductor_sections`, with the sole proof `sorry`.
No definitions or auxiliary theorems are introduced. The node copy changes only `lean`.

Hypothesis and clause mapping:

- The reduced scheme Y is `(Y : Scheme.{u}) [IsReduced Y]`.
- The finite list of components with a distinguished first member is
  `C : Fin (r + 1) → Scheme.{u}`, indexed from zero. Thus Lean's `r + 1` is
  the prose's number of components, and `C 0` is its Z_1.
- Each component's reduced closed subscheme structure is supplied by
  `i : ∀ k, C k ⟶ Y`, `[∀ k, IsClosedImmersion (i k)]`, and
  `[∀ k, IsReduced (C k)]`. `hcomponents` says each image belongs to
  `irreducibleComponents Y`; `hcover` says their union is all of Y.
- The reduced closed subscheme on the union of the remaining components is
  `(Z : Scheme.{u}) (j : Z ⟶ Y) [IsClosedImmersion j] [IsReduced Z]`.
  `hZ` identifies its image with the union indexed by `k ≠ 0`.
- The ideal sheaf I is `j.ker`, the recorded dependency's declaration.
  `I₁ := I.comap (i 0)` is its image ideal on the first component, not an
  arbitrary ideal and not an unjustified identification of pullback modules.
  Mathlib defines `comap` through the closed subscheme base change, i.e. the
  extended ideal `I O_{Z_1}`.
- The invertible module and nonnegative exponent are `(M : Y.Modules)
  [M.IsInvertible] (m : ℕ)`. `N := M.tensorPow m` includes exponent zero.
- `N₁ := (pullback (i 0)).obj N` is the restricted tensor power. This is
  canonically isomorphic to `((pullback (i 0)).obj M).tensorPow m` by the
  existing `nonempty_pullback_tensorPow_iso` in
  `WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula` (lines 73–82).
  Using the former avoids choosing an arbitrary isomorphism in the section map.
- The ideal products are `I.toModules ⊗ N` and `I₁.toModules ⊗ N₁`.
  Their inclusions into the line bundles are explicitly `a` and `b`, obtained
  by tensoring `toModulesι` with the line bundle and composing with the left
  unitor. Tensoring with an invertible module preserves the injection, so these
  tensor products realize the ideal products in the prose.
- The global-sections isomorphism is `∃ e : Γ(I.toModules ⊗ N, ⊤) ≃+
  Γ(I₁.toModules ⊗ N₁, ⊤)`. The equation for every source section says its
  image, included by `b`, is the canonical restriction of its inclusion by `a`.
  Thus this is the canonical restriction bijection, not just existence of an
  unrelated additive equivalence. Restriction is intrinsically linear over
  Γ(Y,O_Y), with scalars on the target acting through `(i 0).app ⊤`.
- For every right-hand section `s`, `∃! t : Γ(N, ⊤), ...` asserts unique
  extension as a section of the ambient tensor power. The two equations say
  restriction to the first component equals `b.app ⊤ s` and restriction to Z
  is zero. In particular uniqueness is among all sections satisfying these two
  equations, with no extra nonvanishing constraint on that uniqueness assertion.
- The final pointwise equivalence says y is in the nonvanishing locus of any
  such extension iff it is the image of some x in the original section's locus.
  Each locus is rendered by exactly the germ-outside-maximal-ideal-times-stalk
  formula used in `Sheaf.AlgebraicGeometry.Ample`, `Scheme.Modules.IsAmple`.
  The equivalence implies both containment in Z_1 and agreement there, since
  `(i 0).base` is injective. There is no ampleness hypothesis.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`
  (sectionwise reducedness, with the stated stalkwise equivalence).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (closed embedding, surjective stalk maps).
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`, maximal irreducible subsets.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `tensorPow`, and the monoidal
  structure on scheme modules. IsInvertible is locally trivial of rank one;
  quasi-coherence follows from this definition, rather than being an added hypothesis.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `AlgebraicGeometry.Scheme.Hom.ker`.
- `Sheaf.AlgebraicGeometry.Ample`: `AlgebraicGeometry.Scheme.Modules.IsAmple`
  was read for its nonvanishing formula. That dependency has no separate locus
  declaration: the theorem writes its formula inline and does not import an
  otherwise unused ampleness predicate.

Other existing APIs used: `IdealSheafData.comap` from Mathlib's
`IdealSheaf.Functorial`; `toModules` and `toModulesι` from
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module` (kernel module and
its inclusion); `pullbackUnitApp` from
`WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit` (adjunction unit on sections).
Their definitions and docstrings were read. All variables and the universe are bound.

Source checked: the local Stacks source is absent on this machine, so read
https://raw.githubusercontent.com/stacks/stacks-project/master/varieties.tex,
labels `remark-conductor` (09NW) and
`lemma-dim-1-noetherian-reduced-separated-has-ample` (09NX).
09NW proves I → I(A/J) is an isomorphism for a reduced ring with V(I)∪V(J)=Spec A,
and similarly for a projective module. 09NX uses exactly the displayed global
sections equality and ideal-supported extension. The node correctly isolates this
argument; it needs no Noetherian, separated, dimension-one, or ampleness assumption.

Edge cases: one component is `r = 0`, so the union of other components is empty,
Z is empty, I=O_Y, and restriction is tautological. The empty Y has no component
and cannot satisfy `hcomponents`, exactly as in the prose with a distinguished Z_1.
The exponent zero gives the structure sheaf, with no positivity restriction.
Zero sections have empty nonvanishing locus. For disjoint components this is
extension by zero. For `k[x,y]/(xy)`, first component V(y), other component V(x),
I=(x), J_1=(y), and I∩J_1=0; the section at the intersection vanishes on both sides.
No characteristic or finite-type restriction is imposed. The universe `u` is arbitrary.

Searches for an existing statement:

- `msearch.py ... leansearch "conductor ideal global sections reduced scheme components"`:
  service unavailable, Internal Server Error, no result; no mathematical verdict assigned.
- `msearch.py ... leanfinder "Global sections of an invertible sheaf vanishing on other
  irreducible components extend uniquely from one component of a reduced scheme"`:
  eight results, including `exists_of_res_eq_of_qcqs_of_top`,
  `exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen`,
  `IsReduced.component_reduced`, and `Scheme.zero_of_zero_cover`; no exact statement.
- `msearch.py ... loogle "Scheme.Hom.ker, Scheme.Modules"`: no hits,
  unknown identifier Scheme.Hom.ker in that service's index.
- `msearch.py ... grep "conductor|ideal.*[Mm]odule" AlgebraicGeometry`: seven
  generic ideal/module hits, no conductor-sections theorem.
- `rg -n 'conductor|lem-sc-conductor-sections'` in source `WeilConjectures` and
  project `lean/Sheaf`: no result. `grep -rn 'lem-sc-conductor-sections'` in the
  source repository: no result. Searches for `conductor_sections|ConductorSections`
  in Mathlib, WeilConjectures, lean/Sheaf, and `dag/lean_names_upstream.json`: no result.
- Additional direct searches found the existing ideal-sheaf module bridge and
  pullback section APIs, so no duplicate definitions or new nodes were needed.

Validation: server single-file compile passed, without errors or warnings (2.2 s).
No statement fault or STATEMENT-DISPUTED issue was found.

## Second reading by H1

I read the node, its source (Stacks `varieties.tex`, Remark 09NW at label
`remark-conductor`, and the displayed equality in the proof of Lemma 09NX), all
statement dependencies, and `ConductorSections.lean` independently.

The statement checklist and verdicts are as follows.

- `Y : Scheme.{u}` with `[IsReduced Y]` renders the reduced scheme Y; no
  Noetherian, separated, characteristic, or finite-type assumption is added.
- `r : ℕ`, `C : Fin (r+1) → Scheme.{u}`, and `i : ∀ k, C k ⟶ Y` render the
  finite components with distinguished `C 0 = Z₁`; the two typeclass binders
  render closed immersions and reduced component structures.
- `hcomponents` puts every component image in `irreducibleComponents Y`, and
  `hcover` says their union is all of Y, exactly the component hypotheses.
- `Z`, `j`, its closed-immersion and reduced instances, and `hZ` render the
  reduced closed subscheme on the union of components with `k ≠ 0`.
- `M : Y.Modules`, `[M.IsInvertible]`, and `m : ℕ` render an invertible module
  and arbitrary nonnegative tensor exponent (including zero).
- The lets render `N = M.tensorPow m`, its pullback `N₁`, `I = j.ker`,
  `I₁ = I.comap (i 0)`, and the ideal-product inclusions `a` and `b` via
  `toModulesι`, tensoring, and the left unitor.
- The additive equivalence `e` and its equation with `pullbackUnitApp` state the
  canonical restriction isomorphism on the two ideal products, rather than an
  unrelated equivalence.
- For every right-hand section `s`, the `∃! t` clause gives the unique ambient
  section whose restriction to `C 0` is `b.app ⊤ s` and whose restriction to Z
  is zero. The following universal clause gives the stated nonvanishing-locus
  equivalence, with the germ/maximal-ideal formula from `IsAmple` inline.
  Quantifier order and all three conclusion clauses agree with the node.

Edge cases checked: `r = 0` gives one component and the empty union for Z;
`m = 0` gives the structure module; zero sections have empty nonvanishing
loci; an empty Y cannot satisfy the component-cover hypotheses; arbitrary
characteristic and universe `u` are admitted. The finite index is nonempty
because it is `Fin (r+1)`.

Searches found no duplicate conductor-sections declaration in Mathlib,
`WeilConjectures`, or `lean/Sheaf`; LeanSearch was unavailable, LeanFinder and
Loogle returned only generic scheme/sheaf results, and direct `rg` searches for
`conductor`, `conductor_sections`, and the node id found no existing statement.
The existing dependency `AlgebraicGeometry.Scheme.Modules.IsAmple` was opened
and is the absolute Stacks 01PS notion used by the inline locus formula.

The worker report incorrectly said the Stacks source was absent; it is available
in `/home/ubuntu/c1-stacks-review/varieties.tex`. I corrected that assessment in
this report only. No Lean or node statement mismatch was found, so no source or
signature change was needed. The module compiles cleanly with `scompile.py`.

## Reviewer fix (R-cse1150)

The statement was mathematically right; four form changes, no change of content:

- Component list in the form of the landed sibling `conductorIdeal_restriction_isIso`
  (lem-sc-conductor-ideal-restriction): `{ι : Type v} [Finite ι]`, a distinguished `a : ι`
  in place of `Fin (r + 1)` and `0`, `Set.range (i b)`, and the hypothesis `hdistinct`
  (the prose lists distinct components `Z_1, …, Z_r`; the delivery omitted it).
- Module pullback is the project's `tensorPullback` (def-pc-module-pullback), not Mathlib's
  abstract `Scheme.Modules.pullback`; restriction of global sections is the unit of the
  canonical adjunction pinned in `exists_tensorPullbackAdjunction`
  (lem-pc-module-pullback-adjunction), in place of `pullbackUnitApp`.
- The non-vanishing loci use `nonvanishingLocus` (STATE NON-VANISHING LOCUS) instead of the
  inline germ predicate, and the last clause is the set equality
  `nonvanishingLocus N t = i a '' nonvanishingLocus N₁ (μ₁.app ⊤ s)`.
- The ideal-product inclusions are renamed `μ`, `μ₁` (the index is `a`, as in the sibling).
