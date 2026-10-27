## Worker report

The module `Sheaf.AlgebraicGeometry.Modules.NormFrameTensorSectionGluing` states
`AlgebraicGeometry.Scheme.Modules.norm_frame_tensor_section_gluing`, with one
postponed proof, and constructs the local pure tensor section helper
`AlgebraicGeometry.Scheme.Modules.tensorPowLocalSection` by recursion with real data.
No node statement, dependency list or proof plan was changed. There are no new nodes,
no repaired dependency records, and no disputed statements.

Hypotheses, in the order of the node:

- A morphism of schemes is `{Y Z : Scheme.{u}} (p : Y ⟶ Z)`. The universe is explicit.
- For every open V, a multiplication- and 1-preserving function is exactly
  `ν : ∀ V : Z.Opens, Γ(Y, p ⁻¹ᵁ V) →* Γ(Z, V)`.
  This is a monoid homomorphism, with no additivity or zero-preservation assumption.
- Restriction compatibility is `hν`, quantified over every inclusion `h : W ≤ V`
  and every section `a`; the source restriction uses `p.preimage_mono h` and the
  target uses `h`.
- The invertible module is `(M : Y.Modules) [M.IsInvertible]`, using the recorded
  scheme-module predicate, not a second invertibility definition.
- An arbitrary cover is `(I : Type w) (V : I → Z.Opens)` with
  `hcover : ⨆ i, V i = ⊤`. No finite or nonempty index hypothesis is imposed.
- The given sections are `e : ∀ i, Γ(M, p ⁻¹ᵁ V i)`. The hypothesis
  `he : ∀ i, IsFreeGenerator (e i)` uses the upstream definition: on every smaller
  open, multiplication by the restricted section is bijective. Thus it means
  exactly that multiplication by e is a structure-sheaf isomorphism, not only
  that the sections generate the module of sections on the displayed chart.

Conclusions, clause by clause:

- `∃ uij : ∀ i j, Γ(Y, p ⁻¹ᵁ (V i ⊓ V j))ˣ` supplies actual units.
  The first equality is the displayed equation e_i = u_ij e_j, with both frames
  restricted to that overlap. The following `∀ a ... → a = uij i j` states the
  uniqueness of this unit, rather than assuming transition data as input.
- `∃ vij : ∀ i j, Γ(Z, V i ⊓ V j)ˣ` supplies target units, and
  `vij i j = Units.map (ν (V i ⊓ V j)) (uij i j)` is their prescribed value.
- `∀ i, vij i i = 1` states the diagonal normalization on V_i ∩ V_i.
- The next clause states v_ji = v_ij^{-1}, after restricting both units to any
  W contained in V_i and V_j. `Units.map` uses the actual ring restrictions.
- The next clause states v_ik = v_ij v_jk on every W contained in the three charts.
  Taking W to be their intersection is the node's displayed triple-overlap law;
  the all-subopen form is equivalent by functoriality of restriction.
- `∃ N : Z.Modules, N.IsInvertible ∧ ∃ f ...` gives the required invertible
  module and sections. `∀ i, IsFreeGenerator (f i)` states that they are frames.
  The next equality is precisely f_i = v_ij f_j on each overlap.
- The binders `∀ n : ℕ, 1 ≤ n →` occur inside these fixed existential choices
  of N and f. Positive natural numbers represent exactly the integers ≥ 1.
- The next two predicates state invertibility of `M.tensorPow n` and
  `N.tensorPow n`, using the tensor powers supplied by the ample-module dependency.
- The two following frame predicates state that `tensorPowLocalSection (e i) n`
  and `tensorPowLocalSection (f i) n` generate those tensor powers.
- The two following equalities give their overlap transitions as `(uij i j)^n`
  and `(vij i j)^n`, respectively, with scalar coercions from the units.
- Every global section is `s : Γ(M.tensorPow n, ⊤)`. The existential family
  `b : ∀ i, Γ(Y, p ⁻¹ᵁ V i)` and its equalities say s restricts to b_i e_i^n.
  The following `∀ a ... → a = b i` also records uniqueness of each coefficient.
- `∃! t : Γ(N.tensorPow n, ⊤), ...` gives exactly one target section with
  restriction `ν (V i) (b i) • tensorPowLocalSection (f i) n` on every chart.
  Uniqueness of b makes this equivalent to the norm-of-coefficients rule for
  the coefficients determined by the frames.
- There is no extra assumption on p or ν: in particular no finiteness,
  surjectivity, norm-degree identity, vanishing rule, additivity, or ν(0)=0.

The local tensor-section helper belongs to the section-power operation in this
node, as permitted for canonical maps/helpers by brief-stage2 §1. It does not
introduce another module tensor product or another tensor power. It uses the
existing `tensorPow`, `unitSectionsEquiv`, and `tmulSection` at each recursive
step. The upstream `tensorPowSection` instead takes a morphism from the unit on
the whole scheme; it does not directly take a section on an arbitrary open.
The helper is its pure-section counterpart and is listed in `lean.declarations`.
The existing tensor power convention is M^0 = O and M^(n+1) = M ⊗ M^n;
in particular the n=1 frame identifies with e through the right unitor.
No noncanonical choice, new tensor product, hidden data axiom, or postponed helper
lemma is used.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `tensorPow`.
- `WeilConjectures.AlgebraicGeometry.Ample`: recorded `IsAmple` and its source
  show that the node's powers are exactly the above existing `tensorPow`.
- `WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator` (publicly exposed
  by TensorSection): `IsFreeGenerator`; its full signature and docstring were read.
- `WeilConjectures.AlgebraicGeometry.Modules.TensorSection`:
  `tmulSection` and `unitSectionsEquiv`, the real sheafified pure tensors and unit.

Recorded proof dependency modules are imported without `public`, so stage 3 has
its supplied plan: `WeilConjectures.Topology.GlueSheavesOfModules`
(`AlgebraicGeometry.glue_sheaves_of_modules`),
`WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`
(`AlgebraicGeometry.Scheme.Modules.invertible_pullback_tensor`),
`WeilConjectures.AlgebraicGeometry.Modules.RestrictionTensorComparison`
(`AlgebraicGeometry.Scheme.Modules.exists_restriction_tensor_comparison`),
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal`
(`SheafOfModules.monoidalCategory`, `symmetricCategory`),
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
(`SheafOfModules.cochainModulesMonoidal`, the recorded tensor-product interface),
`Sheaf.CategoryTheory.RingedSiteModules` (`CategoryTheory.ringedSiteModules`),
`Sheaf.AlgebraicGeometry.CoherentFiniteType`
(`AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType` and its exposed
quasi-coherence interface), `Mathlib.AlgebraicGeometry.Modules.Tilde`
(`AlgebraicGeometry.tildeFinsupp`, `tildeSelf`, `isoTop`) and
`Mathlib.CategoryTheory.Sites.Spaces` (`Opens.grothendieckTopology`).
No dependency repair was needed. The norm lemmas were read in the local Stacks
source `literature/stacks-project/divisors.tex`, labels lemma-norm-invertible
and lemma-norm-map-invertible, together with section-norms.

Edge cases checked before writing:

- Empty I: the cover equation forces Z empty and the sheaf axiom gives the unique
  global section. All transition and chart assertions are vacuous; no binder excludes it.
- Empty source/preimage charts: their section rings may be the zero ring, whose unit
  group is still defined; unital multiplicativity sends its sole element to 1.
  Neither an injective norm nor a nonzero-chart condition has been added.
- One chart and n=1: the formulas reduce to norm of the single coefficient, with
  the existing tensorPow right-unit identification. Identity p and identity ν
  recover the original framed section under the canonical gluing isomorphism.
- A constant-1 multiplicative map is allowed: in particular the zero section need
  not be sent to zero. No ring-hom encoding that would accidentally force additivity
  or ν(0)=0 has been used.
- Arbitrarily large cover index: Type w is independent of the scheme universe.
  No smallness condition beyond the existing scheme-module category is introduced.
- Nonreduced schemes and arbitrary characteristics are admitted: only section rings,
  modules, unit groups and their restriction maps appear.

Searches for an exact existing statement (2026-10-24):

- msearch.py leanfinder, query "Restriction compatible multiplicative maps on
  structure sheaves glue norm transition functions of invertible modules and
  tensor power sections": 8 hits on structure-sheaf fraction representations,
  Proj maps, and scheme-gluing sheaves; none asserts this norm-frame theorem.
- msearch.py loogle, query `"norm", "IsInvertible"`: OK, 0 hits.
- msearch.py grep, query `norm.*(transition|cocycle|tensorPow)`: OK, 0 hits.
- msearch.py leansearch, query "A multiplicative map of structure sheaves glues
  norm line bundles and their tensor power sections": 8 hits including
  `TopCat.Sheaf.interUnionPullbackConeLift`, `StructureSheaf.comap`,
  `SheafOfModules.sectionsMap` and `ModuleCat.Tilde.smul_section_apply`;
  none gives the asserted construction and coefficient rule.
- rg on the prescribed Mathlib module directories and both project source trees
  for norm/transition/cocycle/tensorPow, IsFreeGenerator, tensorPowSection,
  tensorPowLocalSection, and section-power variants: the scheme frame predicate,
  tensorPow, pure section product, and global morphism-power construction were
  located and reused. No norm-frame tensor-section gluing theorem or direct local
  section-power operation was found. rg for the item's exact id in
  `lean/WeilConjectures` returned no match. Relevant global-morphism power source
  was read in `WeilConjectures/AlgebraicGeometry/Modules/ClearDenominators.lean`.
- DAG searches for IsFreeGenerator and free-generator/section-power notions found
  applications and frame lemmas, not another node carrying this norm theorem.

Validation: the first complete module compiled through the prescribed scompile.py
on the server, with no errors or warnings (3.2 seconds in library mode). After
adding explicit direct imports for all recorded dependencies, the final file also
compiled cleanly through scompile.py (5.5 seconds in library mode). The delivery
dry run repeats the required checks. The main theorem has
exactly one `sorry`; the helper definition contains none.

## Second reading by O3

A separate manual pass by this worker reopened the node and the complete Lean
signature; no other agents were started, as required by the dispatcher brief.
The maintainer supplies the independent review after delivery.

The pass matched p, the monoid maps, hν, invertible M, arbitrary covered V, and
IsFreeGenerator e against every input clause. It checked the orientation of both
unit equations and of the target frames: all are i = (i,j) times j, so the
coefficient rule is b_j = b_i u_ij^n, matching the documented proof. The inverse
clause restricts v_ji and v_ij into the same ring before inversion; the triple
clause restricts all three terms into the same ring before multiplication. Thus
there is no heterogeneous-overlap equality or assumption identifying different
open sets. The two explicit power-transition clauses use the same exponents as
the two frame clauses. Both power invertibility conclusions are retained.

The pass checked quantifier order: N and f precede n and s; b follows s and is
proved unique; t is unique among all global sections satisfying the prescribed
local formula. It checked the empty-cover and constant-1-map cases, and that the
helper's 0 and successor clauses follow the existing tensorPow convention. It
found no missing hypothesis or conclusion. Two minor presentation changes were
made after the first compile: the direct imports for Scheme, IsInvertible and
the recorded symmetric-monoidal module were made explicit, and a leading space
in the theorem docstring was removed. No mathematical statement changed.
