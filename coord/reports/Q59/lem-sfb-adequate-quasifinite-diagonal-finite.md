## Worker report

The module `Sheaf.AlgebraicGeometry.AdequateQuasifiniteDiagonalFinite` states
`CategoryTheory.adequate_quasifinite_diagonal_finite`, with one named theorem and
one `sorry`, and introduces no definitions. The node's mathematical statement and
proof are unchanged. The only additional DAG edges are to existing landed notions
used explicitly in the signature, as permitted by brief-stage2 §5.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A field k: `(k : Type u) [Field k]`, the recorded `Field` of def-weil-field.
- An algebraic stack X over k: `F : BasedCategory.{v, w} (Over (Spec
  (CommRingCat.of k)))` and `hF : IsAlgebraicModuliStack F`. This retains arbitrary
  explicitly declared stack object and morphism universes v and w.
- Finite type of X/k: `hft` asserts existence of a scheme U over k and a map
  `a : BasedFunctor (discreteModuli (yoneda.obj U)) F`, with
  `IsSmoothModuliAtlas F U a ∧ LocallyOfFiniteType U.hom ∧ QuasiCompact U.hom`.
  The atlas is smooth over the stack; U is only finite type over k. In particular,
  neither smoothness of X/k nor an etale atlas is imposed. This is the smooth
  scheme-chart criterion stipulated by the node and used by its proof.
- An affine k-scheme Y: `Y : Over (Spec (CommRingCat.of k))` and `[IsAffine Y.left]`.
  No finite-type hypothesis on Y is added.
- The given k-map phi: `φ : BasedFunctor F (discreteModuli (yoneda.obj Y))`.
  The target is the actual representable sheaf, viewed as a discrete groupoid.
- Adequacy: `hφ : IsAdequateModuliSpace F hF (AlgebraicSpace.schemeSpace Y) φ`.
  The scheme-space construction keeps the Yoneda presheaf definitionally, so this
  is the same phi, without a chosen equivalence or arbitrary replacement map.
  The recorded predicate includes qcqs, the canonical structure-sheaf isomorphism,
  and power lifting on all quasi-coherent algebras of every affine etale 2-base
  change. No exactness hypothesis is added.
- Quasi-finite separated diagonal: `hΔ : HasSchemeStackDiagonalWith ... F`.
  This quantifies over every pair of scheme maps into F, retains their actual
  2-fibre product with both projections, and applies the property to its map to
  the product of the test schemes. Its property is exactly
  `LocallyOfFiniteType f ∧ QuasiCompact f ∧
  (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (y : Spec (CommRingCat.of Ω) ⟶ V), Finite ↥(pullback f y)) ∧
  IsClosedImmersion (pullback.diagonal f)`.
  The first two conjuncts are finite type, the third is finite geometric fibres,
  and the fourth is separatedness. This is also the interface used by the landed
  affine_action_stack_diagonal_quasiFinite theorem.
- The diagonal is finite: `HasFiniteModuliDiagonal F`. The recorded predicate
  states exactly finiteness of the representing map to T ×_k U for all pairs of
  scheme tests, with both projections retained. It does not assert finiteness of
  the projections separately.
- In particular the inertia projection is finite:
  `IsRepresentableFiniteModuliMap (moduliInertiaProjection F)`. This uses the
  existing category of actual vertical automorphisms, its commuting arrows and
  the forgetful projection. These are precisely the objects and projection of
  the diagonal 2-self-pullback in the node, rather than an arbitrary finite stack.
  The predicate tests every scheme base change and identifies its projection
  with a finite scheme morphism.

The scheme-representability in `hΔ` is an equivalent formulation, not an extra
hypothesis: the diagonal of an algebraic stack is representable by spaces, and a
separated locally quasi-finite space over a scheme is a scheme. I read
`literature/stacks-project/spaces-morphisms.tex`,
`lemma-locally-quasi-finite-separated-representable` (lines 10712--10725) and its
preceding explanation. Its base-change stability applies to every diagonal
scheme test. Finite type plus finite geometric fibres gives local quasi-finiteness.
Thus a scheme presentation exists under the node's original hypotheses, including
in positive characteristic. No DM or unramified assumption is introduced.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (class and full docstring read).
- `Sheaf.AlgebraicGeometry.AdequateModuliSpace`:
  `CategoryTheory.IsAdequateModuliSpace`, including all four conjuncts and its
  test-algebra universes.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`;
  `Mathlib.AlgebraicGeometry.Morphisms.Integral`:
  `AlgebraicGeometry.IsIntegralHom`. These are the recorded finite/integral
  predicates. Finite is used by the existing scheme-test definitions; Integral
  is imported for proof step 2.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, and its imported
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.QuasiCompact`. Both complete class signatures were read.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and its
  contravariant map, the proof dependency for the affine comparison.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack` and `CategoryTheory.IsSmoothModuliAtlas`.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`:
  `AlgebraicGeometry.AlgebraicSpace.schemeSpace`, recorded by
  def-trf-scheme-algebraic-space; its representable sheaf data was read.
- `Sheaf.AlgebraicGeometry.SchemeStackDiagonalPresentation`:
  `CategoryTheory.HasSchemeStackDiagonalWith` and its underlying
  `CategoryTheory.IsSchemeStackDiagonalPresentation`.
- `Sheaf.AlgebraicGeometry.FiniteStackSchemeTests`:
  `CategoryTheory.HasFiniteModuliDiagonal` and
  `CategoryTheory.IsRepresentableFiniteModuliMap`.
- `Sheaf.AlgebraicGeometry.ModuliInertia`:
  `CategoryTheory.ModuliInertiaObject`, `CategoryTheory.moduliInertia`, and
  `CategoryTheory.moduliInertiaProjection`.

The three theorem proof dependencies adequate-product-affinization,
stack-diagonal-closed-points and adequate-integral-comparison-finite currently
have no Lean record or Mathlib match; no import is invented for them. Their
mathematical roles and all five proof steps are retained in the theorem docstring.
The proof's existing definition dependencies are imported. The added statement
edges point only to already landed definition nodes, with no new/dependency modules.

Source: I opened Alper, arXiv:1005.2398v3, §8.3, Theorem 8.3.2 and Lemma 8.3.1:
https://arxiv.org/html/1005.2398v3#S8.SS3 . The separated-target part of the proof
makes the diagonal finite; the node keeps the sufficient affine-target hypothesis.
The product affinization, integral comparison, closed-point condition and inertia
base change agree with the node's proof. There is no statement correction or
STATEMENT-DISPUTED finding.

Edge cases checked before writing:

- The empty stack and empty affine target are allowed: the atlas existential does
  not require a nonempty scheme, and no geometric test asserts nonemptiness.
- Affine schemes with their identity adequate moduli map satisfy the expected
  closed finite diagonal conclusion.
- BG for finite group schemes, including mu_p in characteristic p, is allowed:
  finite geometric fibres need not be reduced; the statement requires neither
  unramifiedness nor an etale stack atlas. BG_m is excluded by the diagonal
  geometric-finiteness hypothesis.
- All characteristics and nonperfect base fields are allowed; no characteristic
  or algebraic-closedness assumption is imposed on k.
- The geometric field test is in the scheme universe u, rather than an
  independently smaller universe. Maps to each scheme target specify the
  geometric fibres over that target. Stack universes v,w remain independent.
- The smooth atlas can be singular over k; no false smoothness hypothesis is
  substituted for finite type. No arbitrary quasi-compactness of the identity
  map is used as an input.

Searches made, with no exact existing statement found:

- `msearch.py ... leanfinder`: “Algebraic stack over a field with an affine
  adequate moduli space and quasi finite separated diagonal has finite diagonal
  and finite inertia”. Eight hits, all scheme diagonal or finite-morphism
  properties; none concerns adequate moduli spaces or this stack theorem.
- `msearch.py ... loogle`: `IsAdequateModuliSpace, HasFiniteModuliDiagonal`.
  Zero hits; unknown identifier IsAdequateModuliSpace in the Mathlib index.
- `msearch.py ... grep`: `adequateModuli|adequate_moduli|finiteInertia|finite_inertia`.
  Zero Mathlib hits.
- `msearch.py ... leansearch`: “adequate moduli space affine target quasi finite
  separated diagonal finite”. Eight hits on scheme morphisms, no stack theorem.
- `rg` in `lean/WeilConjectures` for adequate and finite-diagonal/inertia names,
  and for the item id: no adequate theorem or item declaration; diagonal hits
  concern schemes, kernel transforms or finite diagonals in homological algebra.
- `rg` in `lean/Sheaf` for adequate with finite: the affine PGL quotient cites
  this item in its proof docstring but does not state it. Further searches found
  the reusable AdequateModuliSpace, FiniteStackSchemeTests, ModuliInertia and
  SchemeStackDiagonalPresentation modules, all of which are used directly.
- `dag/lean_names_upstream.json` was searched for the finite-stack predicates and
  the proposed theorem name, with no matching existing theorem.

Validation: the initial module passed both sandbox and library compilation through
`scompile.py` with no errors or unexpected warnings. The final module adds the
explicit finite-type statement import and integral/Spec proof imports; its final
compile and delivery dry run are recorded below.

## Second reading by Q59

I performed a second in-thread reading of the node and the complete final signature;
no second agent was started, as the dispatcher expressly forbids that. The maintainer
will supply the independent review. I checked every binder and both conclusion
conjuncts against the node, including the identity of phi under schemeSpace, the
finite-type smooth atlas rather than a smooth stack, finite geometric fibres rather
than reduced geometric fibres, and the actual inertia projection. The scheme
representability in hΔ is justified by the Stacks representability result above.
No mismatch required a mathematical statement change. The only adjustments after
this reading were explicit imports for the finite-type statement dependency and
the integral and Spec steps of the proof.

Final validation: the final module passed `scompile.py` in both sandbox mode
(6.4 seconds) and its actual library module (5.1 seconds), with no errors or
unexpected warnings. `deliver2.py --no-push` printed
`OK (dry run): commit 21c94cc540a passes the preflight and compiles; nothing pushed`.
Only the node's `lean` and `stmt_deps` fields differ from the live input; the
statement, proof and other node fields are preserved. The signature record is
verbatim from the module, and every Lean line is at most 100 characters.
