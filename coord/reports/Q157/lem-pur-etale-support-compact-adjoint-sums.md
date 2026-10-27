## Worker report

The new module `Sheaf.AlgebraicGeometry.EtaleSupportCompactAdjointSums` states
`AlgebraicGeometry.Etale.support_compactImages_adjoint_sums`, with one `sorry` and
no new definitions. The natural-language statement and its accepted seven-step
split are unchanged. The theorem docstring carries all seven proof steps and
names their DAG inputs. The source was read in the local Bhatt--Scholze PDF:
Section 6.4, Example 6.4.1, Lemmas 6.4.2--6.4.6, and Proposition 6.4.8
(printed pages 48--49). In particular the compactness theorem concerns the full
unbounded ordinary etale category, with perfect values, rather than declaring
all finite modules perfect.

Hypotheses and conclusions, clause by clause:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
  `[CharP k p]` with `hp : Nat.Prime p` expresses positive characteristic;
  characteristic of a field is prime whenever positive. `hℓ : Nat.Prime ℓ`
  and `hℓp : ℓ ≠ p` give the other prime and the prime-to-characteristic condition.
- `X.Over (Spec (CommRingCat.of k))`, and the corresponding instance for Y,
  supply their k-structures. `LocallyOfFiniteType` and `QuasiCompact` on the
  two structure morphisms say finite type. The morphism `f` has `f.IsOver`,
  `IsSeparated f`, `LocallyOfFiniteType f`, and `QuasiCompact f`. No separatedness
  of either structure morphism is imposed.
- `c : Compactification f` is precisely the fixed factorization: `c.i` is the
  open immersion, `c.g` is proper, and `c.comm` records their composite.
- `C : Type (u + 1)` with `CommRing C`, `Finite C`, and
  `hC : ∃ m : ℕ, (ℓ : C) ^ m = 0` gives exactly the finite coefficient ring
  annihilated by a power of ell, including the zero ring.
- Every category is the existing `DerivedCategoryModule C T`, the ordinary
  unbounded derived category of `Sheaf T.smallEtaleTopology (ModuleCat C)`.
  The functor named F in the node is written explicitly throughout as
  `rightDerivedLowerShriekOfCompactification (ModuleCat C) c`. Its definition
  is exact termwise open extension followed by total right derived proper
  direct image; no new choice of compactification is made.
- `G` is an arbitrary functor in the reverse direction, and `adj : F ⊣ G`
  fixes its particular adjunction and counit. The two instance binders on F
  supply the specified coherent shift comparisons and exact triangulated
  structure assumed in the node. They do not constrain G or choose an adjoint.
- `N : ℤ` and `hN : 0 ≤ N` give the stated integer bound.
  `hinterval` quantifies over every `a b : ℤ` with `a ≤ b` and every E.
  `DerivedCategory.IsGE E a` and `IsLE E b` express membership in the standard
  interval; the conclusion uses `IsGE (F.obj E) a` and `IsLE (F.obj E) (b + N)`.
- `hprojection` is `IsIso (compactSupportProjectionMapOfCompactification C c K L)`
  for every unbounded K and L. This is the actual coefficient-first canonical
  map with endpoints `L tensor F(K)` and `F(f*L tensor K)`, using exact
  `upperStar.mapDerivedCategory`. Its definition composes signed symmetry,
  the proper/open projection, the canonical comparison of derived and exact
  inverse images, and signed symmetry on the target. Thus its invertibility
  has exactly the convention of the node, without an arbitrary map assumption.
- The existential `hX`, `hY : HasCoproducts.{u + 1} ...` supplies coproducts used
  by the existing compactness predicate; it adds no hypothesis. Compactness
  uses those precise witnesses through explicit `@IsCompactObject` arguments.
- The first conjunct quantifies over every a, b and E. Its hypotheses are
  `DerivedCategory.isBoundedConstructible C X E` (all cohomology constructible
  and zero outside a finite interval) and `hasTorAmplitudeIn C X a b E`
  (all degree-zero module-sheaf tests). Its three conclusions are the same
  bounded constructibility for F(E), Tor amplitude `[a,b+N]`, and compactness
  of F(E). No condition that C is regular or that a finite module is flat occurs.
- The second conjunct supplies `S : Type (u + 1)` and `E : S → ...`, with each
  member bounded constructible, of some finite Tor interval with ordered
  endpoints, compact on X, and with compact F-image. For every arrow h,
  bijectivity of postcomposition on `Hom((E s)⟦n⟧,-)` for all s and all integers n
  implies `IsIso h`, which is exactly detection of isomorphisms by these tests.
- The third conjunct is `∀ I : Type v, PreservesColimitsOfShape (Discrete I) G`.
  The independent explicit universe v includes every existing set-indexed
  coproduct; no existence of coproducts larger than the category supports is
  asserted. The compact family and compactness tests live in u+1 as in the
  published finite-ring generator theorem.
- The final existential supplies `hG : G.CommShift ℤ`. Within its scope the
  exactness assertion is `G.IsTriangulated` for this structure. The following
  equation quantifies over all n and M and reads
  `adj.counit.app (M⟦n⟧) = F.map (cG.hom.app M) ≫ cF.hom.app (G.obj M) ≫
  (shiftFunctor _ n).map (adj.counit.app M)`.
  Lean composition is left-to-right, so this is precisely the displayed
  epsilon equation in the node. The counit belongs to the original `adj`.
- The two constant-complex functors are literally
  `(constantSheaf T.smallEtaleTopology (ModuleCat C)).mapDerivedCategory`
  for T=X,Y. Their `IsTriangulated` clauses and their `PreservesColimitsOfShape`
  clauses give exactly the two asserted properties, for unbounded V.
- For each M, the first coefficient functor is the constant functor on X
  followed by `(derivedTensor ... X).flip.obj (G.obj M)`, i.e. V tensor GM.
  The second is the constant functor on Y followed by
  `(derivedTensor ... Y).flip.obj M` and then G, i.e. G(V tensor M).
  Both have `IsTriangulated` and arbitrary discrete-colimit-preservation clauses.
  Their shifts are the standard exact constant-functor and tensor shift
  structures composed with the existential, adjunction-normalized G-structure;
  no separate shift structures for the composite functors are quantified.

Dependency declarations reused (module names are their actual source modules):

- `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification.Refinement`, with `Compactification` from
  its public import `WeilConjectures.Compactification.Defs`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule` and
  `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`:
  `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`;
  the compact-support functor itself is defined in its public LowerShriek import.
  The theorem permits any fixed adjunction rather than replacing it by a choice.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`:
  `DerivedCategory.TStructure.t`, `IsGE`, `IsLE` and their cohomology descriptions.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `Etale.derivedTensor`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`; exact etale module pullback
  is `Etale.upperStar`, used termwise through `Functor.mapDerivedCategory`.
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `Scheme.IsConstructibleEtaleModuleSheaf`.
- `WeilConjectures.CategoryTheory.CompactObject`: `CategoryTheory.IsCompactObject`.
- `Mathlib.CategoryTheory.Triangulated.Adjunction` and its public imports:
  `Functor.IsTriangulated`, `Adjunction.rightAdjointCommShift`,
  `Adjunction.CommShift`, `Adjunction.isTriangulated_rightAdjoint`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- Three already-landed definition nodes are added to stmt_deps: the bounded
  constructible predicate (`def-weil-pbc-constructible-complexes`, module
  `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`), bounded Tor
  amplitude (`def-kun-tor-amplitude`, module `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`
  reusing the existing Coefficients definition), and the coefficient-first projection
  (`def-pur-compact-support-projection-map`, module
  `Sheaf.AlgebraicGeometry.ShriekTensorComposition`). These additions name existing
  notions already described in the item's unchanged prose. There are no new nodes
  or dependency interface repairs.

All recorded proof modules are imported, including finiteness, truncation,
constructible Serre, signed tensor symmetry, finite-ring compact generators,
compact tests for adjoint coproducts, adjunction shifts, exact derived functors,
sheafification, module and module-sheaf Grothendieck abelianness, termwise derived
coproducts, and tensor exactness and sums. Statement imports are public; the
proof-only imports are plain imports. The proof plan includes the same seven steps
as the node. No proof dependency is dropped.

Edge cases checked before writing: empty X (zero source category), zero C (allowed
by m=0), zero E, empty coproduct index, identity f and its trivial compactification,
N=0, arbitrary negative degree endpoints, and the degenerate interval a>b
(where finite Tor amplitude forces the zero object, so the conclusion still holds).
For C=Z/ell^2 the finite-Tor hypothesis remains essential; the statement never treats
an arbitrary finite module as perfect. X and Y may be nonseparated over k.
Every integer shift is tested. Independent v does not demand nonexistent large
coproducts, since preservation is of existing colimits.

Searches for an existing full statement:

1. `msearch.py ... leanfinder` with query
   "finite etale compact support sends constructible finite Tor amplitude complexes
   to compact objects and right adjoint preserves coproducts": eight hits on
   condensed/profinite module functors, Grothendieck categories, and single complexes;
   no match to this geometric statement and its simultaneous conclusions.
2. `msearch.py ... loogle "CategoryTheory.IsCompactObject, CategoryTheory.Adjunction"`:
   zero hits, unknown identifier IsCompactObject in the Mathlib-only index.
3. `msearch.py ... grep "IsCompactObject|rightAdjointCommShift" CategoryTheory`:
   five hits in Shift/Adjunction, giving only the general shift construction.
4. `msearch.py ... leansearch` with query
   "compact support etale derived finite Tor constructible compact objects right
   adjoint coproducts": eight hits on condensed constant/underlying adjunctions
   and finite coproducts of sheaves; no full statement.
5. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id,
   `support_compactImages_adjoint_sums`, `support.*compact.*adjoint`, and
   `CompactImages`, and the prescribed `grep -rn` of the item id in
   `lean/WeilConjectures`: no existing full theorem. Targeted concept searches
   found `finiteRing_compactGenerators`, `compactTests_rightAdjoint_preservesCoproducts`,
   bounded constructibility, Tor amplitude, the existing coefficient-first map,
   and exact constant/tensor functors. These are reused, not copied.

Validation: server-only `scompile.py Q157 lem-pur-etale-support-compact-adjoint-sums`
compiles the module in module mode, both under the sandbox name and its final library
name. The initial projection probe needed the flat module-pullback instance import;
using the published coefficient-first projection module gives the exact desired map
and imports that instance. The final source has explicit `autoImplicit false`,
explicit universes, no local notation or private declarations, and lines at most
100 characters. Only the named theorem has `sorry`.

No STATEMENT-DISPUTED issue, statement correction, or unresolved node fault.

## Second reading by Q157

This is a final direct self-check; no sub-agent was started, as the dispatch forbids
it. The maintainer supplies the independent delivery review.

Reopened the unchanged node and the final Lean file and checked each clause above.
The first projection probe used the factor-first map; the final statement uses the
published coefficient-first map on the supplied compactification, including the
canonical exact inverse-image identification. Explicit hX/hY arguments ensure
compactness refers to the supplied coproducts, and the existential hG binds the
shift structure used by both G and all composite coefficient functors. The counit
equation composes F(cG), cF, and shifted counit in exactly that order. Checked that
finite type is imposed on both structure maps and f; only f is separated. Checked
that no nonzero-coefficient-ring, nonempty-index, bounded-input-V, regular-ring, or
field-separability restriction is introduced. No additional mismatch was found.
