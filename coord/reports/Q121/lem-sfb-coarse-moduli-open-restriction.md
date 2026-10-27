## Worker report

The module Sheaf.AlgebraicGeometry.CoarseModuliOpenRestriction states
CategoryTheory.coarseModuli_open_restriction, with its sole proof postponed by sorry.
The two data definitions coarseOpenOver and coarseOpenInclusion are just the inherited
base map V.ι ≫ Q.hom and the actual open immersion V.ι in Over S. Neither chooses
an object from an existence assertion. They are helpers belonging to this theorem,
not new notions of stack, open substack, coarse scheme or pullback.

Clause-by-clause correspondence:

- The field is (k : Type u) [Field k]. All categories and schemes are over Spec k.
- The stack X is BasedCategory.{v₁, w₁} (Over (Spec (.of k))), with independent,
  explicitly bound category universes. hX is IsDeligneMumfordModuliStack X, exactly
  the recorded stack, diagonal representability and surjective étale atlas condition.
- Finite type is hft : HasFiniteTypeEtaleModuliAtlas X. As its definition specifies,
  this means an étale surjective atlas whose scheme structure map is locally of
  finite type and quasi-compact. For a DM stack over a field this is finite type;
  smoothness and tameness are not required.
- Finite diagonal is hdiag : HasFiniteModuliDiagonal X. The recorded definition
  represents the two-scheme tests by a scheme Z and requires finiteness of the
  induced map to T ×_k U, retaining BOTH projections. This is not merely finiteness
  of either projection, nor finiteness of stabilizers alone.
- Q : Over (Spec (.of k)) and q : BasedFunctor X (discreteModuli (yoneda.obj Q))
  are the specified coarse scheme and map. hq is the recorded IsCoarseModuliScheme.
- U : OpenModuliSubstack X is the strictly full pullback-stable open substack.
  Its scheme tests are actual open immersions, with comparison of the projection.
- ∃! V : Q.left.Opens supplies existence and uniqueness of the open subscheme.
  The standard restricted scheme V.toScheme has its inherited map to Spec k,
  denoted coarseOpenOver Q V. Open subsets determine open subschemes, so equality
  here is equality of opens, not equality of arbitrary presentations of schemes.
- e is an equivalence from U.category to the recorded moduliTwoFiberProduct of q
  with the discrete map induced by coarseOpenInclusion Q V. Its first projection
  is identified by ModuliTwoIso with fullModuliInclusion X U.property. Thus this
  is the required equivalence OVER X, not just an abstract equivalence of stacks.
- The restricted morphism is e.comp (moduliTwoFiberSnd ...), the actual second
  projection, with target the discrete moduli of coarseOpenOver Q V.
- IsCoarseModuliScheme on this composite retains both clauses: bijectivity of
  composition from maps of V to EVERY algebraic space over k, and bijectivity of
  the induced skeleton-object map for EVERY algebraically closed Ω/k.
  Consequently it is precisely the restriction of q, not a free coarse map.
  The unique-existence predicate includes both the pullback equivalence and the
  coarse conclusion, as asserted together in the node.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: Field.
- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Mathlib.AlgebraicGeometry.Morphisms.Finite: AlgebraicGeometry.IsFinite.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: AlgebraicGeometry.LocallyOfFiniteType;
  QuasiCompact is its imported quasi-compactness condition.
- Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids: CategoryTheory.BasedCategory,
  IsDeligneMumfordModuliStack, discreteModuli, discreteModuliMap, IsCoarseModuliScheme,
  ModuliTwoIso, moduliTwoFiberProduct and moduliTwoFiberFst. The full signatures and
  docstrings of the generic stack/coarse/2-product interfaces were inspected.
- Sheaf.AlgebraicGeometry.FiniteStackSchemeTests: HasFiniteModuliDiagonal and
  HasFiniteTypeEtaleModuliAtlas. The item's stmt_deps gains their already landed
  owning definition node def-sfb-finite-stack-scheme-tests.
- Sheaf.AlgebraicGeometry.OpenModuliSubstack: OpenModuliSubstack,
  OpenModuliSubstack.category, fullModuliInclusion and moduliTwoFiberSnd. The item's
  stmt_deps gains its already landed owning node def-sfb-open-moduli-substack.
- Mathlib.AlgebraicGeometry.Morphisms.Flat is a plain proof dependency, supplying
  AlgebraicGeometry.Flat and flatness of open immersions. IsOpenImmersion is already
  publicly imported by the open-substack interface.

The proof-only nodes lem-sfb-keel-mori-uniform-topological-moduli and
lem-sfb-stack-topology-open-substacks have no Lean records in the read repository.
Their interfaces are not required to TYPE this statement: there are no extra imports
for these unstated proof inputs. The full five-step proof plan, including their
roles, is in the theorem docstring. There are no missing statement prerequisites,
new nodes, dependency repairs, or corrections to the mathematical node statement.
The original reviewer note about equivalence over X is respected explicitly.

Sources opened: literature/stacks-project/stacks-more-morphisms.tex,
theorem-keel-mori (0DUT) and lemma-etale-separated-over-keel-mori (0DUV).
Keel--Mori supplies the uniform categorical quotient and universal homeomorphism;
0DUV supplies its étale local compatibility. The node's open-restriction consequence
is the five-step argument in its proof, not a claim that 0DUV states it verbatim.

Edge cases checked before writing: U empty gives V empty; U = X gives V = Q;
X and Q empty are permitted by the atlas and scheme definitions. Nontrivial
stabilizers are retained by the full categories and geometric skeleton, not
silently removed by taking a fine moduli scheme. Arbitrary characteristic,
non-tame stabilizers, and arbitrary algebraically closed field extensions in the
recorded size convention remain allowed. Q is not separately assumed proper,
smooth, reduced, separated or finite type. Category universes v₁, w₁ remain free;
no equality with u is imposed. No STATEMENT-DISPUTED fault was found.

Searches for an existing statement/notion:

- msearch.py leanfinder, "A coarse moduli space of a Deligne Mumford stack restricts
  to open substacks": eight scheme-restriction hits, no stack/coarse theorem.
- msearch.py loogle, "IsCoarseModuliScheme": no hits, unknown identifier in Mathlib.
- msearch.py grep, "CoarseModuli|OpenSubstack": zero Mathlib hits.
- msearch.py leansearch, "coarse moduli scheme restriction to open substacks":
  eight results for scheme opens and restrictions, none for coarse moduli stacks.
- rg of lean/WeilConjectures and lean/Sheaf for CoarseModuli, coarseModuli,
  OpenSubstack, OpenModuli, finiteDiagonal and finite-type moduli interfaces:
  found the existing generic interfaces above and the consumer
  AbelianLevelCoarseModuli, but no theorem for this restriction.
- grep of the item id in lean/WeilConjectures: no match.
- rg of dag/nodes/sec-six-functors-basics for OpenModuliSubstack and
  HasFiniteModuliDiagonal found the already landed two owning definition nodes;
  these are reused rather than duplicated.

Validation: scompile.py Q121 lem-sfb-coarse-moduli-open-restriction on the module
passed both sandbox and library compilation (3.3 s and 3.4 s), without errors or
warnings. Every variable and universe is bound explicitly; autoImplicit is false.

## Second reading by Q121

Self-review after reopening the node and the emitted Lean signature (the dispatcher
forbids starting another agent; independent maintainer review remains separate).
The original hypotheses correspond in order to k, X/hX, hft, hdiag, Q/q/hq, U.
The finite-type atlas is étale, without an extra smooth-stack assumption. In the
finite-diagonal predicate the finite morphism has target the product of the two
test schemes, not one test scheme. The unique open is quantified in Q.left.Opens.
The e-equivalence is tied to the actual inclusion U → X by the first-projection
2-isomorphism. The second projection, after that same equivalence, is the coarse
morphism in the conclusion. Its definition includes all algebraic-space targets
and the geometric isomorphism-class bijections. No fine-moduli equivalence with V
is asserted. Empty/full opens and all characteristics remain included. The source
proof and all five DAG steps are reproduced in the docstring. No mismatch was
found; no mathematical statement correction was needed. The only DAG changes
are lean and addition of the two existing definition-node dependencies.
