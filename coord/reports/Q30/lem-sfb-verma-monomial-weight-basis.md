## Worker report

The module `Sheaf.Algebra.Lie.VermaMonomialWeightBasis` constructs the rational Verma
quotient and states `LieAlgebra.exists_verma_monomial_weight_basis`, with one `sorry`.
The node statement and all other original fields are unchanged; only `lean` is added.
No new independent notion or dependency module is needed: the ideal, quotient, highest
vector and action are helper declarations belonging to this node's explicit construction.

Hypothesis and clause correspondence:

- The arbitrary-universe rational Lie algebra is `{g : Type u} [LieRing g]
  [LieAlgebra ℚ g]`, with `[FiniteDimensional ℚ g] [HasTrivialRadical ℚ g]`.
  These use the Mathlib matches of def-wf-lie-algebra and def-wf-semisimple-lie-algebra.
- The splitting maximal abelian subalgebra is `(H : LieSubalgebra ℚ g)
  [IsLieAbelian H]`, `hmax` and `hsplit`, exactly as in the recorded root-decomposition
  theorem. Diagonalizability is the supremum of rational eigenspaces being top.
- `R` and `hR` define exactly the nonzero ordinary adjoint weights, using the same
  `LieModule.weightSpace` as the dependency. `Δ`, `b`, `hb`, and `hsign` reproduce its
  simple-root conventions: a rational basis with sign-coherent integer coordinates.
  `AddSubmonoid.closure` is precisely finite sums with natural coefficients.
- `P` with `hP` is R-positive. The sum of positive root spaces is their supremum of
  rational submodules. The analogous negative sum is only contextual notation in the
  node, not an additional asserted result; the theorem uses its individual root spaces.
  Coroots are supplied by the imported root-decomposition theorem and do not enter
  the Verma quotient or its asserted equations.
- `UniversalEnvelopingAlgebra ℚ g` is Mathlib's actual tensor quotient by the relations
  xy-yx=[x,y], not an arbitrary algebra with a supplied PBW property.
- `vermaIdeal` is `Submodule.span U` of the image of n-positive union the range of
  h ↦ ι(h)-algebraMap(η(h)). A U-submodule of its left regular module is a LEFT ideal;
  no two-sided closure is imposed. The rational module structure and left U-action
  descend through Mathlib's standard submodule quotient.
- `VermaModule` is exactly this quotient; `vermaHighestVector` is the class of 1.
  `vermaRepresentation` is the algebra action `Algebra.lsmul` restricted along `ι`.
  The exported Lie action instances pull back the endomorphism action; all their
  data and laws are existing constructions, with no postponed auxiliary proofs.
- The first theorem conjunct identifies the action with `ι(x) • m`. Its Lie laws
  are supplied by the exported instances. The next three conjuncts state v≠0,
  the η-eigenvalue equations, and annihilation by every element of n-positive.
- `N`, the equivalence `β : Fin N ≃ P`, and `hy` encode any ordering without
  repetitions and any choice of nonzero negative-root vectors. There is no
  Chevalley normalization, integrality, or dominance restriction on η.
- The existential `Module.Basis (Fin N → ℕ) ℚ ...` has exactly the required monomial
  vectors. `List.finRange` and `List.prod` retain the noncommutative order.
  Membership in `LieModule.weightSpace` at η-∑a_jβ_j states ordinary simultaneous
  eigenvectors, not generalized eigenvectors.
- `LieSubmodule.lieSpan ℚ g {v} = ⊤` states generation by v as a g-representation.
- The weight-location conjunct quantifies over every rational functional μ and
  requires η-μ in the positive simple-root monoid whenever its weight space is nonzero.
- Equality of the η-weight submodule with `Submodule.span ℚ {v}` gives exactly Qv.
- `∀ μ, FiniteDimensional ℚ (LieModule.weightSpace ... μ)` includes nonoccurring
  weights, whose spaces are zero.
- The final conjunct says that when P is empty every member of the displayed basis
  equals v. Since `Fin N ≃ P` then forces N=0, there is exactly one exponent tuple.

Dependencies read and reused:

- `Sheaf.Algebra.Lie.SplitSemisimpleRootDecomposition`,
  `LieAlgebra.exists_splitSemisimple_rootDecomposition`: full signature and docstring
  read; its actual Mathlib root/weight/simple-base interfaces are used unchanged.
- `Mathlib.Algebra.Lie.Basic`: `LieRing`, `LieAlgebra`, `LieRingModule`, `LieModule`,
  and `LieRingModule.compLieHom` / `LieModule.compLieHom`.
- `Mathlib.Algebra.Lie.Semisimple.Defs` and `.Basic`: `HasTrivialRadical` and
  `hasTrivialRadical_iff_no_solvable_ideals`, exactly the definition-node Mathlib match.
- `Mathlib.Algebra.Lie.Weights.Basic`, `LieModule.weightSpace`: definition and
  `mem_weightSpace` read; intersection of ordinary eigenspaces.
- `Mathlib.Algebra.Lie.UniversalEnveloping`: quotient, `ι`, `lift`, `lift_ι_apply`,
  `lift_unique` read, reusing lem-sfb-enveloping-universal-property's Mathlib match.
- `Mathlib.Algebra.Algebra.Tower`, `Algebra.lsmul`; standard submodule quotient
  structures in `Mathlib.LinearAlgebra.Quotient.Defs` read in full relevant sections.
- The proof-only node lem-sfb-rational-pbw currently has neither a Lean record nor
  a Mathlib match, so it has no module to import. The docstring retains the exact
  PBW proof step for stage 3. No missing proof theorem is assumed as a hypothesis.

Edge cases checked mathematically before writing: g=0 gives empty roots and H=0,
U(0)=Q, no nonzero relations, M=Q, and one basis vector. Arbitrary nonintegral and
nondominant η are allowed (e.g. sl2); its vectors y^a v have weights η-aα.
For A2 the weight η-α1-α2 can have two monomials, so the statement never asserts
all weight spaces have dimension one. Nonoccurring weights give the zero space.
Finite-dimensional g is arbitrary-universe; M is not assumed finite-dimensional.
A left ideal, rather than a two-sided ideal, is essential for nonzero η and is
implemented explicitly.

Searches for existing declarations (logged by msearch.py in searches.jsonl):

- leansearch: `Verma module quotient universal enveloping algebra highest weight basis`:
  8 hits on general quotient bases and root-system weight bases, no Verma module.
- leanfinder: `Verma module quotient universal enveloping algebra positive root highest
  weight ordered monomial basis`: 8 hits, only weight chains and root ambient bases;
  no quotient or monomial basis for Verma modules.
- loogle: `UniversalEnvelopingAlgebra, LieModule.weightSpace`: zero hits.
- grep via msearch.py: `Verma|verma|toLieModule|lieModule|Module.*Lie`, Algebra/Lie:
  generic Lie module results only; no Verma construction.
- rg in both `lean/WeilConjectures` and `lean/Sheaf`: `Verma|verma|monomial.*[Bb]asis`;
  the project has PBW theorems and the rational-highest-weight parent, but no Verma
  quotient or theorem matching this node. An exact item-id search in WeilConjectures
  found no declaration. Searches for all introduced helper names found no collision.
- DAG search found the parent rational-highest-weight node, integrable-finiteness,
  induced-composition-linkage, rational PBW and enveloping universal property; none
  separately defines this node's quotient.

Source reading: current blueprint unit sk-thm-sf-ctf-stability and its current direct-images
proof (3), and Milne printed pp.508–511 (weight gradation, Chevalley construction and
Corollary 23.73) read. The node correctly identifies the underlying Verma argument as an
agent reconstruction and Serre Chapter VII as WANTED; the docstring makes no claim that
Milne contains this PBW/Verma proof. No statement dispute or correction was found.

Independent maintainer review is supplied by the delivery workflow; no other worker was
started, following the dispatcher's explicit instruction.

## Second reading by Q30

A separate worker was not started: the assignment explicitly forbids it and assigns the
independent reading to the maintainer. This is a second self-check, not an independent
review. With the node and module open, the ideal was checked to use U-scalars (left ideal),
the quotient's action to be the canonical one, the ordered product to use an ordered list,
and weight spaces to use ordinary `weightSpace`. All original hypotheses, arbitrary η,
cyclicity, the highest line, finite weight spaces and empty roots are represented above.
The compiler-driven change made the associative commutator Lie structures explicit in
the action construction; it changed no mathematical hypothesis or conclusion.

Validation: scompile.py compiled the complete sandbox module and its named library module
successfully on the server (2026-10-24), with no errors or unexpected warnings. Both
`autoImplicit` and `relaxedAutoImplicit` are disabled. Every delivered declaration has a
source/blueprint docstring; the theorem docstring contains all eight proof steps.
