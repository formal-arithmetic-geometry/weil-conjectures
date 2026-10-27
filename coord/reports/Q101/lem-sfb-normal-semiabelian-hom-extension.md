## Worker report

The module Sheaf.AlgebraicGeometry.NormalSemiabelianHomExtension states
AlgebraicGeometry.normal_semiabelian_hom_extension, with its proof left `sorry`.
The accepted stage-1 statement, proof, dependencies and review are preserved.
The inherited BLOCKED ending concerned a stage-1 unchanged-split gate. The current
queue lists this node at stage 2, and it has no Lean record. The stage handoff
rule of coord/brief-stage2.md §0 therefore authorizes this statement delivery.
No released repair note is present.

Clause-by-clause correspondence:

- S is a scheme: `{S : Scheme.{u}}`.
- S is integral: `[IsIntegral S]`, which includes nonemptiness.
- S is locally Noetherian: `[IsLocallyNoetherian S]`.
- S is normal: `hS` asks that each `S.presheaf.stalk s` is an integral domain
  and integrally closed, using exactly the recorded normal-domain convention.
- P and Q are group schemes over S: `P Q : Grp (Over S)`. The objects contain
  the group laws, identity and inverse, all as morphisms over S with their axioms.
- They are commutative: `[IsCommMonObj P.X] [IsCommMonObj Q.X]`.
- They are smooth: `[Smooth P.X.hom] [Smooth Q.X.hom]`.
- They are separated: `[IsSeparated P.X.hom] [IsSeparated Q.X.hom]`, meaning
  the relative diagonals are closed immersions.
- They are of finite presentation: locally finite presentation and quasi-compactness
  on both structural morphisms. Quasi-separatedness is supplied by separatedness;
  thus no finite-presentation clause is dropped or strengthened.
- They have semiabelian geometric fibres: `hP` and `hQ` use the dependency's
  `HasSemiabelianGeometricFibres`, with its split-torus kernel and fppf-local
  surjection onto an abelian variety over each algebraically closed geometric point.
- The generic point is `genericPoint S`; its canonical residue-field morphism
  is `S.fromSpecResidueField (genericPoint S)`.
- The generic fibres and induced group laws are the objects of the canonical
  functor `(Over.pullback (S.fromSpecResidueField (genericPoint S))).mapGrp`.
- An arbitrary generic group homomorphism is the binder `fη` between these objects.
- Existence of an extension is `∃! f : P ⟶ Q, ...`; the equality is that canonical
  functor's `map f = fη`, so it is exactly restriction of this S-homomorphism.
- The unique-existence quantifier asserts uniqueness among all group homomorphisms
  P to Q over S restricting to fη, with no extra structure or comparison chosen.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Mathlib.AlgebraicGeometry.Properties: AlgebraicGeometry.IsIntegral.
- Mathlib.AlgebraicGeometry.Noetherian: AlgebraicGeometry.IsLocallyNoetherian.
- Mathlib.RingTheory.IntegralClosure.IntegrallyClosed: IsIntegrallyClosed; the
  normal-domain condition pairs this with IsDomain, as its node prescribes.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: AlgebraicGeometry.Smooth.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:
  AlgebraicGeometry.LocallyOfFinitePresentation.
- Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres:
  AlgebraicGeometry.HasSemiabelianGeometricFibres, whose full definition was read.
- Mathlib.AlgebraicGeometry.ResidueField: Scheme.fromSpecResidueField.
- Mathlib.CategoryTheory.Monoidal.Grp: CategoryTheory.Grp and Functor.mapGrp.
  These supply the given groups, their actual homomorphisms and canonical transport.

Plain proof imports include the stated semiabelian-power-integrality,
algebraic-closure connectedness, smooth-connected generic geometry and
proper/finite-fibre theorems, and scheme-theoretic image and closed-immersion
modules. Smooth composition and finite-type Noetherian ascent are already exposed
by statement imports. The graph properness, graph finite-fibre and finite normal
generic-section nodes have no Lean records yet; their proof imports cannot be
added until those statements exist. They are proof prerequisites only, not objects
needed to type this theorem.

Edge cases checked before writing: an empty base is excluded by integrality,
as in the node; no extra global Noetherian or affine hypothesis is imposed.
Rank-zero tori, trivial groups, pure abelian schemes and pure tori are included
by the shared fibre definition. Zero homomorphisms, endomorphisms and field bases
are included. There is no characteristic or dimension restriction. For a field
base restriction is an equivalence, as expected. Universe u is explicit and shared
with the recorded geometric-fibre predicate; no independent smaller test universe
or additional universe equality is imposed. All variables are bound explicitly,
with autoImplicit disabled.

Searches made:

- msearch.py leanfinder: "Every homomorphism between generic fibres of semiabelian
  schemes over a normal integral base extends uniquely". Eight hits concerning
  normalization descent, separated equality, affine-space extensionality and
  residue fields; none is the stated group extension theorem.
- msearch.py leansearch: "Restriction of semiabelian group scheme homomorphisms to
  the generic fibre is bijective". Eight hits about field restrictions, rational
  maps and residue fields; none matches.
- msearch.py loogle: `"GroupScheme", "Hom"`: zero hits.
- msearch.py grep: `semi.?abelian|homomorphism.*generic|generic.*homomorphism`:
  zero Mathlib hits.
- rg over lean/WeilConjectures with the node id and the same conceptual patterns:
  only NormalIntegralGenericHomFull, which concerns finite integral schemes and
  does not assert semiabelian extension. No node-id match.
- rg over lean/Sheaf for semiabelian spellings: found and reused
  SemiabelianGeometricFibres. Other matches are geometric power integrality,
  geometric split quotient, cube-face detection and symmetric-line extension;
  none states the present theorem.
- Current blueprint section sec-six-functors-basics search for semiabelian,
  semi-abelian and generic homomorphisms found no duplicate statement.

Source check: the local Lan PDF named by the node is absent. The author's primary
source is available online: [Lan, §3.3, Proposition the project server](https://www.kwlan.org/articles/cpt-PEL-type-thesis-revision-dense.pdf).
It extends dense-open homomorphisms over a Noetherian normal base uniquely.
The node's generic-point version follows by finite-presentation spreading on
Noetherian affine opens and uniqueness for gluing; the node already records its
separate graph-based proof route. No source-based statement correction is needed.

No new notions or nodes, dependency repairs, or statement disputes were needed.

## Validation

scompile.py passed for this module in both sandbox and library module modes
(exit 0, no errors or unexpected warnings). The deliver2.py --no-push dry run
passed server preflight and per-file compilation: OK at ab2967886b1.
Only the item node field `lean` changes; every Lean line is at most 100 columns.
The delivery contains exactly the node, its Lean module and this report.
The independent second reading is performed by the maintainer, as specified
in this dispatcher brief; this worker has not represented a self-review as
an independent reading.

## Second reading by Q101

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
