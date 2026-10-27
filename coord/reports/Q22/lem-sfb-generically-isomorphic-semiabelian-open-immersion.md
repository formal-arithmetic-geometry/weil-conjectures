## Worker report

Statement only: `AlgebraicGeometry.isOpenImmersion_of_generically_isomorphic_semiabelian`
in `Sheaf.AlgebraicGeometry.GenericallyIsomorphicSemiabelianOpenImmersion`.
Its sole proof is `by sorry`. No definitions, auxiliary theorems, new nodes, dependency
repairs, or statement corrections were needed. The node copy changes only `lean`.

The module docstring distinguishes this agent-extracted lemma from the stronger
special setup of Conrad's printed Theorem 4.4 (abelian generic fibre and Néron target).
The source PDF was opened at the URL in the node and read at Corollary 3.3 and the
proof of Theorem 4.4 (PDF pages 8 and 12–14; printed pages 8 and 12–14).
Conrad's quasi-finite/birational argument and invertible-torsion argument are the
inputs, with the node's explicit arbitrary-target expansions retained in the
full ten-step proof docstring. In particular this delivery does not insert
henselianity from Lemma 4.9 into the statement.

Hypotheses and clauses, in the node's order:

| Node | Lean rendering |
| --- | --- |
| A discrete valuation ring R, integral, local principal-ideal and not a field | `(R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]` |
| Its fraction field F | `(F : Type u) [Field F] [Algebra R F] [IsFractionRing R F]`; any field of fractions with its actual structure map |
| T = Spec R | The base of `Over (Spec (.of R))` |
| Group schemes A and B over T | `(A B : Grp (Over (Spec (.of R))))`; `A.X` and `B.X` are objects over T, with underlying schemes `.left` and structure maps `.hom` |
| Commutative multiplication, identity, inverse and group identities | The `Grp` structure and `[IsCommMonObj A.X] [IsCommMonObj B.X]`; group homomorphisms preserve inverses automatically |
| A is smooth | `[Smooth A.X.hom]` |
| A is separated, i.e. its relative diagonal is closed | `[IsSeparated A.X.hom]`, whose field is `IsClosedImmersion (pullback.diagonal A.X.hom)` |
| A is of finite presentation | `[LocallyOfFinitePresentation A.X.hom] [QuasiCompact A.X.hom]`, together with quasi-separatedness furnished by the separated hypothesis, exactly the dependency node's definition of finite presentation |
| A has semiabelian geometric fibres | `(hA : HasSemiabelianGeometricFibres A)` uses the shared split-torus kernel and fppf-locally-surjective abelian quotient predicate |
| B is smooth and separated | `[Smooth B.X.hom] [IsSeparated B.X.hom]` |
| No quasi-compactness or finite-type assumption on B | No such binder occurs; smoothness only gives local finite presentation |
| A given T-group homomorphism a | `(a : A ⟶ B)` in `Grp (Over (Spec (.of R)))`; `a.hom.hom` is its underlying T-morphism, `a.hom.hom.left` its scheme morphism |
| Its base change a_F is an isomorphism | `hgeneric : IsIso (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map a.hom.hom).left)` |
| Conclusion: the given a is an open immersion | `IsOpenImmersion a.hom.hom.left` |
| No completeness, excellence, or perfect residue field assumption | None appears in the binders or the dependencies' predicates |

`Over.pullback` constructs the actual fibre product on objects and the universal
pullback lift on maps. Thus the generic-isomorphism hypothesis does not quantify
an unrelated isomorphism or add a choice of generic identification. `IsIso` is
on the underlying scheme morphism, precisely as the node states it.

Dependency declarations read and used (full source signatures/docstrings inspected):

- `def-sc-discrete-valuation-ring`: `Mathlib/RingTheory/DiscreteValuationRing/Basic.lean` / `IsDiscreteValuationRing` (Mathlib match, no separate lean record required).
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme` / `AlgebraicGeometry.Spec`.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme` / `AlgebraicGeometry.Scheme`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth` / `AlgebraicGeometry.Smooth`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` / `AlgebraicGeometry.IsClosedImmersion`.
- `def-pc-base-change`: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` / `AlgebraicGeometry.Scheme.Modules.moduleBaseChange`.
- `def-sfb-semiabelian-geometric-fibres`: `Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres` / `AlgebraicGeometry.HasSemiabelianGeometricFibres`.
- `def-sbc-locally-finite-presentation`: `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` / `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion` / `AlgebraicGeometry.IsOpenImmersion`.

For scheme base change the recorded `BaseChangeConventions` module explicitly
instructs use of `Over.pullback`/`Limits.pullback` for schemes and morphisms;
its primary `moduleBaseChange` declaration is for modules only and is not misused.
For separatedness the existing Mathlib `IsSeparated` is used directly; its
closed-diagonal field uses the recorded `IsClosedImmersion`.

All currently stated proof-dependency modules are imported without `public`;
statement-dependency modules are public imports. The following proof nodes
have no usable recorded declaration yet and hence contribute no import:
`lem-sfb-smooth-normal-ascent`, `lem-sfb-smooth-group-invertible-multiplication`,
`lem-sfb-space-unramified-permanence`, `lem-sfb-space-unramified-diagonal-open`,
`lem-sfb-semiabelian-closed-subgroup-trivial-torsion-finite`.
These are proof prerequisites only, not missing notions in this statement.
No import cycle was introduced; the delivered module compiles in module mode.

Edge cases checked before writing:

- Rank-zero torus and dimension-zero trivial semiabelian group are allowed by
  `HasSemiabelianGeometricFibres`; there is no positivity or nontrivial-group binder.
- Mixed and equal characteristic, including imperfect residue fields, are covered.
  The DVR class excludes fields exactly as the definition node requires.
- The target may have infinitely many special-fibre components or fail to be
  quasi-compact. No target finiteness class is assumed; an open immersion is
  the conclusion, without a surjectivity or global isomorphism conclusion.
- The groups cannot have empty underlying schemes because their identity sections
  lie over the nonempty spectrum of the DVR. No extra `Nonempty` assumption is added.
- The kernel in the eventual proof may be nonreduced; no reducedness or étaleness
  of the homomorphism or its special fibre is assumed here.
- All universes are explicitly bound. The ring, a field of fractions, and the
  schemes use `u`, as in the recorded trait-extension interfaces. No independent
  too-small universe is used for geometric test fields.

Searches actually run:

- `msearch.py ... leanfinder`: "A generically isomorphic homomorphism from a
  semiabelian scheme over a discrete valuation ring to a smooth separated group
  scheme is an open immersion". Eight hits: general open-immersion definitions,
  every isomorphism is an open immersion, open immersion plus surjectivity
  characterizes isomorphisms, and open embedding plus stalk isomorphisms criteria.
  None states this generic-isomorphism criterion.
- `msearch.py ... loogle`: "IsOpenImmersion, IsDiscreteValuationRing, Grp".
  Zero hits; service reported unknown identifier `IsOpenImmersion`. This is a
  query/name-resolution limitation, not evidence of mathematical absence.
- `msearch.py ... grep` in Mathlib/AlgebraicGeometry:
  `semi.?abelian|generically.*isomorph|isOpenImmersion.*birational`.
  One hit: `Scheme.Hom.birational` in Birational/Birational.lean (open immersions
  that are dominant are birational); it does not state this result.
- `rg -n 'semiabelian|Semiabelian|generically.*isomorph'` in
  `lean/WeilConjectures` and `lean/Sheaf`: found shared semiabelian-fibre and
  trait-hom-extension modules, integrality of geometric powers, and unrelated
  generic comparisons. No existing theorem for this given homomorphism.
- `rg -n 'lem-sfb-generically-isomorphic-semiabelian-open-immersion'` in
  `lean/WeilConjectures`: no hits.
- Local source reads checked the actual `Grp`, `IsCommMonObj`, `Over.pullback`,
  DVR, scheme/Spec, smoothness, finite presentation, closed/open immersion,
  separatedness, fraction-field and recorded semiabelian-fibre definitions.

No STATEMENT-DISPUTED issue or node fault found.

Validation: `scompile.py Q22 lem-sfb-generically-isomorphic-semiabelian-open-immersion`
compiled the delivered module both as a sandbox file (3.9 s) and under its actual
library name (1.7 s), with no errors or unexpected warnings. The server dry run
and delivery results are recorded below when available.

Delivery dry run: `deliver2.py Q22 lem-sfb-generically-isomorphic-semiabelian-open-immersion --no-push`
reported `OK (dry run)`: preflight and per-file compilation passed.
The node signature was checked verbatim against the module, and only `lean` differs
from the base node.

## Second reading by Q22

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
