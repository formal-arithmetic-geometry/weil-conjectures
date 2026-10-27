## Worker report

The module `Sheaf.AlgebraicGeometry.SemisimpleFixedSubschemeSmooth` states
`AlgebraicGeometry.semisimple_fixed_subscheme_smooth`, with its sole proof `sorry`.
It states the smoothness assertion of Milne, *Algebraic Groups* (2017),
Corollary 13.8, printed p.257, in precisely the affine, finite-type, smooth connected
acting-group specialization of the node. I read printed pp.255–257, including
the definition of fixed subschemes, Lemma 13.6, Theorem 13.7 and Corollary 13.8.
The current blueprint unit is `sk-thm-sf-ctf-stability`; this supporting lemma
requires no change to its statement or proof route. There is no repair note.

The node's statement and proof are unchanged. Its `lean` record is added and
its `stmt_deps` gains the already landed `def-sfb-semisimple-group-scheme-point`,
whose exact definition is used rather than duplicated. No new definitions,
dependency modules, statement corrections or additional postponed theorems.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Algebraically closed field k | `{k : Type u} [Field k] [IsAlgClosed k]` |
| k-group scheme H | `(H : Over (Spec (.of k))) [GrpObj H]`; the group object includes multiplication, identity, inverse and their laws |
| H affine | `[IsAffine H.left]` |
| H finite type over k | `[LocallyOfFiniteType H.hom] [QuasiCompact H.hom]`, exactly the recorded conjunction |
| H smooth | `[Smooth H.hom]` |
| H connected | `[ConnectedSpace H.left]`, including nonemptiness |
| Smooth affine finite-type k-scheme X | `(X : Over (Spec (.of k))) [IsAffine X.left] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [Smooth X.hom]` |
| Action morphism H ×_k X → X | `[action : ModObj H X]`, whose `smul` is the internal morphism on the cartesian monoidal product of schemes over Spec k |
| Identity action law | `ModObj.one_smul`, included in the action structure |
| Associativity action law | `ModObj.mul_smul`, included in the action structure |
| Action laws after every algebra extension | Internal morphism identities yield the pointwise `Hom.mulAction` on each `(Spec A ⟶ H, Spec A ⟶ X)`; conversely affine test schemes detect these identities |
| Rational point s ∈ H(k) | `(s : StandardGroupSchemes.affine k k ⟶ H)` |
| Semisimplicity in every finite-dimensional algebraic representation | `(hs : IsSemisimpleGroupSchemePoint H s)`; its definition quantifies over every finite index type, every `GeneralLinearGroup.RationalHom` with `IsMonHom`, and conjugation to a diagonal matrix |
| Algebraic representations are group-scheme homomorphisms to GL(V) | The existing predicate uses the recorded rational-hom and general-linear-group interfaces, including all algebra-valued points; finite-dimensional vector spaces are tested in a basis |
| Closed subscheme X^s of X | `(F : Over (Spec (.of k))) (i : F ⟶ X) [IsClosedImmersion i.left]` together with `hfixed` |
| Canonical extension s_A | `StandardGroupSchemes.map k (Algebra.ofId k A) ≫ s`, contravariant Spec of the coefficient map followed by s |
| Equalizer of a(s,−) and id, on every commutative k-algebra | `hfixed` quantifies over `(A : Type u) [CommRing A] [Algebra k A]` and each `x : StandardGroupSchemes.affine k A ⟶ X`; its left side says x factors through i, and its right side is `s_A • x = x` |
| Scheme-theoretic rather than rational-point fixedness | The quantifier includes nonreduced algebras and the zero ring. A closed immersion is monic, so every displayed factorization is unique; this is precisely representation of the equalizer subfunctor, not merely equality of underlying supports |
| Conclusion X^s smooth over k | `Smooth F.hom` |
| No connectedness assumption on X | No `ConnectedSpace X.left` or `Nonempty X.left` binder; also none on F |

Dependency declarations used, with full signatures and docstrings read:

- `Field`: `Mathlib.Algebra.Field.Defs`, for `def-weil-field`.
- `IsAlgClosed`: `Mathlib.FieldTheory.IsAlgClosed.Basic`, for the algebraically
  closed clause of `def-weil-algebraic-closure` (not an algebraic-closure object).
- `CategoryTheory.GrpObj`: `Mathlib.CategoryTheory.Monoidal.Grp`, and
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: the recorded group-scheme
  interface for `def-sc-group-scheme`; the latter also supplies the recorded
  `IsSubgroupScheme`, `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme` interfaces
  of `def-sc-group-scheme-subgroup`. No extra subgroup is hypothesized in this item.
- `AlgebraicGeometry.LocallyOfFiniteType` and `QuasiCompact`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`, for
  `def-weil-finite-type-morphism`.
- `AlgebraicGeometry.Smooth`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  for `def-sbc-smooth-morphisms`.
- `ConnectedSpace`: `Mathlib.Topology.Connected.Basic`, for
  `def-weil-connected-scheme` (Mathlib dependency with no separate lean record).
- `AlgebraicGeometry.IsClosedImmersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, for
  `def-weil-closed-immersion`.
- `AlgebraicGeometry.Scheme`, `Scheme.Hom`: `Mathlib.AlgebraicGeometry.Scheme`,
  for `def-pc-scheme`.
- `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, `.lift`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, for
  `def-pc-fibre-product`; the cartesian monoidal structure on `Over (Spec k)`
  uses these fibre products. `ModObj` from `Mathlib.CategoryTheory.Monoidal.Mod`
  and pointwise action from `.Cartesian.Mod` give its standard action interface.
- `AlgebraicGeometry.IsSemisimpleGroupSchemePoint`:
  `Sheaf.AlgebraicGeometry.SemisimpleGroupSchemePoint`, the already landed
  `def-sfb-semisimple-group-scheme-point`; `StandardGroupSchemes.affine` and `.map`
  are from `Sheaf.AlgebraicGeometry.StandardGroupSchemes`, imported publicly there.

The stated proof dependency
`AlgebraicGeometry.semisimple_cyclic_closure_linearlyReductive` from
`Sheaf.AlgebraicGeometry.SemisimpleCyclicClosureLinearlyReductive` is imported
without `public`. Its full signature and proof docstring were read. The other
proof dependency `lem-sfb-linearly-reductive-dense-fixed-smooth` has no recorded
Lean declaration or Mathlib match in the read snapshot, so there is no module
to import for it. Its statement is nevertheless used verbatim in step 3 of the
proof docstring; it is not needed to elaborate the current statement.

Edge cases checked before writing:

- s = 1 gives the whole X as fixed subscheme, with the stated smoothness.
- X may be disconnected or empty. No nonemptiness enters via its binders.
  F may be empty, including for a translation with no fixed point.
- Arbitrary characteristic is retained. In characteristic p the cyclic closure
  may be disconnected (finite prime-to-p torsion); neither the statement nor
  the proof plan replaces it by a connected torus.
- Nonreduced test algebras and the zero algebra are allowed. Quantifying only
  over k-points would lose the equalizer structure and is deliberately avoided.
- The representation predicate includes the empty index type (dimension zero).
- A common explicit universe u for k, schemes and test algebras is the project
  convention and includes coordinate algebras of the affine schemes. No
  independently smaller universe can make the pointwise condition vacuous.
- No reduction or smoothness of F, no freeness of the action, and no extra
  hypothesis on s or the order of s are assumed.

Searches actually run:

- `msearch.py ... leanfinder "The fixed subscheme of a semisimple element acting
  on a smooth affine scheme is smooth"`: eight hits, all general smooth-locus
  or standard-smooth results, no fixed-subscheme assertion.
- `msearch.py ... loogle '"fixed", "Smooth"'`: zero hits.
- `msearch.py ... grep 'semisimple|fixedLocus|fixed.*[Ss]mooth' AlgebraicGeometry`:
  zero hits.
- `msearch.py ... leansearch "fixed subscheme smooth semisimple algebraic group
  action"`: eight hits, general smoothness and abstract fixing-subgroup results,
  no matching scheme-theoretic assertion.
- `rg` in project `lean/WeilConjectures` and `lean/Sheaf`: found the reusable
  semisimple-point predicate and cyclic-closure theorem; no theorem with this
  assertion. `grep -rn` for the item id in `lean/WeilConjectures` found nothing.
- The nearby `Sheaf.AlgebraicGeometry.TorusFixedSchemeSmooth` was read: its acting
  group is a torus and its fixed functor is fixed by the entire torus, so it
  does not state the present single-semisimple-element assertion. The
  cyclic closure can have a finite disconnected factor.
- Read `WeilConjectures.AlgebraicGeometry.OverProduct`: its `Scheme.fixedLocus`
  is the standard equalizer construction, not a theorem about smoothness.
  The present statement supplies F with the exact closed-subfunctor
  characterization; it introduces no second fixed-locus definition.
- DAG searches found `def-sfb-semisimple-group-scheme-point`, which is reused;
  action-groupoid definitions use the same existing Mathlib `ModObj`.

Validation: the final module compiled through `scompile.py Q09
lem-sfb-semisimple-fixed-subscheme-smooth <module>` on 2026-10-24, both as sandbox
and library module, with no errors or unexpected warnings. Every variable and
universe is explicitly bound; `autoImplicit` is false. The final module contains
one named theorem with `sorry`, no proved theorem, no custom definition and no
file-local notation or instance. No statement dispute or node fault was found.

## Second reading by Q09

I reopened the delivered node and final module for a separate clause-by-clause
pass after compilation. As a dispatcher-started single worker I did not launch
another agent or claim an independent reviewer; the maintainer's independent
review is the delivery's next step.

The comparison found the field, algebraic closedness, H group/affineness/finite
type/smoothness/connectedness, X affineness/finite type/smoothness, both action
laws, rational point and representation semisimplicity, closed immersion and
all-algebra equalizer characterization, and the smoothness conclusion exactly
as in the correspondence table. The supplied F and i are determined up to the
unique isomorphism over X by `hfixed`: closed immersion gives injectivity on
A-points, and `hfixed` gives existence exactly on the equalizer subfunctor.
In particular this is not an arbitrary closed subset with the same k-points.
The action `ModObj` contains an actual algebraic action morphism and its laws,
not an arbitrary family of abstract actions. No connectedness was imposed on X.
I rechecked empty X/F, s = 1, the zero/nonreduced algebras, positive characteristic,
and the zero-dimensional representation. No mismatch or code change was needed.
The only metadata addition beyond `lean` is the landed semisimple-definition
node used by the signature. No new node or dependency repair is required.
