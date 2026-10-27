## Worker report

The module `Sheaf.AlgebraicGeometry.NearProjectiveDualComparison` states
`AlgebraicGeometry.NearProjectiveDualComparison.nearProjective_dual_comparison`.
Its only postponed proof is this theorem, with the six accepted proof steps in its
docstring. The node's statement, dependencies and proof are unchanged. No new node
or dependency repair is required. All auxiliary declarations are constructions
belonging to this node and listed in `lean.declarations`.

Source read: `literature/stacks-project/local-cohomology.tex`, Remark `remark-duals`
(Tag 0GAB), lines 5075–5114, and `more-algebra.tex`, Lemma
`lemma-dual-near-projective` (Tag 0G96), lines 17826–17848. The node uses the
same factorization argument for any scheme over Spec A. Neither the argument nor
the formal statement assumes flatness. The source's sheaf comparison is recovered
by its evaluation formula, without assuming a stalk/internal-Hom interchange.

Hypothesis and clause correspondence:

- A Noetherian commutative ring is `(A : CommRingCat.{u}) [IsNoetherianRing A]`.
  The ideal is `(J : Ideal A)`. The finite module is
  `(M : ModuleCat.{u} A) [Module.Finite A M]`.
- For every `a ∈ J`, the hypothesis `hM` supplies `r : ℕ`, a linear map from M
  into `Fin r → A`, a linear map back, and `h.comp f = a • LinearMap.id`.
  A finite product over `Fin r` is exactly the finite direct sum A^r, including r=0.
- N is the existing `Module.Dual A M`. The first conjunct asserts
  `Module.Finite A (Module.Dual A M)`. The second conjunct asserts precisely the
  corresponding finite-free factorizations for every a in J.
- The sheaf clause quantifies over every `(Z : Scheme.{u}) (g : Z ⟶ Spec A)`.
  It imposes no geometric conditions on Z or g.
- `associated A` is the existing `associatedModuleFunctor` on Spec A composed
  with scalar restriction along `(Scheme.ΓSpecIso A).hom`. Thus it applies the
  recorded associated-module construction to the given A-module, retaining its
  underlying elements; it does not introduce another associated-sheaf notion.
  Its values are the sheaves denoted by M-tilde and N-tilde in the node.
- `pulled A g M` and `pulled A g (ModuleCat.of A (Module.Dual A M))` are P and F,
  using exactly `Scheme.Modules.tensorPullback`. `dualSheaf A g M` is G, using
  `SheafOfModules.homObj (R := Z.sheaf) P (SheafOfModules.unit Z.ringCatSheaf)`.
  The existing internal Hom has sections the linear maps of restricted sheaves.
- `pulledSection` takes the recorded associated-module canonical section, applies
  the unit of `tensorPullbackSectionAdjunction`, and restricts to U. Therefore it
  is the actual pulled-back generator. `scalar A g U a` is the image of a under
  A → Γ(Spec A) → Γ(Z) → Γ(U), using ΓSpecIso, g.appTop, and restriction.
- The unique arrow α has source F and target G. Its first predicate says on
  every U and b,b',l,m that α(b times the generator l), evaluated at b' times
  the generator m, equals `b * b' * scalar A g U (l m)`. This is exactly the
  specified local tensor formula. The Hom evaluation is the existing
  `PresheafOfModules.homObjEvalId`. Local generation determines α uniquely;
  the unique existential records canonicity, not a freely supplied map.
- The next two predicates quantify over every U, a in J, and every section of
  `kernel α` and `cokernel α`, respectively, and require its product with
  `scalar A g U a` to vanish. These are categorical kernel and cokernel in
  the actual abelian category of module sheaves. This is equivalent to
  annihilation by J O_Z: locally an extended-ideal section is a finite sum
  of functions times images of a in J; vanishing on these generators implies
  vanishing on that sum, and sheaf separatedness glues the zero equation.
  Conversely all scalar images lie in the extended ideal. This does not replace
  the sheaf cokernel with the possibly different cokernel on sections.
- `pulledEvaluation A g M m` is pullback of the associated-module map induced by
  the actual linear evaluation `LinearMap.applyₗ ... m`, followed by the canonical
  map from the pulled-back associated A to O_Z. `structureLinear` is the inverse
  ΓSpecIso as a linear map; `structureMap` is the inverse of the existing
  associated-module Hom bijection on that map. This is a uniquely specified
  universal construction with real data. `pullbackStructureMap` then uses the
  published `tensorPullbackObjUnitToUnit`. The last predicate, for every m,U,x,
  equates evaluation of α(x) on the pulled-back m with this pulled evaluation
  map applied to x. Equality on all sections is equality of the sheaf morphisms
  in the final clause of the node.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (line 196), every
  ideal finitely generated. `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`
  (line 117), finite generation of the top submodule.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`
  (lines 42 and 74), schemes and their morphisms.
- `WeilConjectures.AlgebraicGeometry.AssociatedModule`: `associatedModuleFunctor`,
  `associatedModule`, and `associatedModuleCanonicalSection`, read in full with
  the tensor-presheaf and sheafification docstrings.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullbackSectionAdjunction`, its normalized unit and the
  imported upstream `tensorPullback`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, transparently
  the existing `SheafOfModules`, with its imported abelian instance.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`: `homObj`;
  the underlying `PresheafOfModules.homObjEvalId` evaluates on the identity open.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`:
  `tensorPullbackObjUnitToUnit`, the normalized adjoint of the structure-sheaf map.
- `Sheaf.AlgebraicGeometry.AssociatedModuleHom`: `associatedModuleHom_bijective`,
  used to construct the canonical map from the associated A to the structure sheaf.
  This is the proof dependency already listed by the node, not a replacement notion.
- The modules of the proof dependencies are imported: `Mathlib.RingTheory.Noetherian.Basic`
  (`Submodule.FG.of_le`), `AssociatedModulePullback` (`associatedModule_pullback`),
  and the modules listed above. Their recorded signatures and docstrings were read.

Edge cases checked before and after writing: zero ring (empty Spec and necessarily
empty Z); M=0; rank r=0; J=0 (annihilation conditions vacuous, comparison still
canonical); J=A (the scalar 1 kills kernel and cokernel); empty Z. A nonflat test is
A=Z/4, M=A/2, J=(2), Z=Spec F_2: α is zero, but the image of J is zero and kills
its nonzero kernel and cokernel. The statement does not incorrectly make α an
isomorphism. The universe u is arbitrary, and ring, modules and schemes may be
placed in any common ambient universe; it does not constrain site object and
morphism universes by a separate added equality. No disputed statement was found.

Searches actually run with the prescribed msearch.py wrapper:

- LeanFinder: `The pullback of the dual of a finite near projective module maps canonically to the sheaf dual with kernel and cokernel annihilated by an ideal`.
  Eight hits: `Module.dual_finite`, `Module.dual_projective`, finite-free pullback
  comparisons and generators. The first two require projectivity, and none states
  the ideal-annihilation result.
- Loogle: `"Module.Dual", "baseChange"`. Three hits: `Module.Dual.baseChange`,
  its pure-tensor formula and iterated base change. These give an algebraic map,
  not the near-projective sheaf assertion.
- Mathlib grep: `dual.*base.?change|near.?projective` in LinearAlgebra.
  Six hits, all in Dual/BaseChange or its import. The module's finite-free
  base-change isomorphism is not the required general near-projective result.
- LeanSearch: `Near projective finite module dual sheaf pullback comparison kernel cokernel annihilated ideal`.
  Eight hits, including dual annihilators, `Module.dual_finite`, and categorical
  cokernels of modules; none matches this theorem.
- Local rg searches in both `lean/WeilConjectures` and `lean/Sheaf` for
  `near.projective`, the item id, dual comparison and base-change phrases.
  No occurrence of this item or near-projective statement. The finite-locally-free
  dual pullback theorem has a stronger hypothesis and no annihilation clause.
  The literal `grep -rn` search for the item id in WeilConjectures also had no hits.
  Declaration-name searches in `dag/lean_names_upstream.json` and both source trees
  found none of the new names. Existing associated sheaf, tensor pullback and
  internal Hom definitions are reused throughout.

Validation: scompile.py compiled both the isolated sandbox and the intended library
module successfully, with no reported error or warning. No library/global build was run.

## Second reading by Q42

No second reading by another worker: this dispatcher assignment prohibits starting
other agents. The maintainer's independent review is the delivery review. In a final
self-check against the node, all hypotheses and clauses were matched as above;
no statement correction or dependency replacement was needed.
