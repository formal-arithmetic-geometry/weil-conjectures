## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.HomFiniteFree` states
`AlgebraicGeometry.abelianVariety_hom_finite_free`, with its entire proof `sorry`.
The node is unchanged except for `lean`. There are no statement corrections,
new independent notions, or dependency-record repairs.

Two real helper constructions belong to this node's own Hom notation:
`abelianVarietyHomSubgroup A B` is the subgroup of `A ⟶ B` with carrier
`{f | IsMonHom f}`. Closure uses existing Mathlib/upstream instances for the
pointwise unit, product, and inverse. `abelianVarietyHom A B` is `Additive` of
that subgroup. Its additive commutative group is inherited from the canonical
pointwise commutative group on morphisms into B. Neither helper uses `sorry`,
choice, an arbitrary morphism, or an assumed group structure. Their declarations
are listed in `lean.declarations`, with source and blueprint docstrings.

Hypothesis and clause correspondence:

- A field k: `{k : Type u} [Field k]`, with explicitly declared universe `u`.
- A and B over k: `(A B : Over (Spec (.of k)))`.
- Their group-scheme structures: `[GrpObj A] [GrpObj B]`.
- A and B abelian varieties: `[IsAbelianVariety A] [IsAbelianVariety B]`,
  precisely proper, smooth, connected from the recorded upstream definition.
- Hom consists of k-group-scheme homomorphisms: the carrier `IsMonHom f`
  of `abelianVarietyHomSubgroup`, with `f` a morphism in the over category.
  This excludes non-homomorphic translations and enforces the k-structure.
- Pointwise addition from B: Mathlib's `CategoryTheory.Hom.commGroup` writes
  it as multiplication `lift f g ≫ μ[B]`; the subgroup inherits this exact
  operation, and `Additive` relabels it as addition. Zero and negation are
  respectively the constant unit map and composition with inversion on B.
- Free abelian of finite rank, with a finite Z-basis:
  `∃ n : ℕ, Nonempty (Module.Basis (Fin n) ℤ (abelianVarietyHom A B))`.
  The Z-module structure is the standard integer action on an abelian group.
  A `Module.Basis` gives unique finitely supported integer coordinates; the
  index `Fin n` is finite and allows n=0. No bound not stated in the node is added.
- End_k(A) is Hom_k(A,A): exactly the same helper with both arguments A;
  there is no unrelated ring or abstract group substituted for it.
- A unital associative ring: `∃ r : Ring (abelianVarietyHom A A), ...`.
  The existential asserts the ring axioms, including both distributive laws,
  while the following equalities specify its canonical operations.
- Its pointwise additive group: `r.toAddCommGroup = Additive.addCommGroup`.
  The right side explicitly names the instance on `Additive` of the subgroup,
  rather than using `inferInstance` inside the scope of the ring binder (which
  could pick the ring's own additive group and become tautological).
- Multiplication is composition: for every f,g, `(r.mul f g).val = g.val ≫ f.val`.
  Lean's `g ≫ f` is f composed with g, so the orientation is exactly fg=f∘g.
- Its multiplicative identity: `r.one.val = 𝟙 A`. The subtype inclusion is
  injective, so this specifies the element itself.
- Its additive group is free of finite rank: the final finite-basis existential
  on `abelianVarietyHom A A`. The ring's additive group is identified with the
  canonical group by the preceding equality, so this is the stated group.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs, via the upstream abelian-variety import.
- `AlgebraicGeometry.IsAbelianVariety`,
  WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs, reexported by Basic.
- `CategoryTheory.GrpObj` and `CategoryTheory.IsMonHom`,
  Mathlib.CategoryTheory.Monoidal.Grp and Mathlib.CategoryTheory.Monoidal.Mon;
  reexported through the imported group-object framework. Read also
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs for its explicit convention
  that these specialize to the node's group schemes and homomorphisms.
- `Module.Free` and `Module.Basis`, Mathlib.LinearAlgebra.FreeModule.Basic.
  The statement uses the actual finite basis, rather than a private predicate
  for freeness. `Module.Free` is the dependency's recorded notion of having a basis.
- `AlgebraicGeometry.IsAbelianVariety.isCommMonObj`,
  WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic. This is needed already
  by the subgroup's commutative group structure and closure of pointwise products.
- Closure instances `CategoryTheory.MonObj.isMonHom_one`, `isMonHom_mul`,
  WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Mon; inverse closure
  is Mathlib.CategoryTheory.Monoidal.Cartesian.Grp's `IsMonHom f⁻¹` instance.
- Proof imports: Sheaf.GroupTheory.TorsionfreeRationalizationInjective
  (`AddCommGroup.rationalizationMap_injective`),
  Mathlib.NumberTheory.Padics.RingHoms (`Padic`, `PadicInt`, quotient maps),
  Mathlib.Algebra.Module.ZLattice.Basic (`instModuleFinite_of_discrete_submodule`),
  Mathlib.LinearAlgebra.FreeModule.PID (`Module.basisOfFiniteTypeTorsionFree'`,
  `Submodule.basisOfPid`). The three geometric proof inputs
  lem-sfb-abelian-tate-action-saturation, lem-sfb-abelian-degree-polynomial,
  and lem-sfb-simple-isogeny-decomposition have no recorded Lean yet and
  are not required to type this statement; no speculative import was added.

Source and edge-case checks:

Read Milne AV I Section 10, especially Theorem 10.15 and its proof, printed
pp.49–50, and the endomorphism conventions printed pp.42–43, using pdftotext
on the repository's PDF. The source covers arbitrary k, not merely algebraically
closed k. The theorem has no characteristic or algebraic-closure hypothesis.
For the zero variety or a zero Hom group, `Fin 0` permits the empty basis.
`Ring` does not require `Nontrivial`, so the zero variety's one-element endomorphism
ring with 1=0=id is included. No positivity of dimension or basis rank is imposed.
For A=B the Hom group is definitionally the same type as the End group.
The helper's source does not need A abelian to construct the subgroup, but the
main theorem explicitly retains the node's abelian-variety hypotheses on both.
The same universe for k and its schemes is the recorded upstream scheme convention,
not a specialization of a new independent coefficient universe.

Existing-declaration searches (msearch.py, group Q115, this item):

- LeanFinder, “Homomorphisms of abelian varieties form a finite rank free abelian
  group”: eight hits, including Module.Finite.addMonoidHom, Module.Free.addMonoidHom,
  FGModuleCat.instFiniteHom, FreeAbelianGroup.instFiniteInt. None treats geometric
  abelian-variety homomorphisms; the additive Hom results assume already finite/free
  abstract underlying modules, so they cannot replace this theorem.
- Loogle, “Module.Free, Module.Finite, CategoryTheory.Grp”: zero hits.
- msearch grep, “AddCommGroup.*[Hh]om|[Hh]om.*[Ff]inite|[Ee]nd.*[Rr]ing” in
  CategoryTheory/Monoidal: nine hits, all unrelated distributor or ring-object facts.
- LeanSearch, “Hom group of abelian varieties finite free integer module”: eight
  hits on abstract additive/commutative groups, module Hom, and free abelian groups;
  no matching geometric result.
- rg in lean/WeilConjectures and lean/Sheaf for the item id,
  hom_finite_free, finite_free_hom: only the downstream proof citation in
  PolarizedOddLevelRigidity and unrelated coherent/condensed Hom lemmas.
- rg in the upstream AbelianVariety and GroupScheme directories for finite Hom,
  free Hom, and endomorphism ring: no statement of finite-freeness or canonical
  endomorphism ring on these group-scheme morphisms.
- rg in the upstream-name inventory, Mathlib, WeilConjectures and Sheaf for
  abelianVarietyHom and abelianVariety_hom_finite_free: no existing declarations.
- Read the Mathlib group-object Hom and bundled CommGrp sources: the canonical
  pointwise group exists on all scheme maps, but there is no existing additive
  group of group-scheme homomorphisms, or its End ring, to reuse verbatim.
  Therefore the helper is the actual subgroup construction using the existing
  IsMonHom notion, not a second definition of group-scheme homomorphism.

Validation: scompile.py compiled the sandbox and its library-path module cleanly,
without errors or non-sorry warnings (latest successful run: 6.2 s and 2.0 s).
The module has one postponed named theorem and two completely defined helpers;
maximum line width is 91. No STATEMENT-DISPUTED fault was found.

## Second reading by Q115

A separate rereading pass of the full node and final module checked all binders,
both finite-basis conclusions, and all ring clauses. This pass was performed
by the same worker because the dispatcher explicitly prohibits starting agents;
the maintainer's independent review remains the independent reader.

The first compiler pass found closure-instance application errors, repaired by
explicitly typed existing-instance terms in the subgroup fields. The second pass
found linter warnings for implicit instance use, repaired by underscore-prefixed
binder names. Semantic rereading caught the risk of `inferInstance` selecting the
existential ring's own additive group; the final signature instead explicitly
uses `Additive.addCommGroup`. Thus the compatibility equality is substantive.
The composition orientation was checked against Milne's fg=f∘g convention:
`g.val ≫ f.val`, not the opposite. The carrier uses all k-homomorphisms, not
maps on k-rational points; properness, smoothness, connectedness, and both group
structures remain present. The zero ring and empty basis remain admitted.
No hypothesis or conclusion of the node was changed. No new-node or dependency
module section is needed because the delivery contains neither.
