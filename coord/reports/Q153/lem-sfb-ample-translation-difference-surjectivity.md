## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.AmpleTranslationDifferenceSurjectivity`
states `AlgebraicGeometry.IsAbelianVariety.exists_iso_translation_tensor_dual_of_homogeneous`.
Its only theorem proof is `sorry`; it defines no objects. The node is unchanged except for
its `lean` attachment. No new nodes, dependency repairs, or statement correction are needed.

The statement was checked against the local Milne, *Abelian Varieties*, Chapter I,
Proposition 8.14, printed p.39; Proposition 8.4(b), printed pp.35–36; and the definition
of lambda on p.34. Proposition 8.14 is surjectivity for a specified ample invertible
module, and 8.4(b) defines the homogeneous classes without assuming algebraic equivalence.
The nine proof steps of the node are carried into the theorem docstring.

Every hypothesis and clause is rendered as follows:

| Node clause | Lean |
| --- | --- |
| k a field | `{k : Type u} [Field k]` |
| k algebraically closed | `[IsAlgClosed k]` |
| A/k a group scheme | `(A : Over (Spec (.of k))) [GrpObj A]` |
| A an abelian variety, proper, smooth, connected | `[IsAbelianVariety A]` |
| M an ample invertible O_A-module | `(M : A.left.Modules) (hM : IsAmple A.hom M)`; `IsAmple` is by definition `M.IsInvertible` and existence of a positive very ample tensor power |
| L an invertible O_A-module | `(L : A.left.Modules) [Scheme.Modules.IsInvertible L]` |
| Every b in A(k) | `∀ b : 𝟙_ (Over (Spec (.of k))) ⟶ A` |
| Translation t_b(x)=x+b | `(AlgebraicGeometry.GrpObj.mulRight A b).left`; its actual definition is `lift (𝟙 A) (toUnit A ≫ b) ≫ μ[A]` |
| Invariance t_b^*L isomorphic to L | `Nonempty ((Scheme.Modules.tensorPullback (GrpObj.mulRight A b).left).obj L ≅ L)` |
| Some a in A(k) | `∃ a : 𝟙_ (Over (Spec (.of k))) ⟶ A` |
| L isomorphic to t_a^*M tensor M inverse | `Nonempty (L ≅ (Scheme.Modules.tensorPullback (GrpObj.mulRight A a).left).obj M ⊗ Scheme.Modules.dual M)` |
| Tensor inverse-image pullback | `Scheme.Modules.tensorPullback`, the actual change-of-rings construction on inverse image |
| Sheaf tensor product over O_A | `⊗` in the existing monoidal category of `A.left.Modules`, the localized sectionwise tensor |
| M inverse = sheaf Hom(M,O_A) | `Scheme.Modules.dual M`, defined as `homObj M (SheafOfModules.unit _)` |
| No characteristic or dimension restriction | No characteristic, nonzero-dimension, prime-to-integer, or dimension binders |

Dependency declarations were read at their definitions, including full signatures and
docstrings. Public imports use the recorded interfaces:

- `Mathlib.Algebra.Field.Defs`: `Field`; available through the field-theory import.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, the algebraically closed clause of
  def-weil-algebraic-closure. No chosen algebraic closure is required in this statement.
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`:
  `AlgebraicGeometry.IsAbelianVariety`; it deliberately does not take a group structure as
  an argument, so `[GrpObj A]` is stated separately as its documentation requires.
- `WeilConjectures.AlgebraicGeometry.Modules.VeryAmple`:
  `AlgebraicGeometry.IsAmple`; its first conjunct supplies invertibility of M. Its proper
  scheme convention applies since A is proper.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, the locally rank-one module predicate.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  the recorded module for def-pc-module-pullback. Its public upstream import supplies
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`; no alternate pullback is introduced.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  the recorded module for def-pur-sheaf-tensor-product, supplying
  `SheafOfModules.cochainModulesMonoidal` for the existing localization tensor.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`:
  `AlgebraicGeometry.GrpObj.mulRight`, the canonical right translation.
- `WeilConjectures.AlgebraicGeometry.Modules.Dual`:
  `AlgebraicGeometry.Scheme.Modules.dual` and `homObj`, the dual clause already in
  def-sc-invertible-module. This is not a new notion or an arbitrary inverse choice.

All currently recorded proof-dependency modules are imported without `public`, except
modules already public for a statement dependency. Mathlib proof matches are imported
from their source modules. The two proof nodes lem-trf-proper-field-invertible-coherent
and lem-sfb-projective-line-module-serre-duality currently have no recorded Lean module;
there is consequently no proof import for them. They are not needed to type the statement.
No proof import cycle is introduced; in particular the parent homogeneous-to-algebraically-
trivial theorem and polarization calculus are not imported as proof inputs.

Edge cases checked mathematically before drafting:

- Dimension zero is retained: over an algebraically closed field the abelian variety is
  the point, its invertible modules are trivial, and the identity point witnesses the
  conclusion. Neither homogeneous quantification nor the existential excludes it.
- L = O_A is retained, with the identity translation giving M tensor its dual.
- Positive characteristic is retained, including when the auxiliary tensor exponent in
  the proof is divisible by the characteristic: the proof takes a = nb and never divides
  by n or extracts an nth root.
- The empty scheme is excluded by the source's abelian-variety hypothesis: connectedness
  includes nonemptiness and the group identity also supplies a rational point. No extra
  nonemptiness hypothesis is added.
- Ampleness is essential: M = O_A on a positive-dimensional abelian variety would give
  only the trivial difference, so omitting hM would be false. The actual hypothesis is
  not a tautological morphism property or an unspecified map.
- The existential witnesses an actual rational point and an actual module isomorphism;
  it does not merely assert algebraic equivalence or assume an identification of Pic^0.

Searches made before drafting (the wrapper also records exact results in searches.jsonl):

1. `leanfinder`: "Every homogeneous invertible sheaf on an abelian variety over an
   algebraically closed field is a translation difference of a fixed ample invertible
   sheaf". Eight hits: Weierstrass point classes and affine point-to-class maps,
   `CommRing.relPic`, `Submodule.range_unitsToPic`, `CommRing.relPic_eq_top`. None states
   this scheme-theoretic surjectivity theorem.
2. `loogle`: "IsAmple, IsAbelianVariety, GrpObj.mulRight". Zero hits, unknown identifier
   IsAmple (the service indexes Mathlib, not these project declarations).
3. `msearch grep`, Mathlib AlgebraicGeometry:
   `translation.*(ample|invertible)|homogeneous.*(line|invertible)|polarization`.
   Zero hits.
4. `leansearch`: "An ample line bundle on an abelian variety realizes every translation
   invariant line bundle as its translation tensor its dual". Eight hits, including
   analytic `AmpleSet.vadd`, `Submodule.tensorInvEquiv`, tensor-dual equivalences and
   `TensorPower.mulEquiv`; none states the assertion.
5. `rg` in the upstream abelian-variety modules and in `lean/Sheaf`, for translation,
   homogeneous, polarization, and translation-difference variants. Existing project
   polarization calculus supplies classification and a finite-kernel/isogeny criterion,
   not this homogeneous translation-difference statement; the homogeneous acyclicity
   module supplies the correct translation interface; the homogeneous algebraic-triviality
   module cites this item as a proof prerequisite. No exact existing declaration found.
6. `rg` of the exact node id through `lean/WeilConjectures` and `lean/Sheaf` found only
   the parent theorem's proof citation. `rg` of the proposed declaration name through
   Lean sources and `dag/lean_names_upstream.json` found no existing declaration.

Validation: the prescribed `scompile.py` compiled both sandbox and actual module paths
cleanly against the published library, approximately 16 seconds each. No warning was
reported. The JSON signature is extracted verbatim from the theorem keyword to before
`:=`; all variables and the universe are explicitly bound, with both auto-implicit
options disabled. All Lean lines are at most 100 characters.

No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by Q153

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
