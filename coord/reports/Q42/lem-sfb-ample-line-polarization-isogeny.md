## Worker report

The new module `Sheaf.AlgebraicGeometry.AbelianVariety.AmpleLinePolarizationIsogeny`
states `AlgebraicGeometry.IsAbelianVariety.isIsogeny_of_isAmple_classifiesAbelianDifference`.
Its only proof is `sorry`. There are no definitions, new nodes, dependency repairs,
or changes to the accepted natural-language statement or proof split. The proof
plan in the theorem docstring reproduces all eight steps of the accepted split,
including their dependency citations. All recorded proof-dependency modules are
imported, with Mathlib modules for the matched leaves; only the three modules
used in the statement are public imports.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Any field k | `{k : Type u} [Field k]`, with explicit universe `u` |
| A/k an abelian variety | `(A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A]` |
| A chosen normalized dual Poincare datum | `(D : AbelianDualPoincareDatum A)` |
| L an invertible O_A-module | `(L : A.left.Modules) [L.IsInvertible]` |
| L ample | `(hL : Scheme.Modules.IsAmple A.left L)` |
| The group-scheme homomorphism phi_L | `(φ : A ⟶ D.dual) [IsMonHom φ]` |
| It classifies the normalized difference | `(hφ : ClassifiesAbelianDifference D L φ)` |
| The pullback Poincare module is N_L | The defining `Nonempty` isomorphism in `ClassifiesAbelianDifference` |
| Identity-axis rigidification | The existing normalized family and datum, with the normalization equivalence explained below |
| phi_L is an isogeny | `IsIsogeny φ` |
| Surjectivity | The `Surjective φ.left` superclass of `IsIsogeny` |
| Finite scheme-theoretic kernel over k | The field `IsIsogeny.isFinite_ker : IsFinite (GrpObj.ker φ).hom` |
| No separability, perfection or characteristic assumption | No such binder, no `IsAlgClosed` assumption, and no condition on a tensor exponent |

The classifying predicate is the recorded dependency's own declaration, not a
new surrogate. Its isomorphism formulation is equivalent here to an isomorphism
respecting the specified axis trivializations. Given an isomorphism i of the two
normalized line families, restrict i to the identity axis and compose with the
two rigidifications. The resulting discrepancy is an automorphism of O_A, hence
multiplication by a unit on the parameter A. Pull that unit back along the second
projection A x A -> A and rescale i by its inverse. Since that projection composed
with the identity axis is the identity, the rescaled isomorphism respects the
specified rigidifications. Forgetting the rigidification gives the converse.
Thus no existence condition on the classifying homomorphism is dropped; this
uses exactly `ClassifiesAbelianDifference` as defined by its owning node, and
retains the constant factor c*(0*L) in `abelianNormalizedDifference`.

Statement dependencies, with source signatures and docstrings read:

- `def-weil-field`: `Field` in `Mathlib.Algebra.Field.Defs` (the Mathlib match).
- `def-sc-abelian-variety`: `AlgebraicGeometry.IsAbelianVariety` in
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`; its fields are proper,
  smooth and connected, while the group structure is the adjacent `GrpObj` binder.
- `def-sfb-abelian-dual-poincare-datum`: `AlgebraicGeometry.AbelianDualPoincareDatum`,
  `abelianNormalizedDifference`, `abelianIdentityAxis`,
  `abelianRigidificationPullback`, and `ClassifiesAbelianDifference` in
  `Sheaf.AlgebraicGeometry.AbelianVariety.DualPoincareDatum`. The datum supplies
  instances of `GrpObj D.dual` and `IsAbelianVariety D.dual`, the invertible
  universal module, axis trivializations, fibrewise algebraic triviality,
  the tensor group law and the universal property with every rigidification.
- `def-weil-pbc-ample-invertible-module`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple` in
  `WeilConjectures.AlgebraicGeometry.Ample`, the absolute Stacks ampleness
  predicate, rather than the separate complete-linear-system predicate.
- `def-sc-invertible-module`: `AlgebraicGeometry.Scheme.Modules.IsInvertible` in
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, locally rank one.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj` in
  `Mathlib.CategoryTheory.Monoidal.Grp` and `CategoryTheory.IsMonHom` in
  `Mathlib.CategoryTheory.Monoidal.Mon`, specialized to `Over (Spec (.of k))`.
  `GrpObj.ker` is the actual pullback of the homomorphism and the identity section,
  as implemented in `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`.
- `def-sc-isogeny`: `AlgebraicGeometry.IsIsogeny` in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, with homomorphism,
  surjectivity and finite-kernel fields. No numerical degree substitute is used.

Source and edge-case checks:

Read Milne AV I Proposition 8.1 and Remark 8.2, printed p.35, Proposition 8.14
and the normalized-difference discussion, printed pp.39–40. The latter explicitly
retains nonreduced subgroup schemes in positive characteristic and explains
universality for every parameter scheme. Read the current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/`
`sk-thm-sf-ctf-stability/_section.md` and its direct-images proof, clause (3).
This item is the inherited algebraic-geometric auxiliary and changes no unit route.

- Dimension zero is included: the one-point abelian variety, any invertible line
  and its isomorphism to the one-point dual satisfy the formulation. In the proof
  the effective zero divisor may be empty; no positive-dimension binder appears.
- Empty A is not an omitted case: the identity section of a group scheme over a
  field already excludes it. No additional `Nonempty` assumption is needed.
- Arbitrary and imperfect fields are included. The only field assumption is `Field`.
- In characteristic p, nonreduced finite kernels remain allowed. There is no
  `Etale`, separability, reduced-kernel or prime-to-p condition.
- L need not itself have a nonzero section: the proof first takes a positive
  tensor power and proves the requisite complete-system ampleness there.
- The datum is universally quantified; the theorem does not choose one from a
  mere existence theorem or assume equality with another chosen dual.
- Scheme, field and module universes follow the existing dependency's common
  `u` convention. No extra universe equality is imposed on that interface.

Searches for an existing declaration (2026-10-24):

1. `msearch.py Q42 lem-sfb-ample-line-polarization-isogeny leanfinder
   "An ample invertible sheaf on an abelian variety induces an isogeny to its dual"`:
   eight results, `CommRing.Pic.mk_dual` and seven affine-space comparison
   declarations. None states this theorem.
2. `msearch.py ... loogle
   "AlgebraicGeometry.IsIsogeny, AlgebraicGeometry.ClassifiesAbelianDifference"`:
   zero results, Loogle reports the project identifier `IsIsogeny` unknown.
3. `msearch.py ... grep 'IsIsogeny|ClassifiesAbelianDifference' AlgebraicGeometry`:
   zero Mathlib matches.
4. `rg -n 'IsIsogeny|ClassifiesAbelianDifference|polarization'` in the project's
   abelian-variety directories, followed by the wider
   `rg -n 'isIsogeny.*ample|ample.*isIsogeny|polarization|ClassifiesAbelianDifference'
   lean/WeilConjectures lean/Sheaf`: the algebraically closed polarization-calculus
   theorem exists, but not this arbitrary-field theorem for every supplied datum
   and every ample invertible module. Multiplication isogenies and other
   polarization consumers do not give the same statement.
5. `rg -n 'lem-sfb-ample-line-polarization-isogeny' lean/WeilConjectures`: no match.
   No released repair note exists for this item. The current queue lists stage 2;
   the old stage-1 rejection of an unchanged reviewed split is inapplicable.

The example `CompactObject.lean` is now a withdrawn empty module; its node points
to the existing Mathlib compact-object declaration. The active dual-datum and
polarization-calculus modules supply the current module/header conventions.

No statement dispute or node correction is needed.

## Second reading by Q42

A separate pass through the node and the final declaration checked each row of
the correspondence table. In particular, the conclusion was expanded to check
`Surjective φ.left` and finiteness of the scheme-theoretic pullback kernel, and
the classifying hypothesis was expanded to check all four normalized-difference
factors, including c*(0*L). The potential rigidification mismatch is resolved by
the parameter-unit correction described above; it does not require a new
predicate or a restriction to rational points. Both A's and the dual's abelian
variety structures are present. The field has no algebraic-closure or perfection
binder. Absolute ampleness is the prescribed dependency declaration. The proof
plan retains all eight accepted steps and proof imports.

This second pass was performed by this dispatched worker. No other worker was
started, as the dispatch brief forbids it; the maintainer's independent review
remains the independent reading required by this dispatch.

## Validation

`scompile.py Q42 lem-sfb-ample-line-polarization-isogeny <module>` passed on
2026-10-24: sandbox 2.0 s, library 1.8 s, no errors or warnings. The initial
docstring-format warning was repaired and this is the clean recompile. Static
checks confirm that only the item's `lean` field changes, its signature is verbatim,
all module lines are at most 100 characters, and the only theorem proof is `sorry`.
`deliver2.py Q42 lem-sfb-ample-line-polarization-isogeny --no-push` returned
`OK (dry run): commit 7af9197258d passes the preflight and compiles; nothing pushed`.
The staged delivery contains exactly the module, the item node and this report.
