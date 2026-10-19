## Worker report

The assigned node is already stated and reviewed: the repository contains
`AlgebraicGeometry.geometricallyReduced_of_generic_stalks` in
`Sheaf.AlgebraicGeometry.GeometricReducednessFromGenericStalks`, recorded by NL and
reviewed on 2026-10-15. This delivery reuses that exact declaration with `existing: true`.
It delivers no Lean module, adds no definitions, and changes no mathematical statement.

Clause-by-clause correspondence:

- The field is `(k : Type u) [Field k]`.
- The scheme over that field is `(X : Scheme.{u}) [X.Over (Spec (.of k))]`;
  `X ↘ Spec (.of k)` is its given structure morphism.
- Reducedness of X is `[IsReduced X]`, the sectionwise condition equivalent to
  reducedness of all local rings.
- Every irreducible component is quantified by `∀ (Z : Set X),
  Z ∈ irreducibleComponents X →`; every generic point by
  `∀ (ξ : X), IsGenericPoint ξ Z →`.
- Every field extension is `∀ (L : Type u) [Field L] [Algebra k L]`.
- The local ring is Mathlib's `X.presheaf.stalk ξ`.
- The further binder `[Algebra k (X.presheaf.stalk ξ)]` and equality
  `algebraMap k (X.presheaf.stalk ξ) =
  (StructureSheaf.toStalk k ((X ↘ Spec (.of k)) ξ) ≫
  (X ↘ Spec (.of k)).stalkMap ξ).hom`
  specify precisely the canonical k-algebra structure. They impose no extra
  mathematical hypothesis: the composite is a ring homomorphism and its
  `RingHom.toAlgebra` supplies such an instance. Quantifying over all instances
  satisfying this equality prevents an unrelated scalar action.
- The tensor conclusion in the hypothesis is
  `_root_.IsReduced ((X.presheaf.stalk ξ) ⊗[k] L)`.
  `Algebra.TensorProduct.tmul_mul_tmul` gives exactly the stated multiplication.
- The conclusion `GeometricallyReduced (X ↘ Spec (.of k))` means all field
  base changes are reduced, through `geometrically_iff_of_commRing` and
  `geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms`.
- No finite type, Noetherian, quasi-compactness, or finite component hypothesis appears.

Dependency declarations inspected:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`, and its
  section/stalk equivalence theorems.
- `Mathlib.AlgebraicGeometry.Over`: `AlgebraicGeometry.Scheme.Over`.
- `Mathlib.Topology.Sober`: `IsGenericPoint` is `closure {ξ} = Z`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents` is the set of maximal
  irreducible subsets.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra` for field extensions and stalk actions.
- `Mathlib.AlgebraicGeometry.Geometrically.Reduced`:
  `AlgebraicGeometry.GeometricallyReduced`; this is the reduced alternative explicitly
  included in the dependency `def-pc-geometrically-irreducible`'s mathlib_match.
- `Sheaf.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor` uses Mathlib stalk carriers; the item concerns
  the underlying ring stalk, so directly uses `TopCat.Presheaf.stalk` rather than
  constructing another stalk or using a module object as a ring.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`, with ring structure in
  `Mathlib.RingTheory.TensorProduct.Basic`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, used inside geometric reducedness.

Source checked directly in literature/stacks-project/varieties.tex:
`lemma-generic-points-geometrically-reduced` part (3) states the reduced scheme criterion
without finiteness, and `lemma-geometrically-reduced-at-point` identifies the local-ring
condition. The existing declaration docstring carries all four proof steps of the node:
affine minimal-prime localization, joint zero detection, finite independent tensor
coefficients, and reduced affine base-change charts. Its proof remains `sorry`.

Edge cases: the empty scheme has no components and remains empty after base change;
infinite sets of components are allowed by unrestricted quantification over Z; no
characteristic is excluded, including imperfect fields; L=k is included. The universe
u is shared by the field, scheme, and extension quantification exactly as in Mathlib's
geometric property. There is no independent lower test universe making the premise
vacuous. The theorem is universe polymorphic.

Searches:

- msearch.py leanfinder: "A reduced scheme is geometrically reduced if all generic
  stalks remain reduced under every field extension" returned eight reducedness and
  integralness declarations, with no generic-stalk criterion.
- msearch.py loogle: `"GeometricallyReduced"` returned the class, its characterization,
  base-change instances and reducedness consequences, not this criterion.
- msearch.py grep: `generic|IsReduced` in
  `AlgebraicGeometry/Geometrically/Reduced.lean` returned five lines, no criterion.
- rg in upstream WeilConjectures for the item id and declaration name found no match.
- rg in project lean/Sheaf found precisely the existing module named above; its full
  signature and docstring were read and matched against the node.

No statement dispute, new node, dependency repair, or source correction is required.
The dispatch appears to have overlapped the earlier completed NL delivery. Reuse avoids
introducing a second statement of the same fact.

Validation: the dry delivery runs a server-only #check of the existing declaration via
scompile.py, followed by the maintainer preflight; its outcome is recorded by the tool.

## Second reading by NR

I independently opened the node copy, the existing module
`lean/Sheaf/AlgebraicGeometry/GeometricReducednessFromGenericStalks.lean`, every
statement-dependency node and its recorded declaration, and Stacks varieties.tex,
`lemma-generic-points-geometrically-reduced` (04KS), part (3), together with
`lemma-geometrically-reduced-at-point` (035W). The source introduces only a field
and a scheme over it; neither source clause assumes finite type or Noetherianity.
The existing declaration says exactly what the node says.

Object/hypothesis/conclusion inventory and verdicts:

1. Base field k: `(k : Type u) [Field k]`. PASS: Mathlib Field extends CommRing
   and DivisionRing, including nontriviality; no characteristic assumption.
2. Scheme X and its specified k-structure: `(X : Scheme.{u})
   [X.Over (Spec (.of k))]`. PASS: Scheme.Over is OverClass, supplying the
   morphism `X ↘ Spec (.of k)` used consistently throughout the signature.
3. X is reduced: `[IsReduced X]`. PASS: Properties.lean defines sectionwise
   reducedness; `isReduced_of_isReduced_stalk` and
   `isReduced_stalk_of_isReduced` give exactly the node's equivalent local form.
4. Every irreducible component: `∀ (Z : Set X), Z ∈ irreducibleComponents X →`.
   PASS: the dependency's `irreducibleComponents` is `{s | Maximal IsIrreducible s}`;
   its members are closed. This does not restrict the number of components.
5. Every generic point of that component: `∀ (ξ : X), IsGenericPoint ξ Z →`.
   PASS: the dependency's `IsGenericPoint` is `closure {ξ} = Z`, which implies
   membership as well. No integrality of X is assumed.
6. Every field extension, following the component and point binders:
   `∀ (L : Type u) [Field L] [Algebra k L]`. PASS: Algebra is the recorded
   field-extension notion, furnishing exactly the field homomorphism k to L.
7. The local ring is `X.presheaf.stalk ξ`. PASS: TopCat.Presheaf.stalk is the
   colimit over opposite open neighbourhoods, the existing ring of germs.
   The module-stalk dependency explicitly includes these ring stalks; its
   PresheafOfModules.moduleStalkFunctor bundles module carriers over the same
   Mathlib stalk construction. A module carrier is not substituted for the ring.
8. The stalk k-action: `[Algebra k (X.presheaf.stalk ξ)]`, constrained by
   `algebraMap k (X.presheaf.stalk ξ) =
   (StructureSheaf.toStalk k ((X ↘ Spec (.of k)) ξ) ≫
   (X ↘ Spec (.of k)).stalkMap ξ).hom`. PASS: I read both morphism definitions.
   This is the canonical map from k through the base stalk to the local ring of
   X. RingHom.toAlgebra of this composite always supplies a satisfying instance,
   and Algebra.smul_def' determines its action. Universal quantification over
   the instance with this equality is equivalent to using that canonical action;
   it is neither an additional hypothesis nor a vacuous premise.
9. Reduced tensor ring at each such point and extension:
   `_root_.IsReduced ((X.presheaf.stalk ξ) ⊗[k] L)`. PASS: the tensor carrier is
   the dependency's TensorProduct and its algebra multiplication satisfies
   `Algebra.TensorProduct.tmul_mul_tmul`, precisely (a tensor l)(b tensor m)
   = ab tensor lm. No unknown data or private construction is involved.
10. Conclusion: `GeometricallyReduced (X ↘ Spec (.of k))`. PASS: I read its
    class and `geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms`.
    They assert reducedness of the pullback along Spec of every extension k to L.
    This pullback is the dependency's CategoryTheory.Limits.pullback, with the
    same two structure maps. The conclusion has every clause of the node.
11. No finiteness assumption: PASS by full signature inspection. There is no
    finite-type, quasi-compact, finite-component, or Noetherian binder.

Edge cases: for the empty scheme the premise has no component/point to test and
base changes remain empty, so the conclusion holds. The zero section ring of an
empty open is permitted; neither X nor its stalks acquire an extra nontriviality
binder. There is no numerical parameter, hence no n=0 restriction. Characteristic
zero and all positive characteristics, including imperfect fields, are included.
The tensor test includes L=k and extensions with arbitrary transcendence degree.
The single bound universe u is polymorphic, matches Scheme and Mathlib's geometric
property, and does not introduce an independent smaller test universe. All variables
and universes are explicitly bound; larger simultaneous size requirements are
handled by instantiating u larger, as for Mathlib schemes themselves.

Independent searches used different wording from the worker:

- msearch.py leanfinder: `Geometrically reduced scheme detected by residue fields
  at minimal points`; eight hits, consisting of reducedness/integrality criteria
  and algebraic geometric-reducedness definitions, not this scheme criterion.
- msearch.py loogle: `"GeometricallyReduced"`; twelve hits, including the class,
  base change and flat reduced-total-space results. None gives this criterion.
- msearch.py grep: `minimalPrime|genericPoint|localization` in
  AlgebraicGeometry/Geometrically/Reduced.lean; three matches in the proof of
  the flat finite-component theorem, a different statement.
- Direct rg of `generic.*[Rr]educ|[Rr]educ.*generic` in upstream WeilConjectures
  and project lean/Sheaf, followed by exact declaration/id search, locates the
  already landed module and no upstream copy of this criterion. Existing reuse
  is therefore appropriate; no duplicate module is delivered.

H5/H6/H8/H9: the reused module introduces no definitions and its sole theorem has
proof `sorry`. Its module and declaration docstrings name 04KS/035W and the exact
blueprint id. Its four proof steps match the node: identify generic localizations
on affine opens; detect zero using minimal primes and reducedness; detect zero
after tensoring using finitely many independent coefficients; cover the base change
by reduced affine charts. No file-local instance, private notation, hidden let, or
unbound variable occurs in the statement. The dependency module is already landed,
not a new module or node in this delivery; no dependency repair is needed.

Mismatches found: none. Changes: appended this independent second reading only;
kept the existing Lean record and mathematical statement unchanged. No new nodes,
statement correction, or citer-verdict review is applicable. Server compilation
and delivery preflight are performed by deliver2.py through scompile.py; there
are no new Lean files to compile separately.
