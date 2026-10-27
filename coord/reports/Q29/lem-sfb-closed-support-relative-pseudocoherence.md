## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedSupportRelativePseudoCoherence` states
`AlgebraicGeometry.Scheme.isMPseudoCoherentRelativeTo_iff_closedImmersion_pushforward`.
Its only proof is `sorry`. No definitions, helper axioms, or new nodes are introduced.
The node is unchanged outside `lean`.

Source read: `literature/stacks-project/more-morphisms.tex`,
`lemma-closed-morphism-relative-pseudo-coherence` (Tag 09VG), lines 16949 onward.
The node already restricts that source's broader assertion to closed immersions.
The common affine-space embedding argument in the node's four proof steps works
for this restricted statement and arbitrary module derived objects. The theorem's
docstring reproduces all four steps and their dependencies.

Clause-by-clause correspondence:

- Schemes X, Y, S: `{X Y S : Scheme.{u}}`, with an arbitrary explicit universe u.
- Schemes locally of finite type over S: `(fX : X ⟶ S) (fY : Y ⟶ S)` and the
  two instances `[LocallyOfFiniteType fX] [LocallyOfFiniteType fY]`.
- Closed immersion i: `(i : X ⟶ Y) [IsClosedImmersion i]`.
- The immersion is over S: `(_hi : i ≫ fY = fX)`. This is the required triangle,
  not an additional restriction on the closed immersion over the supplied base.
- Every integer m: `(m : ℤ)`, including zero and negative integers.
- Every E in D(O_X): `(E : schemeDerivedCategory X)`. There is no boundedness,
  quasi-coherence, perfectness, or cohomological vanishing hypothesis.
- Relative m-pseudo-coherence on X: `IsMPseudoCoherentRelativeTo fX m E`.
- If and only if: the connective `↔`, preserving both implications.
- Relative m-pseudo-coherence of Ri_*E on Y:
  `IsMPseudoCoherentRelativeTo fY m ((schemeDerivedDirectImage i).obj E)`.
- Derived categories for schemes and the affine/open schemes quantified over by
  the relative definition use precisely its recorded family
  `[∀ T : Scheme.{u}, HasDerivedCategory.{w}
    (SheafOfModules.{u} (moduleRings T.toRingedSpace))]`.
  The explicit arbitrary w is the shared localization-universe convention of
  the dependency definition; it adds no geometric finiteness condition.

Dependency declarations read in full and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme morphisms.
- The convention node `def-pc-morphism-conventions` introduces no declaration;
  `AlgebraicGeometry.LocallyOfFiniteType` is the class in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, available from the imports.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory` (all module derived objects).
- `Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex`:
  `AlgebraicGeometry.Scheme.IsMPseudoCoherentRelativeTo`; this is the actual
  recorded definition, using affine covers, finite affine-space embeddings,
  derived restriction and absolute local strictly perfect approximations.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `AlgebraicGeometry.schemeDerivedDirectImage`, the K-injective-derived functor.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (closed embedding with surjective stalks).

The relative-definition import publicly supplies the derived-category and
scheme-direct-image dependency modules and the absolute predicate
`Scheme.IsMPseudoCoherent` from `Sheaf.AlgebraicGeometry.MPseudoCoherentComplex`.
The proof imports additionally supply `Scheme.isBasis_affineOpens`
(`Mathlib.AlgebraicGeometry.AffineScheme`), `IsClosedImmersion.comp`
(the closed-immersion module), `schemeDerivedDirectImage_openRestriction`
(`WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenRestriction`) and
`derivedDirectImageComposition`
(`WeilConjectures.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded`).
Their recorded signatures and docstrings were read. The proof dependency
`lem-sfb-relative-pseudocoherence-all-affine-charts` has no recorded Lean
statement in the base, so there is no module to import for it yet; it is named
in the proof docstring for stage 3. It is not needed to type this statement.

Edge cases checked before writing: the identity closed immersion gives the
expected invariance; the empty X and empty base are permitted (no nonempty
binder); the zero object and arbitrary unbounded E are permitted; m = 0 and
negative m use the same degree on both sides. Nothing bounds dimensions or
forces finite covers. Arbitrary base schemes are allowed, including
non-Noetherian bases. Neither reducedness nor a nilpotent-thickening condition
is imposed. The source's broader topological-embedding assertion is not part
of the already-corrected node being formalized. No statement fault or disputed
claim was found in the assigned closed-immersion statement.

Searches made with the prescribed `msearch.py Q29
lem-sfb-closed-support-relative-pseudocoherence` wrapper:

- `leanfinder`: "A closed immersion over a scheme preserves and reflects
  relative m pseudo coherence of arbitrary complexes under derived direct image".
  Eight hits: closed-immersion morphism properties and underived module
  pushforward, none the desired theorem.
- `loogle`: `"PseudoCoherent"`. Zero hits.
- `grep`: `relative.*pseudo|pseudo.*coher`. Three unrelated hits in
  pseudometric spaces and bicategory coherence.
- `leansearch`: "Relative m pseudo coherence is invariant under derived direct
  image along a closed immersion over the base". Eight hits concerning
  closed-immersion and other morphism properties, none relative pseudo-coherence.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for closed/pseudo-coherent
  combinations and `IsMPseudoCoherentRelativeTo`, plus the exact blueprint id
  and proposed declaration name in both trees and `dag/lean_names_upstream.json`.
  Found the recorded relative definition and unrelated absolute/underived
  results, no existing statement. A ring-level predicate with the same short
  name has a different namespace and objects and is not this scheme theorem.

## Second reading by Q29

I reread the node against the final module, its two actual relative predicates,
and the actual derived-direct-image definition. The two finite-type hypotheses,
closed-immersion hypothesis, and triangle equation match exactly. The integer
and object quantifiers are unrestricted. The right-hand side pushes E along i,
then tests relative to fY; the left-hand side tests E relative to fX. The same
integer is used on both sides and the result is an equivalence. There is no
quasi-coherent subcategory in the signature and no replacement of the canonical
derived direct image by a supplied map. No mismatch requiring a change was found.
This is the worker's own rereading; the dispatcher brief prohibits starting
another agent and assigns the independent delivery review to the maintainer.

Validation: `scompile.py Q29 lem-sfb-closed-support-relative-pseudocoherence`
compiled both the sandbox and library module cleanly, in 30.4 s and 3.5 s.
The prescribed `deliver2.py ... --no-push` then reported OK: its server preflight
and per-file compilation passed. Only the three intended delivery files were staged.
