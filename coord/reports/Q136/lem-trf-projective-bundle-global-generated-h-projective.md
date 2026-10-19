## Worker report

The module `Sheaf.AlgebraicGeometry.GloballyGeneratedProjectiveBundle` states
`AlgebraicGeometry.isHProjective_projectiveBundle_of_finitely_generated_globalSections`.
It contains one theorem with proof `sorry`, and no definitions or proved statements.
The declaration docstring carries all three proof steps, including the identification of
relative-Proj finite free projective space with the base-change projective space.

Clause-by-clause correspondence:

- Scheme S: `(S : Scheme.{u})`, at an arbitrary explicitly bound universe u.
- O_S-module E: `(E : S.Modules)`.
- Quasi-coherence: `[E.IsQuasicoherent]`.
- Finite type: `[E.IsFiniteType]`; this node hypothesis is retained explicitly.
- Finitely many generating global sections: `hgen : ∃ σ :
  SheafOfModules.GeneratingSections E, σ.IsFiniteType`. Mathlib's structure has an index
  type `σ.I`, global sections `σ.s`, and an epi evaluation map `σ.π`; its IsFiniteType
  class asserts `Finite σ.I`. This is finite generation as a sheaf, not merely generation
  of the module of global sections.
- P_S(E) and its structural morphism: `(SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom`.
  This is exactly the canonical object used by `IsProjectiveBundle`: the affine section
  rings are symmetric algebras, their degree-n pieces are powers of the degree-one range,
  and their restriction maps are canonical. It accepts arbitrary quasi-coherent modules,
  without a local-freeness assumption. No algebra, grading, gluing data, or map is supplied
  as an additional hypothesis.
- Conclusion: `IsHProjective` of this morphism, the recorded finite-projective-space
  convention, not the distinct EGA projective-bundle predicate.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
- `WeilConjectures.AlgebraicGeometry.Coherent`: its module docstring identifies the
  quasi-coherent and finite-type parts of pqf-def-coherent as Mathlib's
  `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType`. The third notion,
  `RingedSpace.IsCoherent`, is not assumed by this node.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`:
  `SheafOfModules.GeneratingSections`, its `epi` field and `IsFiniteType` class.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`: `AlgebraicGeometry.IsProjectiveBundle`
  is read to identify the exact canonical projective bundle. This module publicly imports
  `Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra`, whose
  `AlgebraicGeometry.SymmetricAlgebraSheaf.gradedAlgebraData` is used in the signature.
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`:
  `Scheme.GradedAlgebraData.relProj` and `relProjHom`; the latter is glued from the
  local Proj structural maps, including the degree-zero structural ring map.
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra`:
  `exists_quasiCoherentSymmetricAlgebra`, its universal property and affine comparison
  justify the canonical symmetric-algebra realization used by the bundle dependency.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsHProjective`, whose field is a closed immersion into projective
  space with finite coordinate type and the equation factoring the given morphism.

The statement dependencies' modules are publicly available through the explicit imports.
The recorded proof dependencies are imported (Functoriality, BaseChange, Universal,
RelativeProjectiveSpace, symmetric polynomial Basis), or already imported publicly through
ProjectiveBundleMorphism and its canonical symmetric-algebra module. No import cycle was
introduced. Current published Basic, Coherent, and Projective sources were read with
`scompile.py --source` because the older source checkout lacks those files.

Edge cases checked against the node, source and interfaces:

- E=0 is allowed: its projective bundle is empty and embeds into P^0_S; the proof pads
  the generators by the zero section when needed.
- An empty generating index type is allowed by `σ.IsFiniteType`; it forces E=0.
  Finite nonempty index types can be enumerated by Fin (r+1), without changing the notion.
- S empty is allowed: no nonemptiness, quasi-compactness or separatedness is assumed.
- One global generator gives the closed immersion into P^0_S.
- No field, characteristic restriction, Noetherian hypothesis, finite presentation or
  local freeness is assumed. The source paragraph needs none of the ample-base
  hypothesis used elsewhere in the full Tag 087S lemma.

Searches for an existing statement (2026-10-17 UTC):

- msearch.py leanfinder, query "H-projective projective bundle globally generated finite
  type quasi coherent module": eight hits, including LocalGeneratorsData.IsFiniteType,
  module projectivity results and Proj local finite type; no exact statement.
- msearch.py loogle, query "AlgebraicGeometry.IsHProjective,
  SheafOfModules.GeneratingSections": zero hits (IsHProjective is unknown to Mathlib).
- msearch.py leansearch, query "relative Proj symmetric algebra of finitely globally
  generated module is projective": eight hits (Proj and module-projectivity results),
  no projective-bundle H-projectivity theorem.
- msearch.py grep in Mathlib/AlgebraicGeometry, query
  `IsHProjective|projectiveBundle.*[Gg]lobal|[Gg]lobal.*projectiveBundle`: zero hits.
- rg of WeilConjectures for IsHProjective, ProjectiveBundle, and generating sections:
  no exact theorem; the older checkout lacks the newly published projectivity API.
- rg of WeilConjectures for the item id: zero hits.
- rg of lean/Sheaf for IsProjectiveBundle, relative Proj maps, IsHProjective and globally
  generated bundles: the canonical bundle definition and general projectivity APIs exist,
  but this theorem does not. `dag/lean_names_upstream.json` has IsHProjective and its
  properness instance, not this theorem. The new full declaration name has no match.

Source inspected: literature/stacks-project/morphisms.tex, lines 10848-10887,
Tag 087S, especially its globally generated paragraph. No node fault or statement
correction is needed; no STATEMENT-DISPUTED issue remains. No repair note exists for this item.

Validation: scompile.py Q136 lem-trf-projective-bundle-global-generated-h-projective
compiled the file in the sandbox and at its library module path, exit 0, no diagnostics
(4.1 seconds sandbox, 6.6 seconds module). All universes and variables are explicit.

## Second reading by Q136

Author self-check, under the dispatcher's direct-delivery protocol; the maintainer performs
its independent review. Reopened the node statement and completed Lean signature together.
The scheme and module binders, both module properties, the existence of a finite generating
family, the actual canonical Proj structural map, and its H-projectivity conclusion match
one for one. The finite index type may be empty, exactly as allowed by finite generation;
this preserves E=0, rather than requiring a nonempty chosen family. No arbitrary map,
noncanonical symmetric algebra, or extra geometric property has entered the statement.
The `IsProjectiveBundle` predicate is not an extra hypothesis: its defining construction is
what specifies this particular bundle map. Its canonical construction is used unchanged.
Checked the theorem is only `sorry`, with no helpers, private definitions or local notation.
No mismatch was found and no statement change was made.
