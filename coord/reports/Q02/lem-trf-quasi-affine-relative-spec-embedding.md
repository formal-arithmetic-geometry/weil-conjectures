## Worker report

The module Sheaf.AlgebraicGeometry.QuasiAffineRelativeSpecEmbedding states
`AlgebraicGeometry.isQuasiAffineHom_iff_exists_relativeSpec_embedding`, with proof `sorry`.
It introduces no definitions and changes only the item's `lean` field. The source is Stacks
Project, Morphisms, Tag 01SM, lemma-characterize-quasi-affine, equivalence (1) and (3), read
in literature/stacks-project/morphisms.tex. No statement correction or disputed statement.

Clause-by-clause correspondence:

- Arbitrary schemes X and S, and a morphism f: `{X S : Scheme.{u}} (f : X ⟶ S)`.
  There is no affineness, finiteness, separatedness, or nonemptiness assumption on S or X.
- The definition of quasi-affineness in the node: `IsQuasiAffineHom f`. Its field
  `isQuasiAffine_preimage` quantifies over every affine open of S. Mathlib's absolute
  `Scheme.IsQuasiAffine` includes quasi-compactness and is equivalent to being a
  quasi-compact open subscheme of an affine scheme: the canonical map to the spectrum
  of global sections is an open immersion, and `IsQuasiAffine.of_isImmersion` gives
  the converse for any such embedding.
- The equivalence, in both directions: `↔`.
- Existence of a sheaf of commutative O_S-algebras: `∃ A : S.CommAlgebraSheaf`.
  This is the existing abbreviation `Under S.sheaf`, so its morphisms, including
  the algebra isomorphism below, commute with the O_S structure maps.
- Quasi-coherence of the underlying O_S-module: `A.toModule.IsQuasicoherent`.
  No finite-type or finite-presentation condition is imposed on A.
- Y = Spec_S(A), with its projection π: `∃ (Y : Scheme.{u}) (π : Y ⟶ S),
  IsAffineHom π ∧ Nonempty (A ≅ Under.mk (⟨π.c⟩ : S.sheaf ⟶
  (TopCat.Sheaf.pushforward CommRingCat.{u} π.base).obj Y.sheaf))`.
  This is precisely the relative-spectrum realization supplied by parts (2) and (3)
  of `affine_morphism_relative_spec`: an affine S-scheme with algebra A is unique
  up to S-isomorphism. This is not a replacement by an unspecified map or by an
  arbitrary scheme. The algebra isomorphism is in the category of O_S-algebras,
  retaining the structure map. For an affine open U, affineness identifies Y_U with
  Spec Γ(Y_U,O); the component of the algebra isomorphism then gives exactly the
  chart to Spec A(U) in the dependency statement. Conversely its relative spectrum
  has this affine structure and algebra isomorphism. Since the conclusion is an
  existential embedding, replacing a chosen relative spectrum by its isomorphic
  affine realization over S preserves the conclusion in both directions.
  `Nonempty` expresses existence of an isomorphism within a proposition; no object
  is defined by choice from a postponed existence theorem.
- Existence of the open immersion: `∃ i : X ⟶ Y, IsOpenImmersion i`.
- Quasi-compactness of that immersion as a morphism: `QuasiCompact i`.
  This does not require Y or S to be quasi-compact.
- The triangle commutes: `i ≫ π = f`, namely π composed with i equals f.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine:
  `AlgebraicGeometry.IsQuasiAffineHom` and its affine-preimage field.
- Sheaf.AlgebraicGeometry.CoherentFiniteType (the current pqf-def-coherent module)
  is imported; the quasi-coherent clause itself uses Mathlib's
  `SheafOfModules.IsQuasicoherent`, without its unrelated finite-type conjunct.
- Mathlib.AlgebraicGeometry.OpenImmersion: `AlgebraicGeometry.IsOpenImmersion`.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType and its QuasiCompact dependency:
  `AlgebraicGeometry.QuasiCompact`. LocallyOfFiniteType is not assumed.
- WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec:
  `AlgebraicGeometry.affine_morphism_relative_spec`, whose anti-equivalence and
  affine-chart clauses justify the relative-spectrum witness above.
- Its public dependency WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf:
  `Scheme.CommAlgebraSheaf`, `Scheme.CommAlgebraSheaf.toModule`.

The latter two current upstream modules were read through `scompile.py --source`,
since their published upstream sources are newer than the local slopmaster2 tree.
The proof-dependency modules are imported without `public`; the docstring records
all six proof steps, including the qcqs pushforward, algebra local maps, gluing,
canonical-map identification, local open immersions, and local quasi-compactness.

Edge cases checked mathematically before writing: empty X (the empty affine
S-scheme realizes the zero algebra), empty S (then X is empty), identity of an
arbitrary S (use A = O_S and Y = S), affine morphisms (use i = identity), punctured
affine plane (quasi-affine need not be affine), and non-quasi-compact S (only the
immersion is required quasi-compact as a morphism). The source has no noetherian
or finite-type assumption; none was introduced. All universes and binders are
explicit, with `set_option autoImplicit false`.

Searches made using msearch.py Q02 lem-trf-quasi-affine-relative-spec-embedding:

- leanfinder: "A morphism is quasi affine if and only if it is a quasi compact open
  immersion into a relative spectrum of a quasi coherent algebra". Eight results:
  absolute Scheme.IsQuasiAffine, its canonical immersion, permanence under affine
  morphisms, and quasi-compactness of affine morphisms; no relative-spectrum iff.
- loogle: `"IsQuasiAffine"`. Twelve results on absolute quasi-affine schemes and
  affine-transition limits; no matching relative characterization.
- grep: `quasi.affine|RelativeSpec|relative.*Spec`, subdirectory AlgebraicGeometry.
  Nine results, in absolute QuasiAffine, AffineTransitionLimit, normalization,
  small affine Zariski site, and smooth relative dimension; no match.
- leansearch: "A scheme morphism is quasi affine if and only if it admits a quasi
  compact open immersion into a relative spectrum". Eight results, on absolute
  quasi-affine schemes and affineness; no match.
- rg over WeilConjectures and lean/Sheaf for `relative.?spec|quasi.?affine`, and for
  `isQuasiAffineHom_iff|IsQuasiAffineHom.*↔|exists.*[Rr]elative[Ss]pec|relativeSpec_embedding`.
  Found the existing relative definition, base-change and descent statements,
  and the affine/algebra correspondence. None states this equivalence; the chosen
  declaration name is unused. The exact item-id search over WeilConjectures has
  no hit. Mathlib QuasiAffine.lean and the upstream relative definition were read.

Validation: the first version compiled cleanly with scompile.py (sandbox and library
checks, 2.0 s and 2.3 s). The final explicit proof imports are validated again by
the required delivery dry run.

## Second reading by Q02

This dispatcher-started worker has no second worker and was explicitly instructed
not to start agents. The independent review is the maintainer's. I reread the node,
source, dependency signatures and delivered signature for a consistency check:
the schemes and morphism are arbitrary; the left side quantifies over all affine
opens through the recorded class; A is a commutative algebra sheaf with a
quasi-coherent underlying module; the affine realization with its O_S-algebra
isomorphism is the relative spectrum by the recorded anti-equivalence; i is both
open and quasi-compact; and i followed by π is f. No mathematical mismatch was
found. No definition was copied, no hypothesis was added, and no clause was
removed. Added explicit imports for the stated Mathlib proof dependencies after
the initial successful compile. This is a self-check, not a claim of an independent
second reading.
