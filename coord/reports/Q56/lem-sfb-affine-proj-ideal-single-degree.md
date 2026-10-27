## Worker report

The item is stated by `AlgebraicGeometry.exists_affineProjIdeal_single_degree` in
`lean/Sheaf/AlgebraicGeometry/AffineProjIdealSingleDegree.lean`. Its only proof is
`sorry`, with the six-step DAG proof in its docstring. The statement is unchanged.
One new definition node supplies the general homogeneous quotient grading and its
canonical Proj morphism. No dependency record is replaced.

Hypotheses and clauses, read against the node and divisors.tex Tag 0802:

- The commutative base ring is `(R : Type v) [CommRing R]`; the commutative unital
  algebra is `(A : Type u) [CommRing A] [Algebra R A]`. The universes u and v are
  independent. `𝒜 : ℕ → Submodule R A` and `[GradedAlgebra 𝒜]` give the internal
  direct sum, unit in degree zero, and multiplication of degrees. Since the
  degree-zero submodule contains 1, it contains the scalar image. No isomorphism
  R ≅ A₀ is imposed. These are Mathlib's existing algebra and grading notions.
- The prescribed homogeneous ideal is `I : HomogeneousIdeal 𝒜`. Mathlib's
  homogeneity condition says that every homogeneous projection preserves I;
  this is exactly the direct-sum condition on I. Its pieces are I ∩ Aₙ, and
  the ideal law gives Aₘ Iₙ ⊆ Iₘ₊ₙ.
- The scheme P is Mathlib's `Proj 𝒜`. `[CompactSpace (Proj 𝒜)]` is precisely
  quasi-compactness of its underlying space, without a separation assumption.
- The closed embedding is `homogeneousQuotientProjι 𝒜 I`, defined using the
  actual quotient ring, its explicit image grading, and `Proj.map` of the
  actual quotient homomorphism. It is a closed immersion by the existing
  `Proj.isClosedImmersion_map` applied with `Ideal.Quotient.mk_surjective`.
  Thus its quasi-compactness and quasi-separatedness are automatic properties
  of this specified closed immersion; no independent binders for them are
  appropriate. `[LocallyOfFinitePresentation (homogeneousQuotientProjι 𝒜 I)]`
  supplies the remaining, substantive part of the node's finite-presentation
  hypothesis. Consequently the node's full finite-presentation hypothesis is
  retained, without redundant extra assumptions.
- `∃ (d : ℕ) (_hd : 0 < d)` is the positive common degree. `r : ℕ` and
  `g : Fin r → 𝒜 d` are the finite list, including r=0. The conjunct
  `∀ j, (g j : A) ∈ I` puts every element in I_d.
- The expression `Submodule.span R (Set.range (fun j ↦ (g j : A)))` is exactly
  F=Rg₁+...+Rgᵣ, as a submodule of A contained in I_d. No extra choice of F is
  made. `H.toIdeal = Ideal.span (F : Set A)` says that the homogeneous ideal
  H has underlying ideal FA. Homogeneity is part of the bundled H, rather than
  an unexplained instance assumed on an arbitrary ideal.
- `∃ e : Proj (homogeneousQuotientPiece 𝒜 H) ≅
  Proj (homogeneousQuotientPiece 𝒜 I)` together with
  `e.hom ≫ homogeneousQuotientProjι 𝒜 I = homogeneousQuotientProjι 𝒜 H`
  identifies these schemes over P. Because both maps are closed immersions,
  this is exactly equality as closed subschemes, including their structure
  sheaves. It does not replace scheme equality by equality of closed sets.
- There is no `FiniteType`, `Module.Finite`, `FG`, Noetherian, degree-one
  generation, reducedness, or nonemptiness hypothesis anywhere in the statement.

Dependency declarations read and used:

- `Mathlib.Algebra.Algebra.Hom`: `AlgHom`; and
  `Mathlib.RingTheory.Ideal.Quotient.Operations`: `Ideal.Quotient.algebra`,
  `Ideal.Quotient.mkₐ`. The module uses the standard Algebra class and quotient
  algebra. This is the dependency def-weil-pbc-algebra-hom-quotient.
- `Mathlib.RingTheory.GradedAlgebra.Basic`: `GradedAlgebra`, `GradedRing`,
  `DirectSum.Decomposition`. The existing Mathlib leaf
  def-sfb-nonnegative-graded-algebra is cited by the new node. The original
  def-weil-pbc-graded-sheaf-structures is a sheaf-level generality; its recorded
  `WeilConjectures.AlgebraicGeometry.GradedSheafStructures` declarations
  `GradedSheafAlgebra`, `GradedSheafModule`, and
  `GradedSheafModule.IsLocallyGeneratedInDegreeZero` were read and that module
  is publicly imported, but no sheaf structure is substituted for the affine
  algebra in this statement. Mathlib supplies the exact affine notion.
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme` and `.Basic`:
  `AlgebraicGeometry.Proj`, `projIsoSpec`, `Proj.basicOpen`; these implement
  def-pc-proj. `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor`:
  `Proj.map`, `Proj.map_preimage_basicOpen`, `Proj.awayι_comp_map`.
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality`:
  `Scheme.GradedAlgebraData.relProjMap`,
  `Scheme.GradedAlgebraData.isClosedImmersion_relProjMap`, and the intervening
  restriction and isomorphism declarations were read. The affine specialization
  used here is the already existing `Proj.map`, with closed immersion supplied
  by `WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor`:
  `Proj.isClosedImmersion_map`. There is no new copy of relative Proj.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`, exactly the affine-local
  finite-presentation property recorded on def-sbc-locally-finite-presentation.
- Proof imports with recorded declarations: `Proj.standardOpenProperties` in
  `WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties`;
  `Scheme.Hom.ker` in `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`;
  `Scheme.Modules.quasicoherent_finite_type_affine` in
  `WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`;
  `Localization.Away` and `HomogeneousLocalization.Away` in their Mathlib
  modules; `IsClosedImmersion` in its Mathlib module. The proof dependency
  lem-trf-closed-immersion-finite-presentation-ideal has no recorded declaration,
  so no module is imported for it. It is not needed to type the statement.

Edge cases checked before writing: P empty permits d=1 and r=0. The zero
ring, I=A, and the zero quotient remain permitted; the quotient pieces are
actual images even then. I=0 permits the empty generating family. Nilpotent
homogeneous elements yield empty charts without requiring them to be nonzero.
Gradings concentrated in even degrees are permitted (no degree-one assumption).
An arbitrary scalar map, e.g. a proper inclusion R→A₀, is permitted. Neither
unsaturated ideals nor nilpotents are lost: the conclusion uses scheme
isomorphisms over P. Independent u,v cover scalar rings larger than A.

Searches actually run using msearch.py:

1. LeanFinder: “A homogeneous ideal with finitely presented closed subscheme in
   quasi compact Proj is generated as an ideal sheaf by finitely many homogeneous
   elements of one positive degree”. Eight hits, including homogeneous prime
   ideals, standard open covers, and a finite-type Proj theorem; no match.
2. Loogle: `HomogeneousIdeal, Proj.map`. No hits; service reported unknown
   identifier `Proj.map`. This is not evidence of absence by itself.
3. grep: `quotient|Quotient`, subdirectory `RingTheory/GradedAlgebra`. Five hits
   about the unrelated quotient defining homogeneous localization; no quotient
   grading.
4. LeanSearch: “The quotient of a graded commutative ring by a homogeneous ideal
   has the image grading and an induced closed immersion on Proj”. Eight hits
   on Spec of a quotient, homogeneous ideals, Proj, and standard opens; no
   general quotient grading construction.
5. LeanFinder: “The quotient of any nonnegative graded commutative algebra by a
   homogeneous ideal has the grading given by images of its homogeneous
   submodules”. Eight hits on GradedAlgebra, homogeneous ideals, and polynomial
   gradings; no general quotient grading.

Direct rg in Mathlib, WeilConjectures, Sheaf, and the DAG found only the
field/polynomial quotient grading of def-sfb-coordinate-quotient-grading and
projectiveClosedSubschemeQuotientGrade (polynomial rings). Their full signatures
were read. Neither applies to arbitrary A. rg for Proj/ideal/single-degree
combinations and grep for this item's id in WeilConjectures found no existing
statement. `tools/blueprint_refs.py search 'homogeneous quotient'` found zero
blueprint nodes. Its ancestor command returns None for this inherited chain.

Validation: both delivered modules compiled separately, in dependency order,
through the prescribed scompile.py wrapper, with no errors or non-sorry warnings.
No statement dispute or correction is needed.

## New nodes

`def-sfb-homogeneous-quotient-proj` defines the images of Aₙ in A/I, their
uniquely determined decomposition, the actual graded quotient homomorphism,
and its canonical Proj map. Source: algebra.tex Tag 00JL and constructions.tex
Tag 01MY. The searches above distinguish it from the existing polynomial-over-
field node. The module is
`lean/Sheaf/AlgebraicGeometry/HomogeneousQuotientProj.lean`. Its only postponed
proof is `existsUnique_homogeneousQuotientGrading`; it states unique existence
of the entire grading on the prescribed image submodules. The selected grading
is determined by this uniqueness: the inverse of the canonical sum map, not a
choice from an unconstrained existence statement. Definitions of pieces, quotient
map, and Proj morphism have real data. The theorem's proof docstring explains
projection descent and uniqueness, including the zero quotient. Its node carries
that uniqueness assertion as part of the definition. This is the missing general
notion; the original item gains its id in stmt_deps.

## Second reading by Q56

I reopened the node and both Lean files for a separate sequential reading. No
second agent was used, as required by the dispatcher brief; this section records
that second pass rather than claiming an independent agent review. The
maintainer's independent review remains the next review of the delivery.

I checked the commutative ring/algebra binders, arbitrary scalar map into degree
zero, ℕ-grading, prescribed homogeneous I, compactness of Proj, and full
finite-presentation condition (the two global conditions follow from closed
immersion). I checked each existential and conjunct: d>0, r≥0, homogeneous
generators in I, the precise R-span, its generated ideal H, and the commuting
isomorphism of quotient Proj schemes over the ambient Proj. The last condition
preserves nonreduced structure and is not just a support condition. No stronger
hypothesis was found. The new node's explicit quotient images, unique grading,
actual quotient homomorphism and canonical Proj morphism match its module. The
field-specific coordinate quotient definition was checked again and is
inapplicable to this general statement. No changes were needed in this pass.
