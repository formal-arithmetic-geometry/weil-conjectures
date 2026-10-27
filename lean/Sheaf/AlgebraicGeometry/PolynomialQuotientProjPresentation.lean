/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q88
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
public import Sheaf.AlgebraicGeometry.RelativeProjAffineRestriction
public import Sheaf.AlgebraicGeometry.RelativeProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
public import Sheaf.AlgebraicGeometry.FreeProjectiveBundleBaseChangeSpace
import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.QuasiCoherentModuleColimitEvaluation
import WeilConjectures.AlgebraicGeometry.RelativeProj.Universal
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Polynomial quotient relative Proj presentations

Source: Stacks Project, Constructions, Tags 07ZK, 01M7, 01MA and 01NQ;
Morphisms, Tags 01WC, 01TX and 01TP
(blueprint: lem-sfb-polynomial-quotient-proj-presentation).

A quotient sheaf is presented by its quasi-coherent graded algebra `B` and the
surjective graded quotient map `q` on affine sections. Its ideal is exactly `ker q`;
this is the affine-basis encoding of the given homogeneous ideal, not an additional
hypothesis about a quotient. The local finite-generation hypothesis is point-local
and allows generators of degree zero and the empty generating family.

The actual polynomial quotient rings, their image submodules, and their coordinates
are constructed below. The conclusion identifies these with the sheaf sections and
relative Proj by the quotient map itself. No equality B_0 = O_U is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.PolynomialQuotientProj

variable {U : Scheme.{u}} {n : ℕ} (B : RelativeProjAlgebra U)
  (q : (RelativeProjectiveSpace.algebra U n).affineData ⟶ B.affineData)

/-- The polynomial quotient homomorphism, using the prescribed coefficient and coordinate
identification of the free symmetric algebra.
Source: Stacks, Constructions, 07ZK
(blueprint: lem-sfb-polynomial-quotient-proj-presentation). -/
def polynomialMap (V : U.affineOpens) :
    MvPolynomial (Fin (n + 1)) Γ(U, V.1) →+* B.sections V :=
  (q.app V).toRingHom.comp (RelativeProjectiveSpace.affinePolynomialEquiv U n V).toRingHom

/-- The affine ideal J_V, in polynomial coordinates, is the kernel of the quotient map.
Source: Stacks, Constructions, 07ZK
(blueprint: lem-sfb-polynomial-quotient-proj-presentation). -/
def ideal (V : U.affineOpens) : Ideal (MvPolynomial (Fin (n + 1)) Γ(U, V.1)) :=
  RingHom.ker (polynomialMap B q V)

/-- The literal affine polynomial quotient R[x_0,...,x_n]/J_V.
Source: Stacks, Constructions, 07ZK
(blueprint: lem-sfb-polynomial-quotient-proj-presentation). -/
abbrev quotientRing (V : U.affineOpens) :=
  MvPolynomial (Fin (n + 1)) Γ(U, V.1) ⧸ ideal B q V

/-- The degree-d submodule of the literal quotient is the image of degree-d polynomials.
Source: Stacks, Algebra, graded quotients; Constructions, 01M7
(blueprint: lem-sfb-polynomial-quotient-proj-presentation). -/
def quotientPiece (V : U.affineOpens) (d : ℕ) :
    Submodule Γ(U, V.1) (quotientRing B q V) :=
  (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) Γ(U, V.1) d).map
    (Ideal.Quotient.mkₐ Γ(U, V.1) (ideal B q V)).toLinearMap

/-- The image x-bar_i of a homogeneous coordinate in the literal quotient.
Source: Stacks, Constructions, 01MA
(blueprint: lem-sfb-polynomial-quotient-proj-presentation). -/
def coordinate (V : U.affineOpens) (i : Fin (n + 1)) : quotientRing B q V :=
  Ideal.Quotient.mk (ideal B q V) (MvPolynomial.X i)

/-- The canonical first-isomorphism-theorem comparison with the quotient sheaf's sections.
It maps the class of p to q(p), rather than choosing an arbitrary ring isomorphism.
Source: Stacks, Constructions, 07ZK
(blueprint: lem-sfb-polynomial-quotient-proj-presentation). -/
def quotientEquiv (hq : ∀ V : U.affineOpens, Function.Surjective (q.app V))
    (V : U.affineOpens) : quotientRing B q V ≃+* B.sections V :=
  RingHom.quotientKerEquivOfSurjective
    ((hq V).comp (RelativeProjectiveSpace.affinePolynomialEquiv U n V).surjective)

/-- The complete affine restriction assertion for the polynomial quotient. The grading
is on the actual image submodules. Its map to sections is fixed by quotientEquiv.
The Proj identification is fixed by that map and the existing relative-Proj chart inclusion.
The standard chart isomorphism is expressed as invertibility of basicOpenToSpec, the
canonical localization map. Zero and nilpotent coordinates therefore give empty charts.
Source: Stacks, Constructions, 01M7, 01MA and 01NQ
(blueprint: lem-sfb-polynomial-quotient-proj-presentation). -/
structure AffinePresentation
    (hq : ∀ V : U.affineOpens, Function.Surjective (q.app V)) (V : U.affineOpens) where
  [grading : GradedAlgebra (quotientPiece B q V)]
  sections (d : ℕ) :
    (B.piece d).val.obj (op V.1) ≃ₗ[Γ(U, V.1)] quotientPiece B q V d
  sections_eq (d : ℕ) (s : (B.piece d).val.obj (op V.1)) :
    quotientEquiv B q hq V (sections d s).val =
      (Sigma.ι B.piece d ≫ B.decomposition.hom).val.app (op V.1) s
  gradedMap : quotientPiece B q V →+*ᵍ B.affineData.grading V
  gradedMap_eq : gradedMap.toRingHom = (quotientEquiv B q hq V).toRingHom
  irrelevant : HomogeneousIdeal.irrelevant (B.affineData.grading V) ≤
    (HomogeneousIdeal.irrelevant (quotientPiece B q V)).map gradedMap
  projIso : (B.affineData.relProjHom ⁻¹ᵁ V.1).toScheme ≅ Proj (quotientPiece B q V)
  projIso_eq : Proj.map gradedMap irrelevant ≫ projIso.inv ≫
    (B.affineData.relProjHom ⁻¹ᵁ V.1).ι = B.affineData.relProjι V
  cover : (⨆ i : Fin (n + 1),
    Proj.basicOpen (quotientPiece B q V) (coordinate B q V i)) = ⊤
  affine (i : Fin (n + 1)) :
    IsAffineOpen (Proj.basicOpen (quotientPiece B q V) (coordinate B q V i))
  chart (i : Fin (n + 1)) :
    IsIso (Proj.basicOpenToSpec (quotientPiece B q V) (coordinate B q V i))
  nilpotent_chart (i : Fin (n + 1)) (hi : IsNilpotent (coordinate B q V i)) :
    Proj.basicOpen (quotientPiece B q V) (coordinate B q V i) = ⊥

/-- The assertions of the polynomial-quotient presentation, with the quotient-induced
closed immersion and its normalization under the canonical projective-space comparison.
The comparison is the unique isomorphism supplied by
`existsUnique_freeProjectiveBundleBaseChangeSpace`, with its prescribed affine charts.
Source: Stacks, Constructions, 07ZK, 01M7; Morphisms, 01WC, 01TX, 01TP
(blueprint: lem-sfb-polynomial-quotient-proj-presentation). -/
structure Presentation
    (hq : ∀ V : U.affineOpens, Function.Surjective (q.app V)) where
  comparison : RelativeProjectiveSpace.scheme U n ≅
    ProjectiveSpace (ULift.{u} (Fin (n + 1))) U
  comparison_eq : comparison =
    (RelativeProjectiveSpace.existsUnique_freeProjectiveBundleBaseChangeSpace U n).exists.choose
  comparison_over : comparison.hom ≫ ProjectiveSpace (ULift.{u} (Fin (n + 1))) U ↘ U =
    RelativeProjectiveSpace.π U n
  comparison_chart (V : U.affineOpens) :
    RelativeProjectiveSpace.IsIntegralProjComparison U n V
      (RelativeProjectiveSpace.affineToIntegral U n comparison V)
  closedImmersion : IsClosedImmersion
    (Scheme.GradedAlgebraData.relProjMap q
      (Scheme.GradedAlgebraData.irrelevantLE_of_surjective q hq) ≫ comparison.hom)
  over : Scheme.GradedAlgebraData.relProjMap q
      (Scheme.GradedAlgebraData.irrelevantLE_of_surjective q hq) ≫ comparison.hom ≫
      ProjectiveSpace (ULift.{u} (Fin (n + 1))) U ↘ U = B.affineData.relProjHom
  projective : IsHProjective B.affineData.relProjHom
  proper : IsProper B.affineData.relProjHom
  locallyOfFinitePresentation : LocallyOfFinitePresentation B.affineData.relProjHom
  quasiCompact : QuasiCompact B.affineData.relProjHom
  quasiSeparated : QuasiSeparated B.affineData.relProjHom
  affine (V : U.affineOpens) : AffinePresentation B q hq V

/-- A polynomial quotient by a quasi-coherent homogeneous ideal locally generated by
finitely many homogeneous sections gives the specified closed immersion into projective
space, a projective proper finitely presented structure map, and the canonical affine
quotient section and standard-chart identifications. The quotient is encoded by B and
its surjective graded map q; the given ideal is its kernel. The finite-generation
condition is imposed locally at every point of U, without requiring U quasi-compact.

Source: Stacks Project, Constructions, Tags 07ZK, 01M7, 01MA and 01NQ;
Morphisms, Tags 01WC, 01TX and 01TP
(blueprint: lem-sfb-polynomial-quotient-proj-presentation).

Proof:
1. Identify the polynomial sheaf with Sym(O_U^{n+1}) using
lem-weil-pbc-quasi-coherent-symmetric-algebra and
lem-weil-pbc-symmetric-algebra-free-module-polynomial. The symmetric grading is total
degree by lem-weil-pbc-symmetric-algebra-graded; these identifications commute with
restriction since they fix coefficients and coordinates.
2. The homogeneous ideal is the kernel of q. Its quotient and homogeneous images are
quasi-coherent by lem-weil-pbc-quasi-coherent-module-cokernel-image. Affine sections are
exact and commute with the degree direct sums by
lem-weil-pbc-quasi-coherent-module-colimit-evaluation. Thus the first-isomorphism
comparison identifies the actual polynomial quotient with B.sections V, and its image
submodules with the sections of B.piece d. In particular degree zero is R/(J_V)_0,
not necessarily R. The induced grading has precisely the displayed quotientPiece.
3. lemma-nagata-relative-proj-exists identifies the inverse image of each affine V
with Proj of its graded section ring. Transport by the preceding quotient comparison.
Every positive-degree monomial is divisible by some coordinate. Hence the images of
the n+1 coordinates generate an ideal containing the irrelevant ideal. Apply
prop-nagata-proj-standard-open to obtain the finite cover and the canonical degree-zero
homogeneous-localization chart isomorphisms.
4. lem-trf-free-projective-bundle-base-change-space supplies the chart-normalized
comparison of polynomial relative Proj with base-change projective space.
prop-nagata-relative-proj-functoriality gives the quotient-induced closed immersion;
compose with this comparison. Its over-base equation gives the asserted factorization,
which is projectivity in def-kun-projective.
5. lem-kun-projective-implies-proper gives properness. Its definition supplies finite
type, hence quasi-compactness. Over the locally Noetherian base,
pqf-lem-lft-fp-locnoeth gives local finite presentation. Separatedness implies
quasi-separatedness by lem-pc-separated-quasi-separated, giving finite presentation.
6. Degree-zero equations do not affect this reasoning. The unit ideal makes the
quotient zero, hence every chart empty. A zero or nilpotent coordinate has zero
localization and empty chart. The same arguments include n=0 and the empty base. -/
theorem polynomial_quotient_proj_presentation
    (U : Scheme.{u}) [IsLocallyNoetherian U] (n : ℕ)
    (B : RelativeProjAlgebra U)
    (q : (RelativeProjectiveSpace.algebra U n).affineData ⟶ B.affineData)
    (hq : ∀ V : U.affineOpens, Function.Surjective (q.app V))
    (hfg : ∀ x : U, ∃ (V : U.affineOpens), x ∈ V.1 ∧
      ∃ (t : ℕ) (d : Fin t → ℕ)
        (s : Fin t → (RelativeProjectiveSpace.algebra U n).sections V),
        (∀ j : Fin t, s j ∈ (RelativeProjectiveSpace.algebra U n).grade V (d j)) ∧
        RingHom.ker (q.app V).toRingHom = Ideal.span (Set.range s)) :
    Nonempty (Presentation B q hq) := by
  sorry

end AlgebraicGeometry.PolynomialQuotientProj
