/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus
public import Sheaf.Algebra.Homology.KFlatTensorQuasiIso
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.HomTensorTotal
import Sheaf.Algebra.Homology.KFlatConeTrianglePresentation
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone

/-! # Canonical derived evaluation and signed triangle compatibility

Source: Stacks Project, More on Algebra, Tags 0A67, 0A60, 064J, and
Cohomology on Sites, Tag 08JC (blueprint: lem-trf-derived-evaluation-canonical-map).

The ring is presented on the recorded one-point site. The Hom, tensor, adjunction,
and source shifts are the existing normalized constructions. The evaluation family
below is specified by its transpose equation, rather than a second map definition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace DerivedCategory

/-- The existing one-point ringed-site presentation of D(R).
Source: Stacks 0A67 (blueprint: lem-trf-derived-evaluation-canonical-map). -/
abbrev evaluationDerivedCategory (R : Type u) [CommRing R]
    [HasDerivedCategory.{u}
      (SignedRingedHom.Modules ⊥ (CochainComplex.onePointRingSheaf R))] :=
  DerivedCategory (SignedRingedHom.Modules ⊥ (CochainComplex.onePointRingSheaf R))

variable (R : Type u) [CommRing R]
  [HasDerivedCategory.{u}
    (SignedRingedHom.Modules ⊥ (CochainComplex.onePointRingSheaf R))]

/-- The functor F(K) = RHom(L,M) tensor K, using the native K-flat tensor.
Source: Stacks 0A67, 064J (blueprint: lem-trf-derived-evaluation-canonical-map). -/
abbrev evaluationTensorFunctor (L M : evaluationDerivedCategory R) :=
  tensorLeft ((SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf R) L).obj M)

/-- The covariant composite G(K) = RHom(RHom(K,L),M) of two contravariant Homs.
Source: Stacks 0A67, 08JC (blueprint: lem-trf-derived-evaluation-canonical-map). -/
abbrev evaluationDoubleHomFunctor (L M : evaluationDerivedCategory R) :=
  ((Functor.curry.obj (SignedRingedHom.homFunctor ⊥
    (CochainComplex.onePointRingSheaf R))).flip.obj L).rightOp ⋙
  (Functor.curry.obj (SignedRingedHom.homFunctor ⊥
    (CochainComplex.onePointRingSheaf R))).flip.obj M

/-- The double contravariant shift, including the reversal sign (-1)^m.
Source: Stacks 0A60, sign explanation, and 08JC
(blueprint: lem-trf-derived-evaluation-canonical-map). -/
def evaluationDoubleHomShift (L M K : evaluationDerivedCategory R) (m : ℤ) :
    (evaluationDoubleHomFunctor R L M).obj (K⟦m⟧) ≅
      ((evaluationDoubleHomFunctor R L M).obj K)⟦m⟧ :=
  m.negOnePow •
    ((SignedRingedHom.homFunctor ⊥ (CochainComplex.onePointRingSheaf R)).mapIso
      ((((SignedRingedHom.sourceShift ⊥
        (CochainComplex.onePointRingSheaf R) K m).app L).symm.op).prod (Iso.refl M)) ≪≫
      (SignedRingedHom.sourceShift ⊥ (CochainComplex.onePointRingSheaf R)
        ((SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf R) K).obj L)
        (-m)).app M ≪≫
      eqToIso (congrArg (fun s : ℤ ↦
        ((evaluationDoubleHomFunctor R L M).obj K)⟦s⟧) (neg_neg m)))

/-- The canonical evaluation family is the specified transpose, natural in all three
variables, and compatible with the standard signed shifts and distinguished triangles.
Source: Stacks 0A67, 0A60 (including remark-sign-explanation), 064J and 08JC
(blueprint: lem-trf-derived-evaluation-canonical-map).

Proof:
1. Apply lem-sf-ringed-derived-closed-symmetric-monoidal on the one-point site.
Put A = H(L,M), B = H(K,L). Transpose A tensor K tensor B to A tensor B tensor K
(swapping K,B), then A tensor L, then M, using the two evaluation counits.
Symmetry identifies this with the statement's B tensor A tensor K composite.
2. Counit naturality in K and M gives their covariant squares. For t : L' to L,
both uncurried composites evaluate to h(t(f(x))); transpose to get the L square.
These are adjunction identities, so the calculation applies to derived objects.
3. By prop-pur-kinjective-resolutions-exist and lem-pc-kflat-resolution choose
K-injectives J,I for L,M and a K-flat P for K. The recorded internal Hom and
lem-weil-pbc-site-derived-tensor-descent give the representative
Hom(J,I) tensor P to Hom(Hom(P,J),I). The chain tensor-Hom bijection of
lem-sc-derived-hom-tensor-total gives E(h tensor x)(f) = (-1)^(b*c) h(f(x)).
Here |h|=a, |x|=b, |f|=c; the sign is the swap, and the tensor sums have finite
support in every total degree, even for unbounded complexes.
4. By lem-pc-kflat-cone-triangle-presentation present a distinguished triangle
by a K-flat cone triangle. The isomorphism of lem-pc-tensor-mapping-cone-iso
sends h tensor (y,x) to (h tensor y,(-1)^a h tensor x). It respects the inclusion
and the signed projection, proving F exact. Apply
lem-weil-pbc-ringed-internal-hom-exact-restriction twice in the first variable
to obtain the covariant exact G with its double reversal shift comparison.
5. With def-pur-hom-complex, source-shift reindexing has factor (-1)^(m*q).
The double comparison is (-1)^m times the composite of the two source shifts.
On g of degree n tested at f of degree c it has factor (-1)^(m*(n+c)).
Since n=a+b-m, (b-m)*(c+m)+m*(n+c) equals b*c+m*a modulo two.
This proves the shift square for every integer m, using the tensor multiplier
(-1)^(m*a). The representative comparisons descend it to D(R).
6. Naturality at all three arrows gives the first two triangle squares.
At the connecting arrow w, combine naturality at w with the m=1 shift square:
e3 then G(w) then the G comparison equals F(w) then the F comparison then e1[1].
This is precisely the third square of a triangle morphism. Both image triangles
are distinguished by step 4. No evaluation map has been assumed invertible. -/
theorem derived_evaluation_canonical_map :
    ∃ e : ∀ K L M : evaluationDerivedCategory R,
        (evaluationTensorFunctor R L M).obj K ⟶
          (evaluationDoubleHomFunctor R L M).obj K,
      (∀ K L M : evaluationDerivedCategory R,
        e K L M =
          (SignedRingedHom.adjunction ⊥ (CochainComplex.onePointRingSheaf R)
            ((SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf R) K).obj L)).homEquiv
            _ M ((α_ _ _ _).hom ≫
              _ ◁ ((β_ K _).hom ≫
                (SignedRingedHom.adjunction ⊥
                  (CochainComplex.onePointRingSheaf R) K).counit.app L) ≫
              (SignedRingedHom.adjunction ⊥
                (CochainComplex.onePointRingSheaf R) L).counit.app M)) ∧
      (∀ (K K' L L' M M' : evaluationDerivedCategory R)
        (f : K ⟶ K') (l : L' ⟶ L) (m : M ⟶ M'),
        ((SignedRingedHom.homFunctor ⊥ (CochainComplex.onePointRingSheaf R)).map
          (l.op, m) ⊗ₘ f) ≫ e K' L' M' =
        e K L M ≫ (SignedRingedHom.homFunctor ⊥
          (CochainComplex.onePointRingSheaf R)).map
          (X := (op ((SignedRingedHom.hom ⊥
            (CochainComplex.onePointRingSheaf R) K).obj L), M))
          (Y := (op ((SignedRingedHom.hom ⊥
            (CochainComplex.onePointRingSheaf R) K').obj L'), M'))
          (((SignedRingedHom.homFunctor ⊥ (CochainComplex.onePointRingSheaf R)).map
            (f.op, l)).op, m)) ∧
      ∀ L M : evaluationDerivedCategory R,
        (evaluationTensorFunctor R L M).IsTriangulated ∧
        ∃ _ : (evaluationDoubleHomFunctor R L M).CommShift ℤ,
          (∀ (K : evaluationDerivedCategory R) (m : ℤ),
            ((evaluationDoubleHomFunctor R L M).commShiftIso m).app K =
              evaluationDoubleHomShift R L M K m) ∧
          (evaluationDoubleHomFunctor R L M).IsTriangulated ∧
          (∀ (K : evaluationDerivedCategory R) (m : ℤ),
            e (K⟦m⟧) L M ≫
              ((evaluationDoubleHomFunctor R L M).commShiftIso m).hom.app K =
            ((evaluationTensorFunctor R L M).commShiftIso m).hom.app K ≫
              (e K L M)⟦m⟧') ∧
          ∀ (T : Pretriangulated.Triangle (evaluationDerivedCategory R))
            (_hT : T ∈ Pretriangulated.distinguishedTriangles),
            ∃ t : (evaluationTensorFunctor R L M).mapTriangle.obj T ⟶
                (evaluationDoubleHomFunctor R L M).mapTriangle.obj T,
              t.hom₁ = e T.obj₁ L M ∧ t.hom₂ = e T.obj₂ L M ∧ t.hom₃ = e T.obj₃ L M := by
  sorry

end DerivedCategory
