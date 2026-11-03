/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.AffineCurveRange.LatticePiece.CurveLatticeCompactData
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed

/-!
# Compact-support lattice devissage on an affine curve

Source: latest blueprint, `sec-deligne-laumon-a1/sk-l-dl-a1-endpoints/`
`lem-zl-affine-curve-range.proof.md`, coefficient descent, devissage, and lattice
rationalization. This statement supplies a finite extension filtration, with no
cohomological bound on any constituent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.AffineCurveRange

/-- The actual compact-support coefficient complex is a finite extension of
scalar extensions of ordinary integral compact supports of lisse lattices on
smooth pieces of dimensions zero and one. This is a presentation theorem only:
neither finite-level finiteness nor integral cohomological vanishing is asserted.

Source: latest blueprint, `lem-zl-affine-curve-range.proof.md`, reduction to E,
devissage, and inverting ell; range node steps 1--3, 9--10
(blueprint: lem-zl-affine-curve-lattice-filtration).

Proof: forget the Weil structure and split the smooth affine geometric curve
into finitely many connected components. On each component finite coefficient
descent gives a constructible E-complex. Exact scalar extension lets one take
its degree-zero cohomology to descend the sheaf itself. Shrink to a dense lisse
open, and apply the stratified lattice theorem, shrinking again to its generic
stratum. The reduced complement is a finite set of closed points. On each of
its singleton clopens choose the integral lattice, and glue over the empty
overlaps. Over the algebraically closed field this reduced finite scheme is
smooth of dimension zero. The open lattice piece is smooth of dimension one.
For each lattice take the ordinary compact-support complex recorded in
LatticePiece.integralComplex. Scalar comparison for O_E to E and E to Qbar
identifies its exact extension of scalars with the rational compact-support
complex of that piece. The scalar homomorphism r is the canonical inclusion
of the integral terminal scalar ring into Qbar; the associated module extension
is exact by flatness of localization and of field extension. The point
equivalence identifies this scalar comparison with ordinary module extension.
The actual open counit and closed unit give the open--closed triangle. Apply
compact support, using its triangulated factors and composition comparisons.
Successive open unions of the component opens and of the component complements
give a finite filtration, whose successive cofibers are exactly these scalar
extensions; this is the finite induction in step 10. The first object is the
compact support of the empty open and is zero. The last is the original compact
support, transported to the supplied compactification by independence. Empty
curves use m=0. No lattice or coefficient descent is required to retain a Weil
structure, and no cohomology bound enters this construction.
-/
theorem affineCurve_latticeFiltration
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    (C₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom]
    [IsAffine C₀.left] [SmoothOfRelativeDimension 1 C₀.hom]
    (F : condensedWeilModules (Profinite.padicAlgClRingObj ell)
      (D.geometricFrobenius C₀).hom)
    (hF : IsConstantModelConstructible (Profinite.padicAlgClRingObj ell)
      (D.geometricFiber C₀).left F.carrier)
    (c : Compactification (D.geometricFiber C₀).hom) :
    ∃ (m : ℕ) (T : Fin (m + 1) → DerivedCategory (ModuleCat.{u + 1} (PadicAlgCl ell))),
      IsZero (T 0) ∧
      Nonempty (T (Fin.last m) ≅
        (condensedQbarCompactSections ell D.k c).obj
          ((DerivedCategory.singleFunctor _ 0).obj F.carrier)) ∧
      ∀ j : Fin m, ∃ (d : LatticePiece ell D.k) (r : d.scalarRing →+* PadicAlgCl ell),
        let S : ModuleCat.{u + 1} d.scalarRing ⥤ ModuleCat.{u + 1} (PadicAlgCl ell) :=
          ModuleCat.extendScalars r
        ∃ (_h : PreservesFiniteLimits S)
          (f : T j.castSucc ⟶ T j.succ)
          (g : T j.succ ⟶ S.mapDerivedCategory.obj d.integralComplex)
          (δ : S.mapDerivedCategory.obj d.integralComplex ⟶ T j.castSucc⟦(1 : ℤ)⟧),
          Pretriangulated.Triangle.mk f g δ ∈ distTriang _ := by
  sorry

end WeilConjectures.AffineCurveRange
