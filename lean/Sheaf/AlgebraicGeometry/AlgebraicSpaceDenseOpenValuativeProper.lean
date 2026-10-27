/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.Valuation.ValuationRing
import Sheaf.AlgebraicGeometry.AlgebraicSpaceDenseOpenStackedValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Properness from valuation extensions starting in a dense open

Source: Stacks Project, Morphisms of Spaces, Tag 089G,
`lemma-refined-valuative-criterion-universally-closed`, conditions (1)--(4),
and Tag 03KU, `lemma-separated-implies-valuative`
(blueprint: lem-sfb-space-dense-open-valuative-proper).

Quasi-compactness uses the existing affine-scheme-test predicate. All spaces are over
Spec Z. Maps from spectra are natural transformations from their Yoneda presheaves,
using Mathlib spectra with their unique structure maps to Spec Z.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A separated finite-type morphism is proper if valuation diagrams whose generic map
starts in a quasi-compact dense open admit a lift after a dominating valuation extension.
The fraction field of the extension ring is taken to be its canonical `FractionRing`;
the field map from the original fraction field is the unique induced map.
Source: Stacks Project, Morphisms of Spaces, Tag 089G,
`lemma-refined-valuative-criterion-universally-closed`, and Tag 03KU
(blueprint: lem-sfb-space-dense-open-valuative-proper).

Proof:
1. Given an arbitrary valuation diagram for p, apply
   lem-sfb-space-dense-open-stacked-valuation to obtain C, q, D = C_q, E = C/q,
   L = Frac C, F = Frac E, b, alpha and v. The ring E dominates the original A;
   alpha has generic map hv, closed restriction eta_F, and lies over b restricted to D.
2. Apply the assumed extension property to C, L, v and b. This gives an injective
   local map C to C1 and z : Spec C1 to H with the specified base and generic maps.
3. C1 is torsion-free over C by injectivity and the domain property. Apply
   lem-trf-valuation-torsionfree-flat. Locality makes the extended maximal ideal proper,
   so lem-weil-pbc-flat-faithfully-flat-maximal-ideals gives faithful flatness. By
   lem-weil-pbc-faithfully-flat-surjective-spectrum choose q1 over q.
4. D1 = (C1)_q1 and E1 = C1/q1 are valuation domains: divisibility comparability passes
   to localizations and prime quotients. The contraction equality makes D to D1 local
   and injective, and C to C1 local makes E to E1 local and injective. Thus E1 dominates A.
5. Compare z restricted to D1 with alpha pulled back to D1. They agree over X and on
   Frac C1. By lem-trf-space-fibre-products-etale-covers their equalizer is the scheme
   test of the closed diagonal of p. Its generic point factors through it, so
   lemma-nagata-valuation-factor-closed applied to the identity gives equality.
6. Restrict z to E1. Its base map is the original a pulled back along A to E1.
   Restrict the equality in step 5 to the residue field of D1, namely Frac E1, to get
   exactly eta pulled back along K to Frac E1. This is the extended lift of the original
   arbitrary valuation diagram.
7. Apply lem-sfb-space-qc-valuative-existence-closed: finite type includes affine-test
   quasi-compactness, so p is universally closed. Together with the assumed separatedness
   and finite type this is MapIsProper p. No rank, discreteness, Noetherian or finite
   presentation restriction is used. -/
theorem mapIsProper_of_denseOpen_valuative
    {H X V : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))} (p : H ⟶ X) (h : V ⟶ H)
    (hpsep : MapIsSeparated p) (hpft : MapIsFiniteType p)
    (hh : IsRepresentableWith (fun _ _ f ↦ IsOpenImmersion f.left) h.hom.hom)
    (hqc : MapIsQuasiCompact h.hom.hom) (hd : Dense (pointImage h.hom.hom))
    (hext : ∀ (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
      (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
      (v : yoneda.obj (Over.mk (specULiftZIsTerminal.from (Spec (.of K)))) ⟶ V.obj.obj)
      (x : yoneda.obj (Over.mk (specULiftZIsTerminal.from (Spec (.of R)))) ⟶ X.obj.obj),
      v ≫ h.hom.hom ≫ p.hom.hom =
        yoneda.map (Over.homMk
          (U := Over.mk (specULiftZIsTerminal.from (Spec (.of K))))
          (V := Over.mk (specULiftZIsTerminal.from (Spec (.of R))))
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          (specULiftZIsTerminal.hom_ext _ _)) ≫ x →
      ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : ValuationRing R')
        (ι : R →+* R') (hι : Function.Injective ι) (_ : IsLocalHom ι)
        (z : yoneda.obj (Over.mk (specULiftZIsTerminal.from (Spec (.of R')))) ⟶ H.obj.obj),
        z ≫ p.hom.hom =
          yoneda.map (Over.homMk
            (U := Over.mk (specULiftZIsTerminal.from (Spec (.of R'))))
            (V := Over.mk (specULiftZIsTerminal.from (Spec (.of R))))
            (Spec.map (CommRingCat.ofHom ι))
            (specULiftZIsTerminal.hom_ext _ _)) ≫ x ∧
        yoneda.map (Over.homMk
          (U := Over.mk (specULiftZIsTerminal.from (Spec (.of (FractionRing R')))))
          (V := Over.mk (specULiftZIsTerminal.from (Spec (.of R'))))
          (Spec.map (CommRingCat.ofHom (algebraMap R' (FractionRing R'))))
          (specULiftZIsTerminal.hom_ext _ _)) ≫ z =
          yoneda.map (Over.homMk
            (U := Over.mk (specULiftZIsTerminal.from (Spec (.of (FractionRing R')))))
            (V := Over.mk (specULiftZIsTerminal.from (Spec (.of K))))
            (Spec.map (CommRingCat.ofHom
              (IsFractionRing.lift (A := R) (K := K)
                (g := (algebraMap R' (FractionRing R')).comp ι)
                ((IsFractionRing.injective R' (FractionRing R')).comp hι))))
            (specULiftZIsTerminal.hom_ext _ _)) ≫ v ≫ h.hom.hom) :
    MapIsProper p := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
