/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import WeilConjectures.AlgebraicGeometry.Thickening
import WeilConjectures.AlgebraicGeometry.FormallySmooth
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Sheaf.AlgebraicGeometry.SmoothEtaleLocalSource

/-! # Smooth locus and geometric lifts in an étale nodal model

Source: Stacks Project, morphisms.tex, Tags 01V9 (lemma-smooth-at-point) and
02GL (lemma-etale-over-field); descent.tex, Tag 02KM
(lemma-syntomic-smooth-etale-permanence).
(blueprint: lem-trf-nodal-model-etale-smooth-locus)

The model is the pullback of the existing universal nodal model along `a ↦ h`.
Its two coordinates are pulled back explicitly from the universal quotient ring.
The node locus and the zero scheme of `h` retain their full closed-subscheme structures.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The projection identifies the simultaneous coordinate zero scheme of `uv=h` with `V(h)`.
For an étale chart, nonsmoothness of the original morphism, its chart projection and
its nodal model is equivalent to membership in this zero scheme. Every prescribed point
above a geometric point has a lift with the original field; at a nonsmooth point the
composite lift factors scheme-theoretically through the node locus.

Source: Stacks Project, morphisms.tex, Tags 01V9 (lemma-smooth-at-point) and
02GL (lemma-etale-over-field); descent.tex, Tags 02KM, 04QZ, 04R1 and 04R3;
etale-cohomology.tex, Tag 03PR (lemma-geometric-lift-to-cover).
(blueprint: lem-trf-nodal-model-etale-smooth-locus)

Proof, following the five DAG steps:
1. Over an affine open Spec R of V, put B=R[u,v]/(uv-h). Evaluation at u=v=0
   and the coefficient inclusion give inverse maps B/(u,v) ≅ R/(h). These maps
   respect restriction to smaller affine opens and hence glue to the isomorphism
   over V. Use def-weil-closed-immersion and def-weil-affine-spectrum.
2. On D(u), present B[1/u] as R[v,w,u]/(uv-h,uw-1). The Jacobian in v,w is
   diag(u,u), of invertible determinant u². Thus this is standard smooth by
   def-weil-pbc-standard-smooth-algebra, and smooth by
   lem-weil-pbc-standard-smooth-is-smooth. Convert to scheme smoothness using
   lem-weil-pbc-smooth-ring-map-iff-smooth-affine and identify the open using
   lem-weil-pbc-principal-localization-open-immersion and
   lem-weil-pbc-smooth-restrict-open-subschemes. Exchange u,v for D(v).
3. At a coordinate-zero point w with residue field k, the map R→k kills h.
   Put D=k[a,b]/(a²,b²), I=(ab), E=D/I. The basis 1,a,b,ab shows ab≠0 and
   I²=0 (def-sbc-first-order-thickening). The map B→E, u↦a,v↦b, has image w.
   A lift to D would send u,v to a+λab,b+μab, whose product is ab≠0 while h
   maps to zero. A smooth neighbourhood would supply this impossible lift by
   def-sbc-smooth-morphisms and def-sbc-formally-smooth. Both spectra have a
   single point; use lem-weil-pbc-morphism-factors-through-open-subscheme to
   restrict the lifting problem to the smooth neighbourhood and affine chart.
4. Restrict q to a smooth neighbourhood for f. Etale source-and-target locality
   (lem-sfb-scheme-etale-source-target-properties), with etaleness preserved by
   lem-weil-pbc-etale-composition-cancellation, makes p smooth there. Conversely,
   postcompose a smooth restriction of p with b and descend along q using
   lem-trf-etale-source-smoothness. Apply its pointwise clause to e as well.
   Negate these equivalences and combine with steps 2 and 3.
5. Apply the prescribed-point clause of lem-weil-pbc-etale-cover-geometric-point-lift
   to q and the specified t (or to the jointly surjective family {q,id_X}).
   It supplies a lift with field Ω and image t. If f is nonsmooth at xbar,
   step 4 makes both coordinates vanish in the residue field at e(t), hence
   in Ω. The quotient description in def-weil-closed-immersion gives the
   asserted factorization through the full closed subscheme N.
-/
theorem nodal_model_etale_smooth_locus
    {X Y V U : Scheme.{u}} (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f]
    (b : V ⟶ Y) [Etale b] (q : U ⟶ X) [Etale q] (p : U ⟶ V)
    (hq : q ≫ f = p ≫ b) (h : Γ(V, ⊤))
    (e : U ⟶ (pullback (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h))) [Etale e]
    (he : e ≫ pullback.snd nodalModelBaseMap (nodalBaseMap h) = p) :
    (∃ i : (pullback (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h)).zeroLocusSubscheme
          (Set.range (fun k : Fin 2 ↦
              (pullback.fst nodalModelBaseMap (nodalBaseMap h)).appTop
                ((Scheme.ΓSpecIso (.of nodalModelRing)).inv
                  (Ideal.Quotient.mk _ (MvPolynomial.X k))))) ≅ V.zeroLocusSubscheme {h},
      i.hom ≫ V.zeroLocusSubschemeι {h} =
        (pullback (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h)).zeroLocusSubschemeι
          (Set.range (fun k : Fin 2 ↦
              (pullback.fst nodalModelBaseMap (nodalBaseMap h)).appTop
                ((Scheme.ΓSpecIso (.of nodalModelRing)).inv
                  (Ideal.Quotient.mk _ (MvPolynomial.X k))))) ≫
          pullback.snd nodalModelBaseMap (nodalBaseMap h)) ∧
    (∀ t : U,
      ((¬ ∃ O : X.Opens, q t ∈ O ∧ Smooth (O.ι ≫ f)) ↔
        (¬ ∃ O : U.Opens, t ∈ O ∧ Smooth (O.ι ≫ p))) ∧
      ((¬ ∃ O : U.Opens, t ∈ O ∧ Smooth (O.ι ≫ p)) ↔
        (¬ ∃ O : (pullback (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h)).Opens, e t ∈ O ∧
          Smooth (O.ι ≫ pullback.snd nodalModelBaseMap (nodalBaseMap h)))) ∧
      ((¬ ∃ O : (pullback (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h)).Opens, e t ∈ O ∧
          Smooth (O.ι ≫ pullback.snd nodalModelBaseMap (nodalBaseMap h))) ↔
        e t ∈ (pullback (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h)).zeroLocus
          (Set.range (fun k : Fin 2 ↦
              (pullback.fst nodalModelBaseMap (nodalBaseMap h)).appTop
                ((Scheme.ΓSpecIso (.of nodalModelRing)).inv
                  (Ideal.Quotient.mk _ (MvPolynomial.X k))))))) ∧
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (xbar : Spec (.of Ω) ⟶ X)
        (t : U), q t = xbar default →
      ∃ tbar : Spec (.of Ω) ⟶ U,
        tbar ≫ q = xbar ∧ tbar default = t ∧
        ((¬ ∃ O : X.Opens, xbar default ∈ O ∧ Smooth (O.ι ≫ f)) →
          ∃ nbar : Spec (.of Ω) ⟶
              (pullback (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h)).zeroLocusSubscheme
              (Set.range (fun k : Fin 2 ↦
              (pullback.fst nodalModelBaseMap (nodalBaseMap h)).appTop
                ((Scheme.ΓSpecIso (.of nodalModelRing)).inv
                  (Ideal.Quotient.mk _ (MvPolynomial.X k))))),
            nbar ≫
              (pullback (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h)).zeroLocusSubschemeι
              (Set.range (fun k : Fin 2 ↦
              (pullback.fst nodalModelBaseMap (nodalBaseMap h)).appTop
                ((Scheme.ΓSpecIso (.of nodalModelRing)).inv
                  (Ideal.Quotient.mk _ (MvPolynomial.X k))))) = tbar ≫ e)) := by
  sorry

end AlgebraicGeometry
