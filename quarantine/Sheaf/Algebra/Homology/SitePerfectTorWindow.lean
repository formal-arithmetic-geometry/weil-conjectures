/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
public import Sheaf.Paper.WeilTensorProduct
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Algebra.Homology.RingedSiteTorFlatModel
import Sheaf.Algebra.Homology.SitePerfectUpperModel
import Sheaf.Algebra.Homology.SitePerfectLowerModel

/-!
# Local perfect models in a prescribed Tor interval

Source: Stacks Project, Cohomology on Sites, Tags 08G7 and 08H5
(blueprint: lem-sf-site-perfect-tor-window).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v w w'

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- A locally perfect derived object with Tor interval `[a,b]` admits, over every object,
a covering by finite-free-retract models whose terms vanish outside that same interval.
The tensor is precisely the functor selected by the recorded K-flat descent theorem.
Source: Stacks Project, Tags 08G7 (final displayed model), 08H5 (restriction),
08FX and 08FD (shortening)
(blueprint: lem-sf-site-perfect-tor-window).

Proof:
1. Fix U\in\mathcal C. Choose a covering and bounded finite-projective models P of E there, with
explicit degreewise splittings as retracts of finite free sheaves as in
[def-weil-pbc-strict-perfect-coefficient-package]. Work on each of these slice sites. By
[lem-sf-site-tor-interval-restriction], the restriction of E has the same Tor interval [a,b],
testing against every module sheaf on this slice, not just restrictions of global test sheaves.
Thus H^r(P\otimes^{\mathbf L}F)=0 outside [a,b] on this slice.

2. Every term of P is flat in the sense of [def-pc-flat-sheaf-modules]: by the additive tensor
structure and its unit in [lem-pc-sheaf-modules-tensor-closed], tensoring with a retract of
\mathcal O^{\oplus s} is a retract of the exact functor F\mapsto F^{\oplus s}, so preserves
exact sequences. Hence [lem-pc-bounded-above-flat-kflat-site] makes P K-flat. For any
degree-zero module F, the ordinary complex P\otimes F computes P\otimes^{\mathbf L}F: take a
K-flat flat-term resolution T\to F[0] supplied by [lem-pc-kflat-resolution]; its cone is acyclic
by [lem-pur-quasi-iso-cone-acyclic]. The natural complex isomorphism of
[lem-pc-tensor-mapping-cone-iso], applied with \mathcal A^\bullet=P and K_1\to K_2 equal to T\to
F[0], identifies the cone of P\otimes T\to P\otimes F[0] with P\otimes\operatorname{Cone}(T\to
F[0]). Thus K-flatness [def-pc-kflat-complex] makes P\otimes T\to P\otimes F[0] a
quasi-isomorphism, again by [lem-pur-quasi-iso-cone-acyclic]. Since both P and T are K-flat with
flat terms, [lem-weil-pbc-site-derived-tensor-descent] identifies P\otimes T with the derived
tensor of their represented objects. Termwise tensor symmetry identifies F\otimes P with
P\otimes F[0]. Taking F=\mathcal O gives H^r(P)=0 outside [a,b]. This computation applies to
every bounded finite-projective model constructed below.

3. Let n>b be a degree above which the current model is zero. Then H^n(P)=0 makes d:P^{n-1}\to
P^n an epimorphism. Choose a retraction P^n\xrightarrow{i}\mathcal O^{\oplus
s}\xrightarrow{p}P^n. Forgetting modules preserves epimorphisms by
[lem-weil-pbc-module-sheaves-colimits-forgetful]. By
[lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective], each of the finitely many sections
p(e_j) lifts along d after a cover; successively refine to lift them all on one cover. These
lifts give h:\mathcal O^{\oplus s}\to P^{n-1} with dh=p, hence s_0=hi:P^n\to P^{n-1} satisfies
ds_0=\operatorname{id}. This argument uses only local section lifts, not surjectivity on
sections over the original object.

4. On each member of this cover put K=\ker d. The maps x\mapsto(x-s_0d(x),d(x)) and (k,y)\mapsto
k+s_0(y) identify P^{n-1} with K\oplus P^n. Consequently K is a retract of P^{n-1} and hence of
a finite free sheaf. Since dd^{n-2}=0, the incoming differential lands in K. The complex is
therefore the direct sum of the shortened complex (replace P^{n-1} by K and P^n by zero) and the
two-term identity complex P^n\xrightarrow{1}P^n in degrees n-1,n. The latter has contracting
homotopy the identity backwards, so removing it gives a quasi-isomorphism and preserves the
represented derived object.

5. Choose an initial integer upper bound t\ge b for P. Descending induction from n=t through
n=b+1 using Steps 3 and 4 produces, after a finite succession of covers on this original perfect
chart, a bounded finite-projective complex Q zero in degrees >b. The base case t=b needs no
change; if a top term is zero the splitting is the zero map. Restriction is exact by
[lem-pur-site-restriction-module-adjunction-exact], hence preserves quasi-isomorphisms, and
restricts the displayed retractions sectionwise. At every refinement
[lem-sf-site-tor-interval-restriction] preserves the Tor interval of the represented object.
Iterated slices are slices of the original site by [def-pur-localized-ringed-site]; transitivity
of covers composes these finite refinements. Thus Q still represents the appropriate restriction
of E and has Tor interval [a,b].

6. Set N=\operatorname{coker}(d_Q^{a-1}:Q^{a-1}\to Q^a). By Step 2 applied to Q, for every
module sheaf F the ordinary complex F\otimes Q has zero cohomology in degree a-1. The terms of Q
are flat. Therefore [lem-weil-pbc-site-flat-opcycles-tor-criterion], applied on the current
small slice site with n=a, proves that N is flat. This uses the site's general opcycle
criterion; no assumption of enough points or of constant coefficients is made.

7. The sheaf N has a finite presentation. To see it directly, write retractions
Q^a\xrightarrow{i}\mathcal O^{\oplus s}\xrightarrow{p}Q^a and Q^{a-1}\xrightarrow{j}\mathcal
O^{\oplus r}\xrightarrow{q}Q^{a-1} with pi=1 and qj=1, and put e=ip. Then \mathcal O^{\oplus
s}\oplus\mathcal O^{\oplus r}\xrightarrow{(1-e,\ i d_Q^{a-1}q)}\mathcal O^{\oplus
s}\xrightarrow{\overline p}N\to0 is exact: \ker p=\operatorname{im}(1-e) and the image of
id_Q^{a-1}q is i(\operatorname{im}d_Q^{a-1}), so the cokernel is precisely
Q^a/\operatorname{im}d_Q^{a-1}. These identities hold as sheaf images and cokernels, with no
exactness of global sections asserted. Thus N satisfies the explicit finite-presentation
hypothesis of Step 8.

8. Apply [lem-sf-site-flat-fp-finite-retract] to N on this slice, using Steps 6 and 7. On its
resulting cover form R with R^a=N, R^r=Q^r for a<r\le b, and zero terms otherwise; its first
differential is induced by d_Q^a, which annihilates \operatorname{im}d_Q^{a-1}. Restrict this
construction to each covering member. Exact restriction
[lem-pur-site-restriction-module-adjunction-exact] preserves its quotient and cohomology. The
quotient chain map Q\to R induces an isomorphism on cohomology: in degree a its kernel
calculation is \ker(d_Q^a)/\operatorname{im}(d_Q^{a-1}), in degree a+1 the incoming image is
unchanged because Q^a\to N is an epimorphism and d_Q^a factors through it, in degrees >a+1 the
adjacent terms and differentials are identical, and below a both cohomologies vanish by the
given Tor interval and Step 2. Hence R represents the restriction of E. Its degree a term is a
finite free retract by the new tool and its other terms retain their retractions. It is zero
outside [a,b]. Finally compose all covers with the original perfect cover using
[def-pur-localized-ringed-site] and the covering transitivity axiom to get the asserted \{V_j\to
U\}.
-/
theorem exists_strictPerfect_model_in_tor_window
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max u v}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v})
    [HasDerivedCategory.{w} (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))]
    [∀ U : C, HasDerivedCategory.{w'} (SheafOfModules.{max u v}
      (((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R).over U))]
    (E : DerivedCategory (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)))
    (_hperfect : IsPerfectOnRingedSiteOfUniverses.{u, v, 0} R E)
    (a b : ℤ) (_hab : a ≤ b)
    (_hTor : ∀ (F : SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))
        (r : ℤ), r < a ∨ b < r →
      IsZero ((DerivedCategory.homologyFunctor _ r).obj
        ((wfSiteDerivedTensor J R).obj
          (E, (DerivedCategory.singleFunctor _ 0).obj F)))) :
    ∀ U : C, ∃ S : Sieve U, S ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), S f →
        ∃ P : StrictPerfectCoefficientRepresentationOfUniverses.{u, v, 0} R V
          (ringedSiteDerivedRestrictionOfUniverses
            ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) V E),
          ∀ r : ℤ, r < a ∨ b < r → IsZero (P.F.X r) := by
  classical
  obtain ⟨Q, _, hbound, ⟨e⟩⟩ :=
    (torAmplitude_iff_exists_bounded_flat_model J R E a b _hab).1 _hTor
  have hcoh (r : ℤ) (hr : b < r) :
      IsZero ((DerivedCategory.homologyFunctor _ r).obj E) := by
    exact (HomologicalComplex.ExactAt.of_isZero (hbound r (Or.inr hr))).isZero_homology.of_iso
      ((DerivedCategory.homologyFunctor _ r).mapIso e ≪≫
        (DerivedCategory.homologyFunctorFactors _ r).app Q)
  intro U
  obtain ⟨S, hS, hP⟩ := exists_strictPerfect_upper_model J R E _hperfect b hcoh U
  have hlocal (V : C) (f : V ⟶ U) (hf : S f) :
      ∃ T : Sieve V, T ∈ J V ∧
        ∀ (W : C) (g : W ⟶ V), T g →
          ∃ P : StrictPerfectCoefficientRepresentationOfUniverses.{u, v, 0} R W
            (ringedSiteDerivedRestrictionOfUniverses
              ((sheafCompose J
                (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) W E),
            ∀ r : ℤ, r < a ∨ b < r → IsZero (P.F.X r) := by
    obtain ⟨P, hupper⟩ := hP V f hf
    exact exists_strictPerfect_lower_model J R E V P a b _hab hupper _hTor
  choose T hT hmodel using hlocal
  refine ⟨Sieve.bind S (fun {V} {f} hf ↦ T V f hf),
    J.bind_covering hS (fun _ _ hf ↦ hT _ _ hf), ?_⟩
  intro V f hf
  obtain ⟨W, g, h, hh, hg, _⟩ := hf
  exact hmodel W h hh V g hg

end SheafOfModules
