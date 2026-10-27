/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.FinitePresentationFamilyDescent
import WeilConjectures.AlgebraicGeometry.ExistsIsSeparatedOverPullbackMap
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.AffineImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism
import WeilConjectures.AlgebraicGeometry.CoherentPseudoCoherent
import WeilConjectures.AlgebraicGeometry.DerivedPullback
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness

/-! # A derived Chow neighbourhood for a scheme

Source: Stacks Project, more-morphisms.tex, Tag 0CSJ, lemma-derived-chow, clauses (1)--(6)
(blueprint: lem-sfb-derived-chow-neighbourhood).

Projective space is the Proj of the polynomial algebra on n + 1 homogeneous coordinates.
The comparison restricts to the entire inverse image of V in X times projective space.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A derived Chow neighbourhood with a pseudo-coherent kernel supported on its closed graph.
Source: Stacks Project, Tag 0CSJ, lemma-derived-chow, clauses (1)--(6)
(blueprint: lem-sfb-derived-chow-neighbourhood).

Proof plan:
1. Use [lemma-nagata-noetherian-inverse-system-affine] to write $\operatorname{Spec}A$ as the
   limit of the spectra of its finitely generated integer subalgebras. Apply
   [lem-weil-pbc-finite-presentation-family-descent] to the singleton family $X$. Apply
   [lem-weil-pbc-descend-separated] to its structure morphism, increasing the stage so it is
   separated. This gives a finite type $\mathbf Z$-subalgebra $A_0\subseteq A$, a separated
   finitely presented $X_0/A_0$, and $X\simeq X_0\times_{A_0}A$. All stages are affine (hence
   qcqs) and the descended source is qcqs, as required by the separatedness descent node. Let
   $x_0$ be the image of $x$. Uses: lemma-nagata-noetherian-inverse-system-affine,
   lem-weil-pbc-finite-presentation-family-descent, lem-weil-pbc-descend-separated.
2. First construct the data over $A_0$. The scheme $\operatorname{Spec}A_0$ is Noetherian by
   [lem-weil-pbc-finite-type-over-noetherian], since it is finite type over $\mathbf Z$; the same
   node makes $X_0$ Noetherian. Choose an affine open $U_0$ containing $x_0$. By
   [lem-weil-pbc-lfp-affine-opens-finite-presentation], its coordinate ring is finitely presented
   over $A_0$, hence finitely generated. Apply [lem-chow-affine-immersion] to obtain
   $j:U_0\hookrightarrow P_0=\mathbf P^n_{A_0}$. The projection $P_0\to\operatorname{Spec}A_0$ is
   proper by [lemma-nagata-projective-space-base-change-proper], hence separated and finite type
   by [def-weil-proper-morphism]; the Noetherian node also makes $P_0$ Noetherian. By
   [lem-sfb-finite-type-composition-base-change], $T_0=X_0\times_{A_0}P_0$ is finite type over
   $X_0$, so is Noetherian by the same Noetherian node. Uses:
   lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-lfp-affine-opens-finite-presentation,
   lem-chow-affine-immersion, lemma-nagata-projective-space-base-change-proper,
   def-weil-proper-morphism, lem-sfb-finite-type-composition-base-change.
3. Let $Z_0$ be the scheme-theoretic image of $(\mathrm{id}_{U_0},j):U_0\to T_0$
   [def-nagata-scheme-theoretic-image]. The open inclusion $U_0\hookrightarrow X_0$ is
   quasi-compact by [lem-sfb-noetherian-open-closed-finite-presentation]. Apply
   [lemma-nagata-scheme-image-partial-section], using separatedness of $P_0/A_0$, to obtain
   $b_0^{-1}(U_0)\simeq U_0$, identified with the original graph. Thus there is exactly one $z_0$
   above $x_0$. Uses: def-nagata-scheme-theoretic-image,
   lem-sfb-noetherian-open-closed-finite-presentation, lemma-nagata-scheme-image-partial-section.
4. Let $Y_0\subseteq P_0$ be the scheme-theoretic image of $j$. The immersion $j$ is the closed
   immersion $U_0\hookrightarrow\mathbf A^n_{A_0}$ followed by the open immersion $\mathbf
   A^n_{A_0}\hookrightarrow P_0$ into the Noetherian $P_0$, so it is quasi-compact by
   [lem-sfb-noetherian-open-closed-finite-presentation]. By
   [lemma-nagata-immersion-open-in-scheme-image], it identifies $U_0$ with an open $J_0\subseteq
   Y_0$. By the minimal property [lemma-nagata-scheme-theoretic-closure-minimal], $Z_0$ lies in
   the closed subscheme $X_0\times_{A_0}Y_0$ (closed by
   [lem-weil-pbc-closed-immersion-base-change]) and is the image there of the same graph: a closed
   subscheme there is also closed in $T_0$, so the two minimal images coincide. Interchange the
   two factors and apply [lemma-nagata-scheme-image-partial-section] with open $J_0\subseteq Y_0$
   and separated $X_0/A_0$. It gives $c_0^{-1}(J_0)\simeq J_0$, again the original graph. Choose
   an open $V_0\subseteq P_0$ whose intersection with $Y_0$ is $J_0$; such an open exists by the
   subspace topology. Then $c_0^{-1}(V_0)=b_0^{-1}(U_0)$ as open subschemes of $Z_0$, since both
   equal the graph, and $c_0^{-1}(V_0)\to V_0$ is the closed immersion $Y_0\cap V_0\hookrightarrow
   V_0$. Uses: lem-sfb-noetherian-open-closed-finite-presentation,
   lemma-nagata-immersion-open-in-scheme-image, lemma-nagata-scheme-theoretic-closure-minimal,
   lemma-nagata-scheme-image-partial-section, lem-weil-pbc-closed-immersion-base-change.
5. Write $h_0:Z_0\hookrightarrow T_0$. Since $T_0$ is Noetherian,
   [lem-sfb-noetherian-open-closed-finite-presentation] (with the open immersion the identity)
   makes $h_0$ finitely presented; $Z_0$ is Noetherian by
   [lem-weil-pbc-finite-type-over-noetherian], as a closed immersion is finite type. Put
   $E_0=(h_{0,*}\mathcal O_{Z_0})[0]$. The structure sheaf $\mathcal O_{Z_0}$ is quasi-coherent of
   finite type, hence coherent on the locally Noetherian $Z_0$ by [pqf-lem-coherent-ft-locnoeth].
   By [lem-pc-closed-immersion-coherent-cohomology] its pushforward is coherent. Hence
   [lem-sc-coherent-pseudo-coherent] makes $E_0$ pseudo-coherent. It is zero on $T_0\setminus
   h_0(Z_0)$ by the definition of ordinary pushforward. Its restriction to $X_0\times_{A_0}V_0$ is
   precisely the degree-zero pushforward of the structure sheaf of $W_0=c_0^{-1}(V_0)$. Uses:
   lem-sfb-noetherian-open-closed-finite-presentation, lem-weil-pbc-finite-type-over-noetherian,
   pqf-lem-coherent-ft-locnoeth, lem-pc-closed-immersion-coherent-cohomology,
   lem-sc-coherent-pseudo-coherent.
6. Pull back $U_0,V_0,Z_0$ to $A$, set $n$ equal to the integer just constructed, and denote the
   resulting closed immersion by $h:Z\hookrightarrow T=X\times_A P$. Projective spaces commute
   with base change by [lemma-nagata-projective-space-base-change-pullback]. Closed immersions
   remain closed by [lem-weil-pbc-closed-immersion-base-change]. Finiteness of presentation also
   persists: locally the finitely generated ideal $(f_1,\ldots,f_r)$ defining $h_0$ pulls back to
   the ideal generated by the images of those same $f_i$; its closed immersion is affine and thus
   quasi-compact and quasi-separated. The inverse images of $U_0,V_0$ agree in $Z$ by
   associativity of fibre products, and the restricted isomorphism and closed immersion pull back
   to the required ones. In particular $b^{-1}(U)\simeq U$ gives a unique $z$ over the chosen $x$,
   and this point belongs to $c^{-1}(V)$. Uses:
   lemma-nagata-projective-space-base-change-pullback, lem-weil-pbc-closed-immersion-base-change.
7. Let $q:T\to T_0$ be the projection and set $E=Lq^*E_0$ [def-pc-derived-pullback]. Locally
   represent $E_0$ by a bounded-above finite free complex, as in
   [def-pur-pseudo-coherent-complex]. It is K-flat by [lem-pc-bounded-above-flat-kflat], so its
   termwise pullback computes the derived pullback and remains bounded-above finite free. Thus $E$
   is pseudo-coherent. Restrictions of derived pullback commute with this calculation, or
   equivalently with derived-pullback composition
   [lem-pc-ringed-spaces-derived-pullback-composition]. The complement $T\setminus h(Z)$ is
   exactly $q^{-1}(T_0\setminus h_0(Z_0))$ by the inverse-image construction of a closed
   subscheme. Since $E_0$ is zero on the latter open, $E$ is zero on the former; in particular
   every $H^j(E)_t$ there is zero. Uses: def-pc-derived-pullback, def-pur-pseudo-coherent-complex,
   lem-pc-bounded-above-flat-kflat, lem-pc-ringed-spaces-derived-pullback-composition.
8. It remains to identify $E$ on the whole open $X\times_A V$, not merely on $U\times_A V$. Apply
   [lem-sfb-relative-flat-closed-kernel-base-change] with $S_0=\operatorname{Spec}A_0$,
   $S=\operatorname{Spec}A$, $Y_0=V_0$, and $i_0:W_0\hookrightarrow X_0\times_{A_0}V_0$. Its two
   flatness hypotheses hold: $W_0\to X_0$ is the open immersion $U_0\hookrightarrow X_0$ (its
   local ring maps are identities), while $V_0\to\operatorname{Spec}A_0$ is flat because the
   projective standard charts are polynomial algebras by
   [lem-weil-pbc-projective-space-standard-charts], and their structural maps are flat by
   [lem-nagata-polynomial-projection-flat]; their open restrictions are flat on stalks, or by
   [lem-pc-affine-flat-module-localization-preserves-flatness]. By derived-pullback composition,
   the left side of the comparison is $E|_{X\times_A V}$; the right side is the degree-zero
   pushforward of $\mathcal O_{W}$ for $W=Z\cap(X\times_A V)$. Ordinary pushforward restricted to
   an open is pushforward of the restriction, directly on sections. This is $(h_*\mathcal
   O_Z)[0]|_{X\times_A V}$ and proves the remaining clause. Uses:
   lem-sfb-relative-flat-closed-kernel-base-change, lem-weil-pbc-projective-space-standard-charts,
   lem-pc-ringed-spaces-derived-pullback-composition, lem-nagata-polynomial-projection-flat,
   lem-pc-affine-flat-module-localization-preserves-flatness.
-/
theorem exists_derivedChow_neighbourhood
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{u}) (W : Y.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]
    (A : CommRingCat.{u}) (X : Scheme.{u}) (f : X ⟶ Spec A)
    [IsSeparated f] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (x : X) :
    ∃ (U : X.Opens) (n : ℕ)
      (V : (Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (n + 1))) A).Opens)
      (Z : Scheme.{u}) (h : Z ⟶ pullback f (Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (n
        + 1))) A)) (z : Z)
      (E : schemeDerivedCategory (pullback f (Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin
        (n + 1))) A))),
      x ∈ U ∧ IsClosedImmersion h ∧ LocallyOfFinitePresentation h ∧
      QuasiCompact h ∧ QuasiSeparated h ∧
      IsIso ((h ≫ pullback.fst f (Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (n + 1))) A))
        ∣_ U) ∧
      (h ≫ pullback.fst f (Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (n + 1))) A)) z = x
        ∧
      IsClosedImmersion ((h ≫ pullback.snd f (Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin
        (n + 1))) A)) ∣_ V) ∧
      (h ≫ pullback.fst f (Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (n + 1))) A)) ⁻¹ᵁ U
        = (h ≫ pullback.snd f (Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (n + 1))) A))
        ⁻¹ᵁ V ∧
      z ∈ (h ≫ pullback.fst f (Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (n + 1))) A))
        ⁻¹ᵁ U ∧
      Nonempty (
        (SheafOfModules.overFunctor.{u}
          (moduleRings (pullback f (Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (n + 1)))
            A)).toRingedSpace)
          ((pullback.snd f (Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (n + 1))) A)) ⁻¹ᵁ
            V)).mapDerivedCategory.obj E ≅
        (SheafOfModules.overFunctor.{u}
          (moduleRings (pullback f (Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (n + 1)))
            A)).toRingedSpace)
          ((pullback.snd f (Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (n + 1))) A)) ⁻¹ᵁ
            V)).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings (pullback f (Proj.projectiveSpaceOverAffineToSpec
              (ULift.{u} (Fin (n + 1))) A)).toRingedSpace)) 0).obj
            ((Modules.pushforward h).obj
              (SheafOfModules.unit (moduleRings Z.toRingedSpace))))) ∧
      IsPseudoCoherent (pullback f (Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (n + 1)))
        A)) E ∧
      ∀ (j : ℤ)
        (t : (pullback f
          (Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (n + 1))) A) : Scheme.{u})),
        t ∉ Set.range h →
        Subsingleton (↑(TopCat.Presheaf.stalk
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (pullback f (Proj.projectiveSpaceOverAffineToSpec
              (ULift.{u} (Fin (n + 1))) A)).toRingedSpace)) j).obj E).val.presheaf
          t)) := by
  sorry

end AlgebraicGeometry.Scheme
