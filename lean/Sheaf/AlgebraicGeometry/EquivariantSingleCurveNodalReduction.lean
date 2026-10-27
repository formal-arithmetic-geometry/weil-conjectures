/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.AlgebraicGeometry.QuasiSplitNodalFibres
public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.StalkAut
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChangeSection
public import Sheaf.FieldTheory.FieldTower
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.Topology.GDelta.Basic
import Sheaf.RingTheory.FieldsExcellent
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective
import Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange
import Sheaf.AlgebraicGeometry.Morphisms.GenericFiniteOpenNeighborhood
import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
import WeilConjectures.FieldTheory.TensorFieldExtensionGaloisInvariants

/-! # Equivariant marked nodal reduction of a single curve

Source: de Jong, Families of curves and alterations, Theorem 2.4 and Remark 2.5,
pp. 602--603, Lemmas 5.5 and 5.7, pp. 614--615, and Theorem 5.9 proof, p. 617
(blueprint: lem-sfb-equivariant-single-curve-nodal-reduction).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Equivariant one-curve alteration, with the prescribed input group allowed to act
nonfaithfully or semilinearly. The two function-field inclusions are fixed by the transported
maps of generic stalks; the fixed fields use the actual induced scheme automorphisms.
The zero-dimensional conclusion identifies the base with Spec e by its structure map.

Source: de Jong, Theorem 2.4, Remark 2.5, Lemmas 5.5 and 5.7, and Theorem 5.9 proof
(blueprint: lem-sfb-equivariant-single-curve-nodal-reduction).

Proof (the node's thirteen steps):
1. Put $K=k(Y)$ and $F=k(C)$. Apply equivariant flat preparation to $(g,H,E)$, obtaining
   $S,P,f,M,a,b_0$ with $K_0=k(S)/K$ finite purely inseparable. Put $F_0=k(P)=F\otimes_K K_0$. The
   generic curve of $P/S$ is smooth geometrically integral and its reduced generic marking is
   finite etale. The $H$-action is retained. Fields are excellent, finite-type algebras and their
   localizations are excellent, and finite-type schemes over a field are Noetherian; hence all
   bases constructed below are excellent Noetherian. This step prepares the generic curve and the
   target, and makes no stable-modification claim.
   Uses: lem-sfb-equivariant-flat-curve-preparation, lem-exc-fields-excellent, lem-exc-finite-
   type-localization-excellent, lem-weil-pbc-finite-type-over-noetherian.
2. Apply the auxiliary high-genus cover to $P/S$, its marking $M$ and $H$. Denote its output by
   $Q/S_1$, $H_1\twoheadrightarrow H$, and $K_1=k(S_1)$, $F_1=k(Q)$. Its generic fibre is smooth
   geometrically integral of genus at least two. Its generic inverse image of $M$ is a finite set
   of distinct rational points $p_i$, invariant as a set under $H_1$. Every geometric fibre of
   $Q/S_1$ contains no nonconstant image of $\mathbf P^1$. If $A_1=\ker(H_1\to H)$, the cover
   supplies $F_1^{A_1}=F_0$ and $K_1^{A_1}=K_0$. The finite separable auxiliary covering is
   retained: the required conclusion allows the genus to increase and does not prescribe
   $k(V)=F\otimes_K k(B)$.
   Uses: lem-sfb-high-genus-equivariant-cover.
3. Apply stable pointed extension to the smooth pointed generic curve $(Q_\eta,p_i)$ over $S_1$.
   It gives an integral alteration $T\to S_1$, with finite separable generic extension, and a
   stable pointed curve over $T$. Apply semilinear Galois domination to this alteration and $H_1$.
   Obtain a normal projective $S_2$, a surjection $H_2\twoheadrightarrow H_1$, and a map $S_2\to
   T$. Pull the stable pointed curve to $S_2$ and call it $(W,s_i)$. Its generic pointed fibre is
   $Q_\eta\times_{K_1}K_2$, where $K_2=k(S_2)$. For $N_2=\ker(H_2\to H_1)$, domination gives
   $K_2^{N_2}=K_1$ (the separable case). No morphism from $W$ to $P$ has yet been asserted.
   Uses: lem-sfb-stable-pointed-generic-extension, lem-sfb-semilinear-galois-alteration-
   domination.
4. For each $h\in H_2$, the given action on the generic curve identifies the unordered pointed
   generic fibres of $h^*W$ and $W$. Finite-Isom rigidity extends it uniquely to an isomorphism on
   the normal integral base $S_2$. The composite of the extensions for $h,h'$ and the extension
   for $hh'$ have identical generic restrictions, so uniqueness proves the group law; the identity
   extends to the identity. This gives a genuine action preserving the union of the sections,
   allowing permutations. The curve $W/S_2$ is projective in the projective-bundle sense. As $S_2$
   is projective over $k$, it has an absolute ample invertible sheaf. Projective-bundle to
   H-projective conversion makes $W/S_2$ H-projective.
   Uses: lem-sfb-stable-pointed-isom-finite, lem-weil-pbc-projective-ample-invertible, lem-trf-
   projective-bundle-to-h-projective.
5. Apply the Hom-closure theorem to $W/S_2$, the H-projective target $Q\times_{S_1}S_2$, and their
   generic identification. The no-rational-curve condition on this target holds by the high-genus
   cover, since its geometric fibres are geometric fibres of $Q/S_1$ after field extension. Obtain
   an integral projective birational $R\to S_2$, with evaluation $W_R\to Q_R$. The closure and
   evaluation are $H_2$-equivariant by naturality. Apply semilinear Galois domination to $R\to
   S_2$, obtaining normal projective $S_3$, $H_3\twoheadrightarrow H_2$, and $S_3\to R$. This last
   map is equivariant: its translates agree at the generic point because $R\to S_2$ is birational;
   the closed equalizer and reducedness of $S_3$ make them equal. Pull back evaluation and the
   sections. We have an $H_3$-equivariant map $W_3\to Q\to P\to C$ over $S_3\to S_1\to S\to Y$,
   and a stable pointed curve $W_3/S_3$.
   Uses: lem-sfb-high-genus-hom-closure, lem-sfb-high-genus-equivariant-cover, lem-pc-projective-
   base-change, lem-sfb-semilinear-galois-alteration-domination, lem-sfb-stable-pointed-generic-
   extension.
6. For this and every subsequent dominant integral base change $T'\to S_3$, the pulled-back curve
   is integral. Indeed, over an affine domain $A$ in $T'$, on every affine chart
   $\operatorname{Spec}B$ of the flat curve, multiplication by $a\in A\setminus\{0\}$ is injective
   by flat-invertible-sections-torsion-freeness applied to $\mathcal O$. Hence $B\hookrightarrow
   B\otimes_A\operatorname{Frac}(A)$. A nonempty chart has nonempty generic fibre and this generic
   ring is a domain, since the generic curve is geometrically integral. Thus every chart is a
   domain. The generic fibre is irreducible and meets every nonempty open by the same injectivity,
   so the entire curve is irreducible, and is reduced chartwise. Its function field after base
   extension $L'/L$ is the function field $D$ of the preceding generic curve tensored with $L'$;
   this is a domain and is finite dimensional over $D$, hence a field. In particular
   $k(W_3)=F_1\otimes_{K_1}k(S_3)$. The same argument works for purely inseparable base
   extensions.
   Uses: lem-sc-flat-invertible-sections-torsion-free, lem-weil-pbc-finite-dimensional-domain-is-
   field, lem-trf-semistable-marked-base-change.
7. Record how the invariant fields behave at each of our base extensions. Let
   $J'\twoheadrightarrow J$ have kernel $N$, let $L'/L$ be the corresponding finite extension of
   base fields, and suppose $(L')^N=M$ is purely inseparable over $L$. The group $N$ acts
   trivially on the preceding generic curve field $D$ and only on $L'$ in $D'=D\otimes_L L'$. The
   field $D_M=D\otimes_L M$ is a field by the domain and finite-dimension argument of Step 6.
   Tensor invariants over $M$, with vector space $D_M$, give $(D')^N=D_M$. Every element of $D_M$
   has some common characteristic power in $D$: write it as a finite sum of tensors and take a
   power putting all coefficients from $M$ into $L$. In characteristic zero $M=L$ and this is
   equality. Therefore $(D')^N/D$ is purely inseparable.
   Uses: lem-weil-pbc-tensor-field-extension-galois-invariants, lem-weil-pbc-finite-dimensional-
   domain-is-field.
8. If $A=\ker(J\to H)$ and $A'=\ker(J'\to H)$, then $A'\to A$ is surjective. For $z\in(D')^{A'}$,
   Step 7 puts some characteristic power $z^{p^r}$ in $D$. Since all lifts of $A$ fix $z$, that
   power lies in $D^A$. If $D^A/F$ is purely inseparable, a further power lies in $F$. The
   identical power argument for the base fields proves the base invariant assertion. In
   characteristic zero both powers are identities. Start with $F_1^{A_1}=F_0$ and $K_1^{A_1}=K_0$
   from Step 2; $F_0/F$ and $K_0/K$ are purely inseparable by Step 1. The domination steps give
   $(L')^N=L$ in the separable case. Thus for $A_3=\ker(H_3\to H)$ we have $k(W_3)^{A_3}/F$ and
   $k(S_3)^{A_3}/K$ purely inseparable. The same reasoning will apply to the next finite base
   cover and to the final radicial constant change.
9. Apply finite quasi-splitting to $W_3/S_3$ and $H_3$. Its hypotheses hold: the family is
   H-projective, flat and finitely presented, with nonempty connected reduced nodal geometric
   fibres and smooth geometrically integral generic fibre. Obtain normal projective $S_4\to S_3$
   finite surjective generically etale and $H_4\twoheadrightarrow H_3$. Pull the stable curve and
   its sections to $S_4$. The family is quasi-split; the markings remain disjoint and smooth.
   Integrality and the field description follow from Step 6. The base kernel invariant field is
   purely inseparable by finite quasi-splitting; Steps 7--8 therefore retain both invariant-field
   conclusions. The group action on the pulled-back markings permutes the sections. There is no
   finite-etale-marking cover $T_1$ in this construction: the sections were extended from the
   rational points $p_i$ in Step 3.
   Uses: lem-sfb-nodal-finite-quasi-splitting, lem-trf-semistable-marked-base-change, lem-sfb-
   stable-pointed-generic-extension.
10. Apply constant regularization to $S_4\to Y$, $H_4\to H$ and the base invariant conclusion just
   proved. Obtain a finite extension $e/k$, normal projective geometrically integral $B/e$, and a
   finite radicial surjection $B\to S_4$, with the same group $G=H_4$. Write $\alpha:G\to H$,
   $A=\ker\alpha$. The constant lemma gives $e^A/k$ and $k(B)^A/K$ purely inseparable. Pull the
   curve and sections to $B$, naming it $v:V\to B$. Semistable marked base change retains the
   fibre and section assertions; quasi-splitting persists by its base-change clause. The smooth
   geometrically integral generic fibre persists since $B\to S_4$ is dominant. Step 6 proves $V$
   integral. In Steps 7--8 take $J'=J=G$, $N=1$, and the purely inseparable field extension
   $k(B)/k(S_4)$; the same calculation proves $k(V)^A/F$ purely inseparable.
   Uses: lem-sfb-normal-alteration-constant-regularization, lem-trf-semistable-marked-base-change,
   lem-sfb-nodal-finite-quasi-splitting.
11. Let $c:V\to C$ and $b:B\to Y$ be the composites already constructed. The fibre-product
   diagrams give $gc=bv$, and all maps are equivariant via $\alpha$. The map $v$ is H-projective
   by base change. Constant regularization explicitly supplies H-projectivity of $b$. Since $Y$ is
   H-projective over $k$, composition makes $B$ H-projective over $k$. The graph of $B\to S$ is
   closed because $S/k$ is separated; combining it with a projective embedding of $B/k$ proves
   $B\to S$ H-projective. Its base change $P\times_S B\to P$ is H-projective. Likewise an
   embedding $V\hookrightarrow\mathbf P^n_B$ and the map $V\to P\times_S B$ give a closed graph
   embedding into $\mathbf P^n_B\times_B(P\times_S B)$, since the target is separated over $B$.
   Thus evaluation is H-projective, and composition with $P\times_S B\to P\to C$ proves $c$
   H-projective. Projectivity implies properness. Both $c,b$ are dominant with finite function-
   field extensions: the auxiliary cover and all subsequent generic changes are finite. Proper
   closed image proves surjectivity. The generic-finite-neighbourhood lemma gives finiteness over
   dense opens, so $c,b$ are alterations.
   Uses: lem-pc-projective-base-change, lem-trf-h-projective-composition, lem-pc-projective-
   proper, lem-weil-pbc-proper-closed-image, lem-weil-pbc-generic-finite-morphism-open-
   neighborhood, lem-sfb-normal-alteration-constant-regularization.
12. Let $J_B=\bigcup_i s_i(B)$. The generic identification in stable pointed extension and the
   generic evaluation show that the reduced inverse image of $E$ on the generic fibre of $V/B$ is
   contained in these marked points. The closed set $c^{-1}E$ has finitely many irreducible
   components, since $V$ is Noetherian. A component dominating $B$ lies in $J_B$: its generic
   point does, and $J_B$ is closed (a finite union of sections of a separated morphism). Every
   other component has proper closed image by properness of $v$. The nonsmooth locus is closed by
   the nodal Fitting-locus lemma, and has proper closed image because the generic curve is smooth.
   Let $D$ be the union of these finitely many images and all their $G$-translates. Each image
   misses the generic point of the integral base, so $D$ is invariant, closed and nowhere dense.
   It has $c^{-1}E\subseteq v^{-1}D\cup J_B$, and $v$ is smooth over $B\setminus D$.
   Uses: lem-weil-pbc-noetherian-finitely-many-components, lem-weil-pbc-proper-closed-image, lem-
   trf-nodal-family-fitting-singular, lem-sfb-stable-pointed-generic-extension, lem-sfb-high-
   genus-equivariant-cover.
13. For arbitrary $B'\to B$, projectivity is preserved, and semistable marked base change
   preserves flatness, finite presentation, pure relative dimension one, nodal geometric fibres
   and smooth disjoint markings. Nonemptiness, geometric connectedness and reducedness are
   properties of the geometric fibres and persist on extending their algebraically closed fields.
   Quasi-splitting persists by the quasi-splitting lemma: rational nodes and their two rational
   branches remain rational after residue-field extension. The equations $v s_i=1_B$ pull back to
   section equations. This persistence does not require the inverse image of $D$ to be nowhere
   dense or the new generic fibre to lie outside it. If $\dim Y=0$, the constant regularization
   clause gives $B=\operatorname{Spec}e$. Its sole fibre is the smooth generic fibre, and all
   points of $c^{-1}E$ are marked; hence the construction of Step 12 gives $D=\varnothing$.
   Uses: lem-pc-projective-base-change, lem-trf-semistable-marked-base-change, lem-sfb-nodal-
   finite-quasi-splitting, lem-sfb-normal-alteration-constant-regularization.
-/
theorem exists_equivariant_single_curve_nodal_reduction
    (k : Type u) [Field k] (Y C : Scheme.{u})
    (pY : Y ⟶ Spec (.of k)) (pC : C ⟶ Spec (.of k))
    [IsIntegral Y] [IsIntegral C] [IsHProjective pY] [GeometricallyIntegral pY]
    [IsProper pC]
    (hnormal : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
      IsIntegrallyClosed (Y.presheaf.stalk y))
    (g : C ⟶ Y) [IsProper g] [IsDominant g] (hg : g ≫ pY = pC)
    [GeometricallyIntegral (g.fiberToSpecResidueField (genericPoint Y))]
    (hdim : topologicalKrullDim (g.fiber (genericPoint Y)) = 1)
    (H : Type v) [Group H] [Finite H]
    (σk : H →* (k ≃+* k)) (σC : H →* Aut C) (σY : H →* Aut Y)
    (hC : ∀ h : H, (σC h).hom ≫ pC =
      pC ≫ Spec.map (CommRingCat.ofHom (σk h⁻¹).toRingHom))
    (hY : ∀ h : H, (σY h).hom ≫ pY =
      pY ≫ Spec.map (CommRingCat.ofHom (σk h⁻¹).toRingHom))
    (heq : ∀ h : H, (σC h).hom ≫ g = g ≫ (σY h).hom)
    (E : Closeds C) (hE : IsNowhereDense (E : Set C))
    (hEstable : ∀ h : H, (σC h).hom '' (E : Set C) = (E : Set C)) :
    ∃ (e : Type u) (_ : Field e) (_ : Algebra k e), Module.Finite k e ∧
      ∃ (G : Type (max u v)) (_ : Group G) (_ : Finite G) (α : G →* H)
        (γ : G →* (e ≃+* e)), Function.Surjective α ∧
        (∀ (a : G) (z : k), γ a (algebraMap k e z) = algebraMap k e (σk (α a) z)) ∧
        (∃ K : IntermediateField k e,
          (∀ z : e, z ∈ K ↔ ∀ a : α.ker, γ a.val z = z) ∧
          IsPurelyInseparable k K) ∧
        ∃ (B V : Scheme.{u}) (_ : IsIntegral B) (_ : IsIntegral V)
          (q : B ⟶ Spec (.of e)) (v : V ⟶ B) (b : B ⟶ Y) (c : V ⟶ C)
          (τB : G →* Aut B) (τV : G →* Aut V),
          IsHProjective q ∧ GeometricallyIntegral q ∧
          (∀ t : B, IsDomain (B.presheaf.stalk t) ∧
            IsIntegrallyClosed (B.presheaf.stalk t)) ∧
          b ≫ pY = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k e)) ∧
          c ≫ g = v ≫ b ∧
          (∀ a : G, (τB a).hom ≫ q =
            q ≫ Spec.map (CommRingCat.ofHom (γ a⁻¹).toRingHom)) ∧
          (∀ a : G, (τV a).hom ≫ v = v ≫ (τB a).hom) ∧
          (∀ a : G, (τB a).hom ≫ b = b ≫ (σY (α a)).hom) ∧
          (∀ a : G, (τV a).hom ≫ c = c ≫ (σC (α a)).hom) ∧
          IsHProjective b ∧ IsProper b ∧ Surjective b ∧ IsDominant b ∧
          IsHProjective c ∧ IsProper c ∧ Surjective c ∧ IsDominant c ∧
          (∃ U : Y.Opens, Dense (U : Set Y) ∧ IsFinite (b ∣_ U)) ∧
          (∃ U : C.Opens, Dense (U : Set C) ∧ IsFinite (c ∣_ U)) ∧
          (∃ (hb : b (genericPoint B) = genericPoint Y)
              (_ : Algebra Y.functionField B.functionField),
            algebraMap Y.functionField B.functionField =
              (Y.presheaf.stalkSpecializes (specializes_of_eq hb) ≫
                b.stalkMap (genericPoint B)).hom ∧
            Module.Finite Y.functionField B.functionField ∧
            ∃ K : IntermediateField Y.functionField B.functionField,
              (∀ z : B.functionField, z ∈ K ↔
                ∀ a : α.ker, (Scheme.functionFieldAut (τB a.val)).hom z = z) ∧
              IsPurelyInseparable Y.functionField K) ∧
          (∃ (hc : c (genericPoint V) = genericPoint C)
              (_ : Algebra C.functionField V.functionField),
            algebraMap C.functionField V.functionField =
              (C.presheaf.stalkSpecializes (specializes_of_eq hc) ≫
                c.stalkMap (genericPoint V)).hom ∧
            Module.Finite C.functionField V.functionField ∧
            ∃ K : IntermediateField C.functionField V.functionField,
              (∀ z : V.functionField, z ∈ K ↔
                ∀ a : α.ker, (Scheme.functionFieldAut (τV a.val)).hom z = z) ∧
              IsPurelyInseparable C.functionField K) ∧
          IsHProjective v ∧ Flat v ∧
          Smooth (v.fiberToSpecResidueField (genericPoint B)) ∧
          GeometricallyIntegral (v.fiberToSpecResidueField (genericPoint B)) ∧
          ∃ (m : ℕ) (s : Fin m → (B ⟶ V)) (hs : ∀ j, s j ≫ v = 𝟙 B)
            (D : Closeds B) (hfp : LocallyOfFinitePresentation v),
            HasNodalGeometricFibres v ∧
            (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ B),
              IsReduced (pullback v t) ∧ (pullback v t).IsPureDimension 1) ∧
            HasQuasiSplitNodalFibres v ∧
            Pairwise (fun j l : Fin m ↦ Disjoint (Set.range (s j)) (Set.range (s l))) ∧
            (∀ j : Fin m, Set.range (s j) ⊆ (v.smoothLocus : Set V)) ∧
            (∀ a : G, (τV a).hom '' (⋃ j : Fin m, Set.range (s j)) =
              ⋃ j : Fin m, Set.range (s j)) ∧
            IsNowhereDense (D : Set B) ∧
            (∀ a : G, (τB a).hom '' (D : Set B) = (D : Set B)) ∧
            Smooth (v ∣_ (⟨(D : Set B)ᶜ, D.isClosed.isOpen_compl⟩ : B.Opens)) ∧
            c ⁻¹' (E : Set C) ⊆ v ⁻¹' (D : Set B) ∪ ⋃ j : Fin m, Set.range (s j) ∧
            (∀ (B' : Scheme.{u}) (a : B' ⟶ B),
              IsHProjective (pullback.snd v a) ∧ Flat (pullback.snd v a) ∧
              ∃ hfp' : LocallyOfFinitePresentation (pullback.snd v a),
                HasNodalGeometricFibres (pullback.snd v a) ∧
                (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ B'),
                  IsReduced (pullback (pullback.snd v a) t) ∧
                  (pullback (pullback.snd v a) t).IsPureDimension 1) ∧
                HasQuasiSplitNodalFibres (pullback.snd v a) ∧
                (∀ j : Fin m, v.baseChangeSection (s j) (hs j) a ≫ pullback.snd v a = 𝟙 B') ∧
                Pairwise (fun j l : Fin m ↦
                  Disjoint (Set.range (v.baseChangeSection (s j) (hs j) a))
                    (Set.range (v.baseChangeSection (s l) (hs l) a))) ∧
                ∀ j : Fin m, Set.range (v.baseChangeSection (s j) (hs j) a) ⊆
                  ((pullback.snd v a).smoothLocus : Set (pullback (C := Scheme.{u}) v a))) ∧
            (topologicalKrullDim Y = 0 → IsIso q ∧ (D : Set B) = ∅) := by
  sorry

end AlgebraicGeometry
