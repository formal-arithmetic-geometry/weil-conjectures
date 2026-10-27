/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.StalkAut
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.FieldTheory.FieldTower
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.FieldTheory.FiniteGaloisReceivingSeparableExtensions
import WeilConjectures.FieldTheory.TensorFieldExtensionGaloisInvariants
import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalizationDominantLift
import Sheaf.AlgebraicGeometry.SpecSurjectiveBaseChange
import Sheaf.AlgebraicGeometry.ProjectiveLineGenusZero
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.FieldTheory.Normal.Basic

/-! # A finite equivariant cover with high-genus fibre components

Source: de Jong, Families of curves and alterations, §§3.2--3.6, pp.605--608.
(blueprint: lem-sfb-high-genus-equivariant-cover)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- The finite auxiliary cover before stable pointed extension. Actions can be nonfaithful
and semilinear. The algebra maps on function fields are precisely the transported generic
stalk maps, and their ranges are the fixed sets of the kernel of the group surjection.
The marking is rationalized only on the generic fibre; no flat or nodal model is asserted.

Source: de Jong, Families of curves and alterations, §§3.2--3.6, pp.605--608.
(blueprint: lem-sfb-high-genus-equivariant-cover)

Proof (the node's thirteen steps):
1. Apply the local-pencil lemma with the trivial group $J$ and with the reduced generic marking.
   It supplies a finite separable extension $E_0/K$, the normalizations $S_{E_0},P_{E_0}$, and
   finitely many local finite pencils whose generic fibres are etale above $0,1,\infty$ and avoid
   the marking. In positive base dimension $E_0=K$; the field-base clause deals with dimension
   zero, including finite fields. Choose a prime $\ell\geq5$ different from the characteristic
   (one of $5,7$ suffices). We will use the same $\ell$ on every open; our base is over a field,
   so it is invertible everywhere.
   Uses: lem-sfb-invariant-local-curve-pencils.
2. Put $B=K^H$. By the finite-field-action lemma, applied to the image of $H$ on $K$, $K/B$ is
   finite Galois. Transitivity of separability makes $E_0/B$ finite separable. A primitive
   $\ell$th root of unity is separable over $B$, since $T^\ell-1$ has nonzero derivative at every
   root. The common-Galois-extension lemma gives a finite Galois extension $K_0/B$ containing
   $E_0$ and this root. Define $H_0=\{(h,\sigma)\in
   H\times\operatorname{Aut}_B(K_0):\sigma|_K=h|_K\}$. Normal-subextension lifting proves
   $H_0\twoheadrightarrow H$. Its kernel $A_0$ is exactly $\operatorname{Aut}_K(K_0)$. The
   intermediate-extension lemma and finite-Galois fixed-field lemma give $K_0^{A_0}=K$.
   Uses: lem-wf-finite-field-action-fixed-degree, lem-zl-separable-permanence, lem-weil-pbc-
   finite-galois-receiving-separable-extensions, lem-weil-pbc-normal-subextension-automorphism-
   extends, lem-dl-a1-galois-over-intermediate, lem-weil-pbc-finite-galois-fixed-field.
3. Apply the finite normal-model lemma with $L=F\otimes_KK_0$, $E=K_0$, using its scalar-extension
   clause. Denote this field by $F_0$, and the resulting models by $P_0\to S_0$. They are normal
   integral, $S_0/k$ is projective, $P_0/S_0$ is H-projective with pure curve fibres, and $P_0\to
   P\times_SS_0$ is finite surjective. Its generic fibre is $P_K\times_KK_0$. The action
   $(h,\sigma)(f\otimes c)=h(f)\otimes\sigma(c)$ extends to these models by the functoriality
   clause. On $A_0$ it acts only on the second factor. Tensor invariants therefore give
   $F_0^{A_0}=F$. The lemma's final factorization clause gives a finite map from $P_0$ to
   $P_{E_0}$, over $S_0\to S_{E_0}$. Pull back the affine cover from step 1 and compose its
   pencils with this finite map. On the generic fibre the map is just scalar extension, so their
   avoidance persists. The finite-etale algebra criterion writes the three special generic fibres
   as products of finite separable fields; a separable minimal polynomial remains coprime to its
   derivative after scalar extension, proving their etaleness after that extension. Write $M_0$
   for the reduced generic inverse image of $M$.
   Uses: lem-sfb-finite-normal-relative-curve-model, lem-weil-pbc-tensor-field-extension-galois-
   invariants, lem-sc-finite-etale-algebra-criterion, lem-trf-finite-radicial-basechange.
4. For these finitely many pencils let $x_i\in F_0$ be the pullback of the affine coordinate, and
   take the finite list of all $h(x_i)$ and $h(x_i-1)$ for $h\in H_0$. None is zero, because each
   pencil is surjective. The support of the zeros and poles of every member lies in the union $D$
   of the $H_0$-translates of the inverse images of $0,1,\infty$. Each such inverse image is
   reduced finite etale over $K_0$, by step 1 and its scalar extension in step 3. Their reduced
   union $D$ is again finite etale: its residue fields are among those of the finite list of
   closed points. It misses $M_0$, since $H_0$ preserves that marking. Put
   $L=F_0(\sqrt[\ell]{h(x_i)},\sqrt[\ell]{h(x_i-1)}:i,h)$ inside an algebraic closure. The tame
   radical-normalization lemma gives a smooth generic covering curve, unramified over $M_0$. Its
   constant field $E=\{z\in L:z\text{ algebraic over }K_0\}$ is finite separable over $K_0$, and
   the curve viewed over $E$ is smooth projective geometrically integral. It also gives $E\cap
   F_0=K_0$.
   Uses: lem-sfb-tame-radical-curve-normalization.
5. The field $L$ is normal over $B_0=F_0^{H_0}$. To check this explicitly, an embedding over $B_0$
   sends $F_0$ to itself, since $F_0/B_0$ is Galois by the finite-field-action lemma applied to
   the image of $H_0$. It restricts there to the action of some $h\in H_0$. Every adjoined root is
   then sent to a root of a polynomial $T^\ell-h(a)$ from the same list. All these roots lie in
   $L$, since $F_0$ contains every $\ell$th root of unity. Thus every embedding sends $L$ into
   $L$, and onto it by finite dimension. Equivalently, adjoining the roots of all orbit
   polynomials, together with the splitting polynomials defining $F_0/B_0$, realizes $L$ as a
   splitting field over $B_0$. The extension is finite separable by the tower lemma and the tame
   lemma. Define $J_1=\{(h,\tau)\in H_0\times\operatorname{Aut}_{B_0}(L):\tau|_{F_0}=h|_{F_0}\}$.
   The intermediate-isomorphism lifting lemma makes $J_1\twoheadrightarrow H_0$ surjective; this
   allows nonfaithful actions. Its kernel $N_1=\operatorname{Aut}_{F_0}(L)$ has $L^{N_1}=F_0$ by
   the finite-Galois fixed-field lemma.
   Uses: lem-wf-finite-field-action-fixed-degree, lem-sfb-tame-radical-curve-normalization, lem-
   zl-separable-permanence, lem-sfb-normal-intermediate-isomorphism-lifts, lem-weil-pbc-finite-
   galois-fixed-field.
6. Each member of $J_1$ preserves $E$, because it preserves $K_0$ and carries algebraic elements
   to algebraic elements. Apply the finite normal-model lemma to $P_0/S_0$, $L/F_0$, and $E/K_0$.
   Call its models $Q_1/S_1$. It gives finite surjections $S_1\to S_0$ and $Q_1\to
   P_0\times_{S_0}S_1$, H-projectivity and pure one-dimensional geometric fibres, and the required
   smooth geometrically integral generic curve over $E$. Functoriality extends the $J_1$-actions
   to the diagram. The generic marking on $Q_1$ is reduced finite etale over $E$ by the tame
   lemma. Also $E^{N_1}=E\cap L^{N_1}=E\cap F_0=K_0$; the two intersections are inside $L$.
   Uses: lem-sfb-finite-normal-relative-curve-model, lem-sfb-tame-radical-curve-normalization.
7. The primitive root of unity in $K_0$ is a section on every affine open of $S_0$: it is integral
   over its coordinate ring, which is normal and has fraction field $K_0$. On an open $U_i$ from
   step 3 take the relative Fermat covering $C_i\to\mathbf P^1_{U_i}$. Its two radical generators
   embed into $L$ by construction (use the identity translate in the root list). There is a finite
   map $(Q_1)_{U_i}\to C_i$. Indeed, the composite $(Q_1)_{U_i}\to(P_0)_{U_i}\to\mathbf P^1_{U_i}$
   is finite. Over an affine of the line write its normal source as $\operatorname{Spec}R$ and the
   Fermat cover as $\operatorname{Spec}A$. An element of $A$, mapped into $L$, is integral over
   the base affine ring, hence integral over $R$; normality puts it in $R$. These maps glue, since
   their restrictions to $L$ agree. A finite set of base-ring generators for $R$ still generates
   it as an $A$-module, proving finiteness. Each geometric fibre of $C_i/U_i$ is smooth of genus
   $(\ell-1)(\ell-2)/2\geq2$.
   Uses: lem-sfb-fermat-kummer-relative-curve, lem-sfb-finite-normal-relative-curve-model, lem-
   trf-finite-radicial-basechange.
8. Let $s$ be a geometric point of $S_1$ and let $T$ be the reduced scheme of an irreducible
   component of $(Q_1)_s$. Choose $i$ so that its image in $S_0$ lies in $U_i$. The map in step 7
   restricts to a finite map $T\to(C_i)_s$. It is nonconstant: $T$ has dimension one by step 6,
   whereas a fibre of a finite morphism has dimension zero (its coordinate algebra over a field is
   finite-dimensional). Consequently it is dominant onto the integral target curve. By the
   normalization-existence and normalized-curve-smooth lemmas, $T^\nu$ is a smooth proper integral
   curve of dimension one over the algebraically closed residue field. Composing $T^\nu\to T$ with
   the finite map gives a nonconstant map to $(C_i)_s$. Genus monotonicity gives $g(T^\nu)\geq
   g((C_i)_s)\geq2$. This also works for fibres at nonclosed points and arbitrary algebraically
   closed fields, as the Fermat statement covers all geometric fibres.
   Uses: lem-sc-normalization-exists, lem-sc-normalized-curve-smooth, lem-sfb-finite-curve-genus-
   monotonicity, lem-trf-finite-radicial-basechange.
9. We now rationalize the generic marking. The finite-etale algebra criterion writes its
   coordinate algebra as a finite product of finite separable extensions of $E$; use this finite
   list of residue fields. Put $B_1=E^{J_1}$. The finite-field-action lemma gives $E/B_1$ finite
   Galois, after replacing $J_1$ by its finite image. By transitivity all these residue fields are
   finite separable over $B_1$. Choose a common finite Galois extension $K_2/B_1$ receiving them
   and $E$. Define $H_2=\{(j,\sigma)\in J_1\times\operatorname{Aut}_{B_1}(K_2):\sigma|_E=j|_E\}$.
   Normal-subextension lifting gives $H_2\twoheadrightarrow J_1$. Its kernel
   $N_2=\operatorname{Aut}_E(K_2)$ satisfies $K_2^{N_2}=E$ by the intermediate-extension and
   fixed-field lemmas. The case of empty marking simply requires a common extension receiving $E$.
   Uses: lem-sc-finite-etale-algebra-criterion, lem-wf-finite-field-action-fixed-degree, lem-zl-
   separable-permanence, lem-weil-pbc-finite-galois-receiving-separable-extensions, lem-weil-pbc-
   normal-subextension-automorphism-extends, lem-dl-a1-galois-over-intermediate, lem-weil-pbc-
   finite-galois-fixed-field.
10. Apply the scalar-extension clause of the finite normal-model lemma to $Q_1/S_1$, with constant
   field extension $K_2/E$. It gives $S_2=\operatorname{Nor}_{K_2}(S_1)$ and
   $Q_2=\operatorname{Nor}_{L_2}(Q_1)$ with $L_2=L\otimes_EK_2$ a field, finite maps, pure curve
   fibres and smooth geometrically integral generic curve. The latter is exactly the previous
   generic curve after extending scalars, so its reduced inverse marking is a set of distinct
   $K_2$-rational points. Normality of $K_2/B_1$ ensures every $E$-embedding of each marking
   residue field has image in $K_2$; its separable minimal polynomial therefore splits into
   distinct linear factors there. The action $(j,\sigma)(z\otimes c)=j(z)\otimes\sigma(c)$ extends
   to $Q_2/S_2$ by functoriality, preserving this set. Tensor invariants give $L_2^{N_2}=L$. Every
   geometric component of $Q_2/S_2$ maps finitely and nonconstantly to a component of a geometric
   fibre of $Q_1/S_1$ (pure dimension one on the source and finite fibres exclude a point image).
   Lift the induced map to the target component's normalization and apply genus monotonicity as in
   step 8. Its normalization thus also has genus at least two.
   Uses: lem-sfb-finite-normal-relative-curve-model, lem-weil-pbc-tensor-field-extension-galois-
   invariants, lem-sc-normalization-exists, lem-sc-normalized-curve-smooth, lem-sbc-normalization-
   dominant-lift, lem-sfb-finite-curve-genus-monotonicity.
11. Let $A'=\ker(J_1\to H)$, with $J_1\to H$ the composite through $H_0$. The map $A'\to A_0$ is
   surjective with kernel $N_1$. Thus, using steps 3,5,6, an element fixed by $A'$ first lies in
   $L^{N_1}=F_0$, and then is fixed by $A_0$; conversely each element of $F$ is fixed. Hence
   $L^{A'}=F$. On constants the same argument gives $E^{A'}=K_0^{A_0}=K$. Put $A_2=\ker(H_2\to
   H)$. The map $A_2\to A'$ is surjective with kernel $N_2$. Steps 9--10 now give
   $L_2^{A_2}=(L_2^{N_2})^{A'}=L^{A'}=F$ and $K_2^{A_2}=(K_2^{N_2})^{A'}=E^{A'}=K$. These
   equalities use the embeddings induced by the constructed diagram, not arbitrary identifications
   of abstract fields.
12. All total and base function-field extensions in the construction are finite separable: the
   constant ones were chosen so, the radical one is so by the tame lemma, and the remaining ones
   are finite separable scalar extensions (equivalently they are generated by elements annihilated
   by the same separable polynomials after changing coefficients). Transitivity gives $L_2/F$ and
   $K_2/K$ finite separable. The composite $S_2\to S$ is finite surjective. To check the total map
   targets the full base change, first base change the finite surjection $P_0\to P\times_SS_0$ to
   $S_2$; then compose it with the base change to $S_2$ of $Q_1\to P_0\times_{S_0}S_1$ and with
   $Q_2\to Q_1\times_{S_1}S_2$. Each is finite surjective by the model lemma and finite-surjective
   base change. Their composite is $Q_2\to P\times_SS_2$. The model lemma already gives $S_2$
   normal integral projective over $k$, and $Q_2/S_2$ H-projective with pure curve fibres.
   Uses: lem-sfb-tame-radical-curve-normalization, lem-sfb-finite-normal-relative-curve-model,
   lem-zl-separable-permanence, lem-trf-finite-radicial-basechange, lem-weil-pbc-spec-surjective-
   base-change.
13. Finally suppose $u:\mathbf P^1_\Omega\to(Q_2)_s$ were nonconstant for a geometric fibre. Its
   image lies in an irreducible component, and the morphism factors through that component with
   its reduced structure, because the source is integral and reduced. A nonconstant image has
   dimension one, so it is dominant onto that component $T$. The normalization-lifting lemma lifts
   $u$ to $T^\nu$ because $\mathbf P^1_\Omega$ is normal: on its two affine charts $\Omega[t]$, a
   reduced fraction satisfying a monic polynomial must have constant denominator, so these chart
   rings are integrally closed. Normalization and smoothness of $T^\nu$ are as in step 8. Genus
   monotonicity and the projective-line genus computation give $0=g(\mathbf P^1_\Omega)\geq
   g(T^\nu)\geq2$, a contradiction. Rename $S_2,Q_2,K_2,H_2$ as the requested $S_1,Q,K_1,H_1$,
   with $\beta:H_2\to H$ the composite surjection. Steps 10--12 give every asserted clause. No
   stable reduction or extension of sections has entered the construction.
   Uses: lem-sbc-normalization-dominant-lift, lem-sc-normalization-exists, lem-sc-normalized-
   curve-smooth, lem-asd-projective-line-genus-zero, lem-sfb-finite-curve-genus-monotonicity.
-/
theorem exists_high_genus_equivariant_cover
    (k : Type u) [Field k] (S P : Scheme.{u})
    (pS : S ⟶ Spec (.of k)) (pP : P ⟶ Spec (.of k))
    [IsIntegral S] [IsIntegral P] [IsHProjective pS]
    [LocallyOfFiniteType pS] [QuasiCompact pS]
    [LocallyOfFiniteType pP] [QuasiCompact pP]
    (hnormal : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (f : P ⟶ S) [IsHProjective f] (hf : f ≫ pS = pP)
    (hpure : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      (pullback (C := Scheme.{u}) f s).IsPureDimension 1)
    [Smooth (pullback.snd f S.fromSpecFunctionField)]
    [GeometricallyIntegral (pullback.snd f S.fromSpecFunctionField)]
    (M : Closeds P)
    (hMfinite : IsFinite
      ((Scheme.IdealSheafData.vanishingIdeal
        (M.preimage (pullback.fst f S.fromSpecFunctionField).continuous)).subschemeι ≫
          pullback.snd f S.fromSpecFunctionField))
    (hMetale : Etale
      ((Scheme.IdealSheafData.vanishingIdeal
        (M.preimage (pullback.fst f S.fromSpecFunctionField).continuous)).subschemeι ≫
          pullback.snd f S.fromSpecFunctionField))
    (H : Type v) [Group H] [Finite H]
    (σk : H →* (k ≃+* k)) (σP : H →* Aut P) (σS : H →* Aut S)
    (hP : ∀ h : H, (σP h).hom ≫ pP =
      pP ≫ Spec.map (CommRingCat.ofHom (σk h⁻¹).toRingHom))
    (hS : ∀ h : H, (σS h).hom ≫ pS =
      pS ≫ Spec.map (CommRingCat.ofHom (σk h⁻¹).toRingHom))
    (hequiv : ∀ h : H, (σP h).hom ≫ f = f ≫ (σS h).hom)
    (hMstable : ∀ h : H, (σP h).hom '' (M : Set P) = (M : Set P)) :
    ∃ (S₁ Q : Scheme.{u}) (_ : IsIntegral S₁) (_ : IsIntegral Q)
      (b : S₁ ⟶ S) (c : Q ⟶ P) (q : Q ⟶ S₁) (r : Q ⟶ pullback (C := Scheme.{u}) f b)
      (H₁ : Type (max u v)) (_ : Group H₁) (_ : Finite H₁)
      (β : H₁ →* H) (τS : H₁ →* Aut S₁) (τQ : H₁ →* Aut Q),
      Function.Surjective β ∧
      (∀ s : S₁, IsDomain (S₁.presheaf.stalk s) ∧
        IsIntegrallyClosed (S₁.presheaf.stalk s)) ∧
      IsHProjective (b ≫ pS) ∧ LocallyOfFiniteType (b ≫ pS) ∧ QuasiCompact (b ≫ pS) ∧
      LocallyOfFiniteType (c ≫ pP) ∧ QuasiCompact (c ≫ pP) ∧
      IsFinite b ∧ Surjective b ∧ IsFinite r ∧ Surjective r ∧
      r ≫ pullback.fst f b = c ∧ r ≫ pullback.snd f b = q ∧
      (∀ h : H₁, (τS h).hom ≫ b = b ≫ (σS (β h)).hom) ∧
      (∀ h : H₁, (τQ h).hom ≫ c = c ≫ (σP (β h)).hom) ∧
      (∀ h : H₁, (τQ h).hom ≫ q = q ≫ (τS h).hom) ∧
      IsHProjective q ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S₁),
        (pullback (C := Scheme.{u}) q s).IsPureDimension 1) ∧
      Smooth (pullback.snd q S₁.fromSpecFunctionField) ∧
      GeometricallyIntegral (pullback.snd q S₁.fromSpecFunctionField) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S₁)
          (Z : irreducibleComponents (pullback (C := Scheme.{u}) q s)),
        2 ≤ @Scheme.arithmeticGenus Ω _
          ((pullback (C := Scheme.{u}) q s).reducedNormalizationComponent Z).normalization
          ⟨((pullback (C := Scheme.{u}) q s).reducedNormalizationComponent Z).fromNormalization ≫
            (Scheme.IdealSheafData.vanishingIdeal
              ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι ≫
                pullback.snd q s⟩) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S₁)
          (t : ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of Ω)) ⟶ pullback (C := Scheme.{u}) q s),
        t ≫ pullback.snd q s =
            ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of Ω)) ↘ Spec (.of Ω) →
          ∃ x : Spec (.of Ω) ⟶ pullback (C := Scheme.{u}) q s,
            x ≫ pullback.snd q s = 𝟙 _ ∧
            t = (ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of Ω)) ↘ Spec (.of Ω)) ≫ x) ∧
      (∃ (n : ℕ)
          (p : Fin n →
            (Spec S₁.functionField ⟶ pullback (C := Scheme.{u}) q S₁.fromSpecFunctionField)),
        (∀ i : Fin n, p i ≫ pullback.snd q S₁.fromSpecFunctionField = 𝟙 _) ∧
        Function.Injective p ∧
        (∀ z : pullback (C := Scheme.{u}) q S₁.fromSpecFunctionField,
          c (pullback.fst q S₁.fromSpecFunctionField z) ∈ M ↔
            ∃ i : Fin n, z ∈ Set.range (p i)) ∧
        ∀ h : H₁, (τQ h).hom ''
            (⋃ i : Fin n, Set.range (p i ≫ pullback.fst q S₁.fromSpecFunctionField)) =
          ⋃ i : Fin n, Set.range (p i ≫ pullback.fst q S₁.fromSpecFunctionField)) ∧
      (∃ (hb : b (genericPoint S₁) = genericPoint S)
          (_ : Algebra S.functionField S₁.functionField),
        algebraMap S.functionField S₁.functionField =
          (S.presheaf.stalkSpecializes (specializes_of_eq hb) ≫
            b.stalkMap (genericPoint S₁)).hom ∧
        Module.Finite S.functionField S₁.functionField ∧
        Algebra.IsSeparable S.functionField S₁.functionField ∧
        ∀ z : S₁.functionField,
          z ∈ Set.range (algebraMap S.functionField S₁.functionField) ↔
            ∀ a : β.ker, (Scheme.functionFieldAut (τS a.val)).hom z = z) ∧
      (∃ (hc : c (genericPoint Q) = genericPoint P)
          (_ : Algebra P.functionField Q.functionField),
        algebraMap P.functionField Q.functionField =
          (P.presheaf.stalkSpecializes (specializes_of_eq hc) ≫
            c.stalkMap (genericPoint Q)).hom ∧
        Module.Finite P.functionField Q.functionField ∧
        Algebra.IsSeparable P.functionField Q.functionField ∧
        ∀ z : Q.functionField,
          z ∈ Set.range (algebraMap P.functionField Q.functionField) ↔
            ∀ a : β.ker, (Scheme.functionFieldAut (τQ a.val)).hom z = z) := by
  sorry

end AlgebraicGeometry
