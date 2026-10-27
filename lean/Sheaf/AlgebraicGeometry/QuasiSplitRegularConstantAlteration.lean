/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q93
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.StalkAut
public import Sheaf.FieldTheory.FieldTower
public import Sheaf.AlgebraicGeometry.StablePointedCurve
public import Sheaf.AlgebraicGeometry.QuasiSplitNodalFibres
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.ProjectiveGenericallyFinite
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import Sheaf.FieldTheory.CurveFieldKernelInvariantTower
import Sheaf.AlgebraicGeometry.FiniteEquivariantQuasiSplitNodalFibres
import Sheaf.AlgebraicGeometry.NormalAlterationConstantRegularization
import Sheaf.AlgebraicGeometry.StablePointedGenericExtension
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-! # Quasi-split stable curves with regular constants

Source: de Jong, Families of curves and alterations (1997), Lemmas 5.5 and 5.7,
pp. 614--615, §3.11 and the final pullback in Theorem 5.9, p. 617
(blueprint: lem-sfb-quasisplit-regular-constant-alteration).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Simultaneous finite quasi-splitting and radicial regularization of constants,
with the canonical pulled-back family and its diagonal action.
Source: de Jong (1997), Lemmas 5.5 and 5.7, pp. 614--615, §3.11 and Theorem 5.9, p. 617
(blueprint: lem-sfb-quasisplit-regular-constant-alteration).

All algebra structures on function fields are identified with the maps of generic spectra.
Fixed fields are intermediate fields characterized elementwise. Semilinear actions use
inverse elements under the contravariant spectrum functor. No faithfulness is assumed.

Proof (the ten steps of the DAG node):
1. Apply [lem-sfb-nodal-finite-quasi-splitting] to $W\to S$ with the acting group $J$. Its
   hypotheses follow from [def-sfb-stable-pointed-curve] and the assumed H-projectivity and
   smooth geometrically integral generic fibre. Obtain $r:S_4\to S$ and
   $\rho:G\twoheadrightarrow J$ with $S_4$ normal integral projective, $r$ finite surjective
   generically etale, and $L_4^N=L$, where $L=k(S)$, $L_4=k(S_4)$, $N=\ker\rho$. The pulled-back
   family $W_4=W\times_S S_4$ has quasi-split fibres. Set $\alpha=\beta\rho$ and $A=\ker\alpha$.
   On every pullback use the diagonal action; on a pair $(x,t)$ it is $g(x,t)=(\rho(g)x,gt)$.
2. The finite dominant $r$ gives $[L_4:L]<\infty$: over a nonempty affine
   $\operatorname{Spec}R\subset S$, its inverse image is affine with domain coordinate ring $R'$
   finite over $R$; use [lem-trf-finite-domain-fraction-degree] and [lem-sc-integral-function-
   field-affine-fraction]. Since $b_0$ is finite over a dense open of $Y$, $b_4=b_0r$ is finite
   over that same open by [lem-weil-pbc-finite-composition]. It is proper by [lem-weil-pbc-
   finite-morphism-permanence](c), surjective since both factors are, and has finite function-
   field extension by the finite tower $K\subset L\subset L_4$. Thus $b_4:S_4\to Y$ is an
   equivariant alteration.
3. Put $D=k(W)$. Apply [lem-sfb-flat-curve-pullback-function-field] to $W\to S$ and $S_4\to S$.
   Flatness, reduced geometric fibres and dominance follow from the stable-curve conditions (the
   fibres are nonempty); the generic fibre is geometrically integral by hypothesis. It gives
   $W_4$ integral and $D_4=k(W_4)=D\otimes_L L_4$, finite over $D$. For later field
   calculations, $D\otimes_L T$ is a domain for every extension $T/L$: choose a nonempty affine
   chart $\operatorname{Spec}R$ in the geometrically integral generic fibre. By [def-pc-
   geometrically-irreducible], $R\otimes_L T$ is a domain. By [lem-sc-integral-function-field-
   affine-fraction], $D=\operatorname{Frac}R$, so $D\otimes_L T$ is the localization of
   $R\otimes_L T$ at $R\setminus\{0\}$, a multiplicative set avoiding zero. This also proves the
   same assertion for $D_4/L_4$ using its geometrically integral generic fibre.
4. Apply [lem-sfb-curve-field-kernel-invariant-tower] with $L,D,L'=L_4,J'=G,\rho$, the given
   $\beta:J\to H$, and the subfields $K=k(Y)$ and $F=k(C)$. Step 3 checks its domain hypothesis
   for every field extension; Step 2 checks finiteness, and Step 1 gives $(L')^N=L$, hence the
   required purely inseparable fixed-field extension. The assumed $L^{A_0}/K$ and $D^{A_0}/F$
   are precisely its two remaining hypotheses. The conclusion is $L_4^A/K$ and $D_4^A/F$ purely
   inseparable. The tensor action is the action induced by the diagonal scheme action, because
   on products of pulled-back rational functions it sends $d\otimes l$ to $\rho(g)d\otimes gl$.
5. Apply [lem-sfb-normal-alteration-constant-regularization] to $b_4:S_4\to Y$ and $\alpha:G\to
   H$. Step 2 gives an alteration, Step 1 gives normal integral projective finite-type $S_4$,
   and Step 4 gives $L_4^A/K$ purely inseparable. All hypotheses on $Y/k$ are given. Obtain
   $e/k$, $B/e$ and $q:B\to S_4$, with the same group $G$, as in that lemma. In particular $q$
   is finite radicial surjective, $M=k(B)$ is finite purely inseparable over $L_4$, $e^A/k$ and
   $M^A/K$ are purely inseparable, $b=b_4q$ is H-projective, and $\dim Y=0$ implies
   $B=\operatorname{Spec}e$. Its action on $e$ extends the original action on $k$, which factors
   through $\alpha$.
6. The composite $B\to S$ is finite by [lem-weil-pbc-finite-composition], so it is dominant (it
   is surjective), with finite function-field extension $M/L$. The scheme $B$ is H-projective
   over $k$: compose the H-projective $b$ of Step 5 with $Y/k$, using [lem-trf-h-projective-
   composition]. It is proper by [lem-kun-projective-implies-proper], hence of finite type by
   [def-weil-proper-morphism]. Apply [lem-sfb-flat-curve-pullback-function-field] to $W/S$ and
   $B\to S$. This gives the ordinary pullback $V=W\times_S B$ integral, with $k(V)=D\otimes_L M$
   finite over $D$. Associativity of tensor products identifies this field with
   $D_4\otimes_{L_4}M$, by $(d\otimes l)\otimes m\mapsto d\otimes lm$. Apply [lem-sfb-curve-
   field-kernel-invariant-tower] a second time to $L_4,D_4,M$, with the identity group
   surjection $G\to G$ and the map $\alpha:G\to H$. Here the new kernel is
   $\ker(\mathrm{id}_G)=\{1\}$, so its fixed field is $M$ itself; hence the kernel-fixed-field
   hypothesis is exactly the finite purely inseparable extension $M/L_4$ from Step 5. The
   further kernel stays $A=\ker\alpha$. Step 3 gives the domain hypothesis for $D_4/L_4$, and
   Step 4 gives both old invariant hypotheses. It follows that $k(V)^A/F$ is purely inseparable.
7. Pull the sections to $V/B$. The arbitrary-base-change clause of [lem-sfb-stable-pointed-
   generic-extension] preserves all stable pointed conditions, including disjoint smooth
   sections, also with no markings. Their union stays $G$-stable:
   $g(s_i(t),t)=(s_{\rho(g)i}(gt),gt)$. The arbitrary-base-change clause of [lem-sfb-nodal-
   finite-quasi-splitting], applied first over $S_4$, preserves quasi-splitting after $q$. The
   generic fibre is the old smooth geometrically integral curve extended from $L$ to $M$; its
   smoothness follows from the dominant-base-change clause of [lem-trf-semistable-marked-base-
   change] and its geometric integrality from Step 6. H-projectivity of $v$ follows by [lem-pc-
   projective-base-change].
8. The maps $b:B\to Y$ (Step 5) and $Y\to\operatorname{Spec}k$ are H-projective. Twice applying
   [lem-trf-h-projective-composition], also to $v$, gives an embedding
   $i:V\hookrightarrow\mathbf P^n_k$. Define $c=a_0\operatorname{pr}_W:V\to C$. Since $C/k$ is
   proper it is separated, by [def-weil-proper-morphism]. Apply [lem-weil-pbc-fibre-product-
   change-of-base-closed-immersion] with $X=V$, $T=C$, the two maps $c$ and $\mathrm{id}_C$, and
   $S=\operatorname{Spec}k$: the graph $V=V\times_C C\to V\times_k C$ is a closed immersion.
   Follow it by $i\times\mathrm{id}_C$, a closed immersion by [lem-weil-pbc-closed-immersion-
   base-change]. Composition is a closed immersion by [lem-weil-pbc-closed-immersion-comp], and
   [lemma-nagata-projective-space-base-change-pullback] identifies its target with $\mathbf
   P^n_C$. Its projection is $c$, so $c$ is H-projective. This is a two-embedding argument; it
   assumes no projectivity of $C/k$.
9. Both $b,c$ are proper by [lem-kun-projective-implies-proper]. They are dominant: $b$ is a
   composite of surjections, while $c$ has the injective field map $F\hookrightarrow
   D\hookrightarrow k(V)$ from Step 6. Their function-field extensions are finite, respectively
   the tower $K\subset L\subset L_4\subset M$ and $F\subset D\subset k(V)$. Their images are
   closed by [lem-weil-pbc-proper-closed-image]; a closed dense image is the whole integral
   target, so both are surjective. To check the dense-open finiteness explicitly, take a
   nonempty affine target open $\operatorname{Spec}R$ for either map; $R$ is a Noetherian domain
   by [lem-weil-pbc-finite-type-over-noetherian]. Its generic fibre has dimension zero: every
   nonempty affine chart of that fibre has a coordinate domain contained in the finite extension
   of target function fields. Every element is algebraic over the target field; a nonzero
   element has inverse given by its minimal polynomial with nonzero constant term, so that chart
   is a field. Now [lem-fin-projective-generically-finite], applied after restriction
   (projectivity persists by [lem-pc-projective-base-change]), gives finiteness over a nonempty
   open. This open is dense in the integral target. Thus $b,c$ are alterations in the stipulated
   sense.
10. All composites are equivariant by their construction. For the two projections of
   $V=W\times_S B$, the defining equality is $w\operatorname{pr}_W=(B\to S)v$. Composing
   $ga_0=b_0w$ with $\operatorname{pr}_W$ therefore gives $gc=bv$. The finite-cover fixed field
   $k(S_4)^{\ker\rho}=k(S)$ is Step 1; the three purely inseparable invariant extensions and the
   radicial field extension are Steps 4--6; all family properties are Step 7. The zero-
   dimensional assertion is the last clause supplied in Step 5. These are exactly the asserted
   data and conclusions.
-/
theorem exists_quasiSplit_regular_constant_alteration
    (k : Type u) [Field k] (Y C S W : Scheme.{u})
    [IsIntegral Y] [IsIntegral C] [IsIntegral S] [IsIntegral W]
    (pY : Y ⟶ Spec (.of k)) (pC : C ⟶ Spec (.of k)) (pS : S ⟶ Spec (.of k))
    [IsHProjective pY] [GeometricallyIntegral pY] [IsProper pC] [IsHProjective pS]
    (hYnormal : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
      IsIntegrallyClosed (Y.presheaf.stalk y))
    (hSnormal : ∀ t : S, IsDomain (S.presheaf.stalk t) ∧
      IsIntegrallyClosed (S.presheaf.stalk t))
    (g : C ⟶ Y) [IsProper g] (hg : g ≫ pY = pC)
    (hgdominant : g (genericPoint C) = genericPoint Y)
    (b₀ : S ⟶ Y) [IsProper b₀] [Surjective b₀] (hb₀ : b₀ ≫ pY = pS)
    (hb₀finite : ∃ U : Y.Opens, Dense (U : Set Y) ∧ IsFinite (b₀ ∣_ U))
    [Algebra Y.functionField S.functionField] [Module.Finite Y.functionField S.functionField]
    (hb₀field : Spec.map (CommRingCat.ofHom (algebraMap Y.functionField S.functionField)) ≫
      Y.fromSpecFunctionField = S.fromSpecFunctionField ≫ b₀)
    (f : W ⟶ S) [IsHProjective f]
    (n : ℕ) (s : Fin n → (S ⟶ W)) (hs : ∀ i : Fin n, s i ≫ f = 𝟙 S)
    (hstable : IsStablePointedCurve f s hs)
    [Smooth (f.fiberToSpecResidueField (genericPoint S))]
    [GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint S))]
    (a₀ : W ⟶ C) (ha₀ : a₀ ≫ g = f ≫ b₀)
    (ha₀dominant : a₀ (genericPoint W) = genericPoint C)
    [Algebra C.functionField W.functionField] [Module.Finite C.functionField W.functionField]
    (ha₀field : Spec.map (CommRingCat.ofHom (algebraMap C.functionField W.functionField)) ≫
      C.fromSpecFunctionField = W.fromSpecFunctionField ≫ a₀)
    (H : Type v) [Group H] [Finite H] (J : Type w) [Group J] [Finite J]
    (β : J →* H) (hβ : Function.Surjective β)
    (σk : H →* (k ≃+* k)) (σY : H →* Aut Y) (σC : H →* Aut C)
    (σS : J →* Aut S) (σW : J →* Aut W)
    (hY : ∀ h : H, (σY h).hom ≫ pY =
      pY ≫ Spec.map (CommRingCat.ofHom (σk h⁻¹).toRingHom))
    (hC : ∀ h : H, (σC h).hom ≫ pC =
      pC ≫ Spec.map (CommRingCat.ofHom (σk h⁻¹).toRingHom))
    (hS : ∀ j : J, (σS j).hom ≫ pS =
      pS ≫ Spec.map (CommRingCat.ofHom (σk (β j⁻¹)).toRingHom))
    (hgeq : ∀ h : H, (σC h).hom ≫ g = g ≫ (σY h).hom)
    (hb₀eq : ∀ j : J, (σS j).hom ≫ b₀ = b₀ ≫ (σY (β j)).hom)
    (hfeq : ∀ j : J, (σW j).hom ≫ f = f ≫ (σS j).hom)
    (ha₀eq : ∀ j : J, (σW j).hom ≫ a₀ = a₀ ≫ (σC (β j)).hom)
    (hmark : ∀ j : J, Set.image (σW j).hom (⋃ i : Fin n, Set.range (s i)) =
      ⋃ i : Fin n, Set.range (s i))
    (hSinsep : ∃ K : IntermediateField Y.functionField S.functionField,
      (∀ z : S.functionField, z ∈ K ↔
        ∀ a : β.ker, (Scheme.functionFieldAut (σS a.val)).hom z = z) ∧
      IsPurelyInseparable Y.functionField K)
    (hWinsep : ∃ F : IntermediateField C.functionField W.functionField,
      (∀ z : W.functionField, z ∈ F ↔
        ∀ a : β.ker, (Scheme.functionFieldAut (σW a.val)).hom z = z) ∧
      IsPurelyInseparable C.functionField F) :
    ∃ (G : Type (max u v w)) (_ : Group G) (_ : Finite G) (ρ : G →* J),
      Function.Surjective ρ ∧
      ∃ (S₄ : Scheme.{u}) (_ : IsIntegral S₄) (r : S₄ ⟶ S) (σ₄ : G →* Aut S₄),
        IsHProjective (r ≫ pS) ∧
        (∀ t : S₄, IsDomain (S₄.presheaf.stalk t) ∧
          IsIntegrallyClosed (S₄.presheaf.stalk t)) ∧
        IsFinite r ∧ Surjective r ∧
        (∃ U : S.Opens, Dense (U : Set S) ∧ Etale (r ∣_ U)) ∧
        (∀ j : G, (σ₄ j).hom ≫ r = r ≫ (σS (ρ j)).hom) ∧
        (∃ _ : Algebra S.functionField S₄.functionField,
          Spec.map (CommRingCat.ofHom (algebraMap S.functionField S₄.functionField)) ≫
            S.fromSpecFunctionField = S₄.fromSpecFunctionField ≫ r ∧
          ∀ z : S₄.functionField,
            (∃ a : S.functionField, algebraMap S.functionField S₄.functionField a = z) ↔
              ∀ a : ρ.ker, (Scheme.functionFieldAut (σ₄ a.val)).hom z = z) ∧
        ∃ (e : Type u) (_ : Field e) (_ : Algebra k e), Module.Finite k e ∧
          ∃ γ : G →* (e ≃+* e),
            (∀ (j : G) (a : k), γ j (algebraMap k e a) =
              algebraMap k e (σk (β (ρ j)) a)) ∧
            (∃ E : IntermediateField k e,
              (∀ z : e, z ∈ E ↔ ∀ a : (β.comp ρ).ker, γ a.val z = z) ∧
              IsPurelyInseparable k E) ∧
            ∃ (B : Scheme.{u}) (_ : IsIntegral B) (pB : B ⟶ Spec (.of e))
              (q : B ⟶ S₄) (τB : G →* Aut B),
              IsHProjective pB ∧ GeometricallyIntegral pB ∧
              (∀ t : B, IsDomain (B.presheaf.stalk t) ∧
                IsIntegrallyClosed (B.presheaf.stalk t)) ∧
              q ≫ r ≫ pS = pB ≫ Spec.map (CommRingCat.ofHom (algebraMap k e)) ∧
              IsFinite q ∧ Surjective q ∧ UniversallyInjective q ∧
              (∀ j : G, (τB j).hom ≫ pB =
                pB ≫ Spec.map (CommRingCat.ofHom (γ j⁻¹).toRingHom)) ∧
              (∀ j : G, (τB j).hom ≫ q = q ≫ (σ₄ j).hom) ∧
              (∃ _ : Algebra S₄.functionField B.functionField,
                Spec.map (CommRingCat.ofHom (algebraMap S₄.functionField B.functionField)) ≫
                  S₄.fromSpecFunctionField = B.fromSpecFunctionField ≫ q ∧
                Module.Finite S₄.functionField B.functionField ∧
                IsPurelyInseparable S₄.functionField B.functionField) ∧
              IsHProjective (q ≫ r ≫ b₀) ∧ IsProper (q ≫ r ≫ b₀) ∧
              Surjective (q ≫ r ≫ b₀) ∧
              (∃ U : Y.Opens, Dense (U : Set Y) ∧ IsFinite ((q ≫ r ≫ b₀) ∣_ U)) ∧
              (∃ _ : Algebra Y.functionField B.functionField,
                Spec.map (CommRingCat.ofHom (algebraMap Y.functionField B.functionField)) ≫
                  Y.fromSpecFunctionField = B.fromSpecFunctionField ≫ q ≫ r ≫ b₀ ∧
                Module.Finite Y.functionField B.functionField ∧
                ∃ K : IntermediateField Y.functionField B.functionField,
                  (∀ z : B.functionField, z ∈ K ↔
                    ∀ a : (β.comp ρ).ker, (Scheme.functionFieldAut (τB a.val)).hom z = z) ∧
                  IsPurelyInseparable Y.functionField K) ∧
              (topologicalKrullDim Y = 0 → IsIso pB) ∧
              ∃ (_ : IsIntegral (pullback f (q ≫ r)))
                (τV : G →* Aut (pullback f (q ≫ r))),
                (∀ j : G, (τV j).hom ≫ pullback.fst f (q ≫ r) =
                  pullback.fst f (q ≫ r) ≫ (σW (ρ j)).hom) ∧
                (∀ j : G, (τV j).hom ≫ pullback.snd f (q ≫ r) =
                  pullback.snd f (q ≫ r) ≫ (τB j).hom) ∧
                IsHProjective (pullback.snd f (q ≫ r)) ∧
                IsStablePointedCurve (pullback.snd f (q ≫ r))
                  (fun i : Fin n ↦ f.baseChangeSection (s i) (hs i) (q ≫ r))
                  (fun i : Fin n ↦ Scheme.Hom.baseChangeSection_snd f (s i) (hs i) (q ≫ r)) ∧
                Smooth ((pullback.snd f (q ≫ r)).fiberToSpecResidueField (genericPoint B)) ∧
                GeometricallyIntegral
                  ((pullback.snd f (q ≫ r)).fiberToSpecResidueField (genericPoint B)) ∧
                HasQuasiSplitNodalFibres (pullback.snd f (q ≫ r)) ∧
                (∀ j : G, Set.image (τV j).hom
                  (⋃ i : Fin n, Set.range (f.baseChangeSection (s i) (hs i) (q ≫ r))) =
                    ⋃ i : Fin n, Set.range (f.baseChangeSection (s i) (hs i) (q ≫ r))) ∧
                IsHProjective (pullback.fst f (q ≫ r) ≫ a₀) ∧
                IsProper (pullback.fst f (q ≫ r) ≫ a₀) ∧
                Surjective (pullback.fst f (q ≫ r) ≫ a₀) ∧
                (∃ U : C.Opens, Dense (U : Set C) ∧
                  IsFinite ((pullback.fst f (q ≫ r) ≫ a₀) ∣_ U)) ∧
                (∃ _ : Algebra C.functionField (pullback f (q ≫ r)).functionField,
                  Spec.map (CommRingCat.ofHom
                    (algebraMap C.functionField (pullback f (q ≫ r)).functionField)) ≫
                    C.fromSpecFunctionField =
                      (pullback f (q ≫ r)).fromSpecFunctionField ≫ pullback.fst f (q ≫ r) ≫ a₀ ∧
                  Module.Finite C.functionField (pullback f (q ≫ r)).functionField ∧
                  ∃ F : IntermediateField C.functionField (pullback f (q ≫ r)).functionField,
                    (∀ z : (pullback f (q ≫ r)).functionField, z ∈ F ↔
                      ∀ a : (β.comp ρ).ker, (Scheme.functionFieldAut (τV a.val)).hom z = z) ∧
                    IsPurelyInseparable C.functionField F) ∧
                (∀ j : G, (τB j).hom ≫ q ≫ r ≫ b₀ =
                  (q ≫ r ≫ b₀) ≫ (σY (β (ρ j))).hom) ∧
                (∀ j : G, (τV j).hom ≫ pullback.fst f (q ≫ r) ≫ a₀ =
                  (pullback.fst f (q ≫ r) ≫ a₀) ≫ (σC (β (ρ j))).hom) ∧
                (pullback.fst f (q ≫ r) ≫ a₀) ≫ g =
                  pullback.snd f (q ≫ r) ≫ (q ≫ r ≫ b₀) := by
  sorry

end AlgebraicGeometry
