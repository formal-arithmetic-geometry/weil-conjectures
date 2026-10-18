/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback
public import Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius

/-!
# Normalization of the absolute-Frobenius stalk trivialization

Source: Stacks Project, `more-morphisms.tex`, Tag 0F6W
(blueprint: lem-trf-frobenius-stalk-trivialization-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The normalized inverse-Frobenius formula on geometric pro-etale stalks.

Source: Stacks Project, `more-morphisms.tex`, Tag 0F6W, and the normalized stalk
calculation in the proof of `lem-trf-local-frobenius-conjugacy`
(blueprint: lem-trf-frobenius-stalk-trivialization-normalization).
-/
def FrobeniusStalkTrivializationNormalized
    (p : ℕ) (hp : Nat.Prime p) (k : Type u) [Field k] [IsAlgClosed k]
    (hs : (Spec (.of k)).IsCharacteristic p) (X : Scheme.{u})
    (hX : X.IsCharacteristic p) (z : Spec (.of k) ⟶ X)
    (A : Type u) [CommRing A] [Finite A] : Prop :=
  ∀ b : ℕ,
    ∃ (δ : k ≃+* k),
      (∀ x : k, δ x = x ^ p ^ b) ∧
      ∃ (_hδS : Spec.map (CommRingCat.ofHom δ.toRingHom) =
          (Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b),
      ∃ (_hz : Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z =
          z ≫ X.iterateFrobenius hp (hX.2 ⊤) b),
        ∃ (rS : 𝟭 (Spec (.of k)).ProEt ≅ proEtaleBaseChange
            ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b))
          (rX : 𝟭 X.ProEt ≅ proEtaleBaseChange
            (X.iterateFrobenius hp (hX.2 ⊤) b))
          (tauS : proEtaleConstantRingPullback A
            ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b) ≅ 𝟭 _)
          (tauX : proEtaleConstantRingPullback A
            (X.iterateFrobenius hp (hX.2 ⊤) b) ≅ 𝟭 _),
          (∀ (V : (Spec (.of k)).ProEt),
            ∃ hV : (p : Γ(V.left, ⊤)) = 0,
              (rS.hom.app V).left ≫ pullback.fst V.hom
                  ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b) =
                V.left.iterateFrobenius hp hV b) ∧
          (∀ (V : X.ProEt),
            ∃ hV : (p : Γ(V.left, ⊤)) = 0,
              (rX.hom.app V).left ≫ pullback.fst V.hom
                  (X.iterateFrobenius hp (hX.2 ⊤) b) =
                V.left.iterateFrobenius hp hV b) ∧
          (∀ (M : proEtaleRingModules (Spec (.of k))
                (proEtaleConstantRing (Spec (.of k)) A))
            (V : (Spec (.of k)).ProEt)
            (m : M.val.obj (op V)),
            ((proEtaleConstantRingAdjunction A
                ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b)).unit.app M ≫
              (proEtaleConstantRingPushforward A
                ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b)).map
                (tauS.hom.app M)).val.app (op V) m =
              M.val.map (rS.inv.app V).op m) ∧
          (∀ (M : proEtaleRingModules X (proEtaleConstantRing X A))
            (V : X.ProEt) (m : M.val.obj (op V)),
            ((proEtaleConstantRingAdjunction A
                (X.iterateFrobenius hp (hX.2 ⊤) b)).unit.app M ≫
              (proEtaleConstantRingPushforward A
                (X.iterateFrobenius hp (hX.2 ⊤) b)).map
                (tauX.hom.app M)).val.app (op V) m =
              M.val.map (rX.inv.app V).op m) ∧
          (∀ (M : proEtaleRingModules X (proEtaleConstantRing X A))
              (N : ProEtaleGeometricNeighbourhood
                (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z))
              (a : M.val.obj (op N.right)),
            (eqToHom (congrArg (fun w => (finiteCoefficientModuleStalkFunctor w A).obj M)
                _hz) ≫
              (proEtalePullbackStalkComparison A
                (X.iterateFrobenius hp (hX.2 ⊤) b) z).inv.app M ≫
              (finiteCoefficientModuleStalkFunctor z A).map (tauX.hom.app M))
                (proEtaleCoefficientModuleGerm
                  (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z) A M N a) =
            eqToHom (congrArg (fun w => (finiteCoefficientModuleStalkFunctor w A).obj M)
                (by
                  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
                  simp : Spec.map (CommRingCat.ofHom δ.symm.toRingHom) ≫
                    Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z = z))
              ((proEtaleStalkReparam A
                (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z) δ.symm).hom.app M
                (proEtaleCoefficientModuleGerm
                  (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z) A M N a))) ∧
          (∀ (M : proEtaleRingModules X
              (proEtaleConstantRing X A)),
            (proEtalePullbackStalkComparison A z (𝟙 _)).hom.app M ≫
              (proEtaleStalkReparam A z δ).hom.app M =
            (proEtaleStalkReparam A (𝟙 (Spec (.of k))) δ).hom.app
                ((proEtaleConstantRingPullback A z).obj M) ≫
              (proEtalePullbackStalkComparison A z
                (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ 𝟙 _)).hom.app M ≫
              eqToHom (congrArg (fun w =>
                  (finiteCoefficientModuleStalkFunctor w A).obj M)
                (Category.assoc (Spec.map (CommRingCat.ofHom δ.toRingHom))
                  (𝟙 (Spec (.of k))) z))) ∧
          (∀ (H : CochainComplex (proEtaleRingModules X
              (proEtaleConstantRing X A)) ℤ),
            (∃ a₀ b₀ : ℤ, ∀ n : ℤ, n < a₀ ∨ b₀ < n → IsZero (H.X n)) →
            (proEtaleDerivedPullbackStalkComparison A z (𝟙 _)).hom.app
                (DerivedCategory.Q.obj H) ≫
              (proEtaleDerivedStalkReparam A z δ).hom.app
                (DerivedCategory.Q.obj H) =
            (proEtaleDerivedStalkReparam A (𝟙 (Spec (.of k))) δ).hom.app
                ((proEtaleConstantRingDerivedPullback A z).obj
                  (DerivedCategory.Q.obj H)) ≫
              (proEtaleDerivedPullbackStalkComparison A z
                (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ 𝟙 _)).hom.app
                (DerivedCategory.Q.obj H) ≫
              eqToHom (congrArg (fun w =>
                  (proEtaleFiniteCoefficientDerivedStalk A w).obj
                    (DerivedCategory.Q.obj H))
                (Category.assoc (Spec.map (CommRingCat.ofHom δ.toRingHom))
                  (𝟙 (Spec (.of k))) z))) ∧
          (∀ (M : proEtaleRingModules (Spec (.of k))
              (proEtaleConstantRing (Spec (.of k)) A))
              (N : ProEtaleGeometricNeighbourhood
                (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ 𝟙 (Spec (.of k))))
              (a : M.val.obj (op N.right)),
            (eqToHom (congrArg (fun w =>
                (finiteCoefficientModuleStalkFunctor w A).obj M)
              (by rw [_hδS, Category.comp_id, Category.id_comp])) ≫
              (proEtalePullbackStalkComparison A
                ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b) (𝟙 _)).inv.app M ≫
              (finiteCoefficientModuleStalkFunctor (𝟙 (Spec (.of k))) A).map
                (tauS.hom.app M))
                (proEtaleCoefficientModuleGerm
                  (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫
                    𝟙 (Spec (.of k))) A M N a) =
            eqToHom (congrArg (fun w =>
                (finiteCoefficientModuleStalkFunctor w A).obj M)
              (by
                rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
                simp : Spec.map (CommRingCat.ofHom δ.symm.toRingHom) ≫
                  Spec.map (CommRingCat.ofHom δ.toRingHom) ≫
                    𝟙 (Spec (.of k)) = 𝟙 (Spec (.of k))))
              ((proEtaleStalkReparam A
                (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫
                  𝟙 (Spec (.of k))) δ.symm).hom.app M
                (proEtaleCoefficientModuleGerm
                  (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫
                    𝟙 (Spec (.of k))) A M N a))) ∧
          (∀ (M : proEtaleRingModules (Spec (.of k))
              (proEtaleConstantRing (Spec (.of k)) A)),
            eqToHom (congrArg (fun w =>
                (finiteCoefficientModuleStalkFunctor w A).obj M)
              (by rw [_hδS, Category.comp_id, Category.id_comp])) ≫
              (proEtalePullbackStalkComparison A
                ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b) (𝟙 _)).inv.app M ≫
              (finiteCoefficientModuleStalkFunctor (𝟙 (Spec (.of k))) A).map
                (tauS.hom.app M) =
            (proEtaleStalkReparam A
              (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ 𝟙 (Spec (.of k))) δ.symm).hom.app M ≫
              eqToHom (congrArg (fun w =>
                  (finiteCoefficientModuleStalkFunctor w A).obj M)
                (by
                  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
                  simp : Spec.map (CommRingCat.ofHom δ.symm.toRingHom) ≫
                    Spec.map (CommRingCat.ofHom δ.toRingHom) ≫
                      𝟙 (Spec (.of k)) = 𝟙 (Spec (.of k))))) ∧
          (∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)),
            eqToHom (congrArg (fun w => (finiteCoefficientModuleStalkFunctor w A).obj M)
                _hz) ≫
              (proEtalePullbackStalkComparison A
                (X.iterateFrobenius hp (hX.2 ⊤) b) z).inv.app M ≫
              (finiteCoefficientModuleStalkFunctor z A).map (tauX.hom.app M) =
            (proEtaleStalkReparam A (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z)
              δ.symm).hom.app M ≫
              eqToHom (congrArg (fun w => (finiteCoefficientModuleStalkFunctor w A).obj M)
                (by
                  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
                  simp : Spec.map (CommRingCat.ofHom δ.symm.toRingHom) ≫
                    Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z = z))) ∧
          (∀ (H : CochainComplex (proEtaleRingModules (Spec (.of k))
              (proEtaleConstantRing (Spec (.of k)) A)) ℤ),
            (∃ a₀ b₀ : ℤ, ∀ n : ℤ, n < a₀ ∨ b₀ < n → IsZero (H.X n)) →
            eqToHom (congrArg (fun w =>
                (proEtaleFiniteCoefficientDerivedStalk A w).obj
                  (DerivedCategory.Q.obj H))
              (by rw [_hδS, Category.comp_id, Category.id_comp])) ≫
              (proEtaleDerivedPullbackStalkComparison A
                ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b) (𝟙 _)).inv.app
                (DerivedCategory.Q.obj H) ≫
              (proEtaleFiniteCoefficientDerivedStalk A (𝟙 (Spec (.of k)))).map
                ((proEtaleFrobeniusDerivedIso A tauS).hom.app
                  (DerivedCategory.Q.obj H)) =
            (proEtaleDerivedStalkReparam A
              (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫
                𝟙 (Spec (.of k))) δ.symm).hom.app
              (DerivedCategory.Q.obj H) ≫
              eqToHom (congrArg (fun w =>
                  (proEtaleFiniteCoefficientDerivedStalk A w).obj
                    (DerivedCategory.Q.obj H))
                (by
                  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
                  simp : Spec.map (CommRingCat.ofHom δ.symm.toRingHom) ≫
                    Spec.map (CommRingCat.ofHom δ.toRingHom) ≫
                      𝟙 (Spec (.of k)) = 𝟙 (Spec (.of k))))) ∧
          ∃ (comp : ∀ {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W),
              proEtaleConstantRingPullback A (f ≫ g) ≅
                proEtaleConstantRingPullback A g ⋙
                  proEtaleConstantRingPullback A f),
            (∀ {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W)
                (M : proEtaleRingModules Y (proEtaleConstantRing Y A))
                (V : W.ProEt)
                (m : ((proEtaleConstantRingPushforward A f ⋙
                  proEtaleConstantRingPushforward A g).obj M).val.obj (op V)),
              ((conjugateIsoEquiv
                ((proEtaleConstantRingAdjunction A g).comp
                  (proEtaleConstantRingAdjunction A f))
                (proEtaleConstantRingAdjunction A (f ≫ g))
                (comp f g)).hom.app M).val.app (op V) m =
                M.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app V).op m) ∧
            ∃ (w : (Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b ≫ z =
                z ≫ X.iterateFrobenius hp (hX.2 ⊤) b),
              (proEtaleFrobeniusDerivedComp A z
                (X.iterateFrobenius hp (hX.2 ⊤) b)
                (comp z (X.iterateFrobenius hp (hX.2 ⊤) b))).inv ≫
                eqToHom (congrArg (proEtaleConstantRingDerivedPullback A) w.symm) ≫
                (proEtaleFrobeniusDerivedComp A
                  ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b) z
                  (comp ((Spec (.of k)).iterateFrobenius hp (hs.2 ⊤) b) z)).hom ≫
                Functor.whiskerLeft
                  (proEtaleConstantRingDerivedPullback A z)
                  (proEtaleFrobeniusDerivedIso A tauS).hom ≫
                (Functor.rightUnitor _).hom =
              Functor.whiskerRight
                (proEtaleFrobeniusDerivedIso A tauX).hom
                (proEtaleConstantRingDerivedPullback A z) ≫
                (Functor.leftUnitor _).hom ∧
          (∀ (H : CochainComplex (proEtaleRingModules X
              (proEtaleConstantRing X A)) ℤ),
            (∃ a₀ b₀ : ℤ, ∀ n : ℤ, n < a₀ ∨ b₀ < n → IsZero (H.X n)) →
            eqToHom (congrArg (fun w => (proEtaleFiniteCoefficientDerivedStalk A w).obj
                (DerivedCategory.Q.obj H)) _hz) ≫
              (proEtaleDerivedPullbackStalkComparison A
                (X.iterateFrobenius hp (hX.2 ⊤) b) z).inv.app (DerivedCategory.Q.obj H) ≫
              (proEtaleFiniteCoefficientDerivedStalk A z).map
                ((proEtaleFrobeniusDerivedIso A tauX).hom.app (DerivedCategory.Q.obj H)) =
            (proEtaleDerivedStalkReparam A
              (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z) δ.symm).hom.app
                (DerivedCategory.Q.obj H) ≫
              eqToHom (congrArg (fun w => (proEtaleFiniteCoefficientDerivedStalk A w).obj
                (DerivedCategory.Q.obj H))
                (by
                  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
                  simp : Spec.map (CommRingCat.ofHom δ.symm.toRingHom) ≫
                    Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ z = z)))

/-- The specified absolute-Frobenius trivialization satisfies the normalized stalk formulas.

For each iterate `b`, the field automorphism `δ` is the $p^b$-power map and its induced map on
`Spec k` is the iterate Frobenius; naturality gives the displayed point equation.  The
relative-Frobenius site isomorphisms `rS`, `rX` and their projection formulas, and the unit
equations for `tauS` and `tauX`, fix the specified data of
`absoluteFrobenius_proEtale_trivialization_pullback` uniquely.  The germ clauses evaluate
`tauS ∘ c⁻¹` and `tauX ∘ c⁻¹` on every represented germ, with the equality transports from the
point equation, and identify them with the inverse reparametrization `r_{zδ,δ⁻¹}`.  The
remaining clauses give the same equalities as maps, on bounded complexes in the ordinary derived
category, the pullback-along-`z` reparametrization equation, the unit-normalized composition
comparison and the derived pullback equation along `z`.

Proof (the seven steps of the DAG node):

1. Frobenius is natural on characteristic-$p$ schemes: for every scheme map $a:U\to T$, its maps
on sections satisfy $a^\sharp(f^{p^b})=a^\sharp(f)^{p^b}$, and both Frobenius maps are
identities on underlying spaces. Thus $aF_U^b=F_T^ba$ by [def-weil-absolute-frobenius-scheme].
The field map $x\mapsto x^{p^b}$ on $k$ is injective, since $(x-y)^{p^b}=0$ implies $x=y$, and
surjective, since $t^{p^b}-c$ has a root in the algebraically closed field $k$. Hence
$\delta=F_s^b$ is an automorphism, including $\delta=1$ for $b=0$. In particular
$F_X^bz=z\delta$ and $F_V^bv=v\delta$ for every geometric lift $v:s\to V$.

2. First work with a sheaf $M$ on a characteristic-$p$ scheme $T$. Put $P=(F_T^b)^*$,
$Q=(F_T^b)_*$ and $B(V)=V\times_{T,F_T^b}T$. By [lem-pur-frobenius-trivialization-pullback],
$R_V=(F_V^b,h):V\to B(V)$ is the specified natural isomorphism for each weakly etale
$h:V\to T$. Thus the specified direct-image trivialization is $d_M:QM\to M$, with
$d_M(V)=M(R_V)$. Let $\eta:M\to QPM$ be the unit of the module adjunction
[def-weil-pbc-proetale-operations]. Apply [lem-weil-pbc-conjugate-iso-unit-equation] with
$(L_1,R_1)=(P,Q)$, $(L_2,R_2)=(\mathrm{id},\mathrm{id})$, and right-adjoint comparison $d^{-1}$.
The adjoint trivialization is characterized by $Q(\tau_M)\eta_M=d_M^{-1}$. Evaluated at $V$,
the pullback-unit section $\eta_{M,V}(a)\in PM(B(V))$ is sent by $\tau_M$ to
$M(R_V^{-1})(a)\in M(B(V))$. The coefficient identification preserves constant sections by
[prop-weil-pbc-proetale-constant-ring-map], so these are $A$-linear section maps with no
scalar factor.

3. Take a geometric point $u:s\to T$ and a germ $[V,v,a]\in M_{F_T^bu}$, so $hv=F_T^bu=u\delta$.
By the inverse formula in [lem-trf-proetale-pullback-stalk-coherence], $c_{F_T^b,u,M}^{-1}$
represents this germ by the pullback-unit section of $PM$ on $B(V)$ at the lift $w=(v,u)$.
Step 1 gives $h(v\delta^{-1})=u$ and $F_V^b(v\delta^{-1})=v$, hence
$R_V(v\delta^{-1})=(v,u)=w$. The fibre-product universal property [def-pc-fibre-product] and
invertibility of $R_V$ give $R_V^{-1}w=v\delta^{-1}$. Step 2 therefore sends the germ to
$[B(V),w,M(R_V^{-1})(a)]$. The pointed morphism $R_V^{-1}:(B(V),w)\to(V,v\delta^{-1})$
identifies this with $[V,v\delta^{-1},a]$ by the germ relation in
[def-weil-proetale-geometric-stalk].

4. For any scheme automorphism $\beta$ of $s$, precomposition sends a pointed neighbourhood
$(V,v)$ of $u$ to $(V,v\beta)$ of $u\beta$, leaving site arrows and sections unchanged. A
relation $[V',v',a']=[V,v,M(e)(a')]$ with $ev=v'$ remains a relation because
$e(v\beta)=v'\beta$. Thus [def-weil-proetale-geometric-stalk] defines $r_{u,\beta,M}$ on the
quotient, with inverse $r_{u\beta,\beta^{-1},M}$. The maps preserve sums and
$A$-multiplication, and for a sheaf map $f:M\to M'$ both orders send $[V,v,a]$ to
$[V,v\beta,f_V(a)]$, so $r$ is natural. In Step 3 the resulting map is exactly
$r_{u\delta,\delta^{-1},M}$.

5. Specialize Step 3 to $T=s$, $u=\mathrm{id}_s$ and $M=N$: it gives
$[V,v,a]\mapsto[V,v\delta^{-1},a]$ under $c_{\delta,\mathrm{id}_s,N}$. Specialize it to $T=X$,
$u=z$ and $M=H$; since $F_X^bz=z\delta$, it gives
$(\tau_X^{(b)}{}_H)_z\,c_{F_X^b,z,H}^{-1}=r_{z\delta,\delta^{-1},H}$. These are equalities of
maps, since every germ has a representative in the colimit of
[def-weil-proetale-geometric-stalk]. Step 4 proves naturality of the right side; naturality of
the left side is part of [lem-trf-proetale-pullback-stalk-coherence] and of the specified
natural transformation [lem-pur-frobenius-trivialization-pullback].

6. Apply the pullback naturality statement of [lem-pur-frobenius-trivialization-pullback] to
$z:s\to X$. With its specified composition comparison $C:Lz^*L(F_X^b)^*\to L\delta^*Lz^*$, it
gives $\tau_s^{(b)}{}_{Lz^*H}\circ C_H=Lz^*(\tau_X^{(b)}{}_H)$. Take the stalk at
$\mathrm{id}_s$. The composition equation for $c$ in
[lem-trf-proetale-pullback-stalk-coherence] identifies the two source stalks with
$H_{F_X^bz}=H_{z\delta}$. Its reparametrization equation identifies the target maps from
Steps 3--5 as well. This proves the compatibility through the specified composition
comparisons, not through arbitrary isomorphisms.

7. Apply Steps 2--6 in every degree of a bounded complex. All section maps commute with the
differentials by naturality, so the germ equations are equalities of chain maps. The module
pullbacks are exact and their derived pullbacks are the termwise functors by
[def-weil-pbc-proetale-operations]. The cited Frobenius trivialization is the termwise one by
[lem-pur-frobenius-trivialization-pullback], and [lem-trf-proetale-pullback-stalk-coherence]
supplies the stalk comparisons, composition equalities and reparametrizations after
localization. Parts (2) and (3) of [lem-weil-pbc-localization-universal-property] carry their
naturality and equalities to the localization; no resolution choice changes the formula. For
$b=0$, $R_V$, $\delta$, and both germ reparametrizations are identities, consistent with
$\tau^{(0)}=1$.

Source: Stacks Project, `more-morphisms.tex`, Tag 0F6W
(blueprint: lem-trf-frobenius-stalk-trivialization-normalization).
-/
theorem frobeniusStalkTrivializationNormalization
    (p : ℕ) (hp : Nat.Prime p) (k : Type u) [Field k] [IsAlgClosed k]
    (hs : (Spec (.of k)).IsCharacteristic p) (X : Scheme.{u})
    (hX : X.IsCharacteristic p) (z : Spec (.of k) ⟶ X)
    (A : Type u) [CommRing A] [Finite A] :
    FrobeniusStalkTrivializationNormalized p hp k hs X hX z A := by
  sorry

end AlgebraicGeometry.Scheme
