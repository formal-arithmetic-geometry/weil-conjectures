/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteProjectionExchangeData
import WeilConjectures.AlgebraicGeometry.FiniteProjectionTensorSquare
import WeilConjectures.AlgebraicGeometry.FiniteProjectionOpenAssembly
import WeilConjectures.AlgebraicGeometry.FiniteProjectionIdentityNormalization
import WeilConjectures.AlgebraicGeometry.FiniteProjectionRefinementLeft

/-! # Finite projection/exchange transposes

Source: blueprint sec-six-functors/sk-prop-sf-pf-coherence,
prop-sf-pf-coherence.proof.md, open/proper factor calculation, compactification
independence and identity (blueprint: lem-sf-finite-projection-exchange-transposes).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.FiniteProjectionExchange

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The finite coefficient specialization of all three clauses, with no absolute
separatedness imposed. The only separatedness hypotheses are on f and g.
Every compactification is quantified, so the assertion includes the chosen maps
that represent compactification-independent operations. RefinementLaw identifies
both sides after the specified source and target comparisons.
Source: prop-sf-pf-coherence.proof.md, base change, independence and identity
(blueprint: lem-sf-finite-projection-exchange-transposes). -/
def FiniteStatement (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n) : Prop :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  letI : TopologicalSpace (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) := ⊥
  letI : DiscreteTopology (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) :=
    discreteTopology_bot _
  (∀ (X Y Y' : SixFunctorSpace D) (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    (X' : Scheme.{u}) (a : X' ⟶ X.obj.left) (f' : X' ⟶ Y'.obj.left)
    (s : IsPullback a f' f.hom.left g.hom.left) (c : Compactification f.hom.left)
    (K : Dcat (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) X.obj.left)
    (L : Dcat (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) Y.obj.left),
    finiteBC C.l E n hn X.obj.left K → finiteCTF C.l E n hn Y.obj.left L →
    SquareLaw (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) s c K L) ∧
  ∀ (X : SixFunctorSpace D)
    (K L : Dcat (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) X.obj.left),
    finiteBC C.l E n hn X.obj.left K → finiteCTF C.l E n hn X.obj.left L →
    IdentityLaw (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) X.obj.left K L

private theorem exchangeFirst_transpose
    {B' B Y' Y : Scheme.{u}} {h : B' ⟶ B} {p' : B' ⟶ Y'}
    {p : B ⟶ Y} {g : Y' ⟶ Y} (s : CommSq h p' p g)
    (M : Dcat A B) (L : Dcat A Y) :
    ((derivedUpperStarLowerStarAdjunction (ModuleCat A) p').homEquiv _ _).symm
      (exchangeFirst A s M L) = commonTranspose A s M L := by
  dsimp only [exchangeFirst]
  rw [Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_left_symm]
  have hp := homEquiv_symm_rightDerivedLowerStarProjectionMap (ModuleCat A) p'
    ((pull A h).obj M) ((pull A g).obj L)
  erw [hp]
  dsimp only [tensorMap]
  have ht := NatTrans.congr_app
    ((leftDerivedUpperStarTensorComparison (ModuleCat A) p').naturality
      (exchange A s M)) ((pull A g).obj L)
  dsimp at ht
  rw [Functor.map_comp, Category.assoc]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [reassoc_of% ht]
  have he : (pull A p').map (exchange A s M) ≫
      (derivedUpperStarLowerStarAdjunction (ModuleCat A) p').counit.app
        ((pull A h).obj M) =
      (theta A s).hom.app ((push A p).obj M) ≫
        (pull A h).map
          ((derivedUpperStarLowerStarAdjunction (ModuleCat A) p).counit.app M) :=
    mateEquiv_counit
      (derivedUpperStarLowerStarAdjunction (ModuleCat A) p)
      (derivedUpperStarLowerStarAdjunction (ModuleCat A) p')
      (theta A s).hom M
  simp only [commonTranspose, tensorMap, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [← NatTrans.comp_app, ← Functor.map_comp, he, Functor.map_comp, NatTrans.comp_app]
  rfl

private theorem properFirst_transpose
    {B' B Y' Y : Scheme.{u}} {h : B' ⟶ B} {p' : B' ⟶ Y'}
    {p : B ⟶ Y} {g : Y' ⟶ Y} (s : CommSq h p' p g)
    (M : Dcat A B) (L : Dcat A Y) :
    ((derivedUpperStarLowerStarAdjunction (ModuleCat A) p').homEquiv _ _).symm
      (properFirst A s M L) = commonTranspose A s M L := by
  dsimp only [properFirst]
  rw [Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_counit]
  have he := mateEquiv_counit
    (derivedUpperStarLowerStarAdjunction (ModuleCat A) p)
    (derivedUpperStarLowerStarAdjunction (ModuleCat A) p')
    (theta A s).hom (tensor A B M ((pull A p).obj L))
  erw [he]
  have hn := (theta A s).hom.naturality (pi A p M L)
  dsimp at hn
  simp only [Category.assoc]
  erw [reassoc_of% hn]
  rw [← Functor.map_comp_assoc]
  have hp := map_rightDerivedLowerStarProjectionMap_comp_counit (ModuleCat A) p M L
  erw [hp]
  rw [Functor.map_comp, Category.assoc]
  have ht := NatTrans.congr_app
    ((leftDerivedUpperStarTensorComparison (ModuleCat A) h).naturality
      ((derivedUpperStarLowerStarAdjunction (ModuleCat A) p).counit.app M))
    ((pull A p).obj L)
  dsimp at ht
  erw [reassoc_of% ht]
  have hs := tensor_square A s ((push A p).obj M) L
  dsimp only [tensorMap] at hs
  dsimp only [commonTranspose, tensorMap]
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    Category.comp_id]
  rw [← Category.assoc] at hs
  erw [← reassoc_of% hs]
  have hn' := ((derivedTensor (ModuleCat A) B').map
    ((pull A h).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat A) p).counit.app M))).naturality
    ((theta A s).inv.app L)
  dsimp at hn'
  erw [← hn']
  rw [← CategoryTheory.Functor.map_comp_assoc]
  simp only [Iso.hom_inv_id_app]
  have hi := ((derivedTensor (ModuleCat A) B').obj
    ((pull A h).obj ((pull A p).obj ((push A p).obj M)))).map_id
    ((pull A p').obj ((pull A g).obj L))
  erw [hi]
  simp only [Category.id_comp]

private theorem open_source_mem_essImage
    {X' X B' B : Scheme.{u}} {a : X' ⟶ X} {j' : X' ⟶ B'}
    {j : X ⟶ B} {h : B' ⟶ B} [IsOpenImmersion j] [IsOpenImmersion j']
    (s : IsPullback a j' j h) (K : Dcat A X) (P : Dcat A B) :
    (ext A j').essImage
      ((pull A h).obj (tensor A B ((ext A j).obj K) P)) := by
  refine ⟨tensor A X' ((pull A a).obj K) ((pull A j').obj ((pull A h).obj P)), ?_⟩
  let e := (mu A h ((ext A j).obj K) P) ≪≫
    ((derivedTensor (ModuleCat A) B').mapIso ((beta A s).app K)).app
      ((pull A h).obj P) ≪≫
    gamma A j' ((pull A a).obj K) ((pull A h).obj P)
  exact ⟨e.symm⟩

private theorem diamond_equality
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : IsPullback a f' f g) (c : Compactification f)
    (K : Dcat A X) (L : Dcat A Y) :
    diamondLeft A s c K L = diamondRight A s c K L := by
  have hp := properFirst_transpose A
    (c.isPullback_g_ofIsPullback s).flip.toCommSq ((ext A c.i).obj K) L
  have he := exchangeFirst_transpose A
    (c.isPullback_g_ofIsPullback s).flip.toCommSq ((ext A c.i).obj K) L
  have h := ((derivedUpperStarLowerStarAdjunction (ModuleCat A)
    (c.ofIsPullback s).g).homEquiv _ _).symm.injective (hp.trans he.symm)
  exact (open_factor_assembly A s c K L h).1

/-- Finite projection/exchange coherence, including the open restrictions and both
proper transposes, refinement intertwining and identity normalization.
Source: prop-sf-pf-coherence.proof.md, open/proper calculation and identity paragraph
(blueprint: lem-sf-finite-projection-exchange-transposes).

Proof plan (the DAG calculation, with composition read in its displayed order):
1. Fix the indicated compactification and write $J=j_!$, $J'=j'_!$, $A=Lg'^*$, $F=Lp^*$,
$F'=Lp'^*$, $G=Lg^*$, $H=Lh^*$, $S=Rp_*$, $S'=Rp'_*$, $M=JK$, and $\theta:F'G\cong HF$. Write
$\mu_U:U(B\otimes C)\cong UB\otimes UC$ for the canonical tensor comparison and omit only its
indicated arguments. All tensors in this proof are over $\Lambda$ and derived. The canonical
composition and square comparisons are monoidal by [lem-sfb-ringed-derived-monoidal-comparisons];
in particular $$\mu_H H(\mu_F)\theta_{B\otimes C}=(\theta_B\otimes\theta_C)\mu_{F'}F'(\mu_G).$$ By
[def-exchange-projection], put $a_{M,L}=(\varepsilon_{p,M}\otimes1)\mu_F$, let $\pi_{p;M,L}$ be
its adjoint transpose, and let $b_N:GSN\to S'HN$ be the exchange mate of $\theta$. Thus the
transpose of $b_N$ is $H\varepsilon_{p,N}\,\theta_{SN}$. These constructions and the monoidal
comparison theorem apply to arbitrary schemes and ambient unbounded constant-coefficient derived
categories; no absolute separatedness is used.
2. For the open factor put $P=FL$ and use the normalized maps $\gamma:JK\otimes P\cong J(K\otimes
Lj^*P)$ and $\beta:HJ\cong J'A$ of [lem-sf-open-tensor-normalization]. The first route from
$H(JK\otimes P)$ is $H\gamma$ followed by $\beta$ at $K\otimes Lj^*P$ and $J'$ of the canonical
tensor and square comparisons. The second is $\mu_H$, then $\beta_K\otimes1$, then $\gamma'$ at
$(AK,HP)$. Their common target is $J'(AK\otimes Lj'^*HP)$. The second route is a composite of
isomorphisms, so the source too lies in the essential image of $J'$. Restrict both routes by
$Lj'^*$: the restrictions of $\beta$ and $\gamma,\gamma'$ are identities after the open units, and
the remaining tensor/square comparisons agree by the monoidality in step 1. Hence both
restrictions are the identity under the canonical identification with $AK\otimes Lf'^*GL$. Full
faithfulness of $J'$ then gives equality of these two open routes.
3. Consider the proper-factor route which first projects, then exchanges. Set
$d_{M,L}=(1\otimes\theta_L^{-1})\mu_{H;M,FL}$, a map $H(M\otimes FL)\to HM\otimes F'GL$. This
route is $$S'(d_{M,L})\,b_{M\otimes FL}\,G(\pi_{p;M,L}).$$ Its transpose under $F'\dashv S'$ is
$$d_{M,L}\,H(\varepsilon_{p,M\otimes FL})\,\theta_{S(M\otimes FL)}\,F'G(\pi_{p;M,L})
=d_{M,L}\,H(a_{M,L})\,\theta_{SM\otimes L}.$$ Indeed naturality of $\theta$ moves $F'G(\pi)$
across it, and the defining transpose identity $\varepsilon_{p,M\otimes FL}F\pi=a_{M,L}$ cancels
the unit/counit pair. Naturality of $\mu_H$ and the tensor-square equation of step 1 rewrite this
as $$c=(H\varepsilon_{p,M}\otimes1)(\theta_{SM}\otimes1)\mu_{F'}F'(\mu_G):F'G(SM\otimes
L)\longrightarrow HM\otimes F'GL.$$ This is precisely the first common transpose required in (1),
with all its canonical comparisons specified.
4. The other proper-factor route, which first exchanges, is
$$\pi_{p';HM,GL}\,(b_M\otimes1)\mu_G.$$ Its transpose is
$$(\varepsilon_{p',HM}\otimes1)\mu_{F'}F'(b_M\otimes1)F'(\mu_G)
=((\varepsilon_{p',HM}F'b_M)\otimes1)\mu_{F'}F'(\mu_G).$$ Here the second equality is naturality
of $\mu_{F'}$. The mate definition gives $\varepsilon_{p',HM}F'b_M=H\varepsilon_{p,M}\theta_{SM}$,
so this transpose equals $c$ from step 3. The adjunction Hom bijection is injective, hence the two
proper routes agree. In particular this establishes equality of actual morphisms, without assuming
that the projection or exchange maps are invertible.
5. Expand $\operatorname{PF}^c=S(\gamma)\pi_p$ and $\operatorname{Ex}_!^c=S'(\beta)b$ by [def-
exchange-projection]. Naturality of $b$ moves $G S(\gamma)$ through $b$; naturality of $\pi_{p'}$
moves $S'(\beta)\otimes1$ through $\pi_{p'}$. The resulting proper subcomposites agree by steps 3
--4, and the remaining $S'$-images of the open subcomposites agree by step 2. Substitution gives
exactly the displayed projection/exchange equation of (1), for this arbitrary compactification,
including the stated open restrictions and proper transposes. Each ingredient was applied on the
small pro-etale sites; none required $X,Y,Y'$ to be separated over $k$.
6. Check the witnessed comparison domains. By [lem-sf-pullback-tor-amplitude], $Lf^*L$ is bounded
constructible with finite Tor amplitude. Clause (i) of [lem-sf-tensor-ctf] gives $K\otimes
Lf^*L\in D^b_c(X,\Lambda)$ without finite Tor amplitude on $K$. The equivalence in [lem-sf-
proetale-constructible-origin] supplies its etale-origin witness. For the arbitrary $K$, use [lem-
weil-pbc-pullback-preserves-bounded-constructible], not the finite-Tor pullback lemma: it gives
$AK\in D^b_c(X',\Lambda)$ and preserves the cohomological interval. Its coefficient hypothesis
applies: [lem-weil-l-adic-extension-integers-dvr] makes $R$ a DVR with finite residue field. Thus
$R$ is Noetherian, $R/t^m$ is finite by its $t$-power filtration and perfect over $R$ by
$[R\xrightarrow{t^m}R]$; $\ell$ lies in the maximal ideal since $|\ell|_E<1$, so the residue is
torsion. Consequently $(R,(t))$ is the required adic datum and $P_n=A_n$. Apply the finite-Tor
pullback lemma to $g$ and $f'$ for $GL$ and $Lf'^*GL$, then tensor with $AK$ using lem-sf-tensor-
ctf. Constructible origin supplies the witnesses on $X'$ too. Hence every input of the refinement
comparisons in step 7 lies in its witnessed domain.
7. For a refinement between $c_1,c_2$, write $\rho:F_{c_1}\cong F_{c_2}$ and $\rho':F_{c'_1}\cong
F_{c'_2}$ for the specified compact-support comparisons. By [lem-fix-projection-compactification-
comparison], $\rho$ intertwines the projection maps at $(K,L)$, and $\rho'$ does so at $(AK,GL)$.
By [fix-lem-exchanges] (4),
$$\rho'_{AN}\operatorname{Ex}^{c_1}_{!,N}=\operatorname{Ex}^{c_2}_{!,N}G(\rho_N)$$ for $N=K$ and
$N=K\otimes Lf^*L$. Insert these three intertwining equations into the two sides of the equation
of step 5. Both sides for $c_1$ become the corresponding sides for $c_2$ after the same source
comparison $G(\rho_K\otimes1)$ and target comparison $\rho'_{A(K\otimes Lf^*L)}$. All are
isomorphisms. This proves the refinement assertion of (2). The common-refinement independence and
cocycle in [prop-compactification-coherence-detailed] now give the equation for the
compactification-independent transformations.
8. Finally take $f=\mathrm{id}$ and $j=p=\mathrm{id}$. By [lem-sfb-ringed-derived-monoidal-
comparisons] the canonical derived identity comparisons identify the adjunction and tensor
comparison with those of the identity functor. Thus $a=(\varepsilon\otimes1)\mu$ and its transpose
$\pi$ are identities. By [lem-sf-open-tensor-normalization], the open tensor map for the identity
open is the identity under its open unit. The defining composite $S(\gamma)\pi$ of [def-exchange-
projection] is therefore the identity, proving (3).
-/
theorem finite_projection_exchange_transposes
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (_S : SixFunctorOperationDatum D C E n hn) :
    FiniteStatement D C E n hn := by
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot _
  constructor
  · intro X Y Y' f g _ _ _ _ _ _ X' a f' s c K L hK hL
    have hp := properFirst_transpose A
      (c.isPullback_g_ofIsPullback s).flip.toCommSq ((ext A c.i).obj K) L
    have he := exchangeFirst_transpose A
      (c.isPullback_g_ofIsPullback s).flip.toCommSq ((ext A c.i).obj K) L
    have hproper := ((derivedUpperStarLowerStarAdjunction (ModuleCat A)
      (c.ofIsPullback s).g).homEquiv _ _).symm.injective (hp.trans he.symm)
    obtain ⟨hd, ho, ho'⟩ := open_factor_assembly A s c K L hproper
    refine ⟨hd, open_source_mem_essImage A (c.isPullback_i_ofIsPullback s) K
      ((pull A c.g).obj L), ?_, ho, ho', hp, he, ?_⟩
    · exact (ext A (c.ofIsPullback s).i).obj_mem_essImage _
    · intro c₁ c₂ r O e OT eT
      have hl := refinement_left D C E n hn X Y Y' f g X' a f' s K L hK hL
        c₁ c₂ r O e OT eT
      refine ⟨hl, ?_⟩
      rw [← diamond_equality A s c₁ K L, ← diamond_equality A s c₂ K L]
      exact hl
  · intro X K L _ _
    exact identity_normalization A X.obj.left K L

end AlgebraicGeometry.ProEtale.FiniteProjectionExchange
