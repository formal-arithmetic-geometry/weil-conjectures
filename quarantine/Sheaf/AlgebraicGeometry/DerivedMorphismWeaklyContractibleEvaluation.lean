/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
public import Sheaf.AlgebraicGeometry.DerivedMorphismSheafComparison
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization

import Sheaf.AlgebraicGeometry.DerivedHomSheafComparisonLisse
import Sheaf.AlgebraicGeometry.DerivedIsomSheafComparisonFromHom
import Sheaf.AlgebraicGeometry.DerivedScalarExtensionLocalSystems
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

/-!
# Derived morphism sheaves on weakly contractible pro-etale affines

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; Cohomology on Sites, Tags 0946
and 09BE; the blueprint amplification proof, finite-source extension.
(blueprint: lem-weil-pbc-derived-isomorphism-sheaf-wcontractible-evaluation)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
set_option autoImplicit false
namespace AlgebraicGeometry.Scheme

private theorem transpose_unit {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {P : C} {Q : D}
    (f : P ⟶ G.obj Q) :
    adj.unit.app P ≫ G.map ((adj.homEquiv P Q).symm f) = f := by
  exact (adj.homEquiv P Q).apply_symm_apply f

private theorem pairSection_fst {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type (u + 1))]
    (F G : Sheaf J (Type (u + 1))) (U : C)
    (s : F.obj.obj (op U)) (t : G.obj.obj (op U)) :
    (prod.fst : F ⨯ G ⟶ F).hom.app (op U) (sheafPairSection J F G U s t) = s := by
  unfold sheafPairSection
  change ((sheafToPresheaf J (Type (u + 1)) ⋙
    (CategoryTheory.evaluation Cᵒᵖ (Type (u + 1))).obj (op U)).map prod.fst) _ = s
  rw [← ConcreteCategory.comp_apply, inv_prodComparison_map_fst,
    ← ConcreteCategory.comp_apply, Types.binaryProductIso_inv_comp_fst]
  rfl

private theorem pairSection_snd {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type (u + 1))]
    (F G : Sheaf J (Type (u + 1))) (U : C)
    (s : F.obj.obj (op U)) (t : G.obj.obj (op U)) :
    (prod.snd : F ⨯ G ⟶ G).hom.app (op U) (sheafPairSection J F G U s t) = t := by
  unfold sheafPairSection
  change ((sheafToPresheaf J (Type (u + 1)) ⋙
    (CategoryTheory.evaluation Cᵒᵖ (Type (u + 1))).obj (op U)).map prod.snd) _ = t
  rw [← ConcreteCategory.comp_apply, inv_prodComparison_map_snd,
    ← ConcreteCategory.comp_apply, Types.binaryProductIso_inv_comp_snd]
  rfl

private theorem pairSection_ext {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type (u + 1))]
    (F G : Sheaf J (Type (u + 1))) (U : C) (x y : (F ⨯ G).obj.obj (op U))
    (h₁ : (prod.fst : F ⨯ G ⟶ F).hom.app (op U) x =
      (prod.fst : F ⨯ G ⟶ F).hom.app (op U) y)
    (h₂ : (prod.snd : F ⨯ G ⟶ G).hom.app (op U) x =
      (prod.snd : F ⨯ G ⟶ G).hom.app (op U) y) : x = y := by
  let E := sheafToPresheaf J (Type (u + 1)) ⋙
    (CategoryTheory.evaluation Cᵒᵖ (Type (u + 1))).obj (op U)
  apply (ConcreteCategory.bijective_of_isIso (prodComparison E F G)).injective
  apply (ConcreteCategory.bijective_of_isIso
    (Types.binaryProductIso (E.obj F) (E.obj G)).hom).injective
  apply _root_.Prod.ext
  · have ht : prodComparison E F G ≫
        (Types.binaryProductIso (E.obj F) (E.obj G)).hom ≫
        (↾_root_.Prod.fst : (E.obj F × E.obj G) ⟶ E.obj F) = E.map prod.fst := by
      rw [Types.binaryProductIso_hom_comp_fst, prodComparison_fst]
    change (E.map prod.fst) x = (E.map prod.fst) y at h₁
    simpa only [ConcreteCategory.comp_apply, TypeCat.ofHom_apply] using
      (ConcreteCategory.congr_hom ht x).trans
        (h₁.trans (ConcreteCategory.congr_hom ht y).symm)
  · have ht : prodComparison E F G ≫
        (Types.binaryProductIso (E.obj F) (E.obj G)).hom ≫
        (↾_root_.Prod.snd : (E.obj F × E.obj G) ⟶ E.obj G) = E.map prod.snd := by
      rw [Types.binaryProductIso_hom_comp_snd, prodComparison_snd]
    change (E.map prod.snd) x = (E.map prod.snd) y at h₂
    simpa only [ConcreteCategory.comp_apply, TypeCat.ofHom_apply] using
      (ConcreteCategory.congr_hom ht x).trans
        (h₂.trans (ConcreteCategory.congr_hom ht y).symm)


private theorem pairSection_map {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type (u + 1))]
    {F G H K : Sheaf J (Type (u + 1))} (f : F ⟶ H) (g : G ⟶ K)
    (U : C) (s : F.obj.obj (op U)) (t : G.obj.obj (op U)) :
    (prod.map f g).hom.app (op U) (sheafPairSection J F G U s t) =
      sheafPairSection J H K U (f.hom.app (op U) s) (g.hom.app (op U) t) := by
  apply pairSection_ext
  · rw [pairSection_fst]
    change ((prod.map f g ≫ prod.fst).hom.app (op U)) _ = _
    rw [prod.map_fst]
    exact congrArg (f.hom.app (op U)) (pairSection_fst J F G U s t)
  · rw [pairSection_snd]
    change ((prod.map f g ≫ prod.snd).hom.app (op U)) _ = _
    rw [prod.map_snd]
    exact congrArg (g.hom.app (op U)) (pairSection_snd J F G U s t)

private theorem sheaf_binary_ext {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type (u + 1))]
    (P Q : Cᵒᵖ ⥤ Type (u + 1)) (H : Sheaf J (Type (u + 1)))
    (f g : (presheafToSheaf J (Type (u + 1))).obj P ⨯
      (presheafToSheaf J (Type (u + 1))).obj Q ⟶ H)
    (h : ∀ (U : C) (s : P.obj (op U)) (t : Q.obj (op U)),
      f.hom.app (op U) (sheafPairSection J _ _ U
        ((toSheafify J P).app (op U) s) ((toSheafify J Q).app (op U) t)) =
      g.hom.app (op U) (sheafPairSection J _ _ U
        ((toSheafify J P).app (op U) s) ((toSheafify J Q).app (op U) t))) : f = g := by
  let F := presheafToSheaf J (Type (u + 1))
  let V := sheafToPresheaf J (Type (u + 1))
  let k := toSheafify J (P ⨯ Q) ≫ V.map (prodComparison F P Q)
  have hk (U : C) (z : (P ⨯ Q).obj (op U)) :
      k.app (op U) z = sheafPairSection J _ _ U
        ((toSheafify J P).app (op U) ((prod.fst : P ⨯ Q ⟶ P).app (op U) z))
        ((toSheafify J Q).app (op U) ((prod.snd : P ⨯ Q ⟶ Q).app (op U) z)) := by
    apply pairSection_ext
    · rw [pairSection_fst]
      have ht : k ≫ V.map (prod.fst : F.obj P ⨯ F.obj Q ⟶ F.obj P) =
          (prod.fst : P ⨯ Q ⟶ P) ≫ toSheafify J P := by
        dsimp only [k]
        rw [Category.assoc, ← V.map_comp, prodComparison_fst]
        exact (toSheafify_naturality J _).symm
      exact ConcreteCategory.congr_hom (congr_app ht (op U)) z
    · rw [pairSection_snd]
      have ht : k ≫ V.map (prod.snd : F.obj P ⨯ F.obj Q ⟶ F.obj Q) =
          (prod.snd : P ⨯ Q ⟶ Q) ≫ toSheafify J Q := by
        dsimp only [k]
        rw [Category.assoc, ← V.map_comp, prodComparison_snd]
        exact (toSheafify_naturality J _).symm
      exact ConcreteCategory.congr_hom (congr_app ht (op U)) z
  apply (cancel_epi (prodComparison F P Q)).mp
  apply V.map_injective
  apply sheafify_hom_ext J _ _ H.property
  ext U z
  change f.hom.app U (k.app U z) = g.hom.app U (k.app U z)
  rw [hk U.unop]
  exact h U.unop _ _

variable (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]

private theorem comparison_pair
    (S T : Sheaf X.smallEtaleTopology (Type (u + 1))) (V : X.Etale)
    (s : S.obj.obj (op V)) (t : T.obj.obj (op V)) :
    (prodComparison (comparisonSetUpperStar X) S T).hom.app (op ((toProEt X).obj V))
        (((proEtaleSiteComparison X).unit.app (S ⨯ T)).hom.app (op V)
          (sheafPairSection X.smallEtaleTopology S T V s t)) =
      sheafPairSection (ProEt.topology X) _ _ ((toProEt X).obj V)
        (((proEtaleSiteComparison X).unit.app S).hom.app (op V) s)
        (((proEtaleSiteComparison X).unit.app T).hom.app (op V) t) := by
  apply pairSection_ext
  · rw [pairSection_fst]
    have hp := (proEtaleSiteComparison X).unit.naturality (prod.fst : S ⨯ T ⟶ S)
    have h := congrArg (fun k ↦ k.hom.app (op V)
      (sheafPairSection X.smallEtaleTopology S T V s t)) hp
    change _ = ((comparisonSetUpperStar X).map prod.fst).hom.app
      (op ((toProEt X).obj V)) _ at h
    rw [← prodComparison_fst (comparisonSetUpperStar X) S T] at h
    change ((proEtaleSiteComparison X).unit.app S).hom.app (op V)
        ((prod.fst : S ⨯ T ⟶ S).hom.app (op V)
          (sheafPairSection X.smallEtaleTopology S T V s t)) = _ at h
    rw [pairSection_fst] at h
    exact h.symm
  · rw [pairSection_snd]
    have hp := (proEtaleSiteComparison X).unit.naturality (prod.snd : S ⨯ T ⟶ T)
    have h := congrArg (fun k ↦ k.hom.app (op V)
      (sheafPairSection X.smallEtaleTopology S T V s t)) hp
    change _ = ((comparisonSetUpperStar X).map prod.snd).hom.app
      (op ((toProEt X).obj V)) _ at h
    rw [← prodComparison_snd (comparisonSetUpperStar X) S T] at h
    change ((proEtaleSiteComparison X).unit.app T).hom.app (op V)
        ((prod.snd : S ⨯ T ⟶ T).hom.app (op V)
          (sheafPairSection X.smallEtaleTopology S T V s t)) = _ at h
    rw [pairSection_snd] at h
    exact h.symm

private theorem comparisonHom_generator
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (V : X.Etale)
    (f : (derivedSliceRestriction X.smallEtaleTopology B V).obj A ⟶
      (derivedSliceRestriction X.smallEtaleTopology B V).obj D) :
    (derivedHomSheafComparison X B A D).hom.app (op ((toProEt X).obj V))
      (((proEtaleSiteComparison X).unit.app
        (derivedLocalHomSheaf X.smallEtaleTopology B A D)).hom.app (op V)
        ((toSheafify X.smallEtaleTopology
          (derivedLocalHomPresheaf X.smallEtaleTopology B A D)).app (op V) f)) =
      derivedComparisonHomUnit X B A D V f := by
  have hc := transpose_unit (proEtaleSiteComparison X)
    (((sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).homEquiv _ _).symm
      (derivedComparisonHomPresheafMap X B A D))
  have hs := transpose_unit (sheafificationAdjunction X.smallEtaleTopology (Type (u + 1)))
    (Q := ((toProEt X).sheafPushforwardContinuous (Type (u + 1))
      X.smallEtaleTopology (ProEt.topology X)).obj (derivedComparisonHomTarget X B A D))
    (derivedComparisonHomPresheafMap X B A D)
  exact (congrArg (fun k ↦ k.hom.app (op V)
    ((toSheafify X.smallEtaleTopology
      (derivedLocalHomPresheaf X.smallEtaleTopology B A D)).app (op V) f)) hc).trans
    (congrArg (fun k ↦ k.app (op V) f) hs)

private theorem comparisonIso_generator
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (V : X.Etale)
    (f : (derivedSliceRestriction X.smallEtaleTopology B V).obj A ≅
      (derivedSliceRestriction X.smallEtaleTopology B V).obj D) :
    (derivedIsoSheafComparison X B A D).hom.app (op ((toProEt X).obj V))
      (((proEtaleSiteComparison X).unit.app
        (derivedLocalIsoSheaf X.smallEtaleTopology B A D)).hom.app (op V)
        ((toSheafify X.smallEtaleTopology
          (derivedLocalIsoPresheaf X.smallEtaleTopology B A D)).app (op V) f)) =
      derivedComparisonIsoUnit X B A D V f := by
  have hc := transpose_unit (proEtaleSiteComparison X)
    (((sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).homEquiv _ _).symm
      (derivedComparisonIsoPresheafMap X B A D))
  have hs := transpose_unit (sheafificationAdjunction X.smallEtaleTopology (Type (u + 1)))
    (Q := ((toProEt X).sheafPushforwardContinuous (Type (u + 1))
      X.smallEtaleTopology (ProEt.topology X)).obj (derivedComparisonIsoTarget X B A D))
    (derivedComparisonIsoPresheafMap X B A D)
  exact (congrArg (fun k ↦ k.hom.app (op V)
    ((toSheafify X.smallEtaleTopology
      (derivedLocalIsoPresheaf X.smallEtaleTopology B A D)).app (op V) f)) hc).trans
    (congrArg (fun k ↦ k.app (op V) f) hs)

/-- The constant etale sheaf complex, obtained by applying the exact constant-sheaf functor to the
derived category.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; Cohomology on Sites, Tags 0946
and 09BE; the blueprint amplification proof, finite-source extension.
(blueprint: lem-weil-pbc-derived-isomorphism-sheaf-wcontractible-evaluation) -/
noncomputable abbrev constantDerivedEtale :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory

private theorem constant_finite_etale (M : ModuleCat.{u + 1} B) [Module.Finite B M] :
    IsFiniteLocallyConstantSheaf
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).obj M) where
  toIsLocallyConstantSheaf := by
    have : ∀ (V : X.Etale) (P : (Over V)ᵒᵖ ⥤ ModuleCat.{u + 1} B),
        (Over.forget V).op.HasPointwiseRightKanExtension P := by
      intro V P Y
      have : EssentiallySmall.{u + 1} (StructuredArrow Y (Over.forget V).op) :=
        essentiallySmallSelf.{0} _
      have : HasLimitsOfShape (StructuredArrow Y (Over.forget V).op)
          (ModuleCat.{u + 1} B) := hasLimitsOfShape_of_essentiallySmall.{u + 1} _ _
      exact HasLimitsOfShape.has_limit _
    exact (Sheaf.isConstant_of_iso _ (Iso.refl _)).isLocallyConstantSheaf
  toIsFiniteSheaf := ⟨fun Ω _ _ s ↦ by
    have : PreservesFilteredColimitsOfSize.{u, u}
        (CategoryTheory.forget (ModuleCat.{u + 1} B)) :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    have : LocallySmall.{u} X.Etale := locallySmall_self _
    exact ((ModuleCat.isFinitelyGenerated_iff M).2 inferInstance).of_iso
      ((pointSmallEtale s).sheafFiberConstantSheafIso M).symm⟩

/-- The canonical derived Hom and Isom evaluation maps are bijective for a bounded finite source and
a bounded finite locally constant etale target. Finite module cohomology does not mean
perfectness.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; Cohomology on Sites, Tags 0946
and 09BE; the blueprint amplification proof, finite-source extension.
(blueprint: lem-weil-pbc-derived-isomorphism-sheaf-wcontractible-evaluation)

Proof: Step 1. $B$ is Noetherian: every ideal is a finite set and hence generated by its
elements. The bounded finite cohomology hypothesis and
[lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion] make $E$ pseudo-coherent. By
[def-pc-ring-pseudo-coherent-complex] choose a bounded-above finite-free representative $P$ of
$E$, zero above $b$. Choose a representative $N$ of $K$ zero below some $a$, using
[def-sbc-standard-tstructure-derived-category]. Applying the constant-sheaf functor to $P$
represents $\underline E$: constant presheaves preserve kernels, and set sheafification
preserves finite limits, hence the underlying constant-sheaf functor preserves kernels. For a
surjection of coefficient modules, its underlying set map is the coequalizer of the two
projections of its kernel pair: a function constant on the fibres factors uniquely through the
quotient. Constant presheaves preserve this sectionwise coequalizer. Set sheafification, being a
left adjoint by [def-weil-pbc-sheafification], preserves that coequalizer and hence gives an
epimorphism of underlying sheaves of sets; finite-limit preservation identifies its sheafified
kernel pair. Thus the induced map of constant module sheaves is an epimorphism. Applying the
induced addition and $B$-action gives exactness on constant module sheaves, so cohomology and
quasi-isomorphisms are preserved. Exact restriction and exact $\nu_X^*$ preserve these
representatives and bounds. We do not shorten $P$ to a perfect complex. The coefficient and
constant-object identifications under geometric inverse image follow as well: a constant sheaf
of sets is the coproduct of copies of the final sheaf indexed by its elements (sheafify the
identical description of the constant presheaf); the inverse image is a finite-limit-preserving
left adjoint, so preserves this coproduct and final object, together with the induced module
operations.

Step 2. Put $M=R\mathcal Hom_{B_X}(\underline E,K)$ on the etale site. Apply
[lem-weil-pbc-ringed-site-bounded-free-rhom-model] to $(\underline P,N)$. Its degree-$n$ model
$T$ has only the indices $a-n\leq i\leq b$. For $P^i=B^{r_i}$, the sheaf-Hom definition
identifies $\mathcal Hom(\underline{P^i},N^{i+n})$ with $(N^{i+n})^{r_i}$: a map is determined
by the images of the $r_i$ standard basis vectors. The same formula holds after any slice
restriction or $\nu_X^*$. These functors preserve finite products, and exactness preserves
cohomology and quasi-isomorphisms. The matrices of $d_P$ and the maps $d_N$ give exactly the
same differential $d_Nf-(-1)^nf d_P$ on both sides. Applying the same model theorem on the
pro-etale site therefore gives the canonical comparison $\nu_X^*M\simeq R\mathcal Hom(\underline
E,\nu_X^*K)$. On slices its restriction is the derived internal Hom of the restricted objects,
by this same termwise calculation. The model vanishes for $n<a-b$, so it is bounded below even
though $P$ may be unbounded to the left.

Step 3. On every etale slice, [lem-pur-rhom-global-sections] identifies the morphism presheaf
with $V\mapsto H^0(V,M)$, by step 2. Choose a K-injective representative $J$ of $M$. By
[lem-pur-kinjective-restrict-localized], $J|_V$ remains K-injective, so this presheaf is
$V\mapsto\ker(J^0(V)\to J^1(V))/\operatorname{im}(J^{-1}(V)\to J^0(V))$. Sheafify this
kernel-image quotient. Exact module sheafification sends its kernel and image to the sheaf
kernel and image and fixes each already-sheaf term $J^i$. The result is precisely
$\ker(d_J^0)/\operatorname{im}(d_J^{-1})=H^0(M)$. This proves the identification $\mathcal
H_{E,K}=H^0(M)$ directly (the elementary kernel-quotient calculation of Tag 0BKV), naturally in
$M$. Exact $\nu_X^*$ gives $\nu_X^*\mathcal H_{E,K}\simeq H^0(\nu_X^*M)$. These canonical maps
extend actual etale-local pullback: the global-Hom formula sends a derived map to its
internal-Hom class, and the kernel-quotient map sends that class to its cohomology-sheaf
section. All maps arise from these same representatives and the induced localization functors.

Step 4. Evaluation over the weakly contractible $U$ is exact by
[lem-weil-pbc-proetale-wcontractible-affine-evaluation-colimits]. In a resolution $\nu_X^*M\to
J$ used to compute derived sections, evaluation preserves the quasi-isomorphism: exactness makes
its evaluated cohomology equal to evaluated sheaf cohomology. Consequently
$H^0(R\Gamma(U,\nu_X^*M))=H^0(\nu_X^*M)(U)$. Apply [lem-pur-rhom-global-sections] on the slice
and the model's slice calculation to identify the left side with the actual derived Hom in the
first displayed bijection. The site and coefficient identification with $U_{\mathrm{proet}}$ is
[lem-weil-proetale-weakly-etale-localization], since $U$ is an object of $X_{\mathrm{proet}}$.
This proves the Hom bijection.

Step 5. For the isomorphism assertion also form the morphism sheaves for $(K,\underline E)$,
$(K,K)$ and $(\underline E,\underline E)$. By
[lem-weil-pbc-finite-ring-derived-local-constancy], etale locally $K$ has a bounded finite
coefficient model. The calculation of steps 1-3 therefore applies on this covering to each pair,
giving the same comparison of morphism sheaves for all four pairs. The local finite-diagonal
comparisons agree on overlaps because they are the canonical comparisons induced by pullback of
morphisms, so they identify the pulled-back etale morphism sheaves with the degree-zero
cohomology sheaves of the four pro-etale derived internal Homs. To evaluate these on $U$, work
now entirely on $X_{\mathrm{proet}}$: for any pair $(A,D)$ among the four pulled-back pairs,
choose a complex $L$ representing $A$ and a K-injective representative $J$ of $D$. By
[def-pur-derived-internal-hom], its derived internal Hom is represented by $\mathcal
Hom^\bullet(L,J)$. Restriction of $J$ remains K-injective by
[lem-pur-kinjective-restrict-localized]. For an object $V\to U$, the slice-Hom formula reads
$\mathcal Hom(L^i,J^{i+n})(V)=\operatorname{Hom}(L^i|_V,J^{i+n}|_V)$ on the pro-etale site and
its slice at $U$; products are sectionwise, so restriction identifies every degree and the
differential $d_Jf-(-1)^nf d_L$ of this complex with $\mathcal Hom^\bullet(L|_U,J|_U)$. The
derived internal Hom definition therefore identifies its restriction with the derived internal
Hom on the slice. [lem-pur-rhom-global-sections] and exact evaluation as in step 4 give the
actual Hom comparison on $U$ for each pair. Composition and identities commute with these
comparisons: the presheaf maps are induced by the functor on localized derived categories; their
degree-zero classes and sheafification give the same compositions, and exact evaluation passes
these classes to the same global morphisms. Now the isomorphism presheaf is the set of pairs
$(f,h)$ satisfying $hf=1_{\underline E}$ and $fh=1_K$, projected to $f$. The inverse is unique,
since $h=h(fh')=(hf)h'=h'$. Sheafification preserves this finite-limit description by
[lem-weil-pbc-sheafification-sets-exact], as do geometric inverse image and section evaluation.
Applying the four Hom comparisons gives precisely pairs of actual inverse derived maps. This
proves the Isom bijection and the identity and composition clauses.

Step 6. Naturality in the two variables and slice restriction follows from the canonical map
taking an actual derived morphism to its internal-Hom class: precomposition, postcomposition and
restriction act on that same map, and the identifications above commute with them. For $B\to C$
as in the statement, the derived tensor-pullback isomorphism of
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback] identifies $\nu_X^*(F\otimes_B^L C)$ with
$(\nu_X^*F)\otimes_B^L C$, naturally in $F$ and therefore in actual derived maps $f$. Thus on
localized etale morphisms the two routes send $f$ to the very same map $(\nu_X^*f)\otimes_B^L
C$. Sheafify this equality; the canonical actual-morphism-to-sheaf-class maps on the pro-etale
site respect the tensor functor, so the resulting square of morphism sheaves commutes.
Evaluation on $U$ and the Hom bijections already proved identify its bottom map with actual
derived scalar extension. The inverse-pair description of step 5 gives the same square for Isom,
since a functor carries inverse pairs to inverse pairs. Apply the Hom computation over $C$ using
the assumed boundedness of $E_C,K_C$; do not tensor the $B$-Hom complex to claim a base-change
isomorphism for internal Hom. No Tor-dimension assumption is used. -/
theorem derivedMorphism_weaklyContractible_evaluation [Finite B]
    (E : DerivedCategory (ModuleCat.{u + 1} B))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (hE : (DerivedCategory.TStructure.t (C := ModuleCat.{u + 1} B)).bounded E)
    (hEf : ∀ n : ℤ, Module.Finite B
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} B) n).obj E))
    (hK : (DerivedCategory.TStructure.t
      (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))).bounded K)
    (hKf : ∀ n : ℤ, IsFiniteLocallyConstantSheaf
      ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) n).obj K))
    (U : X.ProEt) [IsAffine U.left]
    (hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} U) :
    Function.Bijective
        (derivedHomEvaluation X B ((constantDerivedEtale X B).obj E) K U hU) ∧
      Function.Bijective
        (derivedIsoEvaluation X B ((constantDerivedEtale X B).obj E) K U hU) := by
  let A := (constantDerivedEtale X B).obj E
  have hA : (DerivedCategory.TStructure.t
      (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))).bounded A :=
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).bounded_mapDerivedCategory_obj hE
  have hAf (n : ℤ) : IsFiniteLocallyConstantSheaf
      ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) n).obj A) := by
    have := hEf n
    have := constant_finite_etale X B
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} B) n).obj E)
    let e : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} B) n).obj E) ≅
        (DerivedCategory.homologyFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) n).obj A :=
      (Functor.mapDerivedCategoryHomologyFunctorIso
        (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) n).app E
    exact IsFiniteLocallyConstantSheaf.of_iso e
  have hAD := derivedHomSheafComparison_isIso_lisse X B A K hA hAf hK.1
  have hDA := derivedHomSheafComparison_isIso_lisse X B K A hK hKf hA.1
  have hAA := derivedHomSheafComparison_isIso_lisse X B A A hA hAf hA.1
  have hDD := derivedHomSheafComparison_isIso_lisse X B K K hK hKf hK.1
  have := derivedIsoSheafComparison_isIso_of_hom X B A K hAD hDA hAA hDD
  constructor
  · exact (Equiv.ofBijective (proEtaleDerivedHomUnit X B A K U)
      (proEtaleDerivedUnits_bijective X B A K U hU).1).symm.bijective.comp
        (ConcreteCategory.bijective_of_isIso ((derivedHomSheafComparison X B A K).hom.app (op U)))
  · exact (Equiv.ofBijective (proEtaleDerivedIsoUnit X B A K U)
      (proEtaleDerivedUnits_bijective X B A K U hU).2).symm.bijective.comp
        (ConcreteCategory.bijective_of_isIso ((derivedIsoSheafComparison X B A K).hom.app (op U)))

variable (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))

/-- Both evaluation maps extend pullback of actual etale-local morphisms and isomorphisms.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; Cohomology on Sites, Tags 0946
and 09BE; the blueprint amplification proof, finite-source extension.
(blueprint: lem-weil-pbc-derived-isomorphism-sheaf-wcontractible-evaluation)

Proof: The two transpositions defining the comparison are inverse to the corresponding
adjunction hom equivalences. Apply their unit identities to the indicated actual etale-local
map, then use naturality to restrict along g. The result is the pro-etale sheafification unit of
its actual pullback. Evaluation cancels that unit by the inverse of its bijection. The same
computation on hom and inverse gives the Isom assertion. -/
theorem derivedMorphism_evaluation_extends_local
    (U : X.ProEt) [IsAffine U.left]
    (hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} U) :
    (∀ (V : X.Etale) (g : U ⟶ (toProEt X).obj V)
      (f : (derivedSliceRestriction X.smallEtaleTopology B V).obj A ⟶
        (derivedSliceRestriction X.smallEtaleTopology B V).obj D),
      derivedHomEvaluation X B A D U hU (pulledbackEtaleLocalHom X B A D V f U g) =
        derivedLocalHomRestriction (ProEt.topology X) B
          ((derivedComparison X B).obj A) ((derivedComparison X B).obj D) g
            (derivedComparisonLocalHom X B A D V f)) ∧
    (∀ (V : X.Etale) (g : U ⟶ (toProEt X).obj V)
      (f : (derivedSliceRestriction X.smallEtaleTopology B V).obj A ≅
        (derivedSliceRestriction X.smallEtaleTopology B V).obj D),
      derivedIsoEvaluation X B A D U hU (pulledbackEtaleLocalIso X B A D V f U g) =
        derivedLocalIsoRestriction (ProEt.topology X) B
          ((derivedComparison X B).obj A) ((derivedComparison X B).obj D) g
            (derivedComparisonLocalIso X B A D V f)) := by
  constructor
  · intro V g f
    apply (Equiv.ofBijective (proEtaleDerivedHomUnit X B A D U)
      (proEtaleDerivedUnits_bijective X B A D U hU).1).symm_apply_eq.mpr
    have hc := transpose_unit (proEtaleSiteComparison X)
      (((sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).homEquiv _ _).symm
        (derivedComparisonHomPresheafMap X B A D))
    have hs := transpose_unit (sheafificationAdjunction X.smallEtaleTopology (Type (u + 1)))
      (Q := ((toProEt X).sheafPushforwardContinuous (Type (u + 1))
        X.smallEtaleTopology (ProEt.topology X)).obj (derivedComparisonHomTarget X B A D))
      (derivedComparisonHomPresheafMap X B A D)
    change (derivedHomSheafComparison X B A D).hom.app (op U)
      (pulledbackEtaleLocalHom X B A D V f U g) =
        proEtaleDerivedHomUnit X B A D U
          (derivedLocalHomRestriction (ProEt.topology X) B
            ((derivedComparison X B).obj A) ((derivedComparison X B).obj D) g
              (derivedComparisonLocalHom X B A D V f))
    have hn := (derivedHomSheafComparison X B A D).hom.naturality g.op
    have hn' := congrArg (fun k ↦ k
      (((proEtaleSiteComparison X).unit.app
        (derivedLocalHomSheaf X.smallEtaleTopology B A D)).hom.app (op V)
          ((toSheafify X.smallEtaleTopology
            (derivedLocalHomPresheaf X.smallEtaleTopology B A D)).app (op V) f))) hn
    change (derivedHomSheafComparison X B A D).hom.app (op U)
      (pulledbackEtaleLocalHom X B A D V f U g) = _ at hn'
    have hc' := congrArg (fun k ↦ k.hom.app (op V)
      ((toSheafify X.smallEtaleTopology
        (derivedLocalHomPresheaf X.smallEtaleTopology B A D)).app (op V) f)) hc
    have hs' := congrArg (fun k ↦ k.app (op V) f) hs
    change (derivedHomSheafComparison X B A D).hom.app (op ((toProEt X).obj V))
      (((proEtaleSiteComparison X).unit.app
        (derivedLocalHomSheaf X.smallEtaleTopology B A D)).hom.app (op V)
          ((toSheafify X.smallEtaleTopology
            (derivedLocalHomPresheaf X.smallEtaleTopology B A D)).app (op V) f)) = _ at hc'
    change (((sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).homEquiv
      (derivedLocalHomPresheaf X.smallEtaleTopology B A D)
      (((toProEt X).sheafPushforwardContinuous (Type (u + 1))
        X.smallEtaleTopology (ProEt.topology X)).obj
          (derivedComparisonHomTarget X B A D))).symm
            (derivedComparisonHomPresheafMap X B A D)).hom.app (op V)
        ((toSheafify X.smallEtaleTopology
          (derivedLocalHomPresheaf X.smallEtaleTopology B A D)).app (op V) f) =
            derivedComparisonHomUnit X B A D V f at hs'
    exact hn'.trans ((congrArg
      ((derivedComparisonHomTarget X B A D).obj.map g.op) (hc'.trans hs')).trans
        (NatTrans.naturality_apply
          (toSheafify (ProEt.topology X)
            (derivedLocalHomPresheaf (ProEt.topology X) B
              ((derivedComparison X B).obj A) ((derivedComparison X B).obj D)))
          g.op (derivedComparisonLocalHom X B A D V f)).symm)
  · intro V g f
    apply (Equiv.ofBijective (proEtaleDerivedIsoUnit X B A D U)
      (proEtaleDerivedUnits_bijective X B A D U hU).2).symm_apply_eq.mpr
    have hc := transpose_unit (proEtaleSiteComparison X)
      (((sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).homEquiv _ _).symm
        (derivedComparisonIsoPresheafMap X B A D))
    have hs := transpose_unit (sheafificationAdjunction X.smallEtaleTopology (Type (u + 1)))
      (Q := ((toProEt X).sheafPushforwardContinuous (Type (u + 1))
        X.smallEtaleTopology (ProEt.topology X)).obj (derivedComparisonIsoTarget X B A D))
      (derivedComparisonIsoPresheafMap X B A D)
    change (derivedIsoSheafComparison X B A D).hom.app (op U)
      (pulledbackEtaleLocalIso X B A D V f U g) =
        proEtaleDerivedIsoUnit X B A D U
          (derivedLocalIsoRestriction (ProEt.topology X) B
            ((derivedComparison X B).obj A) ((derivedComparison X B).obj D) g
              (derivedComparisonLocalIso X B A D V f))
    have hn := (derivedIsoSheafComparison X B A D).hom.naturality g.op
    have hn' := congrArg (fun k ↦ k
      (((proEtaleSiteComparison X).unit.app
        (derivedLocalIsoSheaf X.smallEtaleTopology B A D)).hom.app (op V)
          ((toSheafify X.smallEtaleTopology
            (derivedLocalIsoPresheaf X.smallEtaleTopology B A D)).app (op V) f))) hn
    change (derivedIsoSheafComparison X B A D).hom.app (op U)
      (pulledbackEtaleLocalIso X B A D V f U g) = _ at hn'
    have hc' := congrArg (fun k ↦ k.hom.app (op V)
      ((toSheafify X.smallEtaleTopology
        (derivedLocalIsoPresheaf X.smallEtaleTopology B A D)).app (op V) f)) hc
    have hs' := congrArg (fun k ↦ k.app (op V) f) hs
    change (derivedIsoSheafComparison X B A D).hom.app (op ((toProEt X).obj V))
      (((proEtaleSiteComparison X).unit.app
        (derivedLocalIsoSheaf X.smallEtaleTopology B A D)).hom.app (op V)
          ((toSheafify X.smallEtaleTopology
            (derivedLocalIsoPresheaf X.smallEtaleTopology B A D)).app (op V) f)) = _ at hc'
    change (((sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).homEquiv
      (derivedLocalIsoPresheaf X.smallEtaleTopology B A D)
      (((toProEt X).sheafPushforwardContinuous (Type (u + 1))
        X.smallEtaleTopology (ProEt.topology X)).obj
          (derivedComparisonIsoTarget X B A D))).symm
            (derivedComparisonIsoPresheafMap X B A D)).hom.app (op V)
        ((toSheafify X.smallEtaleTopology
          (derivedLocalIsoPresheaf X.smallEtaleTopology B A D)).app (op V) f) =
            derivedComparisonIsoUnit X B A D V f at hs'
    exact hn'.trans ((congrArg
      ((derivedComparisonIsoTarget X B A D).obj.map g.op) (hc'.trans hs')).trans
        (NatTrans.naturality_apply
          (toSheafify (ProEt.topology X)
            (derivedLocalIsoPresheaf (ProEt.topology X) B
              ((derivedComparison X B).obj A) ((derivedComparison X B).obj D)))
          g.op (derivedComparisonLocalIso X B A D V f)).symm)

private theorem homEvaluation_unit
    (U : X.ProEt) [IsAffine U.left]
    (hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} U)
    (s : ((comparisonSetUpperStar X).obj
      (derivedLocalHomSheaf X.smallEtaleTopology B A D)).obj.obj (op U)) :
    proEtaleDerivedHomUnit X B A D U (derivedHomEvaluation X B A D U hU s) =
      (derivedHomSheafComparison X B A D).hom.app (op U) s := by
  exact (Equiv.ofBijective (proEtaleDerivedHomUnit X B A D U)
    (proEtaleDerivedUnits_bijective X B A D U hU).1).apply_symm_apply _

private theorem isoEvaluation_unit
    (U : X.ProEt) [IsAffine U.left]
    (hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} U)
    (s : ((comparisonSetUpperStar X).obj
      (derivedLocalIsoSheaf X.smallEtaleTopology B A D)).obj.obj (op U)) :
    proEtaleDerivedIsoUnit X B A D U (derivedIsoEvaluation X B A D U hU s) =
      (derivedIsoSheafComparison X B A D).hom.app (op U) s := by
  exact (Equiv.ofBijective (proEtaleDerivedIsoUnit X B A D U)
    (proEtaleDerivedUnits_bijective X B A D U hU).2).apply_symm_apply _

/-- Both evaluation maps commute with restriction between affine weakly contractible pro-etale
objects.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; Cohomology on Sites, Tags 0946
and 09BE; the blueprint amplification proof, finite-source extension.
(blueprint: lem-weil-pbc-derived-isomorphism-sheaf-wcontractible-evaluation)

Proof: The comparison is a map of sheaves, so commutes with restriction. The pro-etale
sheafification unit is a natural transformation. At both specified objects it is bijective;
invert those two naturality squares. Composing with the comparison square gives the two asserted
equalities. -/
theorem derivedMorphism_evaluation_restriction
    (U V : X.ProEt) [IsAffine U.left] [IsAffine V.left]
    (hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} U)
    (hV : (ProEt.topology X).IsWeaklyContractible.{u + 1} V) (g : V ⟶ U) :
    (∀ s : ((comparisonSetUpperStar X).obj
      (derivedLocalHomSheaf X.smallEtaleTopology B A D)).obj.obj (op U),
      derivedHomEvaluation X B A D V hV
          (((comparisonSetUpperStar X).obj
            (derivedLocalHomSheaf X.smallEtaleTopology B A D)).obj.map g.op s) =
        derivedLocalHomRestriction (ProEt.topology X) B
          ((derivedComparison X B).obj A) ((derivedComparison X B).obj D) g
            (derivedHomEvaluation X B A D U hU s)) ∧
    (∀ s : ((comparisonSetUpperStar X).obj
      (derivedLocalIsoSheaf X.smallEtaleTopology B A D)).obj.obj (op U),
      derivedIsoEvaluation X B A D V hV
          (((comparisonSetUpperStar X).obj
            (derivedLocalIsoSheaf X.smallEtaleTopology B A D)).obj.map g.op s) =
        derivedLocalIsoRestriction (ProEt.topology X) B
          ((derivedComparison X B).obj A) ((derivedComparison X B).obj D) g
            (derivedIsoEvaluation X B A D U hU s)) := by
  constructor
  · intro s
    apply (proEtaleDerivedUnits_bijective X B A D V hV).1.1
    exact (homEvaluation_unit X B A D V hV _).trans
      ((NatTrans.naturality_apply (derivedHomSheafComparison X B A D).hom g.op s).trans
        ((congrArg ((derivedComparisonHomTarget X B A D).obj.map g.op)
          (homEvaluation_unit X B A D U hU s).symm).trans
            (NatTrans.naturality_apply
              (toSheafify (ProEt.topology X)
                (derivedLocalHomPresheaf (ProEt.topology X) B
                  ((derivedComparison X B).obj A) ((derivedComparison X B).obj D)))
              g.op (derivedHomEvaluation X B A D U hU s)).symm))
  · intro s
    apply (proEtaleDerivedUnits_bijective X B A D V hV).2.1
    exact (isoEvaluation_unit X B A D V hV _).trans
      ((NatTrans.naturality_apply (derivedIsoSheafComparison X B A D).hom g.op s).trans
        ((congrArg ((derivedComparisonIsoTarget X B A D).obj.map g.op)
          (isoEvaluation_unit X B A D U hU s).symm).trans
            (NatTrans.naturality_apply
              (toSheafify (ProEt.topology X)
                (derivedLocalIsoPresheaf (ProEt.topology X) B
                  ((derivedComparison X B).obj A) ((derivedComparison X B).obj D)))
              g.op (derivedIsoEvaluation X B A D U hU s)).symm))

private theorem comparisonHom_comp
    (G : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (comparisonSetUpperStar X).map
        (derivedLocalHomSheafComp X.smallEtaleTopology B A D G) ≫
        derivedHomSheafComparison X B A G =
      prodComparison (comparisonSetUpperStar X)
          (derivedLocalHomSheaf X.smallEtaleTopology B A D)
          (derivedLocalHomSheaf X.smallEtaleTopology B D G) ≫
        prod.map (derivedHomSheafComparison X B A D) (derivedHomSheafComparison X B D G) ≫
          derivedLocalHomSheafComp (ProEt.topology X) B
            ((derivedComparison X B).obj A) ((derivedComparison X B).obj D)
            ((derivedComparison X B).obj G) := by
  apply ((proEtaleSiteComparison X).homEquiv _ _).injective
  apply sheaf_binary_ext X.smallEtaleTopology
    (derivedLocalHomPresheaf X.smallEtaleTopology B A D)
    (derivedLocalHomPresheaf X.smallEtaleTopology B D G)
  intro V f g
  let sf := (toSheafify X.smallEtaleTopology
    (derivedLocalHomPresheaf X.smallEtaleTopology B A D)).app (op V) f
  let sg := (toSheafify X.smallEtaleTopology
    (derivedLocalHomPresheaf X.smallEtaleTopology B D G)).app (op V) g
  have hn := (proEtaleSiteComparison X).unit.naturality
    (derivedLocalHomSheafComp X.smallEtaleTopology B A D G)
  have hn' := congrArg (fun k ↦ k.hom.app (op V)
    (sheafPairSection X.smallEtaleTopology _ _ V sf sg)) hn
  change (derivedHomSheafComparison X B A G).hom.app (op ((toProEt X).obj V))
      (((comparisonSetUpperStar X).map
        (derivedLocalHomSheafComp X.smallEtaleTopology B A D G)).hom.app
        (op ((toProEt X).obj V))
        (((proEtaleSiteComparison X).unit.app _).hom.app (op V)
          (sheafPairSection X.smallEtaleTopology _ _ V sf sg))) = _
  change ((proEtaleSiteComparison X).unit.app _).hom.app (op V)
      ((derivedLocalHomSheafComp X.smallEtaleTopology B A D G).hom.app (op V)
        (sheafPairSection X.smallEtaleTopology _ _ V sf sg)) =
    ((comparisonSetUpperStar X).map
      (derivedLocalHomSheafComp X.smallEtaleTopology B A D G)).hom.app
      (op ((toProEt X).obj V))
      (((proEtaleSiteComparison X).unit.app _).hom.app (op V)
        (sheafPairSection X.smallEtaleTopology _ _ V sf sg)) at hn'
  rw [← hn']
  erw [(derivedLocalHomSheafComp_exists X.smallEtaleTopology B A D G).choose_spec.1]
  erw [comparisonHom_generator]
  change derivedComparisonHomUnit X B A G V (f ≫ g) =
    (derivedLocalHomSheafComp (ProEt.topology X) B _ _ _).hom.app
      (op ((toProEt X).obj V))
      ((prod.map (derivedHomSheafComparison X B A D)
        (derivedHomSheafComparison X B D G)).hom.app (op ((toProEt X).obj V))
        ((prodComparison (comparisonSetUpperStar X) _ _).hom.app
          (op ((toProEt X).obj V))
          (((proEtaleSiteComparison X).unit.app _).hom.app (op V)
            (sheafPairSection X.smallEtaleTopology _ _ V sf sg))))
  erw [comparison_pair, pairSection_map]
  dsimp only [sf, sg]
  erw [comparisonHom_generator, comparisonHom_generator]
  unfold derivedComparisonHomUnit
  erw [(derivedLocalHomSheafComp_exists (ProEt.topology X) B
    ((derivedComparison X B).obj A) ((derivedComparison X B).obj D)
    ((derivedComparison X B).obj G)).choose_spec.1]
  congr 1
  simp [derivedComparisonLocalHom, Functor.map_comp, Category.assoc]

/-- Evaluation preserves composition of derived Hom-sheaf sections whenever their arguments match.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; Cohomology on Sites, Tags 0946
and 09BE; the blueprint amplification proof, finite-source extension.
(blueprint: lem-weil-pbc-derived-isomorphism-sheaf-wcontractible-evaluation)

Proof: Actual local pullback is a functor, and so respects composition. The sheafified
compositions are uniquely specified by their values on local morphisms; the two adjunction
transpositions therefore give a comparison preserving those compositions. On the pro-etale side
the sheafification unit preserves composition and is bijective at U. Cancel its bijection to
obtain the displayed equality. -/
theorem derivedMorphism_evaluation_composition
    (G : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (U : X.ProEt) [IsAffine U.left]
    (hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} U)
    (s : ((comparisonSetUpperStar X).obj
      (derivedLocalHomSheaf X.smallEtaleTopology B A D)).obj.obj (op U))
    (t : ((comparisonSetUpperStar X).obj
      (derivedLocalHomSheaf X.smallEtaleTopology B D G)).obj.obj (op U)) :
    derivedHomEvaluation X B A G U hU (pulledbackDerivedHomComp X B A D G U s t) =
      derivedHomEvaluation X B A D U hU s ≫ derivedHomEvaluation X B D G U hU t := by
  apply (proEtaleDerivedUnits_bijective X B A G U hU).1.1
  rw [homEvaluation_unit]
  have hc := congrArg (fun k ↦ k.hom.app (op U)
    ((inv (prodComparison (comparisonSetUpperStar X)
      (derivedLocalHomSheaf X.smallEtaleTopology B A D)
      (derivedLocalHomSheaf X.smallEtaleTopology B D G))).hom.app (op U)
        (sheafPairSection (ProEt.topology X) _ _ U s t)))
    (comparisonHom_comp X B A D G)
  change (derivedHomSheafComparison X B A G).hom.app (op U)
      (pulledbackDerivedHomComp X B A D G U s t) = _ at hc
  rw [hc]
  change (derivedLocalHomSheafComp (ProEt.topology X) B _ _ _).hom.app (op U)
      ((prod.map (derivedHomSheafComparison X B A D)
        (derivedHomSheafComparison X B D G)).hom.app (op U)
        ((prodComparison (comparisonSetUpperStar X) _ _).hom.app (op U)
          ((inv (prodComparison (comparisonSetUpperStar X) _ _)).hom.app (op U)
            (sheafPairSection (ProEt.topology X) _ _ U s t)))) = _
  have hi : (prodComparison (comparisonSetUpperStar X)
      (derivedLocalHomSheaf X.smallEtaleTopology B A D)
      (derivedLocalHomSheaf X.smallEtaleTopology B D G)).hom.app (op U)
      ((inv (prodComparison (comparisonSetUpperStar X) _ _)).hom.app (op U)
        (sheafPairSection (ProEt.topology X) _ _ U s t)) =
      sheafPairSection (ProEt.topology X) _ _ U s t := by
    exact congrArg (fun k ↦ k.hom.app (op U)
      (sheafPairSection (ProEt.topology X) _ _ U s t))
      (IsIso.inv_hom_id (prodComparison (comparisonSetUpperStar X) _ _))
  rw [hi, pairSection_map, ← homEvaluation_unit X B A D U hU s,
    ← homEvaluation_unit X B D G U hU t]
  exact (derivedLocalHomSheafComp_exists (ProEt.topology X) B
    ((derivedComparison X B).obj A) ((derivedComparison X B).obj D)
    ((derivedComparison X B).obj G)).choose_spec.1 U _ _

private theorem comparisonLocalHom_natural
    (A' D' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (f : A' ⟶ A) (g : D ⟶ D') (V : X.Etale)
    (a : (derivedSliceRestriction X.smallEtaleTopology B V).obj A ⟶
      (derivedSliceRestriction X.smallEtaleTopology B V).obj D) :
    derivedComparisonLocalHom X B A' D' V
      ((derivedSliceRestriction X.smallEtaleTopology B V).map f ≫ a ≫
        (derivedSliceRestriction X.smallEtaleTopology B V).map g) =
      (derivedSliceRestriction (ProEt.topology X) B ((toProEt X).obj V)).map
        ((derivedComparison X B).map f) ≫ derivedComparisonLocalHom X B A D V a ≫
      (derivedSliceRestriction (ProEt.topology X) B ((toProEt X).obj V)).map
        ((derivedComparison X B).map g) := by
  simp only [derivedComparisonLocalHom, Functor.map_comp, Category.assoc]
  have hf := (derivedComparisonSliceIso X B V).inv.naturality f
  have hg := (derivedComparisonSliceIso X B V).hom.naturality g
  dsimp only [Functor.comp_map] at hf hg
  rw [← Category.assoc, ← Category.assoc, ← hf]
  simp only [Category.assoc]
  rw [hg]

private theorem comparisonHom_natural
    (A' D' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (f : A' ⟶ A) (g : D ⟶ D') :
    (comparisonSetUpperStar X).map (derivedLocalHomSheafMap f g) ≫
        derivedHomSheafComparison X B A' D' =
      derivedHomSheafComparison X B A D ≫
        derivedLocalHomSheafMap ((derivedComparison X B).map f)
          ((derivedComparison X B).map g) := by
  let θ := derivedLocalHomSheafMap ((derivedComparison X B).map f)
    ((derivedComparison X B).map g)
  let R := (toProEt X).sheafPushforwardContinuous (Type (u + 1))
    X.smallEtaleTopology (ProEt.topology X)
  have hp : derivedLocalHomPresheafMap f g ≫ derivedComparisonHomPresheafMap X B A' D' =
      derivedComparisonHomPresheafMap X B A D ≫ (R.map θ).hom := by
    ext V a
    change derivedComparisonHomUnit X B A' D' V.unop
      ((derivedSliceRestriction X.smallEtaleTopology B V.unop).map f ≫ a ≫
        (derivedSliceRestriction X.smallEtaleTopology B V.unop).map g) =
      θ.hom.app (op ((toProEt X).obj V.unop)) (derivedComparisonHomUnit X B A D V.unop a)
    have hn := (sheafificationAdjunction (ProEt.topology X) (Type (u + 1))).unit.naturality
      (derivedLocalHomPresheafMap ((derivedComparison X B).map f)
        ((derivedComparison X B).map g))
    have hn' := congrArg (fun k ↦ k.app (op ((toProEt X).obj V.unop))
      (derivedComparisonLocalHom X B A D V.unop a)) hn
    exact (congrArg
      ((toSheafify (ProEt.topology X)
        (derivedLocalHomPresheaf (ProEt.topology X) B
          ((derivedComparison X B).obj A') ((derivedComparison X B).obj D'))).app
            (op ((toProEt X).obj V.unop)))
      (comparisonLocalHom_natural X B A D A' D' f g V.unop a)).trans hn'
  have hs := Adjunction.homEquiv_naturality_right_square
    (sheafificationAdjunction X.smallEtaleTopology (Type (u + 1)))
    (Y := R.obj (derivedComparisonHomTarget X B A D))
    (Y' := R.obj (derivedComparisonHomTarget X B A' D'))
    (derivedLocalHomPresheafMap f g)
      (derivedComparisonHomPresheafMap X B A' D')
      (derivedComparisonHomPresheafMap X B A D) (R.map θ) hp
  exact (proEtaleSiteComparison X).homEquiv_naturality_right_square
    (Y := derivedComparisonHomTarget X B A D)
    (Y' := derivedComparisonHomTarget X B A' D')
    (derivedLocalHomSheafMap f g) _ _ θ hs

/-- Evaluation is natural in both derived arguments, contravariantly in the first and covariantly in
the second.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; Cohomology on Sites, Tags 0946
and 09BE; the blueprint amplification proof, finite-source extension.
(blueprint: lem-weil-pbc-derived-isomorphism-sheaf-wcontractible-evaluation)

Proof: Apply naturality of the comparison slice isomorphisms to f and g. Local derived pullback
then intertwines precomposition and postcomposition. Sheafification and adjunction transposition
preserve this equality of presheaf maps. Finally invert the pro-etale sheafification unit, whose
naturality in both objects follows from its definition, to get the stated conjugation-free
formula. -/
theorem derivedMorphism_evaluation_natural
    (A' D' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (f : A' ⟶ A) (g : D ⟶ D') (U : X.ProEt) [IsAffine U.left]
    (hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} U)
    (s : ((comparisonSetUpperStar X).obj
      (derivedLocalHomSheaf X.smallEtaleTopology B A D)).obj.obj (op U)) :
    derivedHomEvaluation X B A' D' U hU
        (((comparisonSetUpperStar X).map (derivedLocalHomSheafMap f g)).hom.app (op U) s) =
      (derivedSliceRestriction (ProEt.topology X) B U).map
          ((derivedComparison X B).map f) ≫
        derivedHomEvaluation X B A D U hU s ≫
          (derivedSliceRestriction (ProEt.topology X) B U).map
            ((derivedComparison X B).map g) := by
  apply (proEtaleDerivedUnits_bijective X B A' D' U hU).1.1
  have hc := congrArg (fun k ↦ k.hom.app (op U) s)
    (comparisonHom_natural X B A D A' D' f g)
  have hn := (sheafificationAdjunction (ProEt.topology X) (Type (u + 1))).unit.naturality
    (derivedLocalHomPresheafMap ((derivedComparison X B).map f)
      ((derivedComparison X B).map g))
  have hn' := congrArg (fun k ↦ k.app (op U) (derivedHomEvaluation X B A D U hU s)) hn
  exact (homEvaluation_unit X B A' D' U hU _).trans
    (hc.trans ((congrArg
      ((derivedLocalHomSheafMap ((derivedComparison X B).map f)
        ((derivedComparison X B).map g)).hom.app (op U))
      (homEvaluation_unit X B A D U hU s).symm).trans hn'.symm))

/-- Evaluation preserves both the identity morphism and the identity isomorphism.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; Cohomology on Sites, Tags 0946
and 09BE; the blueprint amplification proof, finite-source extension.
(blueprint: lem-weil-pbc-derived-isomorphism-sheaf-wcontractible-evaluation)

Proof: Use the extends-local assertion at the terminal etale object with the identity morphism,
respectively the identity isomorphism. Both the localized comparison functor and restriction
preserve identities, giving the two conclusions. -/
theorem derivedMorphism_evaluation_identity
    (U : X.ProEt) [IsAffine U.left]
    (hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} U) :
    derivedHomEvaluation X B A A U hU (pulledbackDerivedIdentity X B A U) = 𝟙 _ ∧
      derivedIsoEvaluation X B A A U hU (pulledbackDerivedIsoIdentity X B A U) =
        Iso.refl _ := by
  have h := derivedMorphism_evaluation_extends_local (X := X) (B := B) A A U hU
  constructor
  · rw [show pulledbackDerivedIdentity X B A U =
        pulledbackEtaleLocalHom X B A A (Scheme.Etale.mk (𝟙 X)) (𝟙 _) U
          (MorphismProperty.Over.homMk U.hom (by
            change U.hom ≫ 𝟙 X = U.hom
            simp)) by rfl]
    rw [h.1 (Scheme.Etale.mk (𝟙 X))
      (MorphismProperty.Over.homMk U.hom (by
        change U.hom ≫ 𝟙 X = U.hom
        simp)) (𝟙 _)]
    simp [derivedLocalHomRestriction, derivedComparisonLocalHom]
  · rw [show pulledbackDerivedIsoIdentity X B A U =
        pulledbackEtaleLocalIso X B A A (Scheme.Etale.mk (𝟙 X)) (Iso.refl _) U
          (MorphismProperty.Over.homMk U.hom (by
            change U.hom ≫ 𝟙 X = U.hom
            simp)) by rfl]
    rw [h.2 (Scheme.Etale.mk (𝟙 X))
      (MorphismProperty.Over.homMk U.hom (by
        change U.hom ≫ 𝟙 X = U.hom
        simp)) (Iso.refl _)]
    simp [derivedLocalIsoRestriction, derivedComparisonLocalIso]

private theorem comparisonIso_comp
    (G : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (comparisonSetUpperStar X).map
        (derivedLocalIsoSheafComp X.smallEtaleTopology B A D G) ≫
        derivedIsoSheafComparison X B A G =
      prodComparison (comparisonSetUpperStar X)
          (derivedLocalIsoSheaf X.smallEtaleTopology B A D)
          (derivedLocalIsoSheaf X.smallEtaleTopology B D G) ≫
        prod.map (derivedIsoSheafComparison X B A D) (derivedIsoSheafComparison X B D G) ≫
          derivedLocalIsoSheafComp (ProEt.topology X) B
            ((derivedComparison X B).obj A) ((derivedComparison X B).obj D)
            ((derivedComparison X B).obj G) := by
  apply ((proEtaleSiteComparison X).homEquiv _ _).injective
  apply sheaf_binary_ext X.smallEtaleTopology
    (derivedLocalIsoPresheaf X.smallEtaleTopology B A D)
    (derivedLocalIsoPresheaf X.smallEtaleTopology B D G)
  intro V f g
  let sf := (toSheafify X.smallEtaleTopology
    (derivedLocalIsoPresheaf X.smallEtaleTopology B A D)).app (op V) f
  let sg := (toSheafify X.smallEtaleTopology
    (derivedLocalIsoPresheaf X.smallEtaleTopology B D G)).app (op V) g
  have hn := (proEtaleSiteComparison X).unit.naturality
    (derivedLocalIsoSheafComp X.smallEtaleTopology B A D G)
  have hn' := congrArg (fun k ↦ k.hom.app (op V)
    (sheafPairSection X.smallEtaleTopology _ _ V sf sg)) hn
  change (derivedIsoSheafComparison X B A G).hom.app (op ((toProEt X).obj V))
      (((comparisonSetUpperStar X).map
        (derivedLocalIsoSheafComp X.smallEtaleTopology B A D G)).hom.app
        (op ((toProEt X).obj V))
        (((proEtaleSiteComparison X).unit.app _).hom.app (op V)
          (sheafPairSection X.smallEtaleTopology _ _ V sf sg))) = _
  change ((proEtaleSiteComparison X).unit.app _).hom.app (op V)
      ((derivedLocalIsoSheafComp X.smallEtaleTopology B A D G).hom.app (op V)
        (sheafPairSection X.smallEtaleTopology _ _ V sf sg)) =
    ((comparisonSetUpperStar X).map
      (derivedLocalIsoSheafComp X.smallEtaleTopology B A D G)).hom.app
      (op ((toProEt X).obj V))
      (((proEtaleSiteComparison X).unit.app _).hom.app (op V)
        (sheafPairSection X.smallEtaleTopology _ _ V sf sg)) at hn'
  rw [← hn']
  erw [(derivedLocalIsoSheafComp_exists X.smallEtaleTopology B A D G).choose_spec.1]
  erw [comparisonIso_generator]
  change derivedComparisonIsoUnit X B A G V (f ≪≫ g) =
    (derivedLocalIsoSheafComp (ProEt.topology X) B _ _ _).hom.app
      (op ((toProEt X).obj V))
      ((prod.map (derivedIsoSheafComparison X B A D)
        (derivedIsoSheafComparison X B D G)).hom.app (op ((toProEt X).obj V))
        ((prodComparison (comparisonSetUpperStar X) _ _).hom.app
          (op ((toProEt X).obj V))
          (((proEtaleSiteComparison X).unit.app _).hom.app (op V)
            (sheafPairSection X.smallEtaleTopology _ _ V sf sg))))
  erw [comparison_pair, pairSection_map]
  dsimp only [sf, sg]
  erw [comparisonIso_generator, comparisonIso_generator]
  unfold derivedComparisonIsoUnit
  erw [(derivedLocalIsoSheafComp_exists (ProEt.topology X) B
    ((derivedComparison X B).obj A) ((derivedComparison X B).obj D)
    ((derivedComparison X B).obj G)).choose_spec.1]
  congr 1
  apply Iso.ext
  simp [derivedComparisonLocalIso]

/-- Evaluation preserves composition on derived Isom-sheaf sections.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; Cohomology on Sites, Tags 0946
and 09BE; the blueprint amplification proof, finite-source extension.
(blueprint: lem-weil-pbc-derived-isomorphism-sheaf-wcontractible-evaluation)

Proof: Composition of actual isomorphisms is preserved by each local comparison functor.
Sheafified composition is its unique extension. Thus the comparison preserves it. At U the
pro-etale sheafification unit on Isom is bijective and preserves composition, so cancelling that
unit proves the formula. -/
theorem derivedMorphism_isoEvaluation_composition
    (G : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (U : X.ProEt) [IsAffine U.left]
    (hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} U)
    (s : ((comparisonSetUpperStar X).obj
      (derivedLocalIsoSheaf X.smallEtaleTopology B A D)).obj.obj (op U))
    (t : ((comparisonSetUpperStar X).obj
      (derivedLocalIsoSheaf X.smallEtaleTopology B D G)).obj.obj (op U)) :
    derivedIsoEvaluation X B A G U hU (pulledbackDerivedIsoComp X B A D G U s t) =
      derivedIsoEvaluation X B A D U hU s ≪≫ derivedIsoEvaluation X B D G U hU t := by
  apply (proEtaleDerivedUnits_bijective X B A G U hU).2.1
  rw [isoEvaluation_unit]
  have hc := congrArg (fun k ↦ k.hom.app (op U)
    ((inv (prodComparison (comparisonSetUpperStar X)
      (derivedLocalIsoSheaf X.smallEtaleTopology B A D)
      (derivedLocalIsoSheaf X.smallEtaleTopology B D G))).hom.app (op U)
        (sheafPairSection (ProEt.topology X) _ _ U s t)))
    (comparisonIso_comp X B A D G)
  change (derivedIsoSheafComparison X B A G).hom.app (op U)
      (pulledbackDerivedIsoComp X B A D G U s t) = _ at hc
  rw [hc]
  change (derivedLocalIsoSheafComp (ProEt.topology X) B _ _ _).hom.app (op U)
      ((prod.map (derivedIsoSheafComparison X B A D)
        (derivedIsoSheafComparison X B D G)).hom.app (op U)
        ((prodComparison (comparisonSetUpperStar X) _ _).hom.app (op U)
          ((inv (prodComparison (comparisonSetUpperStar X) _ _)).hom.app (op U)
            (sheafPairSection (ProEt.topology X) _ _ U s t)))) = _
  have hi : (prodComparison (comparisonSetUpperStar X)
      (derivedLocalIsoSheaf X.smallEtaleTopology B A D)
      (derivedLocalIsoSheaf X.smallEtaleTopology B D G)).hom.app (op U)
      ((inv (prodComparison (comparisonSetUpperStar X) _ _)).hom.app (op U)
        (sheafPairSection (ProEt.topology X) _ _ U s t)) =
      sheafPairSection (ProEt.topology X) _ _ U s t := by
    exact congrArg (fun k ↦ k.hom.app (op U)
      (sheafPairSection (ProEt.topology X) _ _ U s t))
      (IsIso.inv_hom_id (prodComparison (comparisonSetUpperStar X) _ _))
  rw [hi, pairSection_map, ← isoEvaluation_unit X B A D U hU s,
    ← isoEvaluation_unit X B D G U hU t]
  exact (derivedLocalIsoSheafComp_exists (ProEt.topology X) B
    ((derivedComparison X B).obj A) ((derivedComparison X B).obj D)
    ((derivedComparison X B).obj G)).choose_spec.1 U _ _

private theorem comparisonLocalIso_natural
    (A' D' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (f : A' ≅ A) (g : D ≅ D') (V : X.Etale)
    (a : (derivedSliceRestriction X.smallEtaleTopology B V).obj A ≅
      (derivedSliceRestriction X.smallEtaleTopology B V).obj D) :
    derivedComparisonLocalIso X B A' D' V
      ((derivedSliceRestriction X.smallEtaleTopology B V).mapIso f ≪≫ a ≪≫
        (derivedSliceRestriction X.smallEtaleTopology B V).mapIso g) =
      (derivedSliceRestriction (ProEt.topology X) B ((toProEt X).obj V)).mapIso
        ((derivedComparison X B).mapIso f) ≪≫ derivedComparisonLocalIso X B A D V a ≪≫
      (derivedSliceRestriction (ProEt.topology X) B ((toProEt X).obj V)).mapIso
        ((derivedComparison X B).mapIso g) := by
  apply Iso.ext
  exact comparisonLocalHom_natural X B A D A' D' f.hom g.hom V a.hom

private theorem comparisonIso_natural
    (A' D' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (f : A' ≅ A) (g : D ≅ D') :
    (comparisonSetUpperStar X).map (derivedLocalIsoSheafMap f g) ≫
        derivedIsoSheafComparison X B A' D' =
      derivedIsoSheafComparison X B A D ≫
        derivedLocalIsoSheafMap ((derivedComparison X B).mapIso f)
          ((derivedComparison X B).mapIso g) := by
  let θ := derivedLocalIsoSheafMap ((derivedComparison X B).mapIso f)
    ((derivedComparison X B).mapIso g)
  let R := (toProEt X).sheafPushforwardContinuous (Type (u + 1))
    X.smallEtaleTopology (ProEt.topology X)
  have hp : derivedLocalIsoPresheafMap f g ≫ derivedComparisonIsoPresheafMap X B A' D' =
      derivedComparisonIsoPresheafMap X B A D ≫ (R.map θ).hom := by
    ext V a
    change derivedComparisonIsoUnit X B A' D' V.unop
      ((derivedSliceRestriction X.smallEtaleTopology B V.unop).mapIso f ≪≫ a ≪≫
        (derivedSliceRestriction X.smallEtaleTopology B V.unop).mapIso g) =
      θ.hom.app (op ((toProEt X).obj V.unop)) (derivedComparisonIsoUnit X B A D V.unop a)
    have hn := (sheafificationAdjunction (ProEt.topology X) (Type (u + 1))).unit.naturality
      (derivedLocalIsoPresheafMap ((derivedComparison X B).mapIso f)
        ((derivedComparison X B).mapIso g))
    have hn' := congrArg (fun k ↦ k.app (op ((toProEt X).obj V.unop))
      (derivedComparisonLocalIso X B A D V.unop a)) hn
    exact (congrArg
      ((toSheafify (ProEt.topology X)
        (derivedLocalIsoPresheaf (ProEt.topology X) B
          ((derivedComparison X B).obj A') ((derivedComparison X B).obj D'))).app
            (op ((toProEt X).obj V.unop)))
      (comparisonLocalIso_natural X B A D A' D' f g V.unop a)).trans hn'
  have hs := Adjunction.homEquiv_naturality_right_square
    (sheafificationAdjunction X.smallEtaleTopology (Type (u + 1)))
    (Y := R.obj (derivedComparisonIsoTarget X B A D))
    (Y' := R.obj (derivedComparisonIsoTarget X B A' D'))
    (derivedLocalIsoPresheafMap f g)
      (derivedComparisonIsoPresheafMap X B A' D')
      (derivedComparisonIsoPresheafMap X B A D) (R.map θ) hp
  exact (proEtaleSiteComparison X).homEquiv_naturality_right_square
    (Y := derivedComparisonIsoTarget X B A D)
    (Y' := derivedComparisonIsoTarget X B A' D')
    (derivedLocalIsoSheafMap f g) _ _ θ hs

/-- Evaluation on derived Isom is natural under isomorphisms of its arguments.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; Cohomology on Sites, Tags 0946
and 09BE; the blueprint amplification proof, finite-source extension.
(blueprint: lem-weil-pbc-derived-isomorphism-sheaf-wcontractible-evaluation)

Proof: Repeat the naturality calculation for Hom on the hom components of f, g, and the middle
isomorphism. The constructions on Isom were defined by the same conjugation and mapped inverses.
Isomorphism extensionality then gives the asserted equality. -/
theorem derivedMorphism_isoEvaluation_natural
    (A' D' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (f : A' ≅ A) (g : D ≅ D') (U : X.ProEt) [IsAffine U.left]
    (hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} U)
    (s : ((comparisonSetUpperStar X).obj
      (derivedLocalIsoSheaf X.smallEtaleTopology B A D)).obj.obj (op U)) :
    derivedIsoEvaluation X B A' D' U hU
        (((comparisonSetUpperStar X).map (derivedLocalIsoSheafMap f g)).hom.app (op U) s) =
      (derivedSliceRestriction (ProEt.topology X) B U).mapIso
          ((derivedComparison X B).mapIso f) ≪≫
        derivedIsoEvaluation X B A D U hU s ≪≫
          (derivedSliceRestriction (ProEt.topology X) B U).mapIso
            ((derivedComparison X B).mapIso g) := by
  apply (proEtaleDerivedUnits_bijective X B A' D' U hU).2.1
  have hc := congrArg (fun k ↦ k.hom.app (op U) s)
    (comparisonIso_natural X B A D A' D' f g)
  have hn := (sheafificationAdjunction (ProEt.topology X) (Type (u + 1))).unit.naturality
    (derivedLocalIsoPresheafMap ((derivedComparison X B).mapIso f)
      ((derivedComparison X B).mapIso g))
  have hn' := congrArg (fun k ↦ k.app (op U) (derivedIsoEvaluation X B A D U hU s)) hn
  exact (isoEvaluation_unit X B A' D' U hU _).trans
    (hc.trans ((congrArg
      ((derivedLocalIsoSheafMap ((derivedComparison X B).mapIso f)
        ((derivedComparison X B).mapIso g)).hom.app (op U))
      (isoEvaluation_unit X B A D U hU s).symm).trans hn'.symm))

variable {X B}

/-- The comparison identifying scalar extension of the localized pulled-back object with
localization of the pulled-back scalar extension.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; Cohomology on Sites, Tags 0946
and 09BE; the blueprint amplification proof, finite-source extension.
(blueprint: lem-weil-pbc-derived-isomorphism-sheaf-wcontractible-evaluation) -/
noncomputable def scalarEvaluationTransport
    {B' : Type (u + 1)} [CommRing B']
    (T : DerivedLocalFunctor X.smallEtaleTopology B B')
    (S : DerivedLocalFunctor (ProEt.topology X) B B')
    (c : derivedComparison X B ⋙ S.globalFunctor ≅
      T.globalFunctor ⋙ derivedComparison X B')
    (A : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (U : X.ProEt) :
    (S.localFunctor U).obj
        ((derivedSliceRestriction (ProEt.topology X) B U).obj
          ((derivedComparison X B).obj A)) ≅
      (derivedSliceRestriction (ProEt.topology X) B' U).obj
        ((derivedComparison X B').obj (T.globalFunctor.obj A)) :=
  (S.restrictionIso U).app ((derivedComparison X B).obj A) ≪≫
    (derivedSliceRestriction (ProEt.topology X) B' U).mapIso (c.app A)

variable (X B)

private theorem comparisonHom_scalar
    {B' : Type (u + 1)} [CommRing B']
    (T : DerivedLocalFunctor X.smallEtaleTopology B B')
    (S : DerivedLocalFunctor (ProEt.topology X) B B')
    (c : derivedComparison X B ⋙ S.globalFunctor ≅
      T.globalFunctor ⋙ derivedComparison X B')
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (h : ∀ (V : X.Etale)
      (f : (derivedSliceRestriction X.smallEtaleTopology B V).obj A ⟶
        (derivedSliceRestriction X.smallEtaleTopology B V).obj D),
      derivedComparisonLocalHom X B' (T.globalFunctor.obj A) (T.globalFunctor.obj D) V
          ((T.homPresheafMap A D).app (op V) f) =
        (S.homPresheafMap ((derivedComparison X B).obj A)
            ((derivedComparison X B).obj D) ≫
          derivedLocalHomPresheafMap (c.inv.app A) (c.hom.app D)).app
            (op ((toProEt X).obj V)) (derivedComparisonLocalHom X B A D V f)) :
    (comparisonSetUpperStar X).map (T.homSheafMap A D) ≫
        derivedHomSheafComparison X B' (T.globalFunctor.obj A) (T.globalFunctor.obj D) =
      derivedHomSheafComparison X B A D ≫
        S.homSheafMap ((derivedComparison X B).obj A) ((derivedComparison X B).obj D) ≫
          derivedLocalHomSheafMap (c.inv.app A) (c.hom.app D) := by
  let p := S.homPresheafMap ((derivedComparison X B).obj A)
    ((derivedComparison X B).obj D) ≫
      derivedLocalHomPresheafMap (c.inv.app A) (c.hom.app D)
  let θ := S.homSheafMap ((derivedComparison X B).obj A)
    ((derivedComparison X B).obj D) ≫
      derivedLocalHomSheafMap (c.inv.app A) (c.hom.app D)
  let R := (toProEt X).sheafPushforwardContinuous (Type (u + 1))
    X.smallEtaleTopology (ProEt.topology X)
  have hp : T.homPresheafMap A D ≫
        derivedComparisonHomPresheafMap X B' (T.globalFunctor.obj A) (T.globalFunctor.obj D) =
      derivedComparisonHomPresheafMap X B A D ≫ (R.map θ).hom := by
    ext V f
    change derivedComparisonHomUnit X B' (T.globalFunctor.obj A) (T.globalFunctor.obj D)
        V.unop ((T.homPresheafMap A D).app V f) =
      θ.hom.app (op ((toProEt X).obj V.unop))
        (derivedComparisonHomUnit X B A D V.unop f)
    have hn := (sheafificationAdjunction (ProEt.topology X) (Type (u + 1))).unit.naturality p
    have hn' := congrArg (fun k ↦ k.app (op ((toProEt X).obj V.unop))
      (derivedComparisonLocalHom X B A D V.unop f)) hn
    have ht : (presheafToSheaf (ProEt.topology X) (Type (u + 1))).map p = θ := by
      exact Functor.map_comp _ _ _
    change _ = ((presheafToSheaf (ProEt.topology X) (Type (u + 1))).map p).hom.app
      (op ((toProEt X).obj V.unop)) _ at hn'
    rw [ht] at hn'
    exact (congrArg
      ((toSheafify (ProEt.topology X)
        (derivedLocalHomPresheaf (ProEt.topology X) B'
          ((derivedComparison X B').obj (T.globalFunctor.obj A))
          ((derivedComparison X B').obj (T.globalFunctor.obj D)))).app
            (op ((toProEt X).obj V.unop))) (h V.unop f)).trans hn'
  have hs := Adjunction.homEquiv_naturality_right_square
    (sheafificationAdjunction X.smallEtaleTopology (Type (u + 1)))
    (Y := R.obj (derivedComparisonHomTarget X B A D))
    (Y' := R.obj (derivedComparisonHomTarget X B'
      (T.globalFunctor.obj A) (T.globalFunctor.obj D)))
    (T.homPresheafMap A D) _ _ (R.map θ) hp
  exact (proEtaleSiteComparison X).homEquiv_naturality_right_square
    (Y := derivedComparisonHomTarget X B A D)
    (Y' := derivedComparisonHomTarget X B' (T.globalFunctor.obj A) (T.globalFunctor.obj D))
    (T.homSheafMap A D) _ _ θ hs

private theorem comparisonIso_scalar
    {B' : Type (u + 1)} [CommRing B']
    (T : DerivedLocalFunctor X.smallEtaleTopology B B')
    (S : DerivedLocalFunctor (ProEt.topology X) B B')
    (c : derivedComparison X B ⋙ S.globalFunctor ≅
      T.globalFunctor ⋙ derivedComparison X B')
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (h : ∀ (V : X.Etale)
      (f : (derivedSliceRestriction X.smallEtaleTopology B V).obj A ≅
        (derivedSliceRestriction X.smallEtaleTopology B V).obj D),
      derivedComparisonLocalIso X B' (T.globalFunctor.obj A) (T.globalFunctor.obj D) V
          ((T.isoPresheafMap A D).app (op V) f) =
        (S.isoPresheafMap ((derivedComparison X B).obj A)
            ((derivedComparison X B).obj D) ≫
          derivedLocalIsoPresheafMap (c.app A).symm (c.app D)).app
            (op ((toProEt X).obj V)) (derivedComparisonLocalIso X B A D V f)) :
    (comparisonSetUpperStar X).map (T.isoSheafMap A D) ≫
        derivedIsoSheafComparison X B' (T.globalFunctor.obj A) (T.globalFunctor.obj D) =
      derivedIsoSheafComparison X B A D ≫
        S.isoSheafMap ((derivedComparison X B).obj A) ((derivedComparison X B).obj D) ≫
          derivedLocalIsoSheafMap (c.app A).symm (c.app D) := by
  let p := S.isoPresheafMap ((derivedComparison X B).obj A)
    ((derivedComparison X B).obj D) ≫
      derivedLocalIsoPresheafMap (c.app A).symm (c.app D)
  let θ := S.isoSheafMap ((derivedComparison X B).obj A)
    ((derivedComparison X B).obj D) ≫
      derivedLocalIsoSheafMap (c.app A).symm (c.app D)
  let R := (toProEt X).sheafPushforwardContinuous (Type (u + 1))
    X.smallEtaleTopology (ProEt.topology X)
  have hp : T.isoPresheafMap A D ≫
        derivedComparisonIsoPresheafMap X B' (T.globalFunctor.obj A) (T.globalFunctor.obj D) =
      derivedComparisonIsoPresheafMap X B A D ≫ (R.map θ).hom := by
    ext V f
    change derivedComparisonIsoUnit X B' (T.globalFunctor.obj A) (T.globalFunctor.obj D)
        V.unop ((T.isoPresheafMap A D).app V f) =
      θ.hom.app (op ((toProEt X).obj V.unop))
        (derivedComparisonIsoUnit X B A D V.unop f)
    have hn := (sheafificationAdjunction (ProEt.topology X) (Type (u + 1))).unit.naturality p
    have hn' := congrArg (fun k ↦ k.app (op ((toProEt X).obj V.unop))
      (derivedComparisonLocalIso X B A D V.unop f)) hn
    have ht : (presheafToSheaf (ProEt.topology X) (Type (u + 1))).map p = θ := by
      exact Functor.map_comp _ _ _
    change _ = ((presheafToSheaf (ProEt.topology X) (Type (u + 1))).map p).hom.app
      (op ((toProEt X).obj V.unop)) _ at hn'
    rw [ht] at hn'
    exact (congrArg
      ((toSheafify (ProEt.topology X)
        (derivedLocalIsoPresheaf (ProEt.topology X) B'
          ((derivedComparison X B').obj (T.globalFunctor.obj A))
          ((derivedComparison X B').obj (T.globalFunctor.obj D)))).app
            (op ((toProEt X).obj V.unop))) (h V.unop f)).trans hn'
  have hs := Adjunction.homEquiv_naturality_right_square
    (sheafificationAdjunction X.smallEtaleTopology (Type (u + 1)))
    (Y := R.obj (derivedComparisonIsoTarget X B A D))
    (Y' := R.obj (derivedComparisonIsoTarget X B'
      (T.globalFunctor.obj A) (T.globalFunctor.obj D)))
    (T.isoPresheafMap A D) _ _ (R.map θ) hp
  exact (proEtaleSiteComparison X).homEquiv_naturality_right_square
    (Y := derivedComparisonIsoTarget X B A D)
    (Y' := derivedComparisonIsoTarget X B' (T.globalFunctor.obj A) (T.globalFunctor.obj D))
    (T.isoSheafMap A D) _ _ θ hs

private theorem homEvaluation_scalar
    {B' : Type (u + 1)} [CommRing B']
    (T : DerivedLocalFunctor X.smallEtaleTopology B B')
    (S : DerivedLocalFunctor (ProEt.topology X) B B')
    (c : derivedComparison X B ⋙ S.globalFunctor ≅
      T.globalFunctor ⋙ derivedComparison X B')
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (h : (comparisonSetUpperStar X).map (T.homSheafMap A D) ≫
        derivedHomSheafComparison X B' (T.globalFunctor.obj A) (T.globalFunctor.obj D) =
      derivedHomSheafComparison X B A D ≫
        S.homSheafMap ((derivedComparison X B).obj A) ((derivedComparison X B).obj D) ≫
          derivedLocalHomSheafMap (c.inv.app A) (c.hom.app D))
    (U : X.ProEt) [IsAffine U.left]
    (hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} U)
    (s : ((comparisonSetUpperStar X).obj
      (derivedLocalHomSheaf X.smallEtaleTopology B A D)).obj.obj (op U)) :
    derivedHomEvaluation X B' (T.globalFunctor.obj A) (T.globalFunctor.obj D) U hU
        (((comparisonSetUpperStar X).map (T.homSheafMap A D)).hom.app (op U) s) =
      (scalarEvaluationTransport T S c A U).inv ≫
        (S.localFunctor U).map (derivedHomEvaluation X B A D U hU s) ≫
          (scalarEvaluationTransport T S c D U).hom := by
  apply (proEtaleDerivedUnits_bijective X B' (T.globalFunctor.obj A)
    (T.globalFunctor.obj D) U hU).1.1
  let p := S.homPresheafMap ((derivedComparison X B).obj A)
    ((derivedComparison X B).obj D) ≫
      derivedLocalHomPresheafMap (c.inv.app A) (c.hom.app D)
  let θ := S.homSheafMap ((derivedComparison X B).obj A)
    ((derivedComparison X B).obj D) ≫
      derivedLocalHomSheafMap (c.inv.app A) (c.hom.app D)
  have hn := (sheafificationAdjunction (ProEt.topology X) (Type (u + 1))).unit.naturality p
  have ht : (presheafToSheaf (ProEt.topology X) (Type (u + 1))).map p = θ :=
    Functor.map_comp _ _ _
  have hn' := congrArg (fun k ↦ k.app (op U)
    (derivedHomEvaluation X B A D U hU s)) hn
  change _ = ((presheafToSheaf (ProEt.topology X) (Type (u + 1))).map p).hom.app
    (op U) _ at hn'
  rw [ht] at hn'
  have hp : p.app (op U) (derivedHomEvaluation X B A D U hU s) =
      (scalarEvaluationTransport T S c A U).inv ≫
        (S.localFunctor U).map (derivedHomEvaluation X B A D U hU s) ≫
          (scalarEvaluationTransport T S c D U).hom := by
    simp only [p, NatTrans.comp_app, types_comp_apply, DerivedLocalFunctor.homPresheafMap,
      derivedLocalHomPresheafMap, scalarEvaluationTransport, Iso.trans_inv, Iso.trans_hom,
      Functor.mapIso_inv, Functor.mapIso_hom, Category.assoc]
    dsimp
    simp only [Category.assoc]
  change (toSheafify (ProEt.topology X)
      (derivedLocalHomPresheaf (ProEt.topology X) B'
        ((derivedComparison X B').obj (T.globalFunctor.obj A))
        ((derivedComparison X B').obj (T.globalFunctor.obj D)))).app (op U)
      (p.app (op U) (derivedHomEvaluation X B A D U hU s)) =
    θ.hom.app (op U)
      (proEtaleDerivedHomUnit X B A D U (derivedHomEvaluation X B A D U hU s)) at hn'
  rw [hp] at hn'
  exact (homEvaluation_unit X B' (T.globalFunctor.obj A) (T.globalFunctor.obj D) U hU _).trans
    ((congrArg (fun k ↦ k.hom.app (op U) s) h).trans
      ((congrArg (θ.hom.app (op U)) (homEvaluation_unit X B A D U hU s).symm).trans
        hn'.symm))

private theorem isoEvaluation_scalar
    {B' : Type (u + 1)} [CommRing B']
    (T : DerivedLocalFunctor X.smallEtaleTopology B B')
    (S : DerivedLocalFunctor (ProEt.topology X) B B')
    (c : derivedComparison X B ⋙ S.globalFunctor ≅
      T.globalFunctor ⋙ derivedComparison X B')
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (h : (comparisonSetUpperStar X).map (T.isoSheafMap A D) ≫
        derivedIsoSheafComparison X B' (T.globalFunctor.obj A) (T.globalFunctor.obj D) =
      derivedIsoSheafComparison X B A D ≫
        S.isoSheafMap ((derivedComparison X B).obj A) ((derivedComparison X B).obj D) ≫
          derivedLocalIsoSheafMap (c.app A).symm (c.app D))
    (U : X.ProEt) [IsAffine U.left]
    (hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} U)
    (s : ((comparisonSetUpperStar X).obj
      (derivedLocalIsoSheaf X.smallEtaleTopology B A D)).obj.obj (op U)) :
    derivedIsoEvaluation X B' (T.globalFunctor.obj A) (T.globalFunctor.obj D) U hU
        (((comparisonSetUpperStar X).map (T.isoSheafMap A D)).hom.app (op U) s) =
      (scalarEvaluationTransport T S c A U).symm ≪≫
        (S.localFunctor U).mapIso (derivedIsoEvaluation X B A D U hU s) ≪≫
          scalarEvaluationTransport T S c D U := by
  apply (proEtaleDerivedUnits_bijective X B' (T.globalFunctor.obj A)
    (T.globalFunctor.obj D) U hU).2.1
  let p := S.isoPresheafMap ((derivedComparison X B).obj A)
    ((derivedComparison X B).obj D) ≫
      derivedLocalIsoPresheafMap (c.app A).symm (c.app D)
  let θ := S.isoSheafMap ((derivedComparison X B).obj A)
    ((derivedComparison X B).obj D) ≫
      derivedLocalIsoSheafMap (c.app A).symm (c.app D)
  have hn := (sheafificationAdjunction (ProEt.topology X) (Type (u + 1))).unit.naturality p
  have ht : (presheafToSheaf (ProEt.topology X) (Type (u + 1))).map p = θ :=
    Functor.map_comp _ _ _
  have hn' := congrArg (fun k ↦ k.app (op U)
    (derivedIsoEvaluation X B A D U hU s)) hn
  change _ = ((presheafToSheaf (ProEt.topology X) (Type (u + 1))).map p).hom.app
    (op U) _ at hn'
  rw [ht] at hn'
  have hp : p.app (op U) (derivedIsoEvaluation X B A D U hU s) =
      (scalarEvaluationTransport T S c A U).symm ≪≫
        (S.localFunctor U).mapIso (derivedIsoEvaluation X B A D U hU s) ≪≫
          scalarEvaluationTransport T S c D U := by
    apply Iso.ext
    simp only [p, NatTrans.comp_app, types_comp_apply, DerivedLocalFunctor.isoPresheafMap,
      derivedLocalIsoPresheafMap, scalarEvaluationTransport, Iso.trans_inv, Iso.trans_hom,
      Iso.symm_hom, Functor.mapIso_inv, Functor.mapIso_hom, Category.assoc]
    dsimp
    simp only [Category.assoc]
  change (toSheafify (ProEt.topology X)
      (derivedLocalIsoPresheaf (ProEt.topology X) B'
        ((derivedComparison X B').obj (T.globalFunctor.obj A))
        ((derivedComparison X B').obj (T.globalFunctor.obj D)))).app (op U)
      (p.app (op U) (derivedIsoEvaluation X B A D U hU s)) =
    θ.hom.app (op U)
      (proEtaleDerivedIsoUnit X B A D U (derivedIsoEvaluation X B A D U hU s)) at hn'
  rw [hp] at hn'
  exact (isoEvaluation_unit X B' (T.globalFunctor.obj A) (T.globalFunctor.obj D) U hU _).trans
    ((congrArg (fun k ↦ k.hom.app (op U) s) h).trans
      ((congrArg (θ.hom.app (op U)) (isoEvaluation_unit X B A D U hU s).symm).trans
        hn'.symm))

/-- Derived scalar extension commutes with the evaluation maps. Tensor functors are specified as
left adjoints to the existing derived restriction-of-scalars functors, globally and on every
slice. The three unit equations fix the slice and comparison isomorphisms as the canonical
mates. The equations on morphisms hold generally, so in particular give the stated compatibility
whenever the scalar-extended objects satisfy the bounded finite hypotheses; no finite Tor
dimension is required.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; Cohomology on Sites, Tags 0946
and 09BE; the blueprint amplification proof, finite-source extension.
(blueprint: lem-weil-pbc-derived-isomorphism-sheaf-wcontractible-evaluation)

Proof: Construct derived extension of scalars globally and on each localized site using K-flat
resolutions and ordinary sheafified extension of scalars. Their adjunctions to the existing
exact derived restriction-of-scalars functors specify the tensor functors uniquely up to the
unique unit-compatible isomorphism. Restriction and comparison inverse image commute with
restriction of scalars through the specified canonical isomorphisms. Their adjoint mates give
the restriction and comparison isomorphisms for tensor; on K-flat representatives they are the
usual associativity comparisons for tensor and restriction. This proves invertibility and the
displayed three unit normalizations, as well as the localization coherence fields of T and S.
Applying the local tensor functors to an actual derived morphism gives f tensor C; on
isomorphisms apply the functor also to the inverse. The unit-normalized comparison identifies
doing this before or after local comparison. Sheafify this equality and transpose along the two
adjunctions defining the Hom/Isom comparison maps. At a weakly contractible affine the pro-etale
sheafification units are bijective, so their inverses give the two evaluation equalities. The
calculation applies to arbitrary complexes and uses K-flat resolutions, not a finite
Tor-amplitude assumption. In the node apply it to the constant E and K and apply the main
bijectivity theorem on both sides when the transformed objects remain in its bounded finite
range. Exact constant sheaf commutes with this tensor construction on K-flat representatives. -/
theorem derivedMorphism_evaluation_scalarExtension [Finite B]
    (B' : Type (u + 1)) [CommRing B'] [Finite B'] (φ : B →+* B') :
    ∃ T : DerivedLocalFunctor X.smallEtaleTopology B B',
    ∃ S : DerivedLocalFunctor (ProEt.topology X) B B',
    ∃ c : derivedComparison X B ⋙ S.globalFunctor ≅
      T.globalFunctor ⋙ derivedComparison X B',
      ∃ aT : T.globalFunctor ⊣ Sheaf.derivedRestrictScalars X.smallEtaleTopology φ,
      ∃ aS : S.globalFunctor ⊣ Sheaf.derivedRestrictScalars (ProEt.topology X) φ,
      ∃ aTL : ∀ V : X.Etale, T.localFunctor V ⊣
        Sheaf.derivedRestrictScalars (X.smallEtaleTopology.over V) φ,
      ∃ aSL : ∀ U : X.ProEt, S.localFunctor U ⊣
        Sheaf.derivedRestrictScalars ((ProEt.topology X).over U) φ,
      (∀ (A : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
        (V : X.Etale),
        (aTL V).unit.app ((derivedSliceRestriction X.smallEtaleTopology B V).obj A) ≫
            (Sheaf.derivedRestrictScalars (X.smallEtaleTopology.over V) φ).map
              ((T.restrictionIso V).hom.app A) ≫
            (sliceRestrictScalarsIso X.smallEtaleTopology B φ V).hom.app
              (T.globalFunctor.obj A) =
          (derivedSliceRestriction X.smallEtaleTopology B V).map (aT.unit.app A)) ∧
      (∀ (A : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B)))
        (U : X.ProEt),
        (aSL U).unit.app ((derivedSliceRestriction (ProEt.topology X) B U).obj A) ≫
            (Sheaf.derivedRestrictScalars ((ProEt.topology X).over U) φ).map
              ((S.restrictionIso U).hom.app A) ≫
            (sliceRestrictScalarsIso (ProEt.topology X) B φ U).hom.app
              (S.globalFunctor.obj A) =
          (derivedSliceRestriction (ProEt.topology X) B U).map (aS.unit.app A)) ∧
      (∀ A : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)),
        aS.unit.app ((derivedComparison X B).obj A) ≫
            (Sheaf.derivedRestrictScalars (ProEt.topology X) φ).map (c.hom.app A) =
          (derivedComparison X B).map (aT.unit.app A) ≫
            (comparisonRestrictScalarsIso X B φ).hom.app (T.globalFunctor.obj A)) ∧
      (∀ (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
        (U : X.ProEt) [IsAffine U.left]
        (hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} U),
        (∀ s : ((comparisonSetUpperStar X).obj
          (derivedLocalHomSheaf X.smallEtaleTopology B A D)).obj.obj (op U),
          derivedHomEvaluation X B' (T.globalFunctor.obj A) (T.globalFunctor.obj D) U hU
              (((comparisonSetUpperStar X).map (T.homSheafMap A D)).hom.app (op U) s) =
            (scalarEvaluationTransport T S c A U).inv ≫
              (S.localFunctor U).map (derivedHomEvaluation X B A D U hU s) ≫
                (scalarEvaluationTransport T S c D U).hom) ∧
        (∀ s : ((comparisonSetUpperStar X).obj
          (derivedLocalIsoSheaf X.smallEtaleTopology B A D)).obj.obj (op U),
          derivedIsoEvaluation X B' (T.globalFunctor.obj A) (T.globalFunctor.obj D) U hU
              (((comparisonSetUpperStar X).map (T.isoSheafMap A D)).hom.app (op U) s) =
            (scalarEvaluationTransport T S c A U).symm ≪≫
              (S.localFunctor U).mapIso (derivedIsoEvaluation X B A D U hU s) ≪≫
                scalarEvaluationTransport T S c D U)) := by
  obtain ⟨T, S, c, aT, aS, aTL, aSL, hT, hS, hc, hl⟩ :=
    derivedScalarExtension_localSystems X B B' φ
  refine ⟨T, S, c, aT, aS, aTL, aSL, hT, hS, hc, ?_⟩
  intro A D U _ hU
  constructor
  · exact homEvaluation_scalar X B T S c A D
      (comparisonHom_scalar X B T S c A D (hl A D)) U hU
  · apply isoEvaluation_scalar X B T S c A D
      (comparisonIso_scalar X B T S c A D ?_) U hU
    intro V f
    apply Iso.ext
    exact hl A D V f.hom


end AlgebraicGeometry.Scheme
