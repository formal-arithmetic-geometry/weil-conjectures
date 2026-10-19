/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import Sheaf.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.ChowLemma
import WeilConjectures.AlgebraicGeometry.ProjectiveSpaceReindexImmersion
import all Sheaf.AlgebraicGeometry.ChowRelativeAmpleTwistProperties

/-! # Integral Chow modification with relatively ample twist

Source: Stacks Project, Cohomology of Schemes, Tags 0200 and 0201, and Morphisms,
Tag 02NR, as used in Étale Cohomology, Tag 0A3M
(blueprint: lem-weil-pbc-integral-chow-relatively-ample).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- An integral Chow modification of a separated finite-type scheme over a field,
with the pullback of the projective twist ample on every affine inverse image.
Source: Stacks Project, Tags 0201 (2),(3), 02NR and 0A3M
(blueprint: lem-weil-pbc-integral-chow-relatively-ample).

Proof:
1. The field $k$ is Noetherian: its only ideals are $0$ and $k$. Thus $\operatorname{Spec}k$ is
   Noetherian, and $X$ is Noetherian by [lem-weil-pbc-finite-type-over-noetherian]. Apply [lem-
   weil-pbc-chow-noetherian] to $X\to\operatorname{Spec}k$, obtaining $N$, $\pi_0:Z\to X$ proper
   surjective, an immersion $j_0:Z\to\mathbf P^N_k$ over $k$, and a dense open $U_0\subset X$ over
   which $\pi_0$ is an isomorphism. Since $X$ is integral it is nonempty, so $U_0$ is nonempty;
   choose a nonempty affine open $U\subset U_0$. It remains dense because $X$ is irreducible.
   Properness implies finite type, and composition preserves finite type (compose the affine-local
   finite algebra generating sets and quasi-compact maps). Hence $Z$ is finite type over $k$ and
   Noetherian by [lem-weil-pbc-finite-type-over-noetherian]. Uses: lem-weil-pbc-finite-type-over-
   noetherian, lem-weil-pbc-chow-noetherian, def-pc-integral-scheme, def-weil-proper-morphism,
   def-weil-finite-type-morphism.
2. Identify $V=\pi_0^{-1}(U)$ with $U$ and let $h:V\hookrightarrow Z$ be its open immersion. The
   scheme $Z$ is quasi-separated by [lem-weil-pbc-locally-noetherian-quasi-separated]; since $V$
   is affine, $h$ is quasi-compact and quasi-separated by [lem-weil-pbc-qcqs-morphism-permanence].
   Let $c:Y\hookrightarrow Z$ be its scheme-theoretic image. By [lemma-nagata-scheme-image-ideal-
   qc], $V$ factors through $Y$ and $|Y|$ is the closure of $V$ in $Z$. By [lemma-nagata-scheme-
   image-restrict-open], restriction to $V$ gives the scheme-theoretic image of $\mathrm{id}_V$,
   which is $V$ (its defining kernel is zero). Thus $c^{-1}(V)\to V$ is an isomorphism, and $V$ is
   a dense nonempty open subscheme of $Y$. Uses: lem-weil-pbc-locally-noetherian-quasi-separated,
   lem-weil-pbc-qcqs-morphism-permanence, lemma-nagata-scheme-image-ideal-qc, lemma-nagata-scheme-
   image-restrict-open, def-nagata-scheme-theoretic-image.
3. The closure of the irreducible space $V\simeq U$ is irreducible: if covered by two closed
   subsets, intersect with $V$; one contains all of $V$, hence its closure. To check reducedness,
   on every affine open $B\subset Z$ the ideal of $Y\cap B$ is $I_B=\ker(\mathcal
   O_Z(B)\to\mathcal O_V(B\cap V))$ by [lem-weil-pbc-scheme-image-qc-kernel]. Every local ring of
   the integral $V$ is a domain by [lem-sc-integral-scheme-stalks-in-function-field]; consequently
   a nilpotent section of $\mathcal O_V$ is zero, since every germ is zero. Thus $a^r\in I_B$
   implies $a\in I_B$, so each $\mathcal O_Z(B)/I_B$ is reduced. These affines cover $Y$, proving
   it reduced. The equivalence in [def-pc-integral-scheme] now proves $Y$ integral. This writes
   out the reducedness assertion of Remark 0201 (3), rather than assuming arbitrary Chow
   modifications integral. Uses: lem-weil-pbc-scheme-image-qc-kernel, lem-sc-integral-scheme-
   stalks-in-function-field, def-pc-integral-scheme.
4. Put $\pi=\pi_0\circ c$ and $j=j_0\circ c$. A closed immersion is proper and proper morphisms
   compose by [lem-weil-pbc-proper-fp-permanence], so $\pi$ is proper. Its image is closed by the
   definition of properness, and contains the dense open $U$ because $\pi^{-1}(U)=c^{-1}(V)\simeq
   V\simeq U$; therefore it is all of $X$. The map $j$ is an immersion by the composition clause
   of the same permanence lemma. Since $\pi$ and $X\to\operatorname{Spec}k$ are separated, their
   composite is separated. They are of finite type, so their composite is of finite type as in
   step 1. This supplies all the asserted geometric properties of $Y,\pi,j,U$. Uses: lem-weil-pbc-
   proper-fp-permanence, def-weil-proper-morphism, def-weil-finite-type-morphism.
5. Form $a=(j,\pi):Y\to\mathbf P^N_k\times_k X=\mathbf P^N_X$. It is an immersion by [lem-chow-
   tuple-immersion], applied to the two $k$-morphisms $j$ and $\pi$. The projection $q:\mathbf
   P^N_X\to X$ is proper by [lemma-nagata-projective-space-base-change-proper], hence separated.
   As $q\circ a=\pi$ is proper, [lem-weil-pbc-proper-over-separated] proves that $a$ is proper.
   Thus [lem-weil-pbc-proper-immersion-closed] proves that $a$ is a closed immersion. Only $\pi$,
   not $X\to\operatorname{Spec}k$, was required to be proper. Uses: lem-chow-tuple-immersion, def-
   nagata-projective-space-base-change, lemma-nagata-projective-space-base-change-proper, def-
   weil-proper-morphism, lem-weil-pbc-proper-over-separated, lem-weil-pbc-proper-immersion-closed.
6. Use [lem-weil-pbc-projective-space-standard-charts] with the finite nonempty coordinate set
   $\{0,\ldots,N\}$. Its clauses (a),(b) provide the covering by the pulled-back opens $D_+(T_i)$
   and free generators $T_i$ of the pullback of the Proj twist from $\mathbf P^N_{\mathbf Z}$,
   with $T_i=(T_i/T_j)T_j$ on overlaps. Over $\operatorname{Spec}k$, clause (c) identifies these
   charts with $\operatorname{Spec}k[T_l/T_i:l\ne i]$. On their overlaps, sending the generator
   $e_i^{(1)}$ in [def-pc-projective-space-twist] to $T_i$ respects exactly the relation
   $e_i^{(1)}=(T_i/T_j)e_j^{(1)}$; the resulting local isomorphisms therefore glue. This
   identifies the line bundle used in the statement with the pullback of the Proj twist from
   $\mathbf P^N_{\mathbf Z}$. For $r:\mathbf P^N_X\to\mathbf P^N_k$ the second projection, the
   projections $\rho_X:\mathbf P^N_X\to\mathbf P^N_{\mathbf Z}$ and $\rho_k:\mathbf
   P^N_k\to\mathbf P^N_{\mathbf Z}$ satisfy $\rho_k\circ r=\rho_X$, by the fibre-product universal
   property. Thus pullback composition [def-pc-module-pullback] gives $r^*\mathcal O_{\mathbf
   P^N_k}(1)\cong\rho_X^*\mathcal O_{\mathbf P^N_{\mathbf Z}}(1)=\mathcal O_{\mathbf P^N_X}(1)$
   and, since $r\circ a=j$, $\mathcal L\cong a^*\mathcal O_{\mathbf P^N_X}(1)$. The chart
   generators also prove invertibility. For every affine open $W=\operatorname{Spec}A\subset X$,
   the base change $a_W:\pi^{-1}(W)\to\mathbf P^N_A$ of the closed immersion $a$ is a closed
   immersion by [lem-weil-pbc-proper-fp-permanence] (b). Its composite with the structural
   projection is the restriction of $\pi$. The same equality of projections to $\mathbf
   P^N_{\mathbf Z}$ and pullback composition identify $a_W^*\mathcal O_{\mathbf P^N_A}(1)$ with
   $\mathcal L|_{\pi^{-1}(W)}$, using exactly the definition of the twist in [lem-weil-pbc-
   projective-ample-invertible]. That theorem now proves this restriction invertible and ample.
   Since $W$ is arbitrary this is the required relative ampleness. For the empty affine open the
   inverse image is empty, quasi-compactness holds, and the affine nonvanishing-cover condition is
   vacuous. Uses: def-pc-projective-space-twist, def-pc-module-pullback, lem-weil-pbc-proper-fp-
   permanence, lem-weil-pbc-projective-ample-invertible, lem-weil-pbc-projective-space-standard-
   charts.
-/
theorem exists_integral_chow_relatively_ample
    (k : Type u) [Field k] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (N : ℕ) (Y : Scheme.{u}) (π : Y ⟶ X)
      (j : Y ⟶ ProjectiveSpace (ULift.{u} (Fin (N + 1))) (Spec (.of k))),
      IsIntegral Y ∧ IsSeparated (π ≫ f) ∧ LocallyOfFiniteType (π ≫ f) ∧
        QuasiCompact (π ≫ f) ∧ IsProper π ∧ Surjective π ∧ IsImmersion j ∧
        j ≫ (ProjectiveSpace (ULift.{u} (Fin (N + 1))) (Spec (.of k)) ↘ Spec (.of k)) =
          π ≫ f ∧
        ∃ U : X.Opens, (U : Set X).Nonempty ∧ IsIso (π ∣_ U) ∧
          ∃ _ : ((Scheme.Modules.tensorPullback j).obj
              (ProjectiveSpace.twist (ULift.{u} (Fin (N + 1))) (Spec (.of k)) 1)).IsInvertible,
            ∀ W : X.Opens, IsAffineOpen W →
              ∃ hW : ((Scheme.Modules.tensorPullback (π ⁻¹ᵁ W).ι).obj
                  ((Scheme.Modules.tensorPullback j).obj
                    (ProjectiveSpace.twist (ULift.{u} (Fin (N + 1)))
                      (Spec (.of k)) 1))).IsInvertible,
                @Scheme.Modules.IsAmple (π ⁻¹ᵁ W).toScheme
                  ((Scheme.Modules.tensorPullback (π ⁻¹ᵁ W).ι).obj
                    ((Scheme.Modules.tensorPullback j).obj
                      (ProjectiveSpace.twist (ULift.{u} (Fin (N + 1)))
                        (Spec (.of k)) 1))) hW := by
  classical
  -- The schematic closure of the integral open repairs integrality of the Chow model.
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let Z := ChowModification f
  let p := ChowModification.modificationMap f
  let j₀ := ChowModification.toProjectiveSpace f
  obtain ⟨U, hUd, hUi⟩ := ChowModification.exists_dense_isIso_restrict f
  have hUn : (U : Set X).Nonempty := hUd.nonempty
  have : Nonempty U := hUn.to_subtype
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  let V : Z.Opens := p ⁻¹ᵁ U
  have : IsIso (p ∣_ U) := hUi
  have : Nonempty V := by
    obtain ⟨x, _⟩ := (p ∣_ U).surjective (Classical.arbitrary U)
    exact ⟨x⟩
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion (p ∣_ U)
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (p ≫ f)
  have : QuasiCompact V.ι := inferInstance
  let Y := V.ι.image
  let c : Y ⟶ Z := V.ι.imageι
  let π : Y ⟶ X := c ≫ p
  have : IsReduced Y := IsSchemeTheoreticallyDominant.isReduced V.ι.toImage
  have : IrreducibleSpace Y := by
    rw [irreducibleSpace_def]
    have h := (IrreducibleSpace.isIrreducible_univ V.toScheme).image V.ι.toImage.base
      V.ι.toImage.continuous.continuousOn
    rw [Set.image_univ] at h
    simpa [V.ι.toImage.denseRange.closure_range] using h.closure
  have : IsIntegral Y := isIntegral_of_irreducibleSpace_of_isReduced Y
  have : IsProper π := inferInstance
  have : IsDominant U.ι := ⟨by rwa [DenseRange, Scheme.Opens.range_ι]⟩
  have hdom : IsDominant (V.ι.toImage ≫ π) := by
    have hw : V.ι.toImage ≫ π = (p ∣_ U) ≫ U.ι := by
      dsimp [π, c]
      rw [← Category.assoc, Scheme.Hom.toImage_imageι, morphismRestrict_ι]
    rw [hw]
    infer_instance
  have : IsDominant π := IsDominant.of_comp V.ι.toImage π
  have : Surjective π := inferInstance
  have hπU : IsIso (π ∣_ U) := by
    dsimp [π]
    rw [morphismRestrict_comp]
    infer_instance
  have : Nonempty (ChowModification.index f) := by
    let x : V.toScheme := Classical.arbitrary V
    have hx : j₀ (V.ι x) ∈ ⨆ i, ProjectiveSpace.standardOpen
        (ChowModification.index f) (Spec (.of k)) i := by
      rw [ProjectiveSpace.iSup_standardOpen]
      trivial
    obtain ⟨i, _⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨i⟩
  obtain ⟨N, j, hj, hjf⟩ := exists_reindexed_projective_immersion
    (ChowModification.index f) (c ≫ j₀) (π ≫ f) (by
      simp only [π, j₀, p, Category.assoc, ChowModification.toProjectiveSpace_over])
  have : IsImmersion j := hj
  let n := ULift.{u} (Fin (N + 1))
  let ρ := ProjectiveSpace.toProjInt n (Spec (.of k))
  let t := Proj.twist (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)) 1
  let a := ProjectiveSpace.liftBaseChange π j hjf.symm
  have : IsImmersion a := inferInstance
  have : IsProper (a ≫ (ProjectiveSpace n X ↘ X)) := by
    rw [ProjectiveSpace.liftBaseChange_over]
    infer_instance
  have : IsProper a := IsProper.of_comp a (ProjectiveSpace n X ↘ X)
  have : IsClosedImmersion a :=
    IsClosedImmersion.of_isPreimmersion a a.isClosedMap.isClosed_range
  obtain ⟨eρ⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction ρ
  let e := (Scheme.Modules.tensorPullback j).mapIso
    ((eρ.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction ρ)).app t)
  -- Compare tensor pullback with the usual pullback defining the twist.
  have ht := tensorPullback_invertible ρ t
  have hL := tensorPullback_invertible j ((Scheme.Modules.tensorPullback ρ).obj t)
  have htw : ((Scheme.Modules.tensorPullback j).obj
      (ProjectiveSpace.twist n (Spec (.of k)) 1)).IsInvertible :=
    Scheme.Modules.IsInvertible.of_iso e
  refine ⟨N, Y, π, j, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hj, hjf, U, hUn, hπU, htw, ?_⟩
  intro W hW
  obtain ⟨hA, hample⟩ := projective_ample_affine_open N X Y π a
    (ProjectiveSpace.liftBaseChange_over π j hjf.symm).symm W hW
  obtain ⟨ep⟩ := tensorPullback_pair_iso j ρ a (ProjectiveSpace.toProjInt n X)
    (ProjectiveSpace.liftBaseChange_toProjInt π j hjf.symm).symm t
  let eW := (Scheme.Modules.tensorPullback (π ⁻¹ᵁ W).ι).mapIso (e.symm ≪≫ ep)
  have : ((Scheme.Modules.tensorPullback (π ⁻¹ᵁ W).ι).obj
      ((Scheme.Modules.tensorPullback a).obj
        ((Scheme.Modules.tensorPullback (ProjectiveSpace.toProjInt n X)).obj t))).IsInvertible := hA
  have hW' := Scheme.Modules.IsInvertible.of_iso eW.symm
  exact ⟨hW', (Scheme.Modules.isAmple_iff_of_iso eW).mpr hample⟩

end AlgebraicGeometry
