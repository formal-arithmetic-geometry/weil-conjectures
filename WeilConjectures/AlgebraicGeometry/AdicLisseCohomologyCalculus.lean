/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicLisseCalculusData
import WeilConjectures.AlgebraicGeometry.AdicLisseNormalizedModels
import WeilConjectures.AlgebraicGeometry.AdicLisseExactTensorComparisons
import WeilConjectures.AlgebraicGeometry.AdicLisseLinearDualComparisons

/-! # Cohomology and coefficient duals of adic lisse sheaves

Source: Bhatt--Scholze 6.8.4, 6.8.14--6.8.15.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Qbar : Type (u + 1)) [Field Qbar]
  [Algebra ℚ_[l] Qbar] [IsAlgClosure ℚ_[l] Qbar] (X : Scheme.{u})
  [IsNoetherian X] [X.IsSeparated]
  [hDim : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [hInv : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]


/-- The tensor, cohomology, fibre and linear-dual calculations for the normalized models.
Source: Bhatt--Scholze 6.8.4, 6.8.14--6.8.15; blueprint lisse tensor permanence
(blueprint: lem-per-adic-lisse-cohomology-calculus). -/
structure AdicLisseCohomologyCalculus extends AdicLisseCalculusModels l Qbar X where
  /-- Natural cohomology/tensor comparison, with values still in the exact pbc category. -/
  tensor_cohomology : ∀ a : ℤ,
    ((𝟭 (pbcQbarCategory.{u + 1, u} l Qbar X)).prod realization) ⋙
        adicCalculusTensor l Qbar X comparison ⋙ cohomology a ≅
      ((cohomology a).prod realization) ⋙ adicCalculusTensor l Qbar X comparison
  /-- Fibrewise tensor with a lisse realization is ordinary coefficient tensor. -/
  ordinary_tensor_fiber : ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (x : Spec (.of k) ⟶ X),
    ((𝟭 (pbcQbarCategory.{u + 1, u} l Qbar X)).prod realization) ⋙
        adicCalculusTensor l Qbar X comparison ⋙ fiber k x ≅
      ((fiber k x).prod (lisseAlgebraicFiberFunctor l X x Qbar)) ⋙
        MonoidalCategory.tensor (ModuleCat.{u + 1} Qbar)
  /-- The tensor comparison on geometric fibres, natural in both arguments. -/
  tensor_fiber : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ X)
    (a : ℤ),
    ((𝟭 (pbcQbarCategory.{u + 1, u} l Qbar X)).prod realization) ⋙
        adicCalculusTensor l Qbar X comparison ⋙ cohomology a ⋙ fiber k x ≅
      (((cohomology a ⋙ fiber k x).prod (lisseAlgebraicFiberFunctor l X x Qbar)) ⋙
        (MonoidalCategory.tensor (ModuleCat.{u + 1} Qbar)))
  /-- The displayed fibre calculation is induced by the cohomology comparison. -/
  tensor_fiber_induced : ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (x : Spec (.of k) ⟶ X) (a : ℤ) (K : pbcQbarCategory.{u + 1, u} l Qbar X)
    (L : LisseAlgebraicSheaf l X Qbar),
    (tensor_fiber k x a).hom.app (K, L) =
      (fiber k x).map ((tensor_cohomology a).hom.app (K, L)) ≫
        (ordinary_tensor_fiber k x).hom.app ((cohomology a).obj K, L)
  /-- The contravariant linear dual remains a finite-rank adic lisse sheaf. -/
  dual : (LisseAlgebraicSheaf l X Qbar)ᵒᵖ ⥤ LisseAlgebraicSheaf l X Qbar
  /-- Its fibre is the ordinary coefficient-linear dual. -/
  dual_fiber : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ X)
    (L : LisseAlgebraicSheaf l X Qbar),
    (lisseAlgebraicFiberFunctor l X x Qbar).obj (dual.obj (op L)) ≅
      ModuleCat.of Qbar (Module.Dual Qbar ((lisseAlgebraicFiberFunctor l X x Qbar).obj L))
  /-- Naturality of fibre duality is precomposition with the original fibre map. -/
  dual_fiber_naturality : ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (x : Spec (.of k) ⟶ X) (L M : LisseAlgebraicSheaf l X Qbar) (f : L ⟶ M),
    (lisseAlgebraicFiberFunctor l X x Qbar).map (dual.map f.op) ≫
        (dual_fiber k x L).hom =
      (dual_fiber k x M).hom ≫ ModuleCat.ofHom
        (LinearMap.dualMap ((lisseAlgebraicFiberFunctor l X x Qbar).map f).hom)
  /-- The internal dual belongs to the constructible-Hom domain. -/
  dual_permitted : ∀ L : LisseAlgebraicSheaf l X Qbar,
    commonStageHomPairs l Qbar X
      (op (comparison.functor.obj (realization.obj L)),
        comparison.functor.obj (realization.obj (lisseAlgebraicUnit l X Qbar)))
  /-- The degree-zero linear dual realizes the recorded coefficient derived dual. -/
  dual_realization : ∀ L : LisseAlgebraicSheaf l X Qbar,
    realization.obj (dual.obj (op L)) ≅ comparison.inverse.obj
      ((commonStageDerivedInternalHom l Qbar X).obj
        ⟨(op (comparison.functor.obj (realization.obj L)),
          comparison.functor.obj (realization.obj (lisseAlgebraicUnit l X Qbar))),
          dual_permitted L⟩)

  /-- Naturality of the derived-dual identification, including coefficient-change isomorphisms. -/
  dual_realization_naturality : ∀ (L M : LisseAlgebraicSheaf l X Qbar) (f : L ⟶ M),
    realization.map (dual.map f.op) ≫ (dual_realization L).hom =
      (dual_realization M).hom ≫ comparison.inverse.map
        ((commonStageDerivedInternalHom l Qbar X).map
          (ObjectProperty.homMk
            ((comparison.functor.map (realization.map f)).op,
              𝟙 (comparison.functor.obj (realization.obj (lisseAlgebraicUnit l X Qbar))))))

private theorem induced_tensor_fiber
    (M : AdicLisseCalculusModels l Qbar X)
    (c : ∀ a : ℤ,
      ((𝟭 (pbcQbarCategory.{u + 1, u} l Qbar X)).prod M.realization) ⋙
          adicCalculusTensor l Qbar X M.comparison ⋙ M.cohomology a ≅
        ((M.cohomology a).prod M.realization) ⋙
          adicCalculusTensor l Qbar X M.comparison)
    (b : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ X),
      ((𝟭 (pbcQbarCategory.{u + 1, u} l Qbar X)).prod M.realization) ⋙
          adicCalculusTensor l Qbar X M.comparison ⋙ M.fiber k x ≅
        ((M.fiber k x).prod (lisseAlgebraicFiberFunctor l X x Qbar)) ⋙
          MonoidalCategory.tensor (ModuleCat.{u + 1} Qbar))
    (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ X) (a : ℤ) :
    ∃ e :
      ((𝟭 (pbcQbarCategory.{u + 1, u} l Qbar X)).prod M.realization) ⋙
          adicCalculusTensor l Qbar X M.comparison ⋙ M.cohomology a ⋙ M.fiber k x ≅
        (((M.cohomology a ⋙ M.fiber k x).prod
          (lisseAlgebraicFiberFunctor l X x Qbar)) ⋙
            MonoidalCategory.tensor (ModuleCat.{u + 1} Qbar)),
      ∀ (K : pbcQbarCategory.{u + 1, u} l Qbar X)
        (L : LisseAlgebraicSheaf l X Qbar),
        e.hom.app (K, L) =
          (M.fiber k x).map ((c a).hom.app (K, L)) ≫
            (b k x).hom.app ((M.cohomology a).obj K, L) := by
  let P := (M.cohomology a).prod (𝟭 (LisseAlgebraicSheaf l X Qbar))
  let e := Functor.isoWhiskerRight (c a) (M.fiber k x) ≪≫
    Functor.isoWhiskerLeft P (b k x)
  exact ⟨e, fun _ _ ↦ rfl⟩

/-- Tensoring by a finite-rank lisse adic sheaf preserves the exact completed common-stage
constructible category, commutes naturally with cohomology and geometric fibres, and its
linear dual realizes the coefficient derived internal dual. The bundle records the
canonical finite-stage normalizations, not arbitrary realization or fibre functors.

Source: Bhatt--Scholze, Definitions 6.8.1, 6.8.3, 6.8.8, Lemma 6.8.2,
Propositions 6.8.4, 6.8.14(2), Remark 6.8.15; blueprint lisse tensor permanence proof
(blueprint: lem-per-adic-lisse-cohomology-calculus).

Proof:
1. Choose a common finite coefficient field $E$ for $K$ and $\mathcal L$, as allowed by [def-
   weil-pbc-qbar-category] and [def-pod-lisse-l-adic-sheaves], and an integral representative
   $K_A$, with $A=\mathcal O_E$, uniformizer $\varpi$, $A_n=A/\varpi^n$. By [lem-sfb-noetherian-
   connected-components-open], $X$ is a finite disjoint union of open connected components. On
   each nonempty component choose a geometric point. Clause 2 of [cor-galois-lisse-
   representations] identifies the lisse $E$-sheaf with a continuous finite-dimensional
   representation of its profinite fundamental group. Apply [lem-pod-profinite-stable-lattice]
   to choose an invariant finite-free $A$-lattice. Clause 1 of the representation equivalence
   makes its quotients into finite locally free etale $A_n$-sheaves $L_n$; their quotient maps
   give $L_{n+1}\otimes_{A_{n+1}}A_n\cong L_n$. These systems on disjoint open components form
   one system on $X$. Its rationalization is isomorphic to the original lisse $E$-sheaf by
   clause 2 of the equivalence. Ranks are bounded because there are finitely many components;
   rank zero gives the zero system. No assertion that every pro-etale lisse $E_X$-module has a
   global lisse lattice is used.

2. Put $B=\varprojlim_n(A_n)_X$. By [lem-per-lisse-completed-system-comparison],
   $N=\varprojlim_n u_X^*L_n$ is pro-etale locally finite free over $B$, and $N/\varpi^nN=
   u_X^*L_n$, naturally with their transitions. Clause (ii) of [lem-weil-pbc-integral-
   stratified-perfect-characterization], applied to the single stratum $X$ and the local
   complexes $A^r[0]$, puts $N[0]$ in the exact completed integral category required here,
   including uniform reduction bounds and compatible etale-origin witnesses. Thus $QN$ realizes
   $\mathcal L$ at stage $E$. To use the generic tensor/limit result below, identify its
   coefficient ring $R_X=p_X^*\underline A$ with this $B$ by clause 3 of [det-prop-sfb-qlbar-
   colimit-x-integral-limit]. This is a specified ring-sheaf isomorphism, not an identification
   with the discrete constant sheaf $A_X$.

3. Tensoring $B$-module sheaves with $N$ is exact. Indeed restriction to any slice of a
   trivializing pro-etale covering is exact by [lem-pur-site-restriction-module-adjunction-
   exact], and tensor restricts by [lem-sfb-localized-site-tensor-restriction]. There $N=B^r$,
   so tensor is a finite direct sum of the identity and carries each short exact sequence to its
   direct sum. The kernel and cokernel of any claimed exactness comparison vanish on this cover;
   every local section is therefore locally zero and hence zero by the sheaf axiom. This also
   proves exactness for $r=0$. Consequently, on arbitrary complexes, tensor with $N[0]$
   preserves acyclicity: kernels, images and their quotient commute with this exact additive
   functor. Thus $N[0]$ is K-flat and the ordinary derived tensor $T=K_A\otimes_B^{\mathbf L}N$
   is computed by termwise tensor of any representative $C^\bullet$ of $K_A$.

4. The same kernel/image calculation gives a canonical natural isomorphism $$\mathcal
   H^a(T)\cong\mathcal H^a(K_A)\otimes_BN.$$ More explicitly, tensoring the two exact sequences
   defining the cycles, boundaries and their quotient identifies $Z^a(C\otimes N)$ with
   $Z^a(C)\otimes N$, and the image of $d^{a-1}\otimes1$ with $\operatorname{im}(d^{a-1})\otimes
   N$; quotienting gives the displayed map. This uses the cohomology convention of [def-weil-
   derived-cohomology-sheaves]. It is unchanged under a quasi-isomorphism of representatives,
   since both sides send such a map to an isomorphism, and it is natural in maps of $K_A$ and
   $N$. The bounded cohomology range is unchanged. By clause (iii) of [lem-weil-pbc-integral-
   stratified-perfect-characterization], the cohomology of $K_A$ has finite constant local
   models on finite strata. On a common refinement of their trivializing covers with a cover for
   $N$, its tensor has the model $(B\otimes_A M)^{\oplus r}=B\otimes_A M^{\oplus r}$, with
   $M^{\oplus r}$ finitely presented. The same characterization therefore puts $T$ in the
   required integral category.

5. We now identify this ordinary tensor with the specified completed operation. Apply only the
   final, generic assertion of [det-lem-int-tensor-product], which allows an arbitrary scheme
   $S$, to $S=X$ and $M=N$: its local model is the bounded finite-free complex $A^r[0]$. This
   assertion says that $N\otimes_B^{\mathbf L}-$ preserves sequential derived inverse limits.
   Since $K_A$ is complete, [prop-weil-pbc-koszul-reconstruction] identifies its canonical
   quotient map with $K_A\cong R\varprojlim_n\operatorname{Res}_n K_n$, where
   $K_n=K_A\otimes_B^{\mathbf L}(A_n)_X$. At each level there is the balancing identification
   $$N\otimes_B^{\mathbf
   L}\operatorname{Res}_nK_n\cong\operatorname{Res}_n\bigl(K_n\otimes_{(A_n)_X}^{\mathbf
   L}(N/\varpi^nN)\bigr).$$ On a K-flat representative its map is $y\otimes(x\otimes
   a)\mapsto(x\otimes a)\otimes\bar y$, with the usual degree-zero symmetry; the inverse is
   balancing in the other order. Both maps commute with quotient transitions, because reducing
   $a$ and $y$ before or after this formula gives the same tensor. Taking $R\varprojlim$ and
   using limit preservation identifies $T$ with precisely the completed tensor of [def-weil-
   derived-pullback-tensor-hom]. The comparisons are natural, including in $N$, because the
   product/limit comparison is canonical and the levelwise maps are balanced tensor maps. The
   finite-type characteristic-$p$ tensor-closure assertion earlier in the cited node is not
   applied.

6. Rationalize the integral comparison and the cohomology isomorphism. By [prop-weil-localized-
   tstructure], $Q$ is t-exact and $\mathcal H^a(QK_A)=Q\mathcal H^a(K_A)$, with cohomology
   computed by integral truncations. Thus the preceding steps give
   $Q(K_A\widehat\otimes^{\mathbf L}N)\in D^b_c(X,E)$ and $$\mathcal H^a(QK_A\otimes_E^{\mathbf
   L}QN)\cong Q(\mathcal H^a(K_A)\otimes_BN).$$ The sheaf tensor on the right is the degree-zero
   tensor with $QN$: the integral exactness calculation shows that the tensor of any integral
   heart object with $N$ is concentrated in degree zero, so its rationalized value lies in the
   rational heart. This explains the cohomology sheaves in the statement as rational cohomology
   objects, rather than assigning the unlocalized ambient cohomology sheaf to an arbitrary
   rational representative. All maps extend to rational morphisms: for $f/\varpi^u$ and
   $g/\varpi^v$, the integral naturality square is multiplied by $\varpi^{-(u+v)}$, as in [def-
   weil-derived-pullback-tensor-hom].

7. To compute fibres, restrict to a lisse stratum for $F=\mathcal H^a(K_A)$; such strata and
   finite $A$-module local models exist by [lem-weil-pbc-integral-stratified-perfect-
   characterization]. The sheaf quotients $F/\varpi^nF$ have finite constant models on the
   stratum. Apply [det-pe-finite-local-systems-twist] to descend them to etale local systems.
   Its equivalence also descends their quotient maps and normalization identities; these
   identities hold on the constant finite-module models. Use the adic fibre convention of [def-
   pod-lisse-adic-fibre-functors] there, taking finite-level etale fibres, inverse limit, and
   then inversion of $\varpi$. For the normalized lisse systems of $F$ and $N$, [lem-pod-lisse-
   tensor-and-scalar-extension](2) identifies the level-$n$ tensor fibre with $F_{n,\bar
   x}\otimes_{A_n}L_{n,\bar x}$, by the map sending tensor germs to the germ of their tensor.
   Those maps commute with reduction because the same pure-tensor formula holds at every $n$. By
   [lem-pod-adic-limit-finite-modules](1),(2), the limits recover the finite $A$-modules of the
   two fibres. The second is finite free; after a basis choice tensor with it is a finite direct
   sum, so it commutes with the inverse limit and the displayed fibre becomes $F_{\bar
   x}\otimes_AN_{\bar x}$. This identification itself is basis independent: it is induced by the
   compatible tensor maps. Inverting $\varpi$ gives the desired $E$-fibre formula, and extending
   scalars gives the $\overline{\mathbf Q}_\ell$ formula. This is a calculation of adic fibres,
   with the fibres on $X$ read from their lisse strata; it does not interchange the ordinary
   pro-etale stalk functor with an infinite inverse limit.

8. At every level set $L_n^*=\mathcal Hom_{A_n}(L_n,(A_n)_X)$ on the etale site. Locally
   $L_n=A_n^r$, so $L_n^*=A_n^r$ with the dual basis, and finite-free duality gives
   $L_{n+1}^*\otimes_{A_{n+1}}A_n\cong L_n^*$. These maps agree on overlaps: for a change-of-
   basis matrix $g$, the dual transition is $(g^{-1})^{\mathsf t}$, whose reduction is the
   inverse transpose of the reduction of $g$. Consequently they define a normalized finite-free
   system. By [lem-per-lisse-completed-system-comparison] its inverse-limit realization is the
   locally free $B$-module $N^*=\mathcal Hom_B(N,B)$: reduction of this evaluation-defined
   identification is the identity dual-basis identification on each trivializing cover. Its
   membership in the integral category follows again from [lem-weil-pbc-integral-stratified-
   perfect-characterization], with one stratum and local model $A^r[0]$. It defines a lisse
   $E$-sheaf and hence a lisse $\overline{\mathbf Q}_\ell$-sheaf. Taking finite-level fibres and
   limits as in Step 7 identifies its fibre with $\operatorname{Hom}_A(N_{\bar x},A)$; in a
   basis both sides are $A^r$ and evaluation is $\sum_i a_ib_i$. Inverting $\varpi$ identifies
   it with the $E$-linear dual, and then with the stated algebraic linear dual after extension.

9. Finally identify the derived internal dual. The functor $\mathcal Hom_B(N,-)$ is exact:
   restrict a short exact sequence to a trivializing slice using [lem-pur-site-restriction-
   module-adjunction-exact], then use [lem-sc-finite-free-internal-hom-exact]; the local exact
   sequences imply global exactness by the sheaf axiom. The canonical restriction of ordinary
   sheaf Hom here follows its definition as maps on each slice, so it is compatible with these
   restrictions. Apply [lem-pc-bounded-exact-term-hom-quasi-iso] with the one-term complex
   $N[0]$ to a K-injective resolution $B[0]\to I^\bullet$. It says that $N^*[0]=\mathcal
   Hom^\bullet_B(N[0],B[0])\to\mathcal Hom^\bullet_B(N[0],I^\bullet)$ is a quasi-isomorphism.
   The target computes $R\mathcal Hom_B(N,B)$ by [def-pur-derived-internal-hom]. Thus the
   coefficient derived dual is exactly $N^*[0]$, with its evaluation normalization. It is
   constructible by Step 8, so its rationalization is one of the pairs for which the rational
   internal Hom of [def-weil-derived-pullback-tensor-hom] is defined. Rationalization gives
   $\mathcal L^\vee\cong R\mathcal Hom_E(\mathcal L,E_X)$; the coefficient unit is the image of
   $B[0]$.

10. For $E\subset E'$ the comparisons for completed tensor and internal Hom, their naturality,
   and their identity and tower equations are supplied by [lem-pur-integral-operations-scalar-
   extension]. They apply to $K_A,N$ and the coefficient unit, which lie in the required
   integral categories by the preceding steps. Cohomology also commutes with this scalar
   extension: [lem-sfb-local-field-integral-basis] gives an $A$-basis of $A'=\mathcal O_{E'}$.
   Taking finite-quotient limits gives $B'_X\cong B_X^{\oplus[E':E]}$ as $B_X$-modules. Indeed
   the basis map on coefficients is a homeomorphism for their adic topologies: the ideals
   generated by powers of the two uniformizers are cofinal. In a basis, extension of scalars is
   a finite direct sum and commutes with kernels, images and quotients as in Step 4; hence it is
   t-exact and the cycles-and-boundaries comparison commutes with it. On fibres and duals, the
   maps are respectively $(v\otimes w)\otimes c\mapsto(v\otimes1)\otimes(w\otimes c)$ and
   $(\phi\otimes c)(v\otimes d)=cd\phi(v)$. These formulas agree with the finite-level balanced
   maps and dual evaluations already used. Their identity and associativity equations hold on
   pure tensors and hence on the whole modules. Therefore all cohomology, fibre and dual
   comparisons agree after any further finite extension. Every object, morphism and equality in
   [def-weil-pbc-qbar-category] is represented at a common finite stage; the tower equations
   show that the comparisons descend independently of that stage. This proves all assertions
   over $\overline{\mathbf Q}_\ell$, including naturality.

The integral coefficient transport identifies the two published completed presentations;
it preserves precisely the three integral membership conditions and their normalized
quotient towers. Localize its maps on pure tensors and descend along common finite
coefficient fields. The displayed integral comparisons specify all the functors in the
bundle; the cohomology and fibre tensor comparisons and the dual identification descend
by the compatibilities just established. Naturality on the coefficient localizations
includes coefficient-change isomorphisms, their identities, and their composites. -/
theorem adic_lisse_cohomology_calculus :
    Nonempty (AdicLisseCohomologyCalculus l Qbar X) := by
  classical
  obtain ⟨M⟩ := adic_lisse_normalized_models l Qbar X
  obtain ⟨⟨c⟩, ⟨b⟩⟩ := adic_lisse_exact_tensor_comparisons l Qbar X M
  obtain ⟨d, df, dfn, dp, dr, drn⟩ := adic_lisse_linear_dual_comparisons l Qbar X M
  let e := fun (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ X)
    (a : ℤ) ↦ (induced_tensor_fiber l Qbar X M c b k x a).choose
  refine ⟨{
    toAdicLisseCalculusModels := M
    tensor_cohomology := c
    ordinary_tensor_fiber := b
    tensor_fiber := e
    tensor_fiber_induced := ?_
    dual := d
    dual_fiber := df
    dual_fiber_naturality := dfn
    dual_permitted := dp
    dual_realization := dr
    dual_realization_naturality := drn }⟩
  intro k _ _ x a K L
  exact (induced_tensor_fiber l Qbar X M c b k x a).choose_spec K L

end AlgebraicGeometry.Scheme
