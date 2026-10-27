module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # Compatible affine charts for closed-comparison inverse systems

Source: Stacks Project, limits.tex, Tags 05M5, 01YX and 01YW
(blueprint: lem-trf-closed-comparison-affine-chart-systems).

The upper tail is `Over (op i₀)`. The chart diagrams and cones are Mathlib's
`opensDiagram` and `opensCone`, so their objects are precisely the inverse images
of the initial opens and their arrows are the restricted original arrows.
The tensor product of coordinate rings is expressed as the ring pushout; Mathlib's
`CommRingCat.pushoutCoconeIsColimit` identifies this with the usual algebra tensor
product, with its two standard inclusions. Equations on these inclusions specify
its canonical comparison homomorphism uniquely.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Finite compatible affine charts, their closed comparisons and coordinate-ring limits.

Source: Stacks Project, limits.tex, auxiliary affine-cover reduction under Tag 05M5,
with the chart limits of Tags 01YX and 01YW
(blueprint: lem-trf-closed-comparison-affine-chart-systems).

The transformations `r` and maps `rLim` are the restrictions of the original system
morphism and its limit morphism: their equations with the open inclusions determine
them uniquely. Likewise the two equations for `q` specify the tensor comparison;
those for `g` specify the colimit map, and the projection equations specify the
spectrum isomorphisms canonically.

Proof plan:
1. Choose a finite affine open cover (V_{0,b})_{b\in B} of S_{i_0} using its quasi-compactness
and the finite-affine-cover lemma. For each b, the finite-type definition gives a finite affine
open cover (W_{0,(b,c)})_{c\in A_b} of f_{i_0}^{-1}(V_{0,b}) by opens of X_{i_0} mapping into
V_{0,b}. Put A=\coprod_{b\in B}A_b and b(b,c)=b. Both sets are finite and these source opens
cover X_{i_0}. This uses only quasi-compactness of the base and finite type of f_{i_0}; no
separatedness of the source is needed. Uses: lem-pqf-finite-affine-cover-qc-open, def-weil-
finite-type-morphism.

2. Write s_{ji}:S_j\to S_i, x_{ji}:X_j\to X_i and h_{ji}:X_j\to X_i\times_{S_i}S_j. The
projection p:X_i\times_{S_i}S_j\to X_i is a base change of the affine map s_{ji} and hence
affine. The closed immersion h_{ji} is affine, so x_{ji}=p\circ h_{ji} is affine by composition.
Thus both inverse systems have affine transitions. This factorization does not assert that the
original squares are cartesian. Uses: lem-weil-pbc-affine-morphism-permanence, lem-weil-pbc-
closed-immersion-integral-separated-uc, lem-weil-pbc-affine-composition.

3. Form the specified V_{i,b},W_{i,a},V_b,W_a as pullbacks of the initial open inclusions. Base
change of open immersions makes them open subschemes. Their images are exactly the inverse
images of the initial opens: a morphism into a stage factors through the pullback precisely when
its composite to stage i_0 factors through that initial open, by the fibre-product universal
property. Taking inverse images of the initial covering equalities proves the covering
equalities at every stage and at the limits. The equation f_{i_0}x_{i i_0}=s_{i i_0}f_i gives
W_{i,a}\subseteq f_i^{-1}(V_{i,b(a)}); the analogous cone equation gives W_a\subseteq
f^{-1}(V_{b(a)}). Thus all the indicated restricted morphisms exist. Uses: lem-weil-pbc-open-
immersion-base-change, def-pc-fibre-product, def-weil-open-immersion.

4. For i\ge i_0, the affineness of s_{i i_0} and x_{i i_0} implies that their inverse images
V_{i,b} and W_{i,a} of affine opens are affine. Each f_i is locally of finite type by the
finite-type definition. Apply the all-affine-pairs criterion to the affine opens W_{i,a}\subset
X_i and V_{i,b(a)}\subset S_i constructed above. It says that the actual induced map
A_{i,a}=\Gamma(V_{i,b(a)},\mathcal O)\to C_{i,a}=\Gamma(W_{i,a},\mathcal O) is of finite type.
This application does not require that W_{i,a} be a whole inverse image under f_i. Uses: pqf-
def-affine-morphism, def-weil-finite-type-morphism, lem-weil-pbc-lft-affine-pairs.

5. Fix i\le j in J and a\in A, writing b=b(a). The inverse-image identities give
V_{j,b}=S_j\times_{S_i}V_{i,b}. Since W_{i,a}\to S_i factors through V_{i,b}, the universal
property identifies T:=W_{i,a}\times_{V_{i,b}}V_{j,b} with
(X_i\times_{S_i}S_j)\times_{X_i}W_{i,a}. Pulling back further along h_{ji} gives
X_j\times_{X_i}W_{i,a}=X_j\times_{X_{i_0}}W_{0,a}=W_{j,a}. In each equality the maps to the two
factors agree, so the universal property supplies inverse maps. Consequently the square with
horizontal maps W_{j,a}\to X_j and T\to X_i\times_{S_i}S_j, and vertical maps the restricted
comparison and h_{ji}, is cartesian. Uses: def-pc-fibre-product.

6. The preceding cartesian square expresses the restricted comparison W_{j,a}\to T as a base
change of the given closed immersion h_{ji}. It is therefore a closed immersion. The affine
fibre-product formula identifies T with \operatorname{Spec}(A_{j,a}\otimes_{A_{i,a}}C_{i,a}),
with projections induced by the two tensor inclusions. The affine closed-immersion criterion
then makes its coordinate map onto C_{j,a} surjective. More explicitly, the coordinate map sends
u\otimes v to the image of u under A_{j,a}\to C_{j,a} times the image of v under C_{i,a}\to
C_{j,a}. The two maps agree on A_{i,a} by the system's commutative square, and the tensor
pushout property says that this is the unique map with these two restrictions. Thus it is the
canonical comparison map required in the statement. Uses: lem-weil-pbc-closed-immersion-base-
change, lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-closed-immersion-affine-cover-
criterion, lem-weil-pbc-algebra-tensor-pushout-universal-property.

7. The tail J contains i_0 and is directed: an upper bound in I of two elements of J again
belongs to J. For either original diagram D, any cone (q_j:T\to D_j)_{j\in J} extends to I by
q_i=D(k\to i)q_k, choosing k\ge i,i_0. Two choices give the same map after comparison at a
common upper bound in J. Choosing a common upper bound also proves the extended cone equations,
and this extension is inverse to restriction. It commutes with precomposition by a map of
vertices. Hence the universal property of either original limiting cone remains true after
restriction to J. Uses: def-weil-pbc-category-colimit.

8. Apply the open-restriction statement of the affine-projection/opens lemma to the base system
and V_{0,b}, and to the source system and W_{0,a}. Its hypotheses hold because both systems have
affine transitions by step 2, and the original cones are limiting by assumption. Its conclusions
give exactly V_b=\varprojlim_{i\in J}V_{i,b} and W_a=\varprojlim_{i\in J}W_{i,a}, with the
restricted projections. It also says that the restricted transition morphisms are affine. No
quasi-separatedness hypothesis on X_i is used. Uses: lem-weil-pbc-limit-cone-affine-projections-
opens.

9. For each a, take global sections of the restricted transition maps to form the directed ring
systems A_{i,a} and C_{i,a}. The affine-spectrum correspondence identifies each affine chart
with the spectrum of its stated coordinate ring, and identifies every transition with the
spectrum of its section map. The directed-colimit/spectrum lemma therefore makes
\operatorname{Spec}A_a and \operatorname{Spec}C_a, with their coprojection-induced maps, limits
of the same chart diagrams as in step 8. Uniqueness in the limit universal property supplies the
canonical isomorphisms V_{b(a)}\cong\operatorname{Spec}A_a and W_a\cong\operatorname{Spec}C_a
commuting with every stage projection. Uses: def-weil-affine-spectrum, lem-weil-pbc-spec-
colimit-limit, def-weil-pbc-category-colimit.

10. The squares for W_{j,a}\to V_{j,b(a)} and W_{i,a}\to V_{i,b(a)} commute, so their section
maps g_i:A_{i,a}\to C_{i,a} satisfy g_j\alpha_{ij}=\gamma_{ij}g_i. The colimit universal
property gives g:A_a\to C_a characterized by g\iota_i^A=\iota_i^C g_i. Applying
\operatorname{Spec} shows that \operatorname{Spec}g and the restricted limit map W_a\to V_{b(a)}
have the same composite with every projection to V_{i,b(a)}. The limiting property of V_{b(a)}
makes them equal under the isomorphisms of step 9. Empty initial schemes cause no exception:
take empty index sets for their covers; if S_{i_0} is empty so is X_{i_0} and all its inverse
images. The assertions indexed by a are then vacuous. Uses: def-weil-pbc-category-colimit, def-
weil-affine-spectrum.
-/
theorem exists_closedComparison_affine_chart_systems
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (X S : Iᵒᵖ ⥤ Scheme.{u}) (f : X ⟶ S)
    [∀ i, CompactSpace (S.obj i)] [∀ i, QuasiSeparatedSpace (S.obj i)]
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (S.map t)]
    [∀ i, LocallyOfFiniteType (f.app i)] [∀ i, QuasiCompact (f.app i)]
    (hclosed : ∀ {i j : Iᵒᵖ} (t : i ⟶ j),
      IsClosedImmersion (pullback.lift (X.map t) (f.app i) (f.naturality t)))
    (cX : Cone X) (cS : Cone S) (hcX : IsLimit cX) (hcS : IsLimit cS) (i₀ : I) :
    ∃ (A B : Type u) (b : A → B)
      (V₀ : B → (S.obj (op i₀)).Opens) (W₀ : A → (X.obj (op i₀)).Opens),
      Finite A ∧ Finite B ∧
      (⨆ k, V₀ k) = ⊤ ∧ (⨆ a, W₀ a) = ⊤ ∧
      (∀ k, IsAffineOpen (V₀ k)) ∧ (∀ a, IsAffineOpen (W₀ a)) ∧
      (∀ a, W₀ a ≤ f.app (op i₀) ⁻¹ᵁ V₀ (b a)) ∧
      (∀ i : Over (op i₀),
        (⨆ k, S.map i.hom ⁻¹ᵁ V₀ k) = ⊤ ∧
        (⨆ a, X.map i.hom ⁻¹ᵁ W₀ a) = ⊤) ∧
      (⨆ k, cS.π.app (op i₀) ⁻¹ᵁ V₀ k) = ⊤ ∧
      (⨆ a, cX.π.app (op i₀) ⁻¹ᵁ W₀ a) = ⊤ ∧
      (∀ (k : B) (i : Over (op i₀)), IsAffineOpen (S.map i.hom ⁻¹ᵁ V₀ k)) ∧
      (∀ (a : A) (i : Over (op i₀)), IsAffineOpen (X.map i.hom ⁻¹ᵁ W₀ a)) ∧
      Nonempty (IsLimit (cS.whisker (Over.forget (op i₀)))) ∧
      Nonempty (IsLimit (cX.whisker (Over.forget (op i₀)))) ∧
      (∀ k, Nonempty (IsLimit (opensCone S cS (op i₀) (V₀ k)))) ∧
      (∀ a, Nonempty (IsLimit (opensCone X cX (op i₀) (W₀ a)))) ∧
      ∀ a : A,
        ∃ (r : opensDiagram X (op i₀) (W₀ a) ⟶ opensDiagram S (op i₀) (V₀ (b a)))
          (rLim : (opensCone X cX (op i₀) (W₀ a)).pt ⟶
            (opensCone S cS (op i₀) (V₀ (b a))).pt),
          (∀ i : Over (op i₀),
            r.app i ≫ (opensDiagramι S (op i₀) (V₀ (b a))).app i =
              (opensDiagramι X (op i₀) (W₀ a)).app i ≫ f.app i.left) ∧
          rLim ≫ (cS.π.app (op i₀) ⁻¹ᵁ V₀ (b a)).ι =
            (cX.π.app (op i₀) ⁻¹ᵁ W₀ a).ι ≫
              hcS.lift ((Cone.postcompose f).obj cX) ∧
          (∀ i : Over (op i₀), (r.app i).appTop.hom.FiniteType) ∧
          (∀ (i j : Over (op i₀)) (t : j ⟶ i),
            IsClosedImmersion
              (pullback.lift ((opensDiagram X (op i₀) (W₀ a)).map t)
                (r.app j) (r.naturality t)) ∧
            ∃ q : pushout
                (((opensDiagram S (op i₀) (V₀ (b a))).map t).appTop)
                ((r.app i).appTop) ⟶
              Scheme.Γ.obj (op ((opensDiagram X (op i₀) (W₀ a)).obj j)),
              pushout.inl _ _ ≫ q = (r.app j).appTop ∧
              pushout.inr _ _ ≫ q =
                ((opensDiagram X (op i₀) (W₀ a)).map t).appTop ∧
              Function.Surjective q.hom) ∧
          ∃ (eV : (opensCone S cS (op i₀) (V₀ (b a))).pt ≅
              Spec (colimit ((opensDiagram S (op i₀) (V₀ (b a))) ⋙ Scheme.Γ.rightOp).leftOp))
            (eW : (opensCone X cX (op i₀) (W₀ a)).pt ≅
              Spec (colimit ((opensDiagram X (op i₀) (W₀ a)) ⋙ Scheme.Γ.rightOp).leftOp))
            (g : colimit ((opensDiagram S (op i₀) (V₀ (b a))) ⋙ Scheme.Γ.rightOp).leftOp ⟶
              colimit ((opensDiagram X (op i₀) (W₀ a)) ⋙ Scheme.Γ.rightOp).leftOp),
            (∀ i : Over (op i₀),
              eV.hom ≫ Spec.map (colimit.ι ((opensDiagram S (op i₀) (V₀ (b a))) ⋙
                Scheme.Γ.rightOp).leftOp (op i)) =
                (opensCone S cS (op i₀) (V₀ (b a))).π.app i ≫
                  (ΓSpec.adjunction.unit.app ((opensDiagram S (op i₀) (V₀ (b a))).obj i))) ∧
            (∀ i : Over (op i₀),
              eW.hom ≫ Spec.map (colimit.ι ((opensDiagram X (op i₀) (W₀ a)) ⋙
                Scheme.Γ.rightOp).leftOp (op i)) =
                (opensCone X cX (op i₀) (W₀ a)).π.app i ≫
                  (ΓSpec.adjunction.unit.app ((opensDiagram X (op i₀) (W₀ a)).obj i))) ∧
            (∀ i : Over (op i₀),
              colimit.ι ((opensDiagram S (op i₀) (V₀ (b a))) ⋙ Scheme.Γ.rightOp).leftOp (op i) ≫ g =
                (r.app i).appTop ≫ colimit.ι ((opensDiagram X (op i₀) (W₀ a)) ⋙
                  Scheme.Γ.rightOp).leftOp (op i)) ∧
            eW.hom ≫ Spec.map g = rLim ≫ eV.hom := by
  sorry

end AlgebraicGeometry
