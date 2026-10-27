/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Sheaf.AlgebraicGeometry.RhoSectionModules
public import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousLineBundleSections
public import Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Sheaf.AlgebraicGeometry.GroupScheme.BruhatLongestCellCharts
import Sheaf.AlgebraicGeometry.GeometricallyIrreducibleProduct
import Sheaf.AlgebraicGeometry.GroupScheme.RhoRegularWeylOrbit
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # The invariant section on the double flag variety

Source: Milne, Algebraic Groups (2017), Theorem 21.80, Example 21.83,
Theorem 21.84, Theorem 22.48 and Remark 22.49, pp.450--451 and 479--480.
(blueprint: lem-sfb-double-flag-invariant-boundary)

The external tensor product and its frame are constructed from the two homogeneous
factors. Invariance is expressed in these frames on every test scheme, which is
an identity of rational coactions, including on nonreduced test schemes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite
open scoped MonObj

namespace AlgebraicGeometry

namespace DoubleFlag

/-- The external square of the specified homogeneous invertible module.
Source: Milne, Section 18c and 22.48
(blueprint: lem-sfb-double-flag-invariant-boundary). -/
def externalSquare {F : Type u} [Field F] (Q : Over (Spec (.of F)))
    (L : Q.left.Modules) : (Q ⊗ Q).left.Modules :=
  (Scheme.Modules.pullback (fst Q Q).left).obj L ⊗
    (Scheme.Modules.pullback (snd Q Q).left).obj L

/-- The canonical frame on the external square above a pair of lifts to the group.
The two composition comparisons and the tensor comparison are the usual pullback
isomorphisms, and the last map multiplies the two structure-sheaf factors.
Source: Milne, Section 18c, and 22.48
(blueprint: lem-sfb-double-flag-invariant-boundary). -/
def frame {F : Type u} [Field F] {G Q Z : Over (Spec (.of F))}
    (π : G ⟶ Q) (L : Q.left.Modules)
    (θ : (Scheme.Modules.pullback π.left).obj L ≅ Scheme.Modules.unit G.left)
    (g h : Z ⟶ G) :
    (Scheme.Modules.pullback (lift (g ≫ π) (h ≫ π)).left).obj (externalSquare Q L) ≅
      Scheme.Modules.unit Z.left :=
  (Functor.Monoidal.μIso (Scheme.Modules.pullback (lift (g ≫ π) (h ≫ π)).left)
    ((Scheme.Modules.pullback (fst Q Q).left).obj L)
    ((Scheme.Modules.pullback (snd Q Q).left).obj L)).symm ≪≫
  tensorIso
    (((Scheme.Modules.pullbackComp (lift (g ≫ π) (h ≫ π)).left
      (fst Q Q).left).app L) ≪≫
      (Scheme.Modules.pullbackCongr
        (congrArg Over.Hom.left (lift_fst (g ≫ π) (h ≫ π)))).app L ≪≫
      AssociatedCharacterLineBundle.trivializationAt π L θ g)
    (((Scheme.Modules.pullbackComp (lift (g ≫ π) (h ≫ π)).left
      (snd Q Q).left).app L) ≪≫
      (Scheme.Modules.pullbackCongr
        (congrArg Over.Hom.left (lift_snd (g ≫ π) (h ≫ π)))).app L ≪≫
      AssociatedCharacterLineBundle.trivializationAt π L θ h) ≪≫
  (λ_ (Scheme.Modules.unit Z.left))

/-- The coefficient of a section in the two canonical homogeneous frames.
Source: Milne, Section 18c, and 22.48
(blueprint: lem-sfb-double-flag-invariant-boundary). -/
def coefficient {F : Type u} [Field F] {G Q Z : Over (Spec (.of F))}
    (π : G ⟶ Q) (L : Q.left.Modules)
    (θ : (Scheme.Modules.pullback π.left).obj L ≅ Scheme.Modules.unit G.left)
    (g h : Z ⟶ G) (d : Γ(externalSquare Q L, ⊤)) : RhoSection.Coordinate Z :=
  (frame π L θ g h).hom.app ⊤
    (AssociatedCharacterLineBundle.pullTopSection (lift (g ≫ π) (h ≫ π)).left
      (externalSquare Q L) d)

/-- The actual subalgebra of regular functions fixed by right translation by T.
Equality after pullback along the action and projection is precisely invariance
after every algebra extension, including nonreduced algebras.
Source: Milne, Example 21.83
(blueprint: lem-sfb-double-flag-invariant-boundary). -/
def rightInvariants {F : Type u} [Field F]
    {G T : Grp (Over (Spec (.of F)))} (i : T ⟶ G) :
    Subalgebra F (RhoSection.Coordinate G.X) :=
  AlgHom.equalizer
    (((algΓ (.of F)).map (fst G.X T.X * (snd G.X T.X ≫ i.hom.hom))).unop.hom)
    (((algΓ (.of F)).map (fst G.X T.X)).unop.hom)

end DoubleFlag

/-- The opposite double-flag orbit is the dense nonvanishing open of a nonzero
invariant rho section. Its orbit map is a faithfully flat right T-torsor and its
regular functions are canonically the right T-invariants in F[S]. The final
identity states equivariance for left translation, on every test scheme.

Source: Milne, Theorem 21.80, Example 21.83, Theorem 21.84, Theorem 22.48
and Remark 22.49, pp.450--451 and 479--480.
(blueprint: lem-sfb-double-flag-invariant-boundary)

Proof plan:
1. Apply lem-sfb-bruhat-longest-cell-charts to the reductive group supplied by
   lem-sfb-reductive-borel-pair-structure. Choose n₀ representing w₀. Its Borel
   intersection is T. The finite affine-space flag charts show reducedness and
   quasi-compactness of Q×Q. The product irreducibility lemma gives irreducibility;
   proper base change and composition give separatedness.
2. The nonzero module from lem-sfb-rho-section-modules and the primitive-line
   lemma give a nonzero unipotent-fixed f in E_B(-rho). Its left weight is rho,
   by lem-sfb-rho-regular-weyl-orbit. Thus f(bx)=rho(b)⁻¹f(x) and
   f(xb)=rho(b)f(x) on every test algebra.
3. Comparing f(t n_w) in two ways shows f(n_w)≠0 only when w rho=-rho,
   hence only for w₀. Bruhat strata show f(n₀)≠0; normalize it to 1.
   Its nonvanishing open is the longest cell, also after scalar extension.
4. Set delta(g,h)=f(g⁻¹h). Its right B×B transformation is multiplication
   by rho(b₁)rho(b₂). The transition rule of
   lem-sfb-homogeneous-line-bundle-sections glues it to d in the external square.
   The identity delta(sg,sh)=delta(g,h) is precisely invariance in the displayed
   canonical frames. The value at (1,n₀) is 1, so d is nonzero.
5. On a flag chart with lift a(x), use coordinates (x,a(x)⁻¹y). The open is
   chart×longest-cell. Writing the second coordinate uniquely as un₀B gives
   the local section a(x)u of the orbit map. Its image is exactly X_d, dense
   because X is integral and this open is nonempty.
6. The equality B∩n₀Bn₀⁻¹=T identifies the kernel pair with S×T by
   (g,t)↦(g,gt). The local sections trivialize the right torsor. A split torus
   is flat over F and the projection is surjective, giving faithful flatness.
7. Right-invariant functions descend by evaluating on each local section.
   They agree on overlaps by right T-invariance; gluing gives the inverse of
   pullback. Pullback is injective by those same local sections. The identity
   q(sg)=s q(g) proves the displayed algebraic equivariance.
8. For S=1 the empty root system gives rho=0, f=d=1 and Q=X=U=Spec F;
   both the torsor and the algebra isomorphism are identities. No positive-rank
   or positive-characteristic exclusion occurs. -/
theorem exists_double_flag_invariant_boundary
    {F : Type u} [Field F] [IsAlgClosed F]
    (S T B : Grp (Over (Spec (.of F)))) (hS : IsSemisimpleGroupScheme S.X)
    (hsc : ∀ (S' : Over (Spec (.of F))) [GrpObj S'],
      IsSemisimpleGroupScheme S' → ∀ (f : S' ⟶ S.X) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f)
        (s : StandardGroupSchemes.affine F A ⟶ S'),
        (x ≫ GrpObj.kerι f) * s = s * (x ≫ GrpObj.kerι f)) → IsIso f)
    (iT : T ⟶ S) (iB : B ⟶ S) (j : T ⟶ B) (hpair : IsRhoBorelPair iT iB j)
    (a : ModObj T.X B.X)
    (ha : ∀ (Z : Over (Spec (.of F))) (t : Z ⟶ T.X) (b : Z ⟶ B.X),
      lift t b ≫ a.smul = (t ≫ j.hom.hom) * b * (t ≫ j.hom.hom)⁻¹)
    (Φ : List (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (ρ : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))
    (ρB χ : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))
    (hΦ : Φ.Nodup)
    (hroots : ∀ α, α ∈ Φ ↔ α.hom.hom ≠ 1 ∧
      @TorusCharacterTangent.weightSpace F _ T B a α ≠ ⊥)
    (hρ : ρ.hom.hom ^ 2 = (Φ.map (fun α ↦ α.hom.hom)).prod)
    (hρB : j ≫ ρB = ρ)
    (hρU : ∀ (V : Grp (Over (Spec (.of F)))) (l : V ⟶ B),
      IsClosedSubgroupScheme l.hom.hom → IsNormalSubgroupScheme l.hom.hom →
      ConnectedSpace V.X.left → SolvableGroupStructure.IsUnipotent V →
        l.hom.hom ≫ ρB.hom.hom = 1)
    (hχ : χ.hom.hom = ρB.hom.hom⁻¹)
    (Q : Over (Spec (.of F))) (π : S.X ⟶ Q)
    (hQ : IsProper Q.hom) (hQft : LocallyOfFiniteType Q.hom) (hQqc : QuasiCompact Q.hom)
    (hπflat : Flat π.left) (hπsurj : Surjective π.left)
    (hπinv : (fst S.X B.X * (snd S.X B.X ≫ iB.hom.hom)) ≫ π = fst S.X B.X ≫ π)
    (hπtorsor : IsPullback (fst S.X B.X)
      (fst S.X B.X * (snd S.X B.X ≫ iB.hom.hom)) π π)
    (P : AssociatedCharacterLineBundle.Presentation S B iB Q π χ)
    (hL : P.L.IsInvertible) :
    IsIntegral (Q ⊗ Q).left ∧ QuasiCompact (Q ⊗ Q).hom ∧ IsSeparated (Q ⊗ Q).hom ∧
    ∃ (n₀ : RankOneRoots.normalizer iT) (d : Γ(DoubleFlag.externalSquare Q P.L, ⊤)),
      d ≠ 0 ∧
      (∀ (Z : Over (Spec (.of F))) (s g h : Z ⟶ S.X),
        DoubleFlag.coefficient π P.L P.trivialization (s * g) (s * h) d =
          DoubleFlag.coefficient π P.L P.trivialization g h d) ∧
      (∀ Z : Over (Spec (.of F)),
        {g : Z ⟶ S.X | g ∈ RankOneRoots.pointImage iB Z ∧
          ∃ b : Z ⟶ B.X, g = (toUnit Z ≫ n₀.val) * (b ≫ iB.hom.hom) *
            (toUnit Z ≫ n₀.val)⁻¹} = (RankOneRoots.pointImage iT Z : Set _)) ∧
      ∃ (U : (Q ⊗ Q).left.Opens) (q : S.X ⟶ Over.mk (U.ι ≫ (Q ⊗ Q).hom))
        (aU : ModObj S.X (Over.mk (U.ι ≫ (Q ⊗ Q).hom))),
        (U : Set (Q ⊗ Q).left) =
          Scheme.Modules.nonvanishingLocus (DoubleFlag.externalSquare Q P.L) d ∧
        Dense (U : Set (Q ⊗ Q).left) ∧
        q.left ≫ U.ι = (lift π ((𝟙 S.X * (toUnit S.X ≫ n₀.val)) ≫ π)).left ∧
        Flat q.left ∧ Surjective q.left ∧
        (fst S.X T.X * (snd S.X T.X ≫ iT.hom.hom)) ≫ q = fst S.X T.X ≫ q ∧
        IsPullback (fst S.X T.X)
          (fst S.X T.X * (snd S.X T.X ≫ iT.hom.hom)) q q ∧
        (∀ (Z : Over (Spec (.of F))) (s g : Z ⟶ S.X),
          lift s (g ≫ q) ≫ aU.smul = (s * g) ≫ q) ∧
        ∃ e : RhoSection.Coordinate (Over.mk (U.ι ≫ (Q ⊗ Q).hom)) ≃ₐ[F]
          DoubleFlag.rightInvariants iT,
          (∀ r, (e r).val = ((algΓ (.of F)).map q).unop.hom r) ∧
          ∀ (Z : Over (Spec (.of F))) (s g : Z ⟶ S.X)
            (r : RhoSection.Coordinate (Over.mk (U.ι ≫ (Q ⊗ Q).hom))),
            ((algΓ (.of F)).map (s⁻¹ * g)).unop.hom (e r).val =
              ((algΓ (.of F)).map (lift s⁻¹ (g ≫ q) ≫ aU.smul)).unop.hom r := by
  sorry

end AlgebraicGeometry
